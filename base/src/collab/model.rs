use crate::collab::bind::Host;
use crate::collab::formula::{FormulaRefs, StableFormula};
use crate::collab::fractional_index::{FractionalIndex, FractionalKey, SESSION_SUFFIX_LEN};
use crate::collab::log::{Commit, Lww, SessionId, Timestamp};
use crate::collab::patch::{
    CfPropKind, DefinedNameBody, DefinedNameId, NamedStyle, NamedStyleId, Patch, PropKind, SheetId,
    SheetPropKind, WorkbookPropKind,
};
use crate::constants::{COLUMN_WIDTH_FACTOR, DEFAULT_COLUMN_WIDTH};
use crate::expressions::parser::Parser;
use crate::language::get_default_language;
use crate::locale::get_default_locale;
use crate::model::Model;
use crate::new_empty::{APPLICATION, APP_VERSION, IRONCALC_USER};
use crate::types::{
    sealed::Sealed, Cell, Metadata, Position, RangeRef, Row, Workbook, WorkbookSettings, Worksheet,
};
use crate::tz::Tz;
use bitcode::{Decode, Encode};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

/// What a replica assumes until a peer writes the workbook's locale and timezone registers.
const DEFAULT_LOCALE: &str = "en";
const DEFAULT_TIMEZONE: &str = "UTC";

/// Stable addressing: rows and columns are named by the [`FractionalKey`] they were minted with, and
/// where they currently sit lives in the sheet's [`StableIndexes`] rather than in the name.
///
/// The derives mirror [`Ordinal`](crate::types::Ordinal)'s: they are what the `#[derive]`s on the
/// generic containers, which emit `A: Trait` bounds, ask of the marker.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Encode, Decode, Serialize, Deserialize,
)]
pub struct Stable;

impl Sealed for Stable {}

impl Stable {
    pub(crate) fn row_ordinal(idx: &StableIndexes, key: &FractionalKey) -> Option<i32> {
        idx.rows.position_of(key).map(|p| p as i32 + 1)
    }

    pub(crate) fn col_ordinal(idx: &StableIndexes, key: &FractionalKey) -> Option<i32> {
        idx.cols.position_of(key).map(|p| p as i32 + 1)
    }

    pub(crate) fn row_at(idx: &StableIndexes, ordinal: i32) -> Option<FractionalKey> {
        if ordinal < 1 {
            return None;
        }
        idx.rows.key(ordinal as usize - 1).cloned()
    }

    pub(crate) fn col_at(idx: &StableIndexes, ordinal: i32) -> Option<FractionalKey> {
        if ordinal < 1 {
            return None;
        }
        idx.cols.key(ordinal as usize - 1).cloned()
    }
}

impl Stable {
    /// Takes the spill cell at `(row, column)` out of the slot, putting back the styled empty cell
    /// it covered, if any.
    pub(crate) fn uncover(sheet: &mut Worksheet<Stable>, row: i32, column: i32) {
        match sheet.index.covered.remove(&(row, column)) {
            Some(s) => {
                sheet
                    .sheet_data
                    .set_cell(row, column, Cell::EmptyCell { s });
            }
            None => {
                sheet.sheet_data.remove_cell(row, column);
            }
        }
    }
}

impl Position for Stable {
    type SheetIndex = StableIndexes;
    type WorkbookMeta = WorkbookMeta;
    type Local = CollabSession;
    type UserState = StableUserState;

    const CSE_SPILLS: bool = true;

    fn spill_written(
        sheet: &mut Worksheet<Stable>,
        row: i32,
        column: i32,
        replaced: Option<&Cell>,
    ) {
        sheet.index.spills.0.push((row, column));
        if let Some(Cell::EmptyCell { s }) = replaced {
            if *s != 0 {
                sheet.index.covered.insert((row, column), *s);
            }
        }
    }

    fn drop_spills(sheet: &mut Worksheet<Stable>) {
        let mut spills = std::mem::take(&mut sheet.index.spills.0);
        // Stale or repeated entries no longer hold a spill: skip them.
        for &(row, column) in &spills {
            let cell = sheet.sheet_data.cell(row, column);
            if matches!(cell.as_deref(), Some(Cell::SpillCell { .. })) {
                Stable::uncover(sheet, row, column);
            }
        }
        sheet.index.covered.clear();
        // Keep the capacity for the next evaluate.
        spills.clear();
        sheet.index.spills.0 = spills;
    }

    fn clear_spill(sheet: &mut Worksheet<Stable>, row: i32, column: i32) -> Result<(), String> {
        Stable::uncover(sheet, row, column);
        Ok(())
    }
}

/// Same as [`Link`](crate::types::Link), but an internal location uses stable addressing pattern.
#[derive(Clone, Debug, PartialEq, Encode, Decode)]
pub enum StableLink {
    External {
        target: String,
        tooltip: Option<String>,
    },
    Internal {
        location: StableFormula,
        tooltip: Option<String>,
    },
}

/// A [`Comment`](crate::types::Comment) without its cell: what a comment patch carries, and what
/// [`StableIndexes::comments`] holds by key.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode)]
pub struct CommentBody {
    pub text: String,
    pub author_name: String,
    pub author_id: Option<String>,
}

/// The state a column span holds: what [`StableIndexes::col_spans`] keeps per span, and what the
/// ordinal `cols` records are derived from.
///
/// A span under stable addressing is a *region*, not a fixed set of columns: it covers whatever
/// currently sits between its two corner keys, exactly as [`StableRange`]'s column axis does (see
/// [`resolve_axis`]). Consequences:
///
/// - A column moved out of the region loses the span's properties, and one moved in gains them.
///   That is not Excel's behaviour, but Excel has no concurrent semantics to be faithful to.
/// - A single-column span `(k, k)` follows its column wherever it moves.
/// - A [`FractionalKey::NULL`] corner is an open end, so `(NULL, NULL)` is the storable whole-axis
///   span — the register `set_style` over the whole sheet writes to.
/// - Only concurrency can produce overlapping spans; those resolve per position and per property
///   by register write timestamp — LWW, newest covering span wins — when `cols` is derived.
#[derive(Clone, Debug, PartialEq, Encode, Decode)]
pub struct ColSpan {
    pub width: f64,
    pub custom_width: bool,
    pub hidden: bool,
    pub style: Option<i32>,
}

impl Default for ColSpan {
    fn default() -> Self {
        ColSpan {
            width: DEFAULT_COLUMN_WIDTH / COLUMN_WIDTH_FACTOR,
            custom_width: false,
            hidden: false,
            style: None,
        }
    }
}

/// Undo/redo for a collaborative [`UserModel`](crate::UserModel): stacks of the patches a local
/// action emitted. Declared here, but not consumed until a later round wires undo/redo up.
#[derive(Default)]
pub struct StableUserState {
    pub undo_stack: Vec<Vec<Patch>>,
    pub redo_stack: Vec<Vec<Patch>>,
}

#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct StableIndexes {
    pub rows: FractionalIndex,
    pub cols: FractionalIndex,
    pub registers: SheetRegisters,
    pub parents: HashMap<StableCellAddress, NamedStyleId>,
    /// Deleted rows that still hold a property. We may need to revive them via undo or InsertRows.
    pub hidden_rows: HashMap<FractionalKey, Row>,
    /// Index for cell's own style, if that cell was spilled over.
    pub covered: HashMap<(i32, i32), i32>,
    /// Every merged range, including those that currently resolve to nothing, sorted and
    /// deduplicated. The worksheet's `merged_cells` holds the ones that resolve.
    pub merges: Vec<StableRange>,
    /// The state every column span was written to; the worksheet's `cols` is derived from it.
    pub col_spans: HashMap<(FractionalKey, FractionalKey), ColSpan>,
    /// Comments by cell; the worksheet's `comments` holds the ones whose cell is visible.
    pub comments: HashMap<StableCellAddress, CommentBody>,
    /// Links by cell; the worksheet's `links` holds the ones whose cell is visible.
    pub links: HashMap<StableCellAddress, StableLink>,
    /// Each conditional formatting rule's ranges, by rule key; the rule's ordinal ranges are
    /// derived from them.
    pub cf_ranges: HashMap<FractionalKey, Vec<StableRange>>,
    /// Where spills were written since the last drop; may list a slot twice or one that has since
    /// been overwritten. Rebuilt by one scan on decode.
    #[bitcode(skip)]
    pub spills: Hint<Vec<(i32, i32)>>,
    /// Whether a reorder this commit moved something the sheet's formulas may reference: set when
    /// the index's [`Reorder`](super::fractional_index::Reorder)s are followed, swept into
    /// [`Dirty::sheets`] at the end of the commit.
    #[bitcode(skip)]
    pub reordered: Hint<bool>,
    /// Derived records a commit's writes invalidated; swept by `resync_derived`.
    #[bitcode(skip)]
    pub(crate) derive: Hint<Derive>,
    /// `formulas[f]` describes `shared_formulas[f]`: the cell its text is relative to, and its
    /// slots.
    pub formulas: Vec<FormulaRefs>,
    /// The entries of this sheet holding a slot on a given sheet, the host's own included. Derived
    /// from `formulas`: not encoded, rebuilt on decode.
    #[bitcode(skip)]
    pub referenced_by: HashMap<SheetId, HashSet<u32>>,
    /// The entries of this sheet holding a slot on a given defined name. Derived, as above.
    #[bitcode(skip)]
    pub names_referenced_by: HashMap<DefinedNameId, HashSet<u32>>,
    /// The entries of this sheet holding an unbound slot. Derived, as above.
    #[bitcode(skip)]
    pub unbound: HashSet<u32>,
}

impl StableIndexes {
    pub(crate) fn new(suffix: [u8; 4]) -> Self {
        StableIndexes {
            rows: FractionalIndex::new(vec![], vec![], suffix),
            cols: FractionalIndex::new(vec![], vec![], suffix),
            ..Default::default()
        }
    }

    /// Register entry `f` in the reverse sets; `host` is the id of the sheet it lives on.
    pub(crate) fn register_formula(&mut self, f: u32, host: SheetId) {
        let Some(entry) = self.formulas.get(f as usize) else {
            return;
        };
        for sheet in entry.sheets(host) {
            self.referenced_by.entry(sheet).or_default().insert(f);
        }
        for name in entry.names() {
            self.names_referenced_by.entry(name).or_default().insert(f);
        }
        if entry.unresolved() {
            self.unbound.insert(f);
        }
    }

    /// Takes entry `f` out of the reverse sets, dropping the sets it leaves empty so that equal
    /// `formulas` give equal sets.
    pub(crate) fn unregister_formula(&mut self, f: u32, host: SheetId) {
        let Some(entry) = self.formulas.get(f as usize) else {
            return;
        };
        for sheet in entry.sheets(host) {
            if let Some(set) = self.referenced_by.get_mut(&sheet) {
                set.remove(&f);
                if set.is_empty() {
                    self.referenced_by.remove(&sheet);
                }
            }
        }
        for name in entry.names() {
            if let Some(set) = self.names_referenced_by.get_mut(&name) {
                set.remove(&f);
                if set.is_empty() {
                    self.names_referenced_by.remove(&name);
                }
            }
        }
        self.unbound.remove(&f);
    }
}

/// Local bookkeeping kept inside [StableIndexes] next to the document state: it never takes part
/// in equality, and it is never encoded.
#[derive(Clone, Debug, Default)]
pub struct Hint<T>(pub T);

impl<T> PartialEq for Hint<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

/// Which derived records of a sheet a commit invalidated. See `derive_sparse`.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(crate) struct Derive(u8);

impl Derive {
    pub(crate) const NONE: Derive = Derive(0);
    pub(crate) const COLS: Derive = Derive(1);
    pub(crate) const MERGES: Derive = Derive(2);
    pub(crate) const COMMENTS: Derive = Derive(4);
    pub(crate) const LINKS: Derive = Derive(8);
    pub(crate) const CF: Derive = Derive(16);
    pub(crate) const ALL: Derive = Derive(31);

    pub(crate) fn has(self, flag: Derive) -> bool {
        self.0 & flag.0 != 0
    }
}

impl std::ops::BitOrAssign for Derive {
    fn bitor_assign(&mut self, rhs: Derive) {
        self.0 |= rhs.0
    }
}

/// The last-write guard of every register a sheet owns: only the [`Timestamp`] that last won each,
/// never the value — values stay unwrapped in the worksheet's ordinary fields, as under ordinal
/// addressing.
///
/// An entry outlives its subject: deleting a row keeps its cells' guards, so a concurrent write to
/// one of them older than the delete loses to it. A newer one brings the row back.
#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct SheetRegisters {
    pub cell_values: HashMap<StableCellAddress, Timestamp>,
    pub cell_styles: HashMap<(StableCellAddress, PropKind), Timestamp>,
    pub rows: HashMap<(FractionalKey, PropKind), Timestamp>,
    pub col_spans: HashMap<((FractionalKey, FractionalKey), PropKind), Timestamp>,
    pub props: HashMap<SheetPropKind, Timestamp>,
    pub merges: HashMap<StableRange, Timestamp>,
    pub comments: HashMap<StableCellAddress, Timestamp>,
    pub links: HashMap<StableCellAddress, Timestamp>,
    pub cf: HashMap<(FractionalKey, CfPropKind), Timestamp>,
    /// CF rule identity ↔ storage order; kept sorted, position = priority.
    pub cf_order: Vec<FractionalKey>,
    /// Where a rule sits, for the rules that were ever moved. Position keys are CRDT-only state,
    /// so the value sits with its guard, as in [`WorkbookMeta::sheet_positions`].
    pub cf_positions: HashMap<FractionalKey, Lww<FractionalKey>>,
    /// The bound form of each rule's formula slots, in slot order. The strings the rule itself
    /// carries are derived from these, the way `Workbook::defined_names` is derived.
    pub cf_formulas: HashMap<FractionalKey, Vec<DefinedNameBody>>,
}

/// Workbook-wide registers: those outliving the sheet they talk about, and those no sheet owns.
#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct WorkbookMeta {
    /// AddSheet/DeleteSheet LWW; entries survive deletion (resurrection guard).
    pub sheet_existence: HashMap<u32, Timestamp>,
    /// Tab-order register; the position key is CRDT-only state, so value sits with its guard.
    pub sheet_positions: HashMap<u32, Lww<FractionalKey>>,
    /// Authored sheet names. `Worksheet::name` is the *display* name, derived from these and
    /// repaired for collisions, so the value sits with its guard.
    pub sheet_names: HashMap<u32, Lww<String>>,
    pub props: HashMap<WorkbookPropKind, Timestamp>,
    /// Defined names; entries survive deletion (resurrection guard).
    pub defined_names: HashMap<DefinedNameId, DefinedNameState>,
    /// Named styles; entries survive deletion (resurrection guard).
    pub named_styles: HashMap<NamedStyleId, NamedStyleState>,
    /// The `cell_style_xfs` slot each named style owns.
    pub style_xf: HashMap<NamedStyleId, i32>,
}

#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct DefinedNameState {
    /// The authored scope and name. A scope move is address-shaped like a rename, so one register
    /// carries both and a concurrent redefinition of the formula still survives.
    pub name: Lww<(Option<SheetId>, String)>,
    /// `None` is a deleted name: the entry and its address survive, so an undo can revive it.
    pub formula: Lww<Option<DefinedNameBody>>,
}

/// A named style's two registers. Both are CRDT-only state — the style table shows a *display* name
/// and a locally interned `xf_id` — so each value sits with its own guard, as in
/// [`WorkbookMeta::sheet_positions`].
#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct NamedStyleState {
    /// The authored name, which the display name is derived from and repaired for collisions.
    pub name: Lww<String>,
    /// `None` is a deleted style: the entry and its name survive, so an undo can revive it.
    pub definition: Lww<Option<Box<NamedStyle>>>,
}

/// A description of a continuous range of cells, described using stable identifiers, which can be
/// used to keep track of cell position under various concurrent operations (ex. adding/removing
/// rows or columns). A `None` axis is the whole axis.
#[derive(Encode, Decode, Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct StableRange {
    pub rows: Option<(FractionalKey, FractionalKey)>,
    pub cols: Option<(FractionalKey, FractionalKey)>,
}

/// A cell position, described using stable identifiers, which can be used to keep track of cell
/// position under various concurrent operations (ex. adding/removing rows or columns).
pub type StableCellAddress = (FractionalKey, FractionalKey);

/// Where one axis of a [`StableRange`] currently sits, as a 1-based closed interval.
///
/// A corner that still resolves keeps its identity. One that does not — deleted, or never in this
/// index — clamps to where it would now sit: the `lo` corner takes the element that took its place,
/// the `hi` corner the one just before it. A [`FractionalKey::NULL`] corner is not a position at
/// all but an open end. `None` means clamping collapsed the span.
pub(crate) fn resolve_axis(
    index: &FractionalIndex,
    span: &Option<(FractionalKey, FractionalKey)>,
) -> Option<(i32, i32)> {
    // Open on both ends is the whole axis, exactly as `None` is.
    let span = span
        .as_ref()
        .filter(|(lo, hi)| !lo.is_empty() || !hi.is_empty());
    let Some((lo, hi)) = span else {
        return Some((1, index.len() as i32));
    };
    // An open end takes the axis' extreme, and has to do so before the clamping path below: NULL
    // sorts under every real key, so `lower_bound` would put an open *upper* bracket at 0.
    let lo_ord = if lo.is_empty() {
        Some(1)
    } else {
        index.position_of(lo).map(|p| p as i32 + 1)
    };
    let hi_ord = if hi.is_empty() {
        Some(index.len() as i32)
    } else {
        index.position_of(hi).map(|p| p as i32 + 1)
    };
    match (lo_ord, hi_ord) {
        // Concurrent moves can invert the corners; the rectangle they bound is still the same one.
        (Some(lo), Some(hi)) => Some((lo.min(hi), lo.max(hi))),
        (lo_ord, hi_ord) => {
            let lo = lo_ord.unwrap_or_else(|| index.active_index(lo) as i32 + 1);
            let hi = hi_ord.unwrap_or_else(|| index.active_index(hi) as i32);
            (lo <= hi).then_some((lo, hi))
        }
    }
}

impl StableRange {
    /// The 1-based ordinal rectangle `(row1, column1, row2, column2)` this currently denotes, or
    /// `None` if it collapsed. An unbounded axis spans whatever the index holds right now.
    pub fn resolve(&self, idx: &StableIndexes) -> Option<(i32, i32, i32, i32)> {
        let (row1, row2) = resolve_axis(&idx.rows, &self.rows)?;
        let (column1, column2) = resolve_axis(&idx.cols, &self.cols)?;
        Some((row1, column1, row2, column2))
    }

    pub(crate) fn merged_rect(&self, idx: &StableIndexes) -> Option<(i32, i32, i32, i32)> {
        self.resolve(idx)
            .filter(|(r1, c1, r2, c2)| (r1, c1) != (r2, c2))
    }

    pub fn to_ordinal(&self, idx: &StableIndexes) -> Option<RangeRef> {
        let (row1, column1, row2, column2) = self.resolve(idx)?;
        Some(RangeRef {
            rows: self.rows.as_ref().map(|_| (row1, row2)),
            cols: self.cols.as_ref().map(|_| (column1, column2)),
        })
    }

    pub fn contains(&self, idx: &StableIndexes, row: &FractionalKey, col: &FractionalKey) -> bool {
        let Some((row1, column1, row2, column2)) = self.resolve(idx) else {
            return false;
        };
        match (Stable::row_ordinal(idx, row), Stable::col_ordinal(idx, col)) {
            (Some(r), Some(c)) => (row1..=row2).contains(&r) && (column1..=column2).contains(&c),
            _ => false,
        }
    }
}

impl Worksheet<Stable> {
    pub(crate) fn row_by_index(&self, ordinal: i32) -> Option<&Row> {
        let at = self.rows.binary_search_by_key(&ordinal, |r| r.r).ok()?;
        self.rows.get(at)
    }

    pub(crate) fn row_by_key(&self, key: &FractionalKey) -> Option<&Row> {
        match self.index.rows.position_of(key) {
            Some(p) => self.row_by_index(p as i32 + 1),
            None => self.index.hidden_rows.get(key),
        }
    }

    /// The ordinal `(row, column)` cell `at` sits at, `None` when its row or column is not visible.
    pub(crate) fn ordinal(&self, at: &StableCellAddress) -> Option<(i32, i32)> {
        Some((
            Stable::row_ordinal(&self.index, &at.0)?,
            Stable::col_ordinal(&self.index, &at.1)?,
        ))
    }

    /// The style patches wrote at `(row, column)`, `None` for no cell. A spill's own style comes
    /// from the row or column at evaluation time, which replicas see at different moments: what a
    /// spill answers is the authored style it covers.
    pub(crate) fn authored_style(&self, (row, column): (i32, i32)) -> Option<i32> {
        match &*self.sheet_data.cell(row, column)? {
            Cell::SpillCell { .. } => self.index.covered.get(&(row, column)).copied(),
            cell => Some(cell.get_style()),
        }
    }
    /// Where the host of a formula entry sits: its ordinal, or, while its row or column is hidden,
    /// where it would sit. Any fixed choice keeps the entry a function of the index.
    pub(crate) fn host_of(&self, sheet_id: usize, at: &StableCellAddress) -> Host {
        let place = |index: &FractionalIndex, key: &FractionalKey| {
            index
                .position_of(key)
                .unwrap_or_else(|| index.active_index(key)) as i32
                + 1
        };
        Host::relative(
            sheet_id as u32,
            place(&self.index.rows, &at.0),
            place(&self.index.cols, &at.1),
        )
    }

    /// The record a row property is written to: at its ordinal in `rows` while the row is visible
    /// (created there if absent), in `hidden_rows` while it is not.
    pub fn row_mut(&mut self, identity: &FractionalKey) -> &mut Row {
        let Some(p) = self.index.rows.position_of(identity) else {
            let hidden = &mut self.index.hidden_rows;
            return hidden
                .entry(identity.clone())
                .or_insert_with(|| Row::new(0));
        };
        let r = p as i32 + 1;
        match self.rows.binary_search_by_key(&r, |row| row.r) {
            Ok(at) => &mut self.rows[at],
            Err(at) => self.rows.insert_mut(at, Row::new(r)),
        }
    }
}

/// A collaborative model: the evaluation engine running directly on stably addressed storage.
pub type CollabModel<'a> = Model<'a, Stable>;

/// The replica-local half of a [`CollabModel`]: who we are, and what we have not shipped yet.
#[derive(Debug, Default)]
pub struct CollabSession {
    /// This replica's identity: the suffix of every [`FractionalKey`] it mints.
    pub session: SessionId,
    /// Commits produced locally and not yet handed to the log.
    pub pending: Vec<Commit>,
    /// What the commit being applied changed that lowered formulas depend on.
    pub(crate) dirty: Dirty,
    /// How each live defined name lowers into a formula, as of the last commit: a name whose view
    /// changes re-lowers its users.
    pub(crate) name_views: Vec<(DefinedNameId, NameView)>,
    /// Whenever formula couldn't bind name to specific defined_name_id or sheet_id (eg. because
    /// they were not created yet) it will land here and rebound when an object with relevant name
    /// has been defined.
    pub(crate) unresolved: HashMap<String, HashSet<(SheetId, StableCellAddress)>>,
    /// How many commits took the full (structural) `resync_derived` path.
    #[cfg(test)]
    pub(crate) full_resyncs: u64,
}

/// What a commit changed that lowered formulas read, collected while its patches apply and
/// consumed once at its end.
#[derive(Debug, Default)]
pub(crate) struct Dirty {
    /// Sheets whose rows or columns moved other than by a tail append, or that were added, deleted,
    /// renamed or moved in the tab order: their `referenced_by` entries re-lower.
    pub(crate) sheets: HashSet<SheetId>,
    /// Defined names whose lowered form may have changed: their users re-lower.
    pub(crate) names: HashSet<DefinedNameId>,
    /// Whether a sheet or a name appeared, went or was renamed, so unbound names may resolve
    /// differently.
    pub(crate) unbound: bool,
    /// Whether the defined names and the parse tables need re-deriving.
    pub(crate) structural: bool,
}

/// What a defined name lowers to inside a formula: its display name, the position of its scope
/// sheet (`None` when global, `Some(None)` when the sheet is gone) and the text of its body.
pub(crate) type NameView = (String, Option<Option<u32>>, String);

impl CollabModel<'static> {
    /// An empty replica: a workbook with **no sheets at all**, since every sheet arrives as a
    /// [`Patch::AddSheet`](crate::collab::patch::Patch::AddSheet) like any other write.
    ///
    /// `session` is this replica's identity and the suffix of every [`FractionalKey`] it mints, so
    /// it must be non-zero: the all-zero suffix is
    /// [`virtual_key`](crate::collab::fractional_index::virtual_key)'s.
    #[allow(clippy::expect_used)]
    pub fn new(session: SessionId) -> Self {
        debug_assert!(session != 0, "session 0 is reserved for virtual keys");
        let locale = get_default_locale();
        let language = get_default_language();
        let workbook = Workbook {
            shared_strings: vec![],
            defined_names: vec![],
            worksheets: vec![],
            styles: Default::default(),
            name: String::new(),
            settings: WorkbookSettings {
                tz: DEFAULT_TIMEZONE.to_string(),
                locale: DEFAULT_LOCALE.to_string(),
            },
            // Not a replicated register: blank rather than clock-stamped, so two replicas of the
            // same log stay byte-for-byte equal.
            metadata: Metadata {
                application: APPLICATION.to_string(),
                app_version: APP_VERSION.to_string(),
                creator: IRONCALC_USER.to_string(),
                last_modified_by: IRONCALC_USER.to_string(),
                created: String::new(),
                last_modified: String::new(),
            },
            tables: HashMap::new(),
            theme: Default::default(),
            meta: Default::default(),
        };
        CollabModel {
            workbook,
            parsed_formulas: Vec::new(),
            parsed_defined_names: HashMap::new(),
            shared_strings: HashMap::new(),
            parser: Parser::new(vec![], vec![], HashMap::new(), locale, language),
            locale,
            language,
            tz: Tz::parse(DEFAULT_TIMEZONE).expect("UTC is a valid timezone"),
            variable_stack: HashMap::new(),
            last_variable_id: 0,
            lambdas: HashMap::new(),
            last_lambda_id: 0,
            evaluation: Default::default(),
            cf_cache: HashMap::new(),
            links: HashMap::new(),
            shared_formula_lookup: Vec::new(),
            local: CollabSession {
                session,
                ..Default::default()
            },
        }
    }
}

impl CollabModel<'_> {
    /// The suffix this replica mints [`FractionalKey`]s with.
    pub(crate) fn suffix(&self) -> [u8; SESSION_SUFFIX_LEN] {
        self.local.session.to_be_bytes()
    }
}

// Two of these build stable storage out of an ordinal model, through a helper `collab-test` gates.
#[cfg(all(test, not(feature = "collab-test")))]
mod test {
    use super::*;
    use crate::cf_types::{CfRuleInput, ValueOperator};
    use crate::types::{Cell, Color, Dxf, Fill, Row, SheetData, SheetState, Worksheet};

    fn mint(index: &mut FractionalIndex, count: usize) -> Vec<FractionalKey> {
        (0..count)
            .map(|i| index.create_key(i).expect("index has room").clone())
            .collect()
    }

    #[test]
    fn stable_worksheet_round_trip() {
        let mut index = StableIndexes::new([b'x', 0, 0, 0]);
        let rows = mint(&mut index.rows, 5);
        let cols = mint(&mut index.cols, 3);

        // Cells sit at the ordinal their keys have in the index.
        let mut sheet_data = SheetData::new();
        for r in 0..rows.len() {
            for c in 0..cols.len() {
                let cell = Cell::NumberCell {
                    v: (10 * r + c) as f64,
                    s: 0,
                };
                sheet_data.set_cell(r as i32 + 1, c as i32 + 1, cell);
            }
        }

        // The keyed sources live in the index, and travel with it.
        let mut index = index;
        index.col_spans.insert(
            (cols[1].clone(), cols[1].clone()),
            ColSpan {
                width: 42.0,
                custom_width: true,
                hidden: false,
                style: Some(0),
            },
        );
        index.merges.push(StableRange {
            rows: Some((rows[0].clone(), rows[1].clone())),
            cols: Some((cols[0].clone(), cols[1].clone())),
        });
        index.comments.insert(
            (rows[3].clone(), cols[2].clone()),
            CommentBody {
                text: "note".to_string(),
                author_name: "me".to_string(),
                author_id: None,
            },
        );
        let mut ws = Worksheet::<Stable> {
            dimension: "A1:C5".to_string(),
            cols: vec![],
            rows: vec![Row {
                r: 3,
                height: 21.0,
                custom_format: false,
                custom_height: true,
                s: 0,
                hidden: false,
            }],
            name: "Stable".to_string(),
            sheet_data,
            shared_formulas: vec![],
            sheet_id: 1,
            state: SheetState::Visible,
            color: Color::None,
            merged_cells: vec![],
            comments: vec![],
            frozen_rows: 0,
            frozen_columns: 0,
            show_grid_lines: true,
            conditional_formatting: vec![],
            links: HashMap::new(),
            index,
        };

        // 1. Resolution is a round trip on both axes, and answers nothing for a key it never saw.
        for (i, key) in rows.iter().enumerate() {
            let ordinal = i as i32 + 1;
            assert_eq!(Stable::row_ordinal(&ws.index, key), Some(ordinal));
            assert_eq!(Stable::row_at(&ws.index, ordinal).as_ref(), Some(key));
        }
        for (i, key) in cols.iter().enumerate() {
            let ordinal = i as i32 + 1;
            assert_eq!(Stable::col_ordinal(&ws.index, key), Some(ordinal));
            assert_eq!(Stable::col_at(&ws.index, ordinal).as_ref(), Some(key));
        }
        let stranger = FractionalKey::from([0xffu8, 0, 0, 0, 0].as_slice());
        assert_eq!(Stable::row_ordinal(&ws.index, &stranger), None);
        assert_eq!(Stable::col_ordinal(&ws.index, &stranger), None);
        assert_eq!(Stable::row_at(&ws.index, 0), None);
        assert_eq!(Stable::row_at(&ws.index, 6), None);

        // 2. A read by keys is a resolution followed by a read by ordinal.
        let cell_at = |ws: &Worksheet<Stable>, row: &FractionalKey, col: &FractionalKey| {
            let r = Stable::row_ordinal(&ws.index, row)?;
            let c = Stable::col_ordinal(&ws.index, col)?;
            ws.sheet_data.cell(r, c).map(|cell| cell.into_owned())
        };
        let number = |v: f64| Some(Cell::NumberCell { v, s: 0 });
        assert_eq!(cell_at(&ws, &rows[1], &cols[2]), number(12.0));

        // 3. A move of the index is followed by the same move of the cells, so each cell keeps the
        //    keys it was written under.
        ws.index.rows.move_to(0..1, 5); // first row to the end
        ws.sheet_data.move_row(1, 5);
        ws.rows[0].r = 2; // and so does the row record
        assert_eq!(Stable::row_ordinal(&ws.index, &rows[0]), Some(5));
        assert_eq!(Stable::row_ordinal(&ws.index, &rows[1]), Some(1));
        assert_eq!(cell_at(&ws, &rows[0], &cols[2]), number(2.0));
        assert_eq!(cell_at(&ws, &rows[1], &cols[2]), number(12.0));
        assert_eq!(ws.sheet_data.cell(5, 3).as_deref(), number(2.0).as_ref());

        // 4. A removal takes the key out of the ordering and its row out of the cells, shifting
        //    everything after it up.
        ws.index.rows.remove_key(&rows[1]);
        ws.sheet_data.remove_rows(1, 1);
        ws.rows[0].r = 1;
        assert_eq!(Stable::row_ordinal(&ws.index, &rows[1]), None);
        assert_eq!(Stable::row_ordinal(&ws.index, &rows[2]), Some(1));
        assert_eq!(Stable::row_ordinal(&ws.index, &rows[0]), Some(4));
        assert_eq!(cell_at(&ws, &rows[2], &cols[2]), number(22.0));

        // 5. The whole sheet survives bitcode, ordering context included.
        let decoded: Worksheet<Stable> = bitcode::decode(&bitcode::encode(&ws)).unwrap();
        assert_eq!(decoded, ws);
        assert_eq!(Stable::row_ordinal(&decoded.index, &rows[2]), Some(1));
        assert_eq!(Stable::col_at(&decoded.index, 3).as_ref(), Some(&cols[2]));
        assert_eq!(cell_at(&decoded, &rows[2], &cols[2]), number(22.0));
    }

    #[test]
    fn stable_range_resolve_and_clamp() {
        let mut index = StableIndexes::new([b'x', 0, 0, 0]);
        let rows = mint(&mut index.rows, 6);
        let cols = mint(&mut index.cols, 4);

        let rect = StableRange {
            rows: Some((rows[1].clone(), rows[4].clone())),
            cols: Some((cols[0].clone(), cols[2].clone())),
        };
        assert_eq!(rect.resolve(&index), Some((2, 1, 5, 3)));
        assert!(rect.contains(&index, &rows[2], &cols[1]));
        assert!(!rect.contains(&index, &rows[0], &cols[1])); // above the rectangle

        // An unbounded axis is whatever the index holds right now, so it grows with the index.
        let full_rows = StableRange {
            rows: None,
            cols: Some((cols[0].clone(), cols[2].clone())),
        };
        assert_eq!(full_rows.resolve(&index), Some((1, 1, 6, 3)));
        index.rows.create_key(6);
        assert_eq!(full_rows.resolve(&index), Some((1, 1, 7, 3)));
        assert_eq!(rect.resolve(&index), Some((2, 1, 5, 3)));

        // Concurrent moves can drag the lo corner past the hi one; the resolved rectangle stays
        // ordered, because two corners that still resolve bound the same rectangle either way.
        index.rows.move_to(1..2, 5);
        assert_eq!(rect.resolve(&index), Some((4, 1, 5, 3)));
        index.rows.move_to(4..5, 1);
        assert_eq!(rect.resolve(&index), Some((2, 1, 5, 3)));

        // Deleting the hi corner clamps it to the element just before where it used to sit.
        index.rows.remove_key(&rows[4]);
        assert_eq!(rect.resolve(&index), Some((2, 1, 4, 3)));

        // Deleting everything the rectangle covered collapses it.
        for key in [&rows[1], &rows[2], &rows[3]] {
            index.rows.remove_key(key);
        }
        assert_eq!(rect.resolve(&index), None);
        assert!(!rect.contains(&index, &rows[0], &cols[0]));
    }

    #[test]
    fn stable_col_span_semantics() {
        let mut index = StableIndexes::new([b'x', 0, 0, 0]);
        let cols = mint(&mut index.cols, 6);
        // A span resolves as a range's column axis does.
        struct Span(FractionalKey, FractionalKey);
        impl Span {
            fn resolve(&self, index: &StableIndexes) -> Option<(i32, i32)> {
                resolve_axis(&index.cols, &Some((self.0.clone(), self.1.clone())))
            }
        }
        let span = |min: &FractionalKey, max: &FractionalKey| Span(min.clone(), max.clone());
        let wide = span(&cols[0], &cols[3]);
        assert_eq!(wide.resolve(&index), Some((1, 4)));

        // A span is a region between its corners; the degenerate `(k, k)` follows its column.
        let single = span(&cols[4], &cols[4]);
        assert_eq!(single.resolve(&index), Some((5, 5)));
        index.cols.move_to(4..5, 6);
        assert_eq!(single.resolve(&index), Some((6, 6)));
        assert_eq!(wide.resolve(&index), Some((1, 4)));

        // `(NULL, NULL)` is the whole axis — the whole-sheet styling register — and tracks it as it
        // grows.
        let all = span(&FractionalKey::NULL, &FractionalKey::NULL);
        assert_eq!(all.resolve(&index), Some((1, 6)));
        index.cols.create_key(6).expect("index has room");
        assert_eq!(all.resolve(&index), Some((1, 7)));

        // A half-open span runs from its one real corner to the end of the axis, and keeps
        // tracking that end as columns are appended past it.
        let tail = span(&cols[2], &FractionalKey::NULL);
        let head = span(&FractionalKey::NULL, &cols[2]);
        assert_eq!(tail.resolve(&index), Some((3, 7)));
        assert_eq!(head.resolve(&index), Some((1, 3)));
        index.cols.create_key(7).expect("index has room");
        assert_eq!(tail.resolve(&index), Some((3, 8)));
        assert_eq!(head.resolve(&index), Some((1, 3)));
    }

    /// The engine is the same engine: the same edits made to an ordinal model and to a replica
    /// have to give the same values and the same conditional formatting, cell for cell.
    #[test]
    fn stable_eval_matches_ordinal() {
        let mut ordinal = Model::new_empty("model", "en", "UTC", "en").unwrap();
        let mut stable = CollabModel::new(1);
        stable.new_sheet();

        let cf = CfRuleInput::CellIs {
            operator: ValueOperator::GreaterThan,
            formula: "15".to_string(),
            formula2: None,
            format: Dxf {
                fill: Some(Fill {
                    color: Color::Rgb("#FF0000".to_string()),
                }),
                ..Default::default()
            },
            stop_if_true: false,
        };
        for (row, column, value) in [
            (1, 1, "10"),
            (2, 1, "20"),
            (3, 1, "text"),
            (1, 2, "=A1+A2"),
            (2, 2, "=B1*2"),
            (3, 2, "=CONCAT(A3, \"!\")"),
        ] {
            ordinal
                .set_user_input(0, row, column, value.to_string())
                .unwrap();
            stable
                .set_user_input(0, row, column, value.to_string())
                .unwrap();
        }
        ordinal
            .add_conditional_formatting(0, "A1:B3", cf.clone())
            .unwrap();
        stable.add_conditional_formatting(0, "A1:B3", cf).unwrap();
        ordinal.evaluate();
        stable.evaluate();

        let cells = ordinal.get_all_cells();
        assert!(!cells.is_empty());
        // The rule fired on the stable side, so the comparison below is not vacuous.
        assert!(!stable.cf_cache.is_empty());
        for cell in cells {
            let (sheet, row, column) = (cell.index, cell.row, cell.column);
            assert_eq!(
                stable.get_formatted_cell_value(sheet, row, column),
                ordinal.get_formatted_cell_value(sheet, row, column),
                "value at ({sheet}, {row}, {column})"
            );
            assert_eq!(
                stable
                    .get_extended_style_for_cell(sheet, row, column)
                    .map(|s| s.style),
                ordinal
                    .get_extended_style_for_cell(sheet, row, column)
                    .map(|s| s.style),
                "conditional formatting at ({sheet}, {row}, {column})"
            );
        }
    }

    /// A reference names the row it points at, so a move needs no rewrite: both the target and the
    /// cell holding the formula are found wherever they now sit.
    #[test]
    fn stable_eval_tracks_moves() {
        let mut stable = CollabModel::new(1);
        stable.new_sheet();
        for (row, value) in [(1, "10"), (2, "20"), (3, "30"), (4, "40")] {
            stable.set_user_input(0, row, 1, value.to_string()).unwrap();
        }
        // Two rows above its own: 20 now, and 20 still after the move below.
        stable.set_user_input(0, 4, 2, "=A2".to_string()).unwrap();
        stable.evaluate();
        assert_eq!(
            stable.get_formatted_cell_value(0, 4, 2),
            Ok("20".to_string())
        );

        // Second row to the end: the rows now read 10, 30, 40, 20 and the formula cell sits third.
        stable.move_rows_action(0, 2, 1, 2).unwrap();
        stable.evaluate();

        for (row, value) in [(1, "10"), (2, "30"), (3, "40"), (4, "20")] {
            assert_eq!(
                stable.get_formatted_cell_value(0, row, 1),
                Ok(value.to_string()),
                "A{row}"
            );
        }
        // The formula moved with its row and still names the cell it always named.
        assert_eq!(
            stable.get_formatted_cell_value(0, 3, 2),
            Ok("20".to_string())
        );
    }

    /// Spills share the store with authored cells: the row read gives what `cell` gives column by
    /// column, past the index's tail included.
    #[test]
    fn cells_in_row_between_reads_as_cell_does() {
        let mut index = StableIndexes::new([b'x', 0, 0, 0]);
        mint(&mut index.rows, 3);
        mint(&mut index.cols, 8);
        let mut ws = Worksheet::<Stable> {
            dimension: String::new(),
            cols: vec![],
            rows: vec![],
            name: "Stable".to_string(),
            sheet_data: SheetData::new(),
            shared_formulas: vec![],
            sheet_id: 1,
            state: SheetState::Visible,
            color: Color::None,
            merged_cells: vec![],
            comments: vec![],
            frozen_rows: 0,
            frozen_columns: 0,
            show_grid_lines: true,
            conditional_formatting: vec![],
            links: HashMap::new(),
            index,
        };
        let number = |v: f64| Cell::NumberCell { v, s: 0 };
        let spill = |v: f64| Cell::SpillCell {
            a: (2, 1),
            s: 0,
            v: crate::types::SpillValue::Number(v),
        };
        for (column, cell) in [
            (1, number(1.0)),
            (3, number(3.0)),
            (4, Cell::EmptyCell { s: 0 }),
            (5, spill(5.0)),
            (6, number(6.0)),
            (8, number(8.0)),
            (10, spill(10.0)),
        ] {
            ws.update_cell(2, column, cell).unwrap();
        }

        for row in [1, 2, 3, 4] {
            for (first, last) in [(1, 8), (0, 12), (3, 4), (4, 6), (5, 5), (9, 10), (4, 3)] {
                let read: Vec<_> = ws
                    .sheet_data
                    .cells_in_row_between(row, first, last)
                    .map(|(column, cell)| (column, cell.into_owned()))
                    .collect();
                let expected: Vec<_> = (first..=last)
                    .filter_map(|column| Some((column, ws.cell(row, column)?.into_owned())))
                    .collect();
                assert_eq!(read, expected, "row {row}, columns {first}..={last}");
            }
        }
        let read: Vec<_> = ws
            .sheet_data
            .cells_in_row_between(2, 1, 10)
            .map(|(column, _)| column)
            .collect();
        assert_eq!(read, vec![1, 3, 4, 5, 6, 8, 10]);
    }
}
