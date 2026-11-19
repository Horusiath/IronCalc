//! Turning a commit into workbook state.
//!
//! Every patch writes a register guarded by a [`Timestamp`] in [`SheetRegisters`] or
//! [`WorkbookMeta`], and applies iff its stamp is `>=` the stored one — the same `>=` as
//! [`Lww::merge`](crate::collab::log::Lww::merge), so a commit's patches resolve to the last one
//! and redelivery rewrites the same values.
//!
//! Applying is **total**: a patch naming a sheet, row or rule that is not here is a no-op, never an
//! error — a commit is never rejected. Guards outlive their subject, so a write older than a delete
//! cannot resurrect what it deleted.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;

use crate::cf_types::{CfRule, ConditionalFormatting};
use crate::collab::bind::Host;
use crate::collab::codec::CodecError;
use crate::collab::formula::{unresolved_names, FormulaRefs, StableRef};
use crate::collab::fractional_index::{
    virtual_key, Entry, FractionalIndex, FractionalKey, Reorder,
};
use crate::collab::hlc::Hlc;
use crate::collab::log::{Commit, Consumer, Lww, SessionId, Snapshot, Timestamp};
use crate::collab::model::{
    resolve_axis, ColSpan, CollabModel, Dirty, NameView, SheetRegisters, Stable, StableCellAddress,
    StableIndexes, StableLink,
};
use crate::collab::naming::NameRepair;
use crate::collab::patch::{
    CellInput, CfPropKind, CfProperty, ColState, DefinedNameId, DefinedNameProperty, NamedStyle,
    NamedStyleId, NamedStyleProperty, Patch, PropKind, Property, RowState, SheetContent, SheetId,
    SheetIndexSeed, SheetProperty, StableCfRule, StyleCategory, WorkbookProperty,
};
use crate::collab::DynError;
use crate::constants::{DEFAULT_ROW_HEIGHT, LAST_COLUMN, LAST_ROW, ROW_HEIGHT_FACTOR};
use crate::evaluation::KeyBuild;
use crate::expressions::parser::stringify::{to_english_string, to_rc_format};
use crate::expressions::parser::{static_analysis::run_static_analysis_on_node, Node};
use crate::types::{
    Alignment, ArrayKind, Cell, CellStyles, Col, Comment, DefinedName, FormulaValue, MergedCell,
    Position, Row, SheetState, Style, StyleIncludes, Styles, Workbook, Worksheet,
};

/// Version byte prefixing every [`Snapshot::encode`] payload.
pub const SNAPSHOT_FORMAT_VERSION: u8 = 1;

impl Consumer for CollabModel<'_> {
    type Error = DynError;

    fn apply(&mut self, commit: &Commit) -> Result<(), Self::Error> {
        // Receive rule: this commit's stamp is a watermark for our own clock.
        Hlc::sync(commit.hlc);
        let ts = commit.timestamp();
        for patch in &commit.patches {
            self.apply_patch(patch, &ts)?;
        }
        self.resync_derived(&commit.patches);
        Ok(())
    }
}

impl CollabModel<'_> {
    /// Applies a delivered batch of commits, then reconciles the merges concurrency may have
    /// duplicated or overlapped.
    pub fn apply_batch(&mut self, commits: &[Commit]) -> Result<(), DynError> {
        for commit in commits {
            self.apply(commit)?;
        }
        self.reconcile_merges();
        Ok(())
    }
}

impl Snapshot for CollabModel<'static> {
    /// A version byte, then the workbook. Views are per-user state and are never encoded.
    fn encode(&self) -> Vec<u8> {
        let mut out = vec![SNAPSHOT_FORMAT_VERSION];
        out.extend_from_slice(&bitcode::encode(&self.workbook));
        out
    }

    /// `session` is the **restoring** replica's, not the one that wrote the bytes: new keys must
    /// carry the identity of whoever loaded the snapshot.
    fn decode(bytes: &[u8], session: SessionId) -> Result<Self, Self::Error> {
        let (&version, workbook) = bytes.split_first().ok_or("empty snapshot payload")?;
        if version != SNAPSHOT_FORMAT_VERSION {
            return Err(format!("unsupported snapshot format version: {version}").into());
        }

        let mut model = CollabModel::new(session);
        model.workbook = bitcode::decode(workbook)?;
        // The suffix is never in the payload — see `FractionalIndex::decode`.
        let suffix = model.suffix();
        for sheet in &mut model.workbook.worksheets {
            sheet.index.rows.suffix = suffix;
            sheet.index.cols.suffix = suffix;
        }
        for (index, text) in model.workbook.shared_strings.iter().enumerate() {
            model.shared_strings.insert(text.clone(), index);
        }
        for sheet in &mut model.workbook.worksheets {
            rebuild_touched(&mut sheet.index);
            // A snapshot may hold spills: list them once.
            sheet.index.spills.0 = (sheet.sheet_data.cells())
                .filter(|(_, _, cell)| matches!(**cell, Cell::SpillCell { .. }))
                .map(|(row, column, _)| (row, column))
                .collect();
        }
        model.index_unresolved();
        // Re-derives what the payload already holds, as the baseline later commits compare with.
        model.normalize_defined_names();
        model.refresh_parse_tables();
        model.lower_all();
        for i in 0..model.workbook.worksheets.len() {
            model.derive_sparse(i);
        }
        Ok(model)
    }
}

/// Whether `ts` beats the guard stored for `key`, recording it when it does.
fn wins<K: Clone + Eq + Hash>(
    registers: &mut HashMap<K, Timestamp>,
    key: &K,
    ts: &Timestamp,
) -> bool {
    match registers.get(key) {
        Some(stored) if ts < stored => false,
        _ => {
            registers.insert(key.clone(), *ts);
            true
        }
    }
}

/// Filters out given `props` against the provided timestamp, returning only the more recent ones.
fn winning<'p, K: Clone + Eq + Hash>(
    registers: &mut HashMap<K, Timestamp>,
    key: impl Fn(PropKind) -> K,
    props: &'p [Property],
    ts: &Timestamp,
) -> Vec<&'p Property> {
    props
        .iter()
        .filter(|p| wins(registers, &key(p.kind()), ts))
        .collect()
}

/// An absent alignment and a default one draw the same, and only the absent spelling is what the
/// ordinal model stores — so a style built attribute by attribute has to come back to it.
fn canonical(mut style: Style) -> Style {
    if style.alignment.as_ref() == Some(&Alignment::default()) {
        style.alignment = None;
    }
    style
}

/// `own` with `props` written into it, interned. Index 0 is the default style.
fn overlay(styles: &mut Styles, own: i32, props: &[&Property]) -> i32 {
    let mut style = styles.get_style(own).unwrap_or_default();
    for p in props {
        p.write_into(&mut style);
    }
    styles.get_style_index_or_create(&canonical(style))
}

/// `own` reduced to the attributes `kept` admits, the rest at their defaults, interned.
fn filter_styles(styles: &mut Styles, own: i32, kept: impl Fn(PropKind) -> bool) -> i32 {
    let source = styles.get_style(own).unwrap_or_default();
    let mut style = Style::default();
    for k in PropKind::STYLE.into_iter().filter(|k| kept(*k)) {
        if let Some(p) = Property::read(&source, k) {
            p.write_into(&mut style);
        }
    }
    styles.get_style_index_or_create(&canonical(style))
}

/// The registers a seeded `style` has to guard: only the attributes it sets. A default attribute
/// has no entry, as on a row nobody ever formatted, so a seed of a million plain rows costs nothing.
fn set_kinds(style: &Style) -> impl Iterator<Item = PropKind> {
    Property::diff(&Style::default(), style)
        .0
        .into_iter()
        .map(|p| p.kind())
}

/// Returns styles included categories for a given cell.
pub(crate) fn owned_categories(
    registers: &HashMap<(StableCellAddress, PropKind), Timestamp>,
    at: &StableCellAddress,
    reference: Option<&Timestamp>,
) -> StyleIncludes {
    let mut owned = StyleIncludes {
        number_format: false,
        font: false,
        fill: false,
        border: false,
        alignment: false,
        protection: false,
    };
    // One pass over the kinds; a category's first later stamp settles it, the rest are not read.
    for kind in PropKind::STYLE {
        let Some(category) = kind.category() else {
            continue;
        };
        if !category.included(&owned) && registers.get(&(at.clone(), kind)) > reference {
            category.mark(&mut owned);
        }
    }
    owned
}

/// Sheet names are case-insensitively unique and capped at Excel's 31, mirrored by
/// [`is_valid_sheet_name`](crate::new_empty::is_valid_sheet_name).
pub(crate) const SHEET_NAMES: NameRepair = NameRepair {
    case_insensitive: true,
    max_len: 31,
};

/// Style names are case-sensitive — `get_style_index_by_name` matches exactly — and capped at
/// OOXML's 255.
pub(crate) const STYLE_NAMES: NameRepair = NameRepair {
    case_insensitive: false,
    max_len: 255,
};

/// Defined names are case-insensitively unique within a scope — every upstream lookup folds case,
/// from `Parser::get_defined_name` to `is_valid_defined_name` — and capped at Excel's 255.
pub(crate) const DEFINED_NAMES: NameRepair = NameRepair {
    case_insensitive: true,
    max_len: 255,
};

/// Whether the style table holds this entry itself rather than deriving it from a register, by
/// `Styles::is_builtin_style`'s rule. No patch authors a built-in — `create_named_style` files
/// `builtin_id: 0`, and every named-style mutator refuses a built-in name — so the rest is derived.
fn is_builtin_entry(entry: &CellStyles) -> bool {
    entry.builtin_id > 0 || entry.name.eq_ignore_ascii_case("normal")
}

/// Whether a commit can have changed which names are live, and so needs the names re-derived.
fn touches_sheet_names(patches: &[Patch]) -> bool {
    patches.iter().any(|patch| {
        matches!(
            patch,
            Patch::AddSheet { .. }
                | Patch::DeleteSheet { .. }
                | Patch::SetSheetProperty {
                    property: SheetProperty::Name(_),
                    ..
                }
        )
    })
}

fn displaces(reorders: &[Reorder], len: usize) -> bool {
    let inserted: usize = (reorders.iter())
        .map(|r| match r {
            Reorder::Inserted { count, .. } => *count,
            _ => 0,
        })
        .sum();
    let old = len.saturating_sub(inserted);
    (reorders.iter()).any(|r| match r {
        Reorder::Inserted { at, .. } => *at < old,
        Reorder::Removed { .. } | Reorder::Moved { .. } => true,
    })
}

fn store_style(sheet: &mut Worksheet<Stable>, (row, column): (i32, i32), s: i32) {
    let cell = sheet.sheet_data.cell(row, column);
    if matches!(cell.as_deref(), Some(Cell::SpillCell { .. })) {
        // Kept for when the spill goes, and shown meanwhile as the ordinal model shows it.
        match s {
            0 => sheet.index.covered.remove(&(row, column)),
            s => sheet.index.covered.insert((row, column), s),
        };
        if let Some(cell) = sheet.sheet_data.cell_mut(row, column) {
            cell.set_style(s);
        }
        return;
    }
    if s == 0 && matches!(cell.as_deref(), None | Some(Cell::EmptyCell { .. })) {
        sheet.sheet_data.remove_cell(row, column);
        return;
    }
    match sheet.sheet_data.cell_mut(row, column) {
        Some(cell) => cell.set_style(s),
        None => {
            sheet
                .sheet_data
                .set_cell(row, column, Cell::EmptyCell { s });
        }
    }
}

#[derive(Clone, Copy)]
enum Axis {
    Rows,
    Columns,
}

impl Worksheet<Stable> {
    /// Applies the reordering events from [FractionalIndex::reorders] for a given axis onto
    /// sheet's rows/column, so that they keep the same order as the fractional index.
    fn apply_reorder(&mut self, axis: Axis) {
        let Worksheet {
            index,
            sheet_data,
            rows,
            ..
        } = self;
        let fi = match axis {
            Axis::Rows => &mut index.rows,
            Axis::Columns => &mut index.cols,
        };
        let reorders = fi.reorders();
        if reorders.is_empty() {
            return;
        }
        index.reordered.0 |= displaces(reorders, fi.len());
        // On the rows axis the row records follow the same change as the cells: record `r` keeps
        // naming `active[r - 1]`, and `rows` stays sorted by `r`. A removed row's record goes with
        // it; the handler that hides a row takes out what it keeps first.
        for &change in reorders {
            match (axis, change) {
                (Axis::Rows, Reorder::Inserted { at, count }) => {
                    let (at, count) = (at as i32 + 1, count as i32);
                    for row in rows.iter_mut().filter(|row| row.r >= at) {
                        row.r += count;
                    }
                    sheet_data.insert_rows(at, count);
                }
                (Axis::Columns, Reorder::Inserted { at, count }) => {
                    sheet_data.insert_columns(at as i32 + 1, count as i32)
                }
                (Axis::Rows, Reorder::Removed { at, count }) => {
                    let (first, count) = (at as i32 + 1, count as i32);
                    rows.retain_mut(|row| {
                        if row.r >= first + count {
                            row.r -= count;
                            return true;
                        }
                        row.r < first
                    });
                    sheet_data.remove_rows(first, count);
                }
                (Axis::Columns, Reorder::Removed { at, count }) => {
                    sheet_data.remove_columns(at as i32 + 1, count as i32)
                }
                (Axis::Rows, Reorder::Moved { from, to }) => {
                    let (from, to) = (from as i32 + 1, to as i32 + 1);
                    let (lo, hi) = (from.min(to), from.max(to));
                    let start = rows.partition_point(|row| row.r < lo);
                    let end = rows.partition_point(|row| row.r <= hi);
                    let span = &mut rows[start..end];
                    for row in span.iter_mut() {
                        row.r = match row.r {
                            r if r == from => to,
                            r if from < to => r - 1,
                            r => r + 1,
                        };
                    }
                    // The moved record went from one end of the span to the other.
                    if from < to && span.first().is_some_and(|row| row.r == to) {
                        span.rotate_left(1);
                    } else if from > to && span.last().is_some_and(|row| row.r == to) {
                        span.rotate_right(1);
                    }
                    sheet_data.move_row(from, to);
                }
                (Axis::Columns, Reorder::Moved { from, to }) => {
                    sheet_data.move_column(from as i32 + 1, to as i32 + 1)
                }
            }
        }
        fi.clear_reorders();
    }
}

/// Applies a delete stamped `at` to the cell at `(row, column)`: what [`keep_cell`] keeps stays,
/// the rest goes. A spill is no cell, and a position outside the index holds nothing but spills.
fn retain_cell(
    sheet: &mut Worksheet<Stable>,
    styles: &mut Styles,
    (row, column): (i32, i32),
    at: Hlc,
) {
    let Worksheet {
        sheet_data, index, ..
    } = sheet;
    let Some(cell) = sheet_data.cell_mut(row, column) else {
        return;
    };
    let keys = (
        index.rows.key(row as usize - 1),
        index.cols.key(column as usize - 1),
    );
    let kept = match keys {
        (Some(r), Some(c)) if !matches!(cell, Cell::SpillCell { .. }) => {
            keep_cell(&index.registers, styles, &(r.clone(), c.clone()), at, cell)
        }
        _ => false,
    };
    if !kept {
        sheet_data.remove_cell(row, column);
    }
}

/// The cell a [`CellInput`] materializes into, keeping the style already on the cell. A formula
/// cell points at entry `f` of the sheet's formulas.
fn build_cell(input: &CellInput, style: i32, shared_string: i32, f: i32) -> Cell {
    match input {
        CellInput::Number(v) => Cell::NumberCell { v: *v, s: style },
        CellInput::Boolean(v) => Cell::BooleanCell { v: *v, s: style },
        CellInput::Text(_) => Cell::SharedString {
            si: shared_string,
            s: style,
        },
        CellInput::Error(ei) => Cell::ErrorCell {
            ei: ei.clone(),
            s: style,
        },
        CellInput::Formula(_) => Cell::CellFormula {
            f,
            s: style,
            v: FormulaValue::Unevaluated,
        },
        CellInput::Array(_) => Cell::ArrayFormula {
            f,
            s: style,
            r: (1, 1),
            kind: ArrayKind::Dynamic,
            v: FormulaValue::Unevaluated,
        },
        // A nonsensical extent from the wire is clamped to the grid rather than trusted.
        CellInput::Cse { width, height, .. } => Cell::ArrayFormula {
            f,
            s: style,
            r: ((*width).clamp(1, LAST_COLUMN), (*height).clamp(1, LAST_ROW)),
            kind: ArrayKind::Cse,
            v: FormulaValue::Unevaluated,
        },
    }
}

/// Whether a cell outlives a delete stamped `at`: each half survives only under a guard strictly
/// newer than it, and a surviving half resets the dominated one to its default.
fn keep_cell(
    registers: &SheetRegisters,
    styles: &mut Styles,
    address: &StableCellAddress,
    at: Hlc,
    cell: &mut Cell,
) -> bool {
    let newer_value = if let Some(v) = registers.cell_values.get(address) {
        v.hlc > at
    } else {
        false
    };
    // Per attribute: only the ones stamped after the delete survive it.
    let kept = |k| {
        registers
            .cell_styles
            .get(&(address.clone(), k))
            .is_some_and(|s| s.hlc > at)
    };
    let any_style = PropKind::STYLE.into_iter().any(kept);
    if newer_value && !any_style {
        cell.set_style(0);
    }
    if any_style {
        cell.set_style(filter_styles(styles, cell.get_style(), kept));
        if !newer_value {
            *cell = Cell::EmptyCell {
                s: cell.get_style(),
            };
        }
    }
    newer_value || any_style
}

/// Whether a write stamped `ts` to `at` is dead: its row or column was removed at or after it,
/// revived since or not.
pub(crate) fn cell_deleted(index: &StableIndexes, at: &StableCellAddress, ts: Hlc) -> bool {
    let removed = |e: Option<&Entry>| e.is_some_and(|e| ts <= e.removed_at);
    removed(index.rows.entry_by_id(&at.0)) || removed(index.cols.entry_by_id(&at.1))
}

/// The identities `keys` name, the unknown ones left out.
fn identities(index: &FractionalIndex, keys: &[FractionalKey]) -> Vec<FractionalKey> {
    keys.iter()
        .filter_map(|k| index.entry_by_key(k).map(|e| e.key.clone()))
        .collect()
}

/// Touches the row and column of a write to `at` stamped `ts`, a revive putting its row or column
/// back into the cells too and marking the sheet reordered: a revive at the tail moves nothing, but
/// brings back references lowered dead. Returns whether the write is dead.
fn touch_cell(sheet: &mut Worksheet<Stable>, at: &StableCellAddress, ts: Hlc) -> bool {
    let (row, row_removed) = sheet.index.rows.touch(&at.0, ts);
    if row {
        Stable::drop_spills(sheet);
        sheet.apply_reorder(Axis::Rows);
        unhide_row(sheet, &at.0);
    }
    let (col, col_removed) = sheet.index.cols.touch(&at.1, ts);
    if col {
        Stable::drop_spills(sheet);
        sheet.apply_reorder(Axis::Columns);
    }
    sheet.index.reordered.0 |= row || col;
    ts <= row_removed || ts <= col_removed
}

fn rebuild_touched(index: &mut StableIndexes) {
    let registers = &index.registers;
    let (row_floor, col_floor) = (index.rows.moved_floor(), index.cols.moved_floor());
    let mut rows: HashMap<_, _, KeyBuild> = HashMap::default();
    let mut cols: HashMap<_, _, KeyBuild> = HashMap::default();
    let cells = (registers.cell_values.iter())
        .chain((registers.cell_styles.iter()).map(|((at, _), ts)| (at, ts)));
    for ((row, col), ts) in cells {
        if ts.hlc > row_floor {
            let stamp = rows.entry(row).or_insert(ts.hlc);
            *stamp = (*stamp).max(ts.hlc);
        }
        if ts.hlc > col_floor {
            let stamp = cols.entry(col).or_insert(ts.hlc);
            *stamp = (*stamp).max(ts.hlc);
        }
    }
    for (row, ts) in rows {
        index.rows.touch(row, ts);
    }
    for (col, ts) in cols {
        index.cols.touch(col, ts);
    }
    // The active order already reflects every touch: it was encoded, or seeded, after them.
    debug_assert!(
        index.rows.reorders().is_empty() && index.cols.reorders().is_empty(),
        "a rebuilt touch changed visibility"
    );
    index.rows.clear_reorders();
    index.cols.clear_reorders();
}

/// Puts a row's record back among the visible ones if the row is visible again: called for every
/// row an index operation may have revived, after its reorders were followed.
fn unhide_row(sheet: &mut Worksheet<Stable>, identity: &FractionalKey) {
    if !sheet.index.hidden_rows.contains_key(identity) {
        return;
    }
    let Some(p) = sheet.index.rows.position_of(identity) else {
        return;
    };
    let Some(mut row) = sheet.index.hidden_rows.remove(identity) else {
        return;
    };
    row.r = p as i32 + 1;
    let at = sheet.rows.partition_point(|other| other.r < row.r);
    sheet.rows.insert(at, row);
}

/// Applies a delete to a row record: only the properties `kept` (written after the delete)
/// survive it.
fn filter_row(styles: &mut Styles, row: &mut Row, kept: impl Fn(PropKind) -> bool) {
    row.s = filter_styles(styles, row.s, &kept);
    row.custom_format = row.s != 0;
    if !kept(PropKind::Height) {
        row.height = DEFAULT_ROW_HEIGHT / ROW_HEIGHT_FACTOR;
        row.custom_height = false;
    }
    if !kept(PropKind::Hidden) {
        row.hidden = false;
    }
}

/// The ordinal `cols` records `index.col_spans` resolves to: per column and per property, the
/// covering span whose register for it is newest, coalesced into runs of equal records. A span
/// open at its upper end also covers the columns past the index's tail.
fn derive_cols(index: &StableIndexes) -> Vec<Col> {
    if index.col_spans.is_empty() {
        return Vec::new();
    }
    let registers = &index.registers.col_spans;
    let len = index.cols.len() as i32;
    // Sorted by span, so that on a tie of stamps the first span wins, whatever the map's order.
    let mut spans: Vec<_> = index.col_spans.iter().collect();
    spans.sort_by_key(|&(span, _)| span);
    struct Covering<'a> {
        interval: Option<(i32, i32)>,
        open: bool,
        state: &'a ColSpan,
        width: Option<Timestamp>,
        hidden: Option<Timestamp>,
        style: Option<Timestamp>,
    }
    let spans: Vec<Covering> = spans
        .into_iter()
        .map(|(span, state)| {
            let stamp = |kind| registers.get(&(span.clone(), kind)).copied();
            Covering {
                interval: resolve_axis(&index.cols, &Some(span.clone())),
                open: span.1.is_empty(),
                state,
                width: stamp(PropKind::Width),
                hidden: stamp(PropKind::Hidden),
                style: PropKind::STYLE.into_iter().filter_map(stamp).max(),
            }
        })
        .collect();
    // The record of one column, or of the tail: the newest covering write of each property.
    let record = |covers: &dyn Fn(&Covering) -> bool| -> ColSpan {
        let newest = |stamp: fn(&Covering) -> Option<Timestamp>| {
            let mut best: Option<(Timestamp, &ColSpan)> = None;
            for span in spans.iter().filter(|span| covers(span)) {
                let Some(ts) = stamp(span) else {
                    continue;
                };
                if best.is_none_or(|(stored, _)| stored < ts) {
                    best = Some((ts, span.state));
                }
            }
            best.map(|(_, state)| state)
        };
        let mut out = ColSpan::default();
        if let Some(state) = newest(|span| span.width) {
            out.width = state.width;
            out.custom_width = state.custom_width;
        }
        if let Some(state) = newest(|span| span.hidden) {
            out.hidden = state.hidden;
        }
        if let Some(state) = newest(|span| span.style) {
            out.style = state.style;
        }
        out
    };
    let mut cols: Vec<Col> = Vec::new();
    let mut push = |min: i32, max: i32, state: ColSpan| {
        if state == ColSpan::default() {
            return;
        }
        if let Some(last) = cols.last_mut() {
            let same = (last.width, last.custom_width, last.hidden, last.style)
                == (state.width, state.custom_width, state.hidden, state.style);
            if same && last.max + 1 == min {
                last.max = max;
                return;
            }
        }
        cols.push(Col {
            min,
            max,
            width: state.width,
            custom_width: state.custom_width,
            hidden: state.hidden,
            style: state.style,
        });
    };
    for column in 1..=len {
        let state = record(&|span: &Covering| {
            span.interval
                .is_some_and(|(lo, hi)| (lo..=hi).contains(&column))
        });
        push(column, column, state);
    }
    if len < LAST_COLUMN {
        push(len + 1, LAST_COLUMN, record(&|span: &Covering| span.open));
    }
    cols
}

/// Renumbers the priorities, which is what a rule's position key *means*: rank by the position
/// written for it, by its own identity when none was, identity breaking any tie. Storage is left
/// alone — it stays in creation order, so the index a caller holds does not move.
fn rank_cf(sheet: &mut Worksheet<Stable>) {
    let registers = &sheet.index.registers;
    let mut rank: Vec<usize> = (0..registers.cf_order.len()).collect();
    // a moved rule sorts by the position written for it, an unmoved one by its identity
    rank.sort_by_cached_key(|&at| {
        let key = &registers.cf_order[at];
        (
            registers.cf_positions.get(key).map_or(key, |p| &p.value),
            key,
        )
    });
    // `at` is the storage slot, `priority` the rank it came out at
    for (priority, at) in rank.into_iter().enumerate() {
        sheet.conditional_formatting[at].priority = priority as u32 + 1;
    }
}

/// Files a rule at the slot its identity key sorts to, which keeps storage in creation order.
fn insert_cf(sheet: &mut Worksheet<Stable>, key: FractionalKey, cf: ConditionalFormatting) {
    let order = &mut sheet.index.registers.cf_order;
    let at = order.binary_search(&key).unwrap_or_else(|at| at);
    order.insert(at, key);
    sheet.conditional_formatting.insert(at, cf);
}

/// Where rule `key` currently sits in storage.
fn cf_slot(sheet: &Worksheet<Stable>, key: &FractionalKey) -> Option<usize> {
    sheet.index.registers.cf_order.binary_search(key).ok()
}

impl CollabModel<'_> {
    pub(crate) fn sheet_index(&self, sheet: SheetId) -> Option<usize> {
        self.workbook
            .worksheets
            .iter()
            .position(|ws| ws.sheet_id == sheet)
    }

    /// Index of `text` in the workbook's shared strings, appending it if it is new.
    fn intern_string(&mut self, text: &str) -> i32 {
        if let Some(&index) = self.shared_strings.get(text) {
            return index as i32;
        }
        let index = self.workbook.shared_strings.len();
        self.workbook.shared_strings.push(text.to_string());
        self.shared_strings.insert(text.to_string(), index);
        index as i32
    }

    /// Index of `style` in the workbook's style table, creating the entry if it is new.
    fn intern_style(&mut self, style: &Style) -> i32 {
        self.workbook.styles.get_style_index_or_create(style)
    }

    /// Puts the worksheets back in tab order. A sheet with no position sorts last by id, which
    /// keeps the ordering total.
    fn sort_sheets(&mut self) {
        let before = self.sheet_ids();
        let positions = std::mem::take(&mut self.workbook.meta.sheet_positions);
        self.workbook.worksheets.sort_by(|a, b| {
            match (
                positions.get(&a.sheet_id).map(|p| &p.value),
                positions.get(&b.sheet_id).map(|p| &p.value),
            ) {
                // A revived sheet's re-filed key can equal one minted into the gap it left.
                (Some(x), Some(y)) => x.cmp(y).then_with(|| a.sheet_id.cmp(&b.sheet_id)),
                (Some(_), None) => Ordering::Less,
                (None, Some(_)) => Ordering::Greater,
                (None, None) => a.sheet_id.cmp(&b.sheet_id),
            }
        });
        self.workbook.meta.sheet_positions = positions;
        self.realign_parsed(before);
    }

    fn sheet_ids(&self) -> Vec<SheetId> {
        (self.workbook.worksheets.iter())
            .map(|ws| ws.sheet_id)
            .collect()
    }

    /// Follows a change to the order of the worksheets, which were in `before` order, with their
    /// parse tables. A sheet that changed position changes the sheet index every reference to it
    /// lowered with, so its users re-lower.
    fn realign_parsed(&mut self, before: Vec<SheetId>) {
        let mut parsed: HashMap<SheetId, (usize, Vec<_>)> = (before.into_iter())
            .zip(std::mem::take(&mut self.parsed_formulas))
            .enumerate()
            .map(|(at, (id, parsed))| (id, (at, parsed)))
            .collect();
        for (at, sheet) in self.workbook.worksheets.iter().enumerate() {
            let entries = match parsed.remove(&sheet.sheet_id) {
                Some((was, entries)) => {
                    if was != at {
                        self.local.dirty.sheets.insert(sheet.sheet_id);
                        self.local.dirty.structural = true;
                    }
                    entries
                }
                None => Vec::new(),
            };
            self.parsed_formulas.push(entries);
        }
    }

    /// Notes that a sheet changed in a way every formula naming it, and every unbound name, may
    /// lower differently after.
    fn sheet_changed(&mut self, sheet: SheetId) {
        let dirty = &mut self.local.dirty;
        dirty.sheets.insert(sheet);
        dirty.unbound = true;
        dirty.structural = true;
    }

    /// Files a sheet's authored name, under the same last-write-wins arbitration as every other
    /// register. Both `AddSheet` and a rename write here; nobody writes the display name.
    fn file_sheet_name(&mut self, sheet: SheetId, name: &str, ts: &Timestamp) {
        self.workbook
            .meta
            .sheet_names
            .entry(sheet)
            .or_default()
            .merge(name.to_string(), ts);
    }

    /// Derives every `Worksheet::name` from the authored names, repairing the collisions concurrent
    /// adds and renames can produce — Excel needs names case-insensitively unique, and formulas
    /// resolve sheets by display name.
    ///
    /// Deterministic and commutative: the inputs are the replicated name registers and their total
    /// stamp order, so every replica derives the same names whatever order the commits arrived in.
    ///
    /// Known limit: formulas name sheets by display-name text, so when a repair renames the losing
    /// sheet, a formula written against that name silently retargets to the winner — convergent
    /// everywhere, but not intent-preserving. It goes away once formulas are stored as typed
    /// `Node<A: Position>` holding stable sheet references rather than strings.
    fn normalize_sheet_names(&mut self) {
        let mut authored: Vec<(Timestamp, (SheetId, usize), String)> = Vec::new();
        for (i, sheet) in self.workbook.worksheets.iter().enumerate() {
            match self.workbook.meta.sheet_names.get(&sheet.sheet_id) {
                Some(lww) => authored.push((lww.timestamp, (sheet.sheet_id, i), lww.value.clone())),
                // Every live sheet arrived as an `AddSheet`, which files the register.
                None => debug_assert!(false, "sheet {} has no authored name", sheet.sheet_id),
            }
        }
        for ((id, i), name) in SHEET_NAMES.assign(authored) {
            if self.workbook.worksheets[i].name != name {
                self.workbook.worksheets[i].name = name;
                self.sheet_changed(id);
            }
        }
    }

    /// Every live named style as `(id, display name)`, in the order the style table shows them:
    /// first write wins, around the built-in entries no register owns.
    pub(crate) fn named_style_display(&self) -> Vec<(NamedStyleId, String)> {
        let authored: Vec<(Timestamp, NamedStyleId, String)> = self
            .workbook
            .meta
            .named_styles
            .iter()
            .filter(|(_, state)| state.definition.value.is_some())
            .map(|(id, state)| (state.name.timestamp, *id, state.name.value.clone()))
            .collect();
        let mut taken = STYLE_NAMES.taken(
            self.workbook
                .styles
                .cell_styles
                .iter()
                .filter(|entry| is_builtin_entry(entry))
                .map(|entry| entry.name.as_str()),
        );
        STYLE_NAMES.assign_within(authored, &mut taken)
    }

    /// Derives the style table from the named-style registers, the way sheet names are derived: the
    /// live styles, named first-write-wins, after the built-ins no register owns.
    fn normalize_named_styles(&mut self) {
        let assignments = self.named_style_display();
        self.workbook.styles.cell_styles.retain(is_builtin_entry);
        for (id, name) in assignments {
            let Some(definition) = self
                .workbook
                .meta
                .named_styles
                .get(&id)
                .and_then(|state| state.definition.value.clone())
            else {
                continue;
            };
            // A quote prefix is a cell's own state, never a style's; the record ignores it.
            let slot = self.workbook.meta.style_xf.get(&id).copied();
            let xf_id = self.workbook.styles.set_base_style(
                slot,
                &canonical(definition.style.clone()),
                definition.includes,
            );
            self.workbook.meta.style_xf.insert(id, xf_id);
            self.workbook.styles.cell_styles.push(CellStyles {
                name,
                xf_id,
                builtin_id: definition.builtin_id,
            });
        }
    }

    /// Returns [NamedStyle]'s `xf_id`, style itself and its include categories for a given cell.
    pub(crate) fn inheritance(
        &self,
        sheet_idx: usize,
        at: &StableCellAddress,
        reference: Option<&Timestamp>,
    ) -> Option<(i32, &NamedStyle, StyleIncludes)> {
        let meta = &self.workbook.meta;
        let index = &self.workbook.worksheets[sheet_idx].index;
        let id = index.parents.get(at)?;
        let definition = meta.named_styles.get(id)?.definition.value.as_deref()?;
        let xf_id = *meta.style_xf.get(id)?;
        let owned = owned_categories(&index.registers.cell_styles, at, reference);
        let inherit = |category: StyleCategory| {
            category.included(&definition.includes) && !category.included(&owned)
        };
        let inherited = StyleIncludes {
            number_format: inherit(StyleCategory::NumberFormat),
            font: inherit(StyleCategory::Font),
            fill: inherit(StyleCategory::Fill),
            border: inherit(StyleCategory::Border),
            alignment: inherit(StyleCategory::Alignment),
            protection: definition.includes.protection,
        };
        Some((xf_id, definition, inherited))
    }

    /// Recomputes cell `at`'s look from its named style: the one place a parent reaches a cell.
    fn derive_cell(&mut self, sheet_idx: usize, at: &StableCellAddress) {
        let index = &self.workbook.worksheets[sheet_idx].index;
        let reference = index
            .registers
            .cell_styles
            .get(&(at.clone(), PropKind::StyleRef));
        // A row or column delete that outranks the reference took it along with the cell.
        if reference.is_some_and(|ts| cell_deleted(index, at, ts.hlc)) {
            return;
        }
        let parent = self
            .inheritance(sheet_idx, at, reference)
            .map(|(xf_id, definition, inherited)| (xf_id, definition.style.clone(), inherited));
        let sheet = &mut self.workbook.worksheets[sheet_idx];
        // Hidden: nothing to show, and a revive re-derives it.
        let Some(position) = sheet.ordinal(at) else {
            return;
        };
        let styles = &mut self.workbook.styles;
        let mut own = styles
            .get_style(sheet.authored_style(position).unwrap_or(0))
            .unwrap_or_default();
        let s = match parent {
            None => styles.get_style_index_or_create(&canonical(own)),
            Some((xf_id, style, inherited)) => {
                for category in StyleCategory::ALL {
                    if category.included(&inherited) {
                        category.copy(&style, &mut own);
                    }
                }
                let apply = StyleIncludes {
                    number_format: !inherited.number_format,
                    font: !inherited.font,
                    fill: !inherited.fill,
                    border: !inherited.border,
                    alignment: !inherited.alignment,
                    protection: !inherited.protection,
                };
                styles.get_parented_style_index_or_create(&canonical(own), xf_id, apply)
            }
        };
        store_style(sheet, position, s);
    }

    fn derive_parented(&mut self) {
        for i in 0..self.workbook.worksheets.len() {
            let mut cells: Vec<StableCellAddress> = self.workbook.worksheets[i]
                .index
                .parents
                .keys()
                .cloned()
                .collect();
            cells.sort();
            for at in &cells {
                self.derive_cell(i, at);
            }
        }
    }

    /// Every live defined name as `(id, scope, display name)`, ordered by id so two replicas that
    /// saw the same writes hold byte-identical workbooks.
    ///
    /// Repair runs per scope bucket: uniqueness is per scope, so a global `total` and a
    /// sheet-scoped `total` coexist and never rename each other.
    pub(crate) fn defined_name_display(&self) -> Vec<(DefinedNameId, Option<SheetId>, String)> {
        let mut buckets: HashMap<Option<SheetId>, Vec<(Timestamp, DefinedNameId, String)>> =
            HashMap::new();
        for (id, state) in &self.workbook.meta.defined_names {
            if state.formula.value.is_some() {
                let (scope, name) = &state.name.value;
                buckets
                    .entry(*scope)
                    .or_default()
                    .push((state.name.timestamp, *id, name.clone()));
            }
        }
        let mut display: Vec<(DefinedNameId, Option<SheetId>, String)> = buckets
            .into_iter()
            .flat_map(|(scope, authored)| {
                DEFINED_NAMES
                    .assign(authored)
                    .into_iter()
                    .map(move |(id, name)| (id, scope, name))
            })
            .collect();
        display.sort_by_key(|(id, ..)| *id);
        display
    }

    /// Derives `Workbook::defined_names` from the registers, the way the style table is derived:
    /// the live names, repaired first-write-wins within each scope. Returns the names whose
    /// lowered form changed since the last call.
    fn normalize_defined_names(&mut self) -> Vec<DefinedNameId> {
        let context = self.defined_name_context();
        let display = self.defined_name_display();
        let mut derived = Vec::with_capacity(display.len());
        let mut views: Vec<(DefinedNameId, NameView)> = Vec::with_capacity(display.len());
        for (id, sheet_id, name) in display {
            let Some(body) = self.formula_of(id) else {
                continue;
            };
            let node = self.lower(
                &body.formula.text,
                &body.formula.refs,
                &Host::relative(0, 1, 1),
            );
            let text = to_english_string(&node, &context);
            let formula = match body.equals {
                true => format!("={text}"),
                false => text,
            };
            let scope = sheet_id.map(|sheet| self.sheet_index(sheet).map(|at| at as u32));
            views.push((id, (name.clone(), scope, formula.clone())));
            derived.push(DefinedName {
                name,
                formula,
                sheet_id,
            });
        }
        self.workbook.defined_names = derived;
        // Both are sorted by id: what is in one and not equal in the other changed.
        let old = std::mem::replace(&mut self.local.name_views, views);
        let new = &self.local.name_views;
        let changed = |from: &[(DefinedNameId, NameView)], to: &[(DefinedNameId, NameView)]| {
            (from.iter())
                .filter(|entry| {
                    to.binary_search_by_key(&entry.0, |(id, _)| *id)
                        .map(|at| &to[at])
                        != Ok(entry)
                })
                .map(|(id, _)| *id)
                .collect::<Vec<_>>()
        };
        let mut ids = changed(&old, new);
        ids.extend(changed(new, &old));
        ids
    }

    /// Re-derives what a commit invalidated. Display names come first: the parse tables resolve
    /// sheets and defined names by them, and formulas show them.
    pub(crate) fn resync_derived(&mut self, patches: &[Patch]) {
        if touches_sheet_names(patches) {
            self.normalize_sheet_names();
        }
        if patches
            .iter()
            .any(|patch| matches!(patch, Patch::SetNamedStyle { .. }))
        {
            self.normalize_named_styles();
            self.derive_parented();
        }
        // A sheet whose rows or columns moved under the formulas that reference it.
        for sheet in &mut self.workbook.worksheets {
            if std::mem::take(&mut sheet.index.reordered.0) {
                self.local.dirty.sheets.insert(sheet.sheet_id);
                self.local.dirty.structural = true;
            }
        }
        let mut dirty = std::mem::take(&mut self.local.dirty);
        if dirty.structural {
            #[cfg(test)]
            {
                self.local.full_resyncs += 1;
            }
            let renamed = self.normalize_defined_names();
            if !renamed.is_empty() {
                dirty.names.extend(renamed);
                dirty.unbound = true;
            }
            self.refresh_parse_tables();
        }
        self.relower_dirty(&dirty);
        // Sparse items are few: every sheet is re-derived, with no tracking of what moved.
        for i in 0..self.workbook.worksheets.len() {
            self.derive_sparse(i);
        }
        self.normalize_cf();
    }

    /// The parser reads sheets and defined names by their display names, and the evaluator reads
    /// defined names parsed.
    fn refresh_parse_tables(&mut self) {
        let defined_names = self.workbook.get_defined_names_with_scope();
        self.parser
            .set_worksheets_and_names(self.workbook.get_worksheet_names(), defined_names);
        self.parse_defined_names();
    }

    /// Re-lowers, once each, the entries holding a slot on something `dirty` names.
    fn relower_dirty(&mut self, dirty: &Dirty) {
        for i in 0..self.workbook.worksheets.len() {
            let index = &self.workbook.worksheets[i].index;
            let mut entries: Vec<u32> = Vec::new();
            for sheet in &dirty.sheets {
                entries.extend(index.referenced_by.get(sheet).into_iter().flatten());
            }
            for name in &dirty.names {
                entries.extend(index.names_referenced_by.get(name).into_iter().flatten());
            }
            if dirty.unbound {
                entries.extend(&index.unbound);
            }
            entries.sort_unstable();
            entries.dedup();
            for f in entries {
                self.relower(i, f as usize);
            }
        }
    }

    /// Lowers entry `f` of worksheet `i` again from its stored node and slots: no parse, and the
    /// text and the static result are regenerated only if a leaf changed.
    pub(crate) fn relower(&mut self, i: usize, f: usize) {
        let sheet = &self.workbook.worksheets[i];
        let (Some(entry), Some((node, _))) = (
            sheet.index.formulas.get(f),
            self.parsed_formulas.get(i).and_then(|parsed| parsed.get(f)),
        ) else {
            return;
        };
        let mut node = Node::clone(node);
        if !self.overwrite_leaves(&mut node, &entry.refs, &sheet.host_of(i, &entry.host)) {
            return;
        }
        self.store_lowered(i, f, node);
    }

    /// Stores `node` as entry `f` of worksheet `i`, appending when `f` is one past the end.
    fn store_lowered(&mut self, i: usize, f: usize, node: Node) {
        let text = to_rc_format(&node);
        let static_result = run_static_analysis_on_node(&node);
        let parsed = (std::sync::Arc::new(node), static_result);
        let sheet = &mut self.workbook.worksheets[i];
        if f == sheet.shared_formulas.len() {
            sheet.shared_formulas.push(text);
            self.parsed_formulas[i].push(parsed);
        } else {
            sheet.shared_formulas[f] = text;
            self.parsed_formulas[i][f] = parsed;
        }
    }

    /// Lowers `formula` into the entry of the cell `at`, at `(row, column)` of worksheet `i`: the
    /// one it holds, `held`, if it already holds a formula, else a new one. Returns the entry.
    fn lower_entry(
        &mut self,
        i: usize,
        held: Option<i32>,
        at: &StableCellAddress,
        (row, column): (i32, i32),
        refs: &[StableRef],
        text: &str,
    ) -> i32 {
        let node = self.lower(text, refs, &Host::relative(i as u32, row, column));
        let entry = FormulaRefs {
            host: at.clone(),
            refs: refs.to_vec(),
        };
        let sheet = &mut self.workbook.worksheets[i];
        let (id, index) = (sheet.sheet_id, &mut sheet.index);
        let f = match held.filter(|f| (*f as usize) < index.formulas.len()) {
            Some(f) => {
                index.unregister_formula(f as u32, id);
                index.formulas[f as usize] = entry;
                f as usize
            }
            None => {
                index.formulas.push(entry);
                index.formulas.len() - 1
            }
        };
        index.register_formula(f as u32, id);
        self.store_lowered(i, f, node);
        f as i32
    }

    /// Lowers every entry from its stored text and slots, and files them: what a decoded workbook
    /// holds, exactly as the commits that wrote it left it.
    fn lower_all(&mut self) {
        self.parsed_formulas = (self.workbook.worksheets.iter())
            .map(|_| Vec::new())
            .collect();
        for i in 0..self.workbook.worksheets.len() {
            let sheet = &mut self.workbook.worksheets[i];
            let (id, count) = (sheet.sheet_id, sheet.shared_formulas.len());
            // Defensive: the two lists are kept aligned, entry for entry.
            sheet.index.formulas.resize_with(count, || FormulaRefs {
                host: (FractionalKey::NULL, FractionalKey::NULL),
                refs: Vec::new(),
            });
            for f in 0..count {
                sheet.index.register_formula(f as u32, id);
            }
            let texts = std::mem::take(&mut sheet.shared_formulas);
            for (f, text) in texts.iter().enumerate() {
                let sheet = &self.workbook.worksheets[i];
                let entry = &sheet.index.formulas[f];
                let node = self.lower(text, &entry.refs, &sheet.host_of(i, &entry.host));
                self.store_lowered(i, f, node);
            }
        }
    }

    /// Rewrites the ordinal `cols`, `merged_cells`, `comments`, `links` and conditional formatting
    /// ranges of worksheet `i` from their keyed sources in its index. A pure function of the
    /// sources and the index, in a fixed order, so replicas holding equal sources hold equal
    /// worksheets.
    pub(crate) fn derive_sparse(&mut self, i: usize) {
        let sheet = &self.workbook.worksheets[i];
        let index = &sheet.index;
        let at = |(row, col): &StableCellAddress| {
            let row = index.rows.position_of(row)? as i32 + 1;
            let column = index.cols.position_of(col)? as i32 + 1;
            Some((row, column))
        };
        let cols = derive_cols(index);
        let merged_cells = (index.merges.iter())
            .filter_map(|range| {
                let (row, column, last_row, last_column) = range.merged_rect(index)?;
                Some(MergedCell {
                    row,
                    column,
                    width: last_column - column + 1,
                    height: last_row - row + 1,
                })
            })
            .collect();
        let mut comments: Vec<Comment> = (index.comments.iter())
            .filter_map(|(key, body)| {
                Some(Comment {
                    text: body.text.clone(),
                    author_name: body.author_name.clone(),
                    author_id: body.author_id.clone(),
                    cell_ref: at(key)?,
                })
            })
            .collect();
        comments.sort_by_key(|c| c.cell_ref);
        let links = (index.links.iter())
            .filter_map(|(key, link)| Some((at(key)?, self.link_view(link))))
            .collect();
        // `cf_order` is aligned with the rules, entry by entry.
        let cf_ranges: Vec<Vec<_>> = (index.registers.cf_order.iter())
            .map(|key| {
                let ranges = index.cf_ranges.get(key).map(Vec::as_slice).unwrap_or(&[]);
                ranges.iter().filter_map(|r| r.to_ordinal(index)).collect()
            })
            .collect();
        let sheet = &mut self.workbook.worksheets[i];
        sheet.cols = cols;
        sheet.merged_cells = merged_cells;
        sheet.comments = comments;
        sheet.links = links;
        for (cf, ranges) in sheet.conditional_formatting.iter_mut().zip(cf_ranges) {
            cf.ranges = ranges;
        }
    }

    pub(crate) fn apply_patch(&mut self, patch: &Patch, ts: &Timestamp) -> Result<(), CodecError> {
        if let Some(sheet) = patch.target_sheet() {
            if let Some(timestamp) = self.workbook.meta.sheet_existence.get(&sheet) {
                if ts < timestamp && self.sheet_index(sheet).is_some() {
                    return Ok(());
                }
            }
        }
        match patch {
            Patch::SetCellValue {
                sheet,
                at,
                value,
                ts: at_ts,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let ts = at_ts.as_ref().unwrap_or(ts);
                let sheet = &mut self.workbook.worksheets[i];
                let dead = touch_cell(sheet, at, ts.hlc);
                // The guard is written either way; only the content is dead under a removal.
                let won = wins(&mut sheet.index.registers.cell_values, at, ts);
                if !won || dead {
                    return Ok(());
                }
                self.write_cell(i, at, value.as_ref());
            }
            Patch::SetCellStyle {
                sheet,
                at,
                props,
                ts: at_ts,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let ts = at_ts.as_ref().unwrap_or(ts);
                let sheet = &mut self.workbook.worksheets[i];
                let dead = touch_cell(sheet, at, ts.hlc);
                let index = &mut self.workbook.worksheets[i].index;
                let won = winning(
                    &mut index.registers.cell_styles,
                    |k| (at.clone(), k),
                    props,
                    ts,
                );
                if won.is_empty() || dead {
                    return Ok(());
                }
                let reference = won.iter().find_map(|p| match p {
                    Property::StyleRef(id) => Some(*id),
                    _ => None,
                });
                match reference {
                    Some(Some(id)) => {
                        index.parents.insert(at.clone(), id);
                    }
                    Some(None) => {
                        index.parents.remove(at);
                    }
                    None => {}
                }
                let parented = reference.is_some() || index.parents.contains_key(at);
                let sheet = &mut self.workbook.worksheets[i];
                // A key with no position names nothing visible: registers only.
                let Some(position) = sheet.ordinal(at) else {
                    return Ok(());
                };
                let s = overlay(
                    &mut self.workbook.styles,
                    sheet.authored_style(position).unwrap_or(0),
                    &won,
                );
                // Nothing left for the cell to hold, so it goes too.
                store_style(sheet, position, s);
                // Whatever just won may have changed what the cell inherits and what it owns.
                if parented {
                    self.derive_cell(i, at);
                }
            }
            Patch::InsertRows { sheet, keys } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                // As the ordinal model resets its spills: what they covered never has to shift.
                Stable::drop_spills(sheet);
                // A revive at the tail moves nothing, but brings back keys references lowered dead.
                let revived = sheet.index.rows.insert_keys_at(keys, ts.hlc);
                sheet.index.reordered.0 |= revived;
                sheet.apply_reorder(Axis::Rows);
                // A fresh key has no record waiting; most sheets have none at all.
                if !sheet.index.hidden_rows.is_empty() {
                    for key in identities(&sheet.index.rows, keys) {
                        unhide_row(sheet, &key);
                    }
                }
            }
            Patch::InsertColumns { sheet, keys } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                // As the ordinal model resets its spills: what they covered never has to shift.
                Stable::drop_spills(sheet);
                let revived = sheet.index.cols.insert_keys_at(keys, ts.hlc);
                sheet.index.reordered.0 |= revived;
                sheet.apply_reorder(Axis::Columns);
            }
            Patch::DeleteRows { sheet, keys, .. } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let Workbook {
                    worksheets, styles, ..
                } = &mut self.workbook;
                let sheet = &mut worksheets[i];
                Stable::drop_spills(sheet);
                // Keys name positions; records are filed by identity.
                let ids = identities(&sheet.index.rows, keys);
                let before: Vec<_> = ids
                    .iter()
                    .map(|k| sheet.index.rows.position_of(k))
                    .collect();
                sheet.index.rows.remove_keys_at(keys, ts.hlc);
                // The delete is one more write per register: it takes what it outranks and leaves
                // what a newer write already claimed.
                let kept = |registers: &SheetRegisters, key: &FractionalKey, kind| {
                    registers
                        .rows
                        .get(&(key.clone(), kind))
                        .is_some_and(|guard| guard.hlc > ts.hlc)
                };
                // A row that went hidden takes its record along, by the position it had.
                for (key, before) in ids.iter().zip(&before) {
                    let Some(p) = before else {
                        continue;
                    };
                    if sheet.index.rows.position_of(key).is_some() {
                        continue;
                    }
                    let r = *p as i32 + 1;
                    let Ok(at) = sheet.rows.binary_search_by_key(&r, |row| row.r) else {
                        continue;
                    };
                    let mut row = sheet.rows.remove(at);
                    filter_row(styles, &mut row, |k| kept(&sheet.index.registers, key, k));
                    if !row.is_empty() {
                        // No position while hidden; 0 keeps replicas byte-identical.
                        row.r = 0;
                        sheet.index.hidden_rows.insert(key.clone(), row);
                    }
                }
                // A hidden row holds no cell newer than the delete: its store row goes whole.
                sheet.apply_reorder(Axis::Rows);
                for (key, before) in ids.iter().zip(&before) {
                    let registers = &sheet.index.registers;
                    match sheet.index.rows.position_of(key) {
                        Some(row) => {
                            let row = row as i32 + 1;
                            for column in sheet.sheet_data.columns_in_row(row) {
                                retain_cell(sheet, styles, (row, column), ts.hlc);
                            }
                            let registers = &sheet.index.registers;
                            let Ok(at) = sheet.rows.binary_search_by_key(&row, |r| r.r) else {
                                continue;
                            };
                            filter_row(styles, &mut sheet.rows[at], |k| kept(registers, key, k));
                            if sheet.rows[at].is_empty() {
                                sheet.rows.remove(at);
                            }
                        }
                        // Hidden before this delete too: the record waiting for it is filtered
                        // all the same, as a write arriving after the delete would be refused.
                        None if before.is_none() => {
                            let Some(row) = sheet.index.hidden_rows.get_mut(key) else {
                                continue;
                            };
                            filter_row(styles, row, |k| kept(registers, key, k));
                            if row.is_empty() {
                                sheet.index.hidden_rows.remove(key);
                            }
                        }
                        None => {}
                    }
                }
            }
            Patch::DeleteColumns { sheet, keys, .. } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let Workbook {
                    worksheets, styles, ..
                } = &mut self.workbook;
                let sheet = &mut worksheets[i];
                Stable::drop_spills(sheet);
                sheet.index.cols.remove_keys_at(keys, ts.hlc);
                sheet.apply_reorder(Axis::Columns);
                let ids = identities(&sheet.index.cols, keys);
                // Spans are regions, not sets of columns: what they cover resolves against the
                // index, which just shrank. Cells of a column still visible go one by one.
                let columns: Vec<i32> = ids
                    .iter()
                    .filter_map(|k| sheet.index.cols.position_of(k))
                    .map(|c| c as i32 + 1)
                    .collect();
                if !columns.is_empty() {
                    for row in sheet.sheet_data.rows() {
                        for &column in &columns {
                            retain_cell(sheet, styles, (row, column), ts.hlc);
                        }
                    }
                }
            }
            Patch::MoveRows { sheet, moves, .. } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                Stable::drop_spills(sheet);
                for (source, dest) in moves {
                    sheet.index.rows.apply_move(source, dest.clone(), ts.hlc);
                }
                sheet.apply_reorder(Axis::Rows);
                // A move revives a hidden row.
                if !sheet.index.hidden_rows.is_empty() {
                    let sources: Vec<FractionalKey> =
                        moves.iter().map(|(s, _)| s.clone()).collect();
                    for key in identities(&sheet.index.rows, &sources) {
                        unhide_row(sheet, &key);
                    }
                }
            }
            Patch::MoveColumns { sheet, moves, .. } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                Stable::drop_spills(sheet);
                for (source, dest) in moves {
                    sheet.index.cols.apply_move(source, dest.clone(), ts.hlc);
                }
                sheet.apply_reorder(Axis::Columns);
            }
            Patch::SetRowProperty {
                sheet,
                row,
                props,
                ts: at_ts,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let ts = at_ts.as_ref().unwrap_or(ts);
                let index = &mut self.workbook.worksheets[i].index;
                let row_deleted =
                    (index.rows.entry_by_id(row)).is_some_and(|e| ts.hlc <= e.removed_at);
                let won = winning(&mut index.registers.rows, |k| (row.clone(), k), props, ts);
                if row_deleted || won.is_empty() {
                    return Ok(());
                }
                let own = self.workbook.worksheets[i]
                    .row_by_key(row)
                    .filter(|r| r.custom_format)
                    .map_or(0, |r| r.s);
                let s = overlay(&mut self.workbook.styles, own, &won);
                let row = self.workbook.worksheets[i].row_mut(row);
                row.s = s;
                row.custom_format = s != 0;
                // A row has no width; the kinds it does not own are simply skipped.
                for property in won {
                    match property {
                        Property::Height(height) => {
                            row.height = *height;
                            row.custom_height = true;
                        }
                        Property::Hidden(hidden) => row.hidden = *hidden,
                        _ => {}
                    }
                }
            }
            Patch::SetColumnSpan {
                sheet,
                span,
                props,
                ts: at_ts,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let ts = at_ts.as_ref().unwrap_or(ts);
                let registers = &mut self.workbook.worksheets[i].index.registers;
                let won = winning(&mut registers.col_spans, |k| (span.clone(), k), props, ts);
                if won.is_empty() {
                    return Ok(());
                }
                let index = &mut self.workbook.worksheets[i].index;
                let own = index.col_spans.get(span).and_then(|c| c.style).unwrap_or(0);
                let s = overlay(&mut self.workbook.styles, own, &won);
                let record = index.col_spans.entry(span.clone()).or_default();
                record.style = (s != 0).then_some(s);
                // A column has no height; the kinds it does not own are simply skipped.
                for property in won {
                    match property {
                        Property::Width(width) => {
                            record.width = *width;
                            record.custom_width = true;
                        }
                        Property::Hidden(hidden) => record.hidden = *hidden,
                        _ => {}
                    }
                }
            }
            Patch::SetMergedRange {
                sheet,
                range,
                merged,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let index = &mut self.workbook.worksheets[i].index;
                if !wins(&mut index.registers.merges, range, ts) {
                    return Ok(());
                }
                match (merged, index.merges.binary_search(range)) {
                    (true, Err(at)) => index.merges.insert(at, range.clone()),
                    (false, Ok(at)) => {
                        index.merges.remove(at);
                    }
                    _ => {}
                }
            }
            Patch::SetComment {
                sheet, at, comment, ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let index = &mut self.workbook.worksheets[i].index;
                if !wins(&mut index.registers.comments, at, ts) {
                    return Ok(());
                }
                match comment {
                    Some(comment) => {
                        index.comments.insert(at.clone(), comment.clone());
                    }
                    None => {
                        index.comments.remove(at);
                    }
                }
            }
            Patch::SetCellLink {
                sheet, at, link, ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let id = self.workbook.worksheets[i].sheet_id;
                let index = &mut self.workbook.worksheets[i].index;
                if !wins(&mut index.registers.links, at, ts) {
                    return Ok(());
                }
                match link {
                    Some(link) => {
                        index.links.insert(at.clone(), link.clone());
                    }
                    None => {
                        index.links.remove(at);
                    }
                }
                // if link refers to object that was not defined yet, remember it
                if let Some(StableLink::Internal { location, .. }) = link {
                    for name in location.unresolved_names() {
                        self.local
                            .unresolved
                            .entry(name.to_uppercase())
                            .or_default()
                            .insert((id, at.clone()));
                    }
                }
            }
            Patch::AddSheet {
                id,
                name,
                position,
                content,
            } => {
                if !wins(&mut self.workbook.meta.sheet_existence, id, ts) {
                    return Ok(());
                }
                self.workbook
                    .meta
                    .sheet_positions
                    .insert(*id, Lww::new(position.clone(), *ts));
                // Same register a rename writes: a redelivered add must not undo a later rename.
                self.file_sheet_name(*id, name, ts);
                if self.sheet_index(*id).is_none() {
                    let sheet = Worksheet {
                        dimension: "A1".to_string(),
                        cols: vec![],
                        rows: vec![],
                        name: name.clone(),
                        sheet_data: Default::default(),
                        shared_formulas: vec![],
                        sheet_id: *id,
                        state: SheetState::Visible,
                        color: Default::default(),
                        merged_cells: vec![],
                        comments: vec![],
                        frozen_rows: 0,
                        frozen_columns: 0,
                        show_grid_lines: true,
                        conditional_formatting: vec![],
                        links: HashMap::new(),
                        index: StableIndexes::new(self.suffix()),
                    };
                    self.workbook.worksheets.push(sheet);
                    self.parsed_formulas.push(Vec::new());
                    if let Some(content) = content {
                        let i = self.workbook.worksheets.len() - 1;
                        self.seed_sheet(i, content, ts)?;
                    }
                }
                self.sort_sheets();
                self.sheet_changed(*id);
            }
            Patch::DeleteSheet { sheet, .. } => {
                if !wins(&mut self.workbook.meta.sheet_existence, sheet, ts) {
                    return Ok(());
                }
                if let Some(i) = self.sheet_index(*sheet) {
                    let before = self.sheet_ids();
                    self.workbook.worksheets.remove(i);
                    self.realign_parsed(before);
                }
                self.sheet_changed(*sheet);
            }
            Patch::SetSheetProperty {
                sheet, property, ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                if let SheetProperty::Position(position) = property {
                    // Tab order outlives the sheet, so its guard rides in `sheet_positions` rather
                    // than the sheet's own registers.
                    if !self
                        .workbook
                        .meta
                        .sheet_positions
                        .entry(*sheet)
                        .or_default()
                        .merge(position.clone(), ts)
                    {
                        return Ok(());
                    }
                    self.sort_sheets();
                    return Ok(());
                }
                if let SheetProperty::Name(name) = property {
                    // The display name is derived, so a rename only files what the user authored.
                    self.file_sheet_name(*sheet, name, ts);
                    self.sheet_changed(*sheet);
                    return Ok(());
                }
                let registers = &mut self.workbook.worksheets[i].index.registers;
                if !wins(&mut registers.props, &property.kind(), ts) {
                    return Ok(());
                }
                let sheet = &mut self.workbook.worksheets[i];
                match property {
                    SheetProperty::Color(color) => sheet.color = color.clone(),
                    SheetProperty::State(state) => sheet.state = state.clone(),
                    SheetProperty::ShowGridLines(show) => sheet.show_grid_lines = *show,
                    SheetProperty::FrozenRows(rows) => sheet.frozen_rows = *rows,
                    SheetProperty::FrozenColumns(columns) => sheet.frozen_columns = *columns,
                    SheetProperty::Name(_) | SheetProperty::Position(_) => {
                        unreachable!("handled above")
                    }
                }
            }
            Patch::SetWorkbookProperty { property, .. } => {
                if !wins(&mut self.workbook.meta.props, &property.kind(), ts) {
                    return Ok(());
                }
                // The locale drives defined-name parsing; the theme and the name drive nothing lowered.
                if !matches!(
                    property,
                    WorkbookProperty::Theme(_) | WorkbookProperty::Name(_)
                ) {
                    self.local.dirty.structural = true;
                }
                match property {
                    WorkbookProperty::Theme(theme) => self.workbook.theme = (**theme).clone(),
                    WorkbookProperty::Locale(locale) => {
                        self.workbook.settings.locale = locale.clone()
                    }
                    WorkbookProperty::Timezone(tz) => self.workbook.settings.tz = tz.clone(),
                    WorkbookProperty::Name(name) => self.workbook.name = name.clone(),
                }
            }
            // `Workbook::defined_names` itself is derived from these registers by
            // `normalize_defined_names`.
            Patch::SetDefinedName { id, property, .. } => {
                let dirty = &mut self.local.dirty;
                dirty.names.insert(*id);
                dirty.unbound = true;
                dirty.structural = true;
                let state = self.workbook.meta.defined_names.entry(*id).or_default();
                // Each value guards itself, and the one this patch does not carry keeps the guard
                // it has — zero for an id first seen here, which any real write then beats.
                match property {
                    DefinedNameProperty::Name(address) => {
                        state.name.merge(address.clone(), ts);
                    }
                    DefinedNameProperty::Definition(formula) => {
                        state.formula.merge(formula.clone(), ts);
                    }
                }
            }
            // The style table itself is derived from these registers by `normalize_named_styles`.
            Patch::SetNamedStyle { id, property, .. } => {
                let state = self.workbook.meta.named_styles.entry(*id).or_default();
                // Each value guards itself, and the one this patch does not carry keeps the guard
                // it has — zero for an id first seen here, which any real write then beats.
                match property {
                    NamedStyleProperty::Name(name) => {
                        state.name.merge(name.clone(), ts);
                    }
                    NamedStyleProperty::Definition(definition) => {
                        state.definition.merge(definition.clone(), ts);
                    }
                }
            }
            Patch::AddConditionalFormat {
                sheet,
                key,
                rule,
                ranges,
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let registers = &mut self.workbook.worksheets[i].index.registers;
                let rule_wins = wins(&mut registers.cf, &(key.clone(), CfPropKind::Rule), ts);
                let ranges_win = wins(&mut registers.cf, &(key.clone(), CfPropKind::Ranges), ts);
                if !rule_wins || !ranges_win {
                    return Ok(());
                }
                if cf_slot(&self.workbook.worksheets[i], key).is_some() {
                    return Ok(());
                }
                let cf_rule = self.install_rule(i, key, rule);
                let sheet = &mut self.workbook.worksheets[i];
                sheet.index.cf_ranges.insert(key.clone(), ranges.clone());
                // The ordinal ranges are derived at the end of the commit.
                let cf = ConditionalFormatting {
                    ranges: Vec::new(),
                    cf_rule,
                    priority: 0,
                };
                insert_cf(sheet, key.clone(), cf);
                rank_cf(sheet);
            }
            Patch::DeleteConditionalFormat { sheet, key, .. } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                // The guards stay: they keep a concurrent edit from resurrecting the rule.
                if let Some(at) = cf_slot(sheet, key) {
                    sheet.index.registers.cf_order.remove(at);
                    sheet.index.registers.cf_formulas.remove(key);
                    sheet.index.cf_ranges.remove(key);
                    sheet.conditional_formatting.remove(at);
                    rank_cf(sheet);
                }
            }
            Patch::SetConditionalFormat {
                sheet,
                key,
                property,
                ..
            } => {
                let Some(i) = self.sheet_index(*sheet) else {
                    return Ok(());
                };
                let sheet = &mut self.workbook.worksheets[i];
                if let CfProperty::Priority(position) = property {
                    // Order outlives the rule's other registers, so its guard rides with its value.
                    if !sheet
                        .index
                        .registers
                        .cf_positions
                        .entry(key.clone())
                        .or_default()
                        .merge(position.clone(), ts)
                    {
                        return Ok(()); // outdated patch
                    }
                    rank_cf(sheet);
                    return Ok(());
                }
                if !wins(
                    &mut sheet.index.registers.cf,
                    &(key.clone(), property.kind()),
                    ts,
                ) {
                    return Ok(());
                }
                let Some(at) = cf_slot(sheet, key) else {
                    return Ok(());
                };
                match property {
                    CfProperty::Rule(rule) => {
                        let cf_rule = self.install_rule(i, key, rule);
                        self.workbook.worksheets[i].conditional_formatting[at].cf_rule = cf_rule;
                    }
                    CfProperty::Ranges(ranges) => {
                        sheet.index.cf_ranges.insert(key.clone(), ranges.clone());
                    }
                    CfProperty::Priority(_) => unreachable!("handled above"),
                }
            }
        }
        Ok(())
    }

    /// Turns a wire rule into a stored one with interning for deduplication.
    fn install_rule(&mut self, i: usize, key: &FractionalKey, wire: &StableCfRule) -> CfRule {
        let mut rule = wire.shape.clone();
        if let (Some(slot), Some(dxf)) = (rule.dxf_id_mut(), wire.dxf.as_ref()) {
            let dxfs = &mut self.workbook.styles.dxfs;
            *slot = match dxfs.iter().position(|held| held == dxf) {
                Some(at) => at as u32,
                None => {
                    dxfs.push(dxf.clone());
                    dxfs.len() as u32 - 1
                }
            };
        }
        let registers = &mut self.workbook.worksheets[i].index.registers;
        if wire.formulas.is_empty() {
            registers.cf_formulas.remove(key);
        } else {
            registers
                .cf_formulas
                .insert(key.clone(), wire.formulas.clone());
        }
        rule
    }

    /// Writes `value` into cell `at` of the `i`-th worksheet, `None` clearing it. The style already
    /// on the cell survives — it is a register of its own.
    fn write_cell(&mut self, i: usize, at: &StableCellAddress, value: Option<&CellInput>) {
        // A key with no position names nothing visible: the write lands in the registers only.
        let Some((row, column)) = self.workbook.worksheets[i].ordinal(at) else {
            return;
        };
        let sheet = &mut self.workbook.worksheets[i];
        let Some(value) = value else {
            sheet.sheet_data.remove_cell(row, column);
            sheet.index.covered.remove(&(row, column));
            return;
        };
        // Interning first: it needs the workbook, the cell needs the sheet.
        let shared_string = match value {
            CellInput::Text(text) => self.intern_string(text),
            _ => 0,
        };
        // A cell that already holds a formula keeps its entry; any other gets a new one.
        let f = match value {
            CellInput::Formula(formula)
            | CellInput::Array(formula)
            | CellInput::Cse { formula, .. } => {
                let sheet = &self.workbook.worksheets[i];
                let held = (sheet.sheet_data.cell(row, column)).and_then(|cell| cell.get_formula());
                self.lower_entry(i, held, at, (row, column), &formula.refs, &formula.text)
            }
            _ => 0,
        };
        let sheet = &mut self.workbook.worksheets[i];
        let style = sheet.authored_style((row, column)).unwrap_or(0);
        let cell = build_cell(value, style, shared_string, f);
        sheet.sheet_data.set_cell(row, column, cell);
        // A spill the value replaced covers nothing any more.
        sheet.index.covered.remove(&(row, column));
        // use [CollabSession::unresolved] to remember the names of object that couldn't be mapped
        // to their IDs
        if let CellInput::Formula(formula)
        | CellInput::Array(formula)
        | CellInput::Cse { formula, .. } = value
        {
            let id = self.workbook.worksheets[i].sheet_id;
            for name in formula.unresolved_names() {
                self.local
                    .unresolved
                    .entry(name.to_uppercase())
                    .or_default()
                    .insert((id, at.clone()));
            }
        }
    }

    /// Rebuilds the unresolved-name register from the workbook: it's only called when a state is
    /// deserialized.
    fn index_unresolved(&mut self) {
        self.local.unresolved.clear();
        for sheet in &self.workbook.worksheets {
            for (row, column, cell) in sheet.sheet_data.cells() {
                let Some(f) = cell.get_formula() else {
                    continue;
                };
                let (Some(row_key), Some(column_key)) = (
                    sheet.index.rows.key(row as usize - 1),
                    sheet.index.cols.key(column as usize - 1),
                ) else {
                    continue;
                };
                let Some(entry) = sheet.index.formulas.get(f as usize) else {
                    continue;
                };
                for name in unresolved_names(&entry.refs) {
                    self.local
                        .unresolved
                        .entry(name.to_uppercase())
                        .or_default()
                        .insert((sheet.sheet_id, (row_key.clone(), column_key.clone())));
                }
            }
            for (at, link) in &sheet.index.links {
                let StableLink::Internal { location, .. } = link else {
                    continue;
                };
                for name in location.unresolved_names() {
                    self.local
                        .unresolved
                        .entry(name.to_uppercase())
                        .or_default()
                        .insert((sheet.sheet_id, at.clone()));
                }
            }
        }
    }

    /// Fills a freshly created sheet from the payload an `AddSheet` carried.
    fn seed_sheet(
        &mut self,
        i: usize,
        content: &SheetContent,
        ts: &Timestamp,
    ) -> Result<(), CodecError> {
        let suffix = self.suffix();
        let sheet = &mut self.workbook.worksheets[i];
        sheet.state = content.state.clone();
        sheet.color = content.color.clone();
        sheet.show_grid_lines = content.show_grid_lines;
        sheet.frozen_rows = content.frozen_rows;
        sheet.frozen_columns = content.frozen_columns;

        match &content.index {
            SheetIndexSeed::Encoded { rows, columns } => {
                sheet.index.rows = FractionalIndex::decode(rows, suffix)?;
                sheet.index.cols = FractionalIndex::decode(columns, suffix)?;
            }
            SheetIndexSeed::Extent {
                rows: height,
                columns: width,
            } => {
                // The used extent first: index ordinals are list positions, so an imported sheet needs
                // the rows and columns before its cells to exist for them to read where the file put them.
                let mut rows: Vec<&FractionalKey> =
                    content.rows.iter().map(|(key, _)| key).collect();
                let mut cols: Vec<&FractionalKey> = content
                    .columns
                    .iter()
                    .flat_map(|((min, max), _)| [min, max])
                    .filter(|key| !key.is_empty())
                    .collect();
                let mut cells = Vec::with_capacity(content.cell_values.len());
                for (at, _) in &content.cell_values {
                    cells.push(at);
                }
                for (at, _) in &content.cell_styles {
                    cells.push(at);
                }
                for (at, _) in &content.comments {
                    cells.push(at);
                }
                for (at, _) in &content.links {
                    cells.push(at);
                }
                for (row, col) in cells {
                    rows.push(row);
                    cols.push(col);
                }
                let rows: Vec<FractionalKey> = (1..=*height)
                    .map(virtual_key)
                    .chain(rows.into_iter().cloned())
                    .collect();
                let cols: Vec<FractionalKey> = (1..=*width)
                    .map(virtual_key)
                    .chain(cols.into_iter().cloned())
                    .collect();
                sheet.index.rows.insert_keys_at(&rows, ts.hlc);
                sheet.apply_reorder(Axis::Rows);
                sheet.index.cols.insert_keys_at(&cols, ts.hlc);
                sheet.apply_reorder(Axis::Columns);
            }
        }

        for (key, state) in &content.rows {
            self.seed_row(i, key, state, ts);
        }
        for (span, state) in &content.columns {
            self.seed_column(i, span, state, ts);
        }
        for (at, value) in &content.cell_values {
            self.workbook.worksheets[i]
                .index
                .registers
                .cell_values
                .insert(at.clone(), *ts);
            self.write_cell(i, at, Some(value));
        }
        let mut interned: HashMap<&Style, (i32, Vec<PropKind>)> = HashMap::new();
        for (at, style) in &content.cell_styles {
            let (s, kinds) = match interned.get(style) {
                Some(hit) => hit,
                None => {
                    let entry = (self.intern_style(style), set_kinds(style).collect());
                    interned.entry(style).or_insert(entry)
                }
            };
            let s = *s;
            let sheet = &mut self.workbook.worksheets[i];
            for &kind in kinds {
                sheet
                    .index
                    .registers
                    .cell_styles
                    .insert((at.clone(), kind), *ts);
            }
            let Some((row, column)) = sheet.ordinal(at) else {
                continue;
            };
            match sheet.sheet_data.cell_mut(row, column) {
                Some(cell) => cell.set_style(s),
                None => {
                    sheet
                        .sheet_data
                        .set_cell(row, column, Cell::EmptyCell { s });
                }
            }
        }

        let below = Timestamp::new(Hlc::new(ts.hlc.get().saturating_sub(1)), ts.session);
        for (at, id, owned) in &content.cell_parents {
            let index = &mut self.workbook.worksheets[i].index;
            index.parents.insert(at.clone(), *id);
            let registers = &mut index.registers.cell_styles;
            registers.insert((at.clone(), PropKind::StyleRef), below);
            for kind in PropKind::STYLE {
                let Some(category) = kind.category() else {
                    continue;
                };
                let key = (at.clone(), kind);
                if category.included(owned) {
                    registers.insert(key, *ts);
                } else if let Some(stamp) = registers.get_mut(&key) {
                    *stamp = below;
                }
            }
            self.derive_cell(i, at);
        }

        let sheet = &mut self.workbook.worksheets[i];
        let index = &mut sheet.index;
        for range in &content.merge_cells {
            index.registers.merges.insert(range.clone(), *ts);
            index.merges.push(range.clone());
        }
        // The payload is ordered, but nothing stops a peer from sending it otherwise.
        index.merges.sort();
        index.merges.dedup();
        for (at, comment) in &content.comments {
            index.registers.comments.insert(at.clone(), *ts);
            index.comments.insert(at.clone(), comment.clone());
        }
        for (at, link) in &content.links {
            index.registers.links.insert(at.clone(), *ts);
            index.links.insert(at.clone(), link.clone());
        }
        sheet.rows.sort_by_key(|row| row.r);

        for (key, state) in &content.conditional_formatting {
            let cf_rule = self.install_rule(i, key, &state.rule);
            let sheet = &mut self.workbook.worksheets[i];
            let registers = &mut sheet.index.registers;
            registers.cf.insert((key.clone(), CfPropKind::Rule), *ts);
            registers.cf.insert((key.clone(), CfPropKind::Ranges), *ts);
            if let Some(position) = &state.position {
                registers
                    .cf_positions
                    .entry(key.clone())
                    .or_default()
                    .merge(position.clone(), ts); // resolve potential conflicting position changes
            }
            sheet
                .index
                .cf_ranges
                .insert(key.clone(), state.ranges.clone());
            let cf = ConditionalFormatting {
                ranges: Vec::new(),
                cf_rule,
                priority: 0,
            };
            // the payload is ordered by key, but nothing stops a peer from sending it otherwise
            insert_cf(sheet, key.clone(), cf);
        }
        rank_cf(&mut self.workbook.worksheets[i]);
        rebuild_touched(&mut self.workbook.worksheets[i].index);

        // sometimes we couldn't resolve location of internal link (it doesn't exist yet), so we
        // need to remember it
        let id = self.workbook.worksheets[i].sheet_id;
        for (at, link) in &content.links {
            let StableLink::Internal { location, .. } = link else {
                continue;
            };
            for name in location.unresolved_names() {
                self.local
                    .unresolved
                    .entry(name.to_uppercase())
                    .or_default()
                    .insert((id, at.clone()));
            }
        }
        self.derive_sparse(i);
        Ok(())
    }

    fn seed_row(&mut self, i: usize, key: &FractionalKey, state: &RowState, ts: &Timestamp) {
        let s = match &state.style {
            Some(style) => self.intern_style(style),
            None => 0,
        };
        let sheet = &mut self.workbook.worksheets[i];
        // Only the registers the seed actually sets: a default height is not a write, so a snapshot
        // never restores one as custom.
        if state.custom_height {
            sheet
                .index
                .registers
                .rows
                .insert((key.clone(), PropKind::Height), *ts);
        }
        if state.hidden {
            sheet
                .index
                .registers
                .rows
                .insert((key.clone(), PropKind::Hidden), *ts);
        }
        if let Some(style) = &state.style {
            for kind in set_kinds(style) {
                sheet.index.registers.rows.insert((key.clone(), kind), *ts);
            }
        }
        let row = Row {
            r: 0,
            height: state.height,
            custom_format: state.custom_format,
            custom_height: state.custom_height,
            s,
            hidden: state.hidden,
        };
        // A full index seed (a sheet copy, a restore) carries hidden rows too.
        match sheet.index.rows.position_of(key) {
            Some(p) => sheet.rows.push(Row {
                r: p as i32 + 1,
                ..row
            }),
            None => {
                sheet.index.hidden_rows.insert(key.clone(), row);
            }
        }
    }

    fn seed_column(
        &mut self,
        i: usize,
        span: &(FractionalKey, FractionalKey),
        state: &ColState,
        ts: &Timestamp,
    ) {
        let style = state.style.as_ref().map(|style| self.intern_style(style));
        let sheet = &mut self.workbook.worksheets[i];
        if state.custom_width {
            sheet
                .index
                .registers
                .col_spans
                .insert((span.clone(), PropKind::Width), *ts);
        }
        if state.hidden {
            sheet
                .index
                .registers
                .col_spans
                .insert((span.clone(), PropKind::Hidden), *ts);
        }
        if let Some(style) = &state.style {
            for kind in set_kinds(style) {
                sheet
                    .index
                    .registers
                    .col_spans
                    .insert((span.clone(), kind), *ts);
            }
        }
        sheet.index.col_spans.insert(
            span.clone(),
            ColSpan {
                width: state.width,
                custom_width: state.custom_width,
                hidden: state.hidden,
                style,
            },
        );
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::unwrap_used)]
    use super::*;
    use crate::cf_types::CfRule;
    use crate::collab::model::CommentBody;
    use crate::collab::model::StableRange;
    use crate::collab::patch::DefinedNameBody;
    use crate::constants::{COLUMN_WIDTH_FACTOR, DEFAULT_COLUMN_WIDTH};
    use crate::types::{Color, RangeRef, Theme};

    /// Method-syntax delivery, chainable straight off [`rec`].
    trait Deliver {
        fn deliver(&self, model: &mut CollabModel<'_>);
    }

    impl Deliver for Commit {
        fn deliver(&self, model: &mut CollabModel<'_>) {
            model.apply(self).unwrap();
        }
    }

    /// A key some session minted: a position, then the session suffix.
    fn minted(position: &[u8], session: u8) -> FractionalKey {
        let mut bytes = position.to_vec();
        bytes.extend_from_slice(&[0, 0, 0, session]);
        FractionalKey::try_from_bytes(&bytes).unwrap()
    }

    /// A wall-clock millisecond in the past — Sept 2020, comfortably below the Nov 2022 constant
    /// [`crate::mock_time`] serves under `cfg(test)`. Fixed rather than read off the clock:
    /// `Consumer::apply` opens with `Hlc::sync`, so a stamp in the future would become the
    /// process-global high watermark and drag every concurrent test's `Hlc::now()` with it. A stamp
    /// from the past is no watermark at all.
    const PAST: Hlc = Hlc::new(1_600_000_000_000 << 16);

    /// A stamp `counter` steps into the millisecond after [`PAST`]: above anything stamped `PAST`,
    /// and sharing a millisecond with its siblings, so only the counter and session separate them.
    fn same_ms(counter: u64) -> Hlc {
        Hlc::new(PAST.get() + (1 << 16) + counter)
    }

    fn styled() -> Style {
        Style {
            quote_prefix: true,
            ..Default::default()
        }
    }

    /// A named style is defined by its formatting categories, never by a quote prefix.
    fn named_styled() -> Style {
        Style {
            font: crate::types::Font {
                b: true,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// A wire rule carrying no bound slots, so the text it ships survives as written: these tests
    /// are about the registers, not about what a formula resolves to.
    fn cf_rule(formula: &str) -> StableCfRule {
        StableCfRule {
            shape: cf_stored(formula),
            formulas: Vec::new(),
            dxf: None,
        }
    }

    fn cf_stored(formula: &str) -> CfRule {
        CfRule::Formula {
            formula: formula.to_string(),
            dxf_id: 0,
            stop_if_true: false,
        }
    }

    const SHEET: SheetId = 42;

    fn cell(model: &CollabModel<'_>, row: &FractionalKey, col: &FractionalKey) -> Option<Cell> {
        let sheet = model.workbook.worksheets.first()?;
        let (row, column) = sheet.ordinal(&(row.clone(), col.clone()))?;
        sheet
            .sheet_data
            .cell(row, column)
            .map(|cell| cell.into_owned())
    }

    /// A sheet with three rows and three columns, as commit 1.
    fn genesis(rows: &[FractionalKey], cols: &[FractionalKey]) -> Commit {
        Commit::new(
            1,
            Hlc::now(),
            vec![
                Patch::AddSheet {
                    id: SHEET,
                    name: "Sheet1".to_string(),
                    position: minted(&[0x10], 1),
                    content: None,
                },
                Patch::InsertRows {
                    sheet: SHEET,
                    keys: rows.to_vec(),
                },
                Patch::InsertColumns {
                    sheet: SHEET,
                    keys: cols.to_vec(),
                },
            ],
        )
    }

    #[test]
    fn apply_registers() {
        let rows: Vec<FractionalKey> = (1..=3).map(virtual_key).collect();
        let cols: Vec<FractionalKey> = (1..=3).map(virtual_key).collect();
        let mut model = CollabModel::new(1);

        let genesis = genesis(&rows, &cols);
        genesis.deliver(&mut model);
        assert_eq!(model.workbook.worksheets.len(), 1);
        assert_eq!(model.workbook.worksheets[0].name, "Sheet1");
        assert_eq!(model.workbook.worksheets[0].sheet_id, SHEET);
        assert_eq!(model.workbook.worksheets[0].index.rows.len(), 3);
        assert_eq!(model.workbook.worksheets[0].index.cols.len(), 3);

        // ---- cells: a literal, a string, a formula, and a clear ----
        let formula = model.bind_text(0, 2, 1, "A1*2");
        let values = Commit::new(
            1,
            Hlc::now(),
            vec![
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    value: Some(CellInput::Number(41.0)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[1].clone()),
                    value: Some(CellInput::Text("hello".to_string())),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[1].clone(), cols[0].clone()),
                    value: Some(CellInput::Formula(formula)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[2].clone(), cols[0].clone()),
                    value: Some(CellInput::Boolean(true)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[2].clone(), cols[0].clone()),
                    value: None,
                    ts: None,
                    prev: Box::default(),
                },
            ],
        );
        values.deliver(&mut model);
        assert_eq!(
            cell(&model, &rows[0], &cols[0]),
            Some(Cell::NumberCell { v: 41.0, s: 0 })
        );
        assert_eq!(
            cell(&model, &rows[0], &cols[1]),
            Some(Cell::SharedString { si: 0, s: 0 })
        );
        assert_eq!(model.workbook.shared_strings, ["hello"]);
        assert_eq!(model.shared_strings.get("hello"), Some(&0));
        assert_eq!(
            cell(&model, &rows[1], &cols[0]),
            Some(Cell::CellFormula {
                f: 0,
                s: 0,
                v: FormulaValue::Unevaluated
            })
        );
        // Interned once, and shown back as what was authored.
        assert_eq!(model.workbook.worksheets[0].shared_formulas.len(), 1);
        assert_eq!(
            model.get_cell_formula(0, 2, 1),
            Ok(Some("=A1*2".to_string()))
        );
        // The last write of a commit is the one that stands, so the cell is gone.
        assert_eq!(cell(&model, &rows[2], &cols[0]), None);

        // ---- every other register kind ----
        let merged = StableRange {
            rows: Some((rows[0].clone(), rows[1].clone())),
            cols: Some((cols[0].clone(), cols[1].clone())),
        };
        let comment = CommentBody {
            text: "look".to_string(),
            author_name: "me".to_string(),
            author_id: None,
        };
        let comment_at = (rows[1].clone(), cols[1].clone());
        let cf_key = minted(&[0x20], 1);
        let name_body = DefinedNameBody {
            formula: model.bind_text(0, 1, 1, "Sheet1!$A$1"),
            equals: false,
        };
        let rest = Commit::new(
            1,
            Hlc::now(),
            vec![
                Patch::SetCellStyle {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    props: vec![Property::QuotePrefix(true)],
                    ts: None,
                    prev: Vec::new(),
                },
                Patch::SetRowProperty {
                    sheet: SHEET,
                    row: rows[0].clone(),
                    props: vec![Property::Height(33.0)],
                    ts: None,
                    prev: Vec::new(),
                },
                Patch::SetColumnSpan {
                    sheet: SHEET,
                    span: (cols[0].clone(), cols[1].clone()),
                    props: vec![Property::Width(120.0)],
                    ts: None,
                    prev: Vec::new(),
                },
                // The whole-sheet span: the register `(NULL, NULL)` names and ordinal code cannot.
                Patch::SetColumnSpan {
                    sheet: SHEET,
                    span: (FractionalKey::NULL, FractionalKey::NULL),
                    props: vec![Property::Hidden(true)],
                    ts: None,
                    prev: Vec::new(),
                },
                Patch::SetSheetProperty {
                    sheet: SHEET,
                    property: SheetProperty::Name("Renamed".to_string()),
                    prev: None,
                },
                Patch::SetSheetProperty {
                    sheet: SHEET,
                    property: SheetProperty::Color(Color::Rgb("#ff0000".to_string())),
                    prev: None,
                },
                Patch::SetMergedRange {
                    sheet: SHEET,
                    range: merged.clone(),
                    merged: true,
                    prev: false,
                },
                Patch::SetComment {
                    sheet: SHEET,
                    at: comment_at.clone(),
                    comment: Some(comment.clone()),
                    prev: None,
                },
                Patch::SetDefinedName {
                    id: 3,
                    property: DefinedNameProperty::Name((None, "total".to_string())),
                    prev: None,
                },
                Patch::SetDefinedName {
                    id: 3,
                    property: DefinedNameProperty::Definition(Some(name_body)),
                    prev: None,
                },
                Patch::SetNamedStyle {
                    id: 7,
                    property: NamedStyleProperty::Definition(Some(Box::new(NamedStyle {
                        style: named_styled(),
                        builtin_id: 0,
                        includes: Default::default(),
                    }))),
                    prev: None,
                },
                Patch::SetNamedStyle {
                    id: 7,
                    property: NamedStyleProperty::Name("Good".to_string()),
                    prev: None,
                },
                Patch::SetWorkbookProperty {
                    property: WorkbookProperty::Locale("es".to_string()),
                    prev: None,
                },
                Patch::SetWorkbookProperty {
                    property: WorkbookProperty::Theme(Box::new(Theme {
                        name: "Dark".to_string(),
                        ..Default::default()
                    })),
                    prev: None,
                },
                Patch::AddConditionalFormat {
                    sheet: SHEET,
                    key: cf_key.clone(),
                    rule: Box::new(cf_rule("A1>0")),
                    ranges: vec![merged.clone()],
                },
                Patch::SetConditionalFormat {
                    sheet: SHEET,
                    key: cf_key.clone(),
                    property: CfProperty::Rule(Box::new(cf_rule("A1>5"))),
                    prev: None,
                },
            ],
        );
        rest.deliver(&mut model);

        let sheet = &model.workbook.worksheets[0];
        let style_index = cell(&model, &rows[0], &cols[0]).unwrap().get_style();
        assert_ne!(style_index, 0);
        assert_eq!(
            model.workbook.styles.get_style(style_index).unwrap(),
            styled()
        );
        assert_eq!(sheet.rows.len(), 1);
        assert_eq!(sheet.rows[0].r, 1); // the ordinal rows[0] sits at
        assert_eq!(sheet.rows[0].height, 33.0);
        assert!(sheet.rows[0].custom_height);
        // Each span keeps its state; the records are what the spans resolve to, the open-ended one
        // covering every column, those past the index's tail included.
        assert_eq!(sheet.index.col_spans.len(), 2);
        assert_eq!(
            sheet.index.col_spans[&(cols[0].clone(), cols[1].clone())].width,
            120.0
        );
        assert!(sheet.index.col_spans[&(FractionalKey::NULL, FractionalKey::NULL)].hidden);
        let hidden = |min, max, width, custom_width| Col {
            min,
            max,
            width,
            custom_width,
            hidden: true,
            style: None,
        };
        let default_width = DEFAULT_COLUMN_WIDTH / COLUMN_WIDTH_FACTOR;
        assert_eq!(
            sheet.cols,
            vec![
                hidden(1, 2, 120.0, true),
                hidden(3, LAST_COLUMN, default_width, false)
            ]
        );
        assert_eq!(sheet.name, "Renamed");
        assert_eq!(sheet.color, Color::Rgb("#ff0000".to_string()));
        assert_eq!(sheet.index.merges, vec![merged.clone()]);
        let merged_cell = MergedCell {
            row: 1,
            column: 1,
            width: 2,
            height: 2,
        };
        assert_eq!(sheet.merged_cells, vec![merged_cell]);
        assert_eq!(sheet.index.comments[&comment_at], comment);
        assert_eq!(
            sheet.comments,
            vec![Comment {
                text: "look".to_string(),
                author_name: "me".to_string(),
                author_id: None,
                cell_ref: (2, 2),
            }]
        );
        assert_eq!(sheet.conditional_formatting.len(), 1);
        assert_eq!(sheet.conditional_formatting[0].cf_rule, cf_stored("A1>5"));
        assert_eq!(sheet.index.cf_ranges[&cf_key], vec![merged.clone()]);
        assert_eq!(
            sheet.conditional_formatting[0].ranges,
            vec![RangeRef::from(&merged_cell)]
        );
        assert_eq!(sheet.conditional_formatting[0].priority, 1);
        assert_eq!(sheet.index.registers.cf_order, vec![cf_key.clone()]);
        assert_eq!(model.workbook.defined_names.len(), 1);
        // The body is stored bound, so it shows the sheet's *current* name with nothing rewritten.
        assert_eq!(model.workbook.defined_names[0].formula, "Renamed!$A$1");
        assert_eq!(model.workbook.settings.locale, "es");
        assert_eq!(model.workbook.theme.name, "Dark");
        let named = model
            .workbook
            .styles
            .get_or_create_style_index_by_name("Good")
            .unwrap();
        assert_eq!(
            model.workbook.styles.get_style(named).unwrap(),
            named_styled()
        );

        // ---- redelivery changes nothing ----
        let before = model.workbook.clone();
        rest.deliver(&mut model);
        assert_eq!(model.workbook, before);

        // ---- a write stamped below the guard is ignored ----
        Commit::new(
            1,
            Hlc::new(1),
            vec![
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    value: Some(CellInput::Number(0.0)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetSheetProperty {
                    sheet: SHEET,
                    property: SheetProperty::Name("Stale".to_string()),
                    prev: None,
                },
            ],
        )
        .deliver(&mut model);
        assert_eq!(
            cell(&model, &rows[0], &cols[0]),
            Some(Cell::NumberCell {
                v: 41.0,
                s: style_index
            })
        );
        assert_eq!(model.workbook.worksheets[0].name, "Renamed");

        // ---- a patch for a sheet nobody has is a no-op, not an error ----
        let before = model.workbook.clone();
        Commit::new(
            1,
            Hlc::now(),
            vec![Patch::SetCellValue {
                sheet: 999,
                at: (rows[0].clone(), cols[0].clone()),
                value: Some(CellInput::Number(1.0)),
                ts: None,
                prev: Box::default(),
            }],
        )
        .deliver(&mut model);
        assert_eq!(model.workbook, before);
    }

    #[test]
    fn apply_structural() {
        // Minted keys and virtual ones side by side: both are just keys to the index.
        let rows = vec![virtual_key(1), virtual_key(2), minted(&[0x00, 0x06], 1)];
        let cols = vec![virtual_key(1), virtual_key(2)];
        let mut log = vec![genesis(&rows, &cols)];

        let mut patches = Vec::new();
        for row in &rows {
            for col in &cols {
                patches.push(Patch::SetCellValue {
                    sheet: SHEET,
                    at: (row.clone(), col.clone()),
                    value: Some(CellInput::Text(format!("{row:?}/{col:?}"))),
                    ts: None,
                    prev: Box::default(),
                });
            }
        }
        log.push(Commit::new(1, Hlc::now(), patches));

        // A move is a pair: the identity that moves, and the destination its author minted.
        let dest = minted(&[0x00, 0x09], 1);
        log.push(Commit::new(
            1,
            Hlc::now(),
            vec![Patch::MoveRows {
                sheet: SHEET,
                moves: vec![(rows[0].clone(), dest.clone())],
                prev: vec![],
            }],
        ));
        log.push(Commit::new(
            1,
            Hlc::now(),
            vec![
                Patch::DeleteRows {
                    sheet: SHEET,
                    keys: vec![rows[1].clone()],
                    prev: Vec::new(),
                },
                Patch::DeleteColumns {
                    sheet: SHEET,
                    keys: vec![cols[1].clone()],
                    prev: Vec::new(),
                },
            ],
        ));

        let mut model = CollabModel::new(1);
        for rec in &log {
            rec.deliver(&mut model);
        }

        let sheet = &model.workbook.worksheets[0];
        // The moved row answers to the key it was minted as, at its new position.
        assert_eq!(Stable::row_ordinal(&sheet.index, &rows[0]), Some(2));
        assert_eq!(Stable::row_ordinal(&sheet.index, &rows[2]), Some(1));
        // ...and its cells moved with it.
        let text = |row: &FractionalKey| match cell(&model, row, &cols[0]) {
            Some(Cell::SharedString { si, .. }) => model.workbook.shared_strings.get(si as usize),
            _ => None,
        };
        assert_eq!(sheet.sheet_data.cells_in_row(2).len(), 1);
        assert_eq!(
            text(&rows[0]),
            Some(&format!("{:?}/{:?}", rows[0], cols[0]))
        );
        assert_eq!(
            text(&rows[2]),
            Some(&format!("{:?}/{:?}", rows[2], cols[0]))
        );
        // The deleted row and column took their cells with them.
        assert_eq!(Stable::row_ordinal(&sheet.index, &rows[1]), None);
        assert_eq!(sheet.sheet_data.rows(), vec![1, 2]);
        assert!(sheet.sheet_data.cells().all(|(_, column, _)| column == 1));
        assert_eq!(sheet.index.rows.len(), 2);
        assert_eq!(sheet.index.cols.len(), 1);

        // The identical sequence lands on the identical workbook — indexes and registers included.
        let mut peer = CollabModel::new(2);
        for rec in &log {
            rec.deliver(&mut peer);
        }
        assert_eq!(peer.workbook, model.workbook);
    }

    #[test]
    fn convergence_smoke() {
        let rows: Vec<FractionalKey> = (1..=3).map(virtual_key).collect();
        let cols: Vec<FractionalKey> = (1..=2).map(virtual_key).collect();
        let doomed: SheetId = 7;

        // The whole scenario is stamped from the fixed past base, so the commits below keep their
        // relative order while none of them touches the process-global clock.
        let root = Commit::new(
            1,
            PAST,
            vec![
                Patch::AddSheet {
                    id: SHEET,
                    name: "Sheet1".to_string(),
                    position: minted(&[0x10], 1),
                    content: None,
                },
                Patch::InsertRows {
                    sheet: SHEET,
                    keys: rows.clone(),
                },
                Patch::InsertColumns {
                    sheet: SHEET,
                    keys: cols.clone(),
                },
                Patch::AddSheet {
                    id: doomed,
                    name: "Doomed".to_string(),
                    position: minted(&[0x20], 1),
                    content: None,
                },
                Patch::InsertRows {
                    sheet: doomed,
                    keys: rows.clone(),
                },
                Patch::InsertColumns {
                    sheet: doomed,
                    keys: cols.clone(),
                },
            ],
        );

        // Everything below is concurrent: same parent, stamps inside one wall millisecond, so only
        // the HLC counter and the session tiebreak separate them.
        let from_a = Commit::new(
            1,
            same_ms(1),
            vec![
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    value: Some(CellInput::Number(1.0)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::MoveRows {
                    sheet: SHEET,
                    moves: vec![(rows[0].clone(), minted(&[0x00, 0x09], 1))],
                    prev: vec![],
                },
                Patch::SetSheetProperty {
                    sheet: SHEET,
                    property: SheetProperty::Name("From A".to_string()),
                    prev: None,
                },
                // Racing the delete below. A literal, not a string: the intern table is local, so a
                // peer that never saw the write would legitimately lack the entry.
                Patch::SetCellValue {
                    sheet: doomed,
                    at: (rows[1].clone(), cols[0].clone()),
                    value: Some(CellInput::Number(99.0)),
                    ts: None,
                    prev: Box::default(),
                },
            ],
        );
        let from_b = Commit::new(
            2,
            same_ms(1),
            vec![
                // Same register, same stamp: the session breaks the tie, identically everywhere.
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    value: Some(CellInput::Number(2.0)),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::MoveRows {
                    sheet: SHEET,
                    moves: vec![(rows[0].clone(), minted(&[0x00, 0x03], 2))],
                    prev: vec![],
                },
                Patch::SetSheetProperty {
                    sheet: SHEET,
                    property: SheetProperty::Name("From B".to_string()),
                    prev: None,
                },
                Patch::DeleteSheet {
                    sheet: doomed,
                    prev: None,
                },
            ],
        );

        // A third concurrent write, one HLC step further: the counter alone puts it above both,
        // low session id notwithstanding.
        let later = Commit::new(
            1,
            same_ms(2),
            vec![Patch::SetSheetProperty {
                sheet: SHEET,
                property: SheetProperty::Name("Later".to_string()),
                prev: None,
            }],
        );

        let mut a = CollabModel::new(1);
        let mut b = CollabModel::new(2);
        root.deliver(&mut a);
        root.deliver(&mut b);
        // Causally respected, but the concurrent commits arrive in different orders.
        from_a.deliver(&mut a);
        later.deliver(&mut a);
        from_b.deliver(&mut a);
        from_b.deliver(&mut b);
        from_a.deliver(&mut b);
        later.deliver(&mut b);

        assert_eq!(a.workbook, b.workbook);
        // The cell tie went to the higher session...
        assert_eq!(
            cell(&a, &rows[0], &cols[0]),
            Some(Cell::NumberCell { v: 2.0, s: 0 })
        );
        // ...but the sheet name went to the highest counter in that millisecond.
        assert_eq!(a.workbook.worksheets[0].name, "Later");
        // One row moved twice, still exactly one row.
        assert_eq!(a.workbook.worksheets[0].index.rows.len(), 3);
        assert_eq!(
            a.workbook.worksheets[0]
                .index
                .rows
                .view()
                .filter(|k| **k == rows[0])
                .count(),
            1
        );
        // The delete wins over the write to the sheet it removed, whichever arrived first.
        assert_eq!(a.workbook.worksheets.len(), 1);
        assert!(a.workbook.meta.sheet_existence.contains_key(&doomed));
    }

    /// Overlapping spans and reordered rules: two things only concurrency can produce, and both
    /// have to read the same on every replica whatever order the commits arrived in.
    #[test]
    fn overlap_and_priority() {
        let rows: Vec<FractionalKey> = (1..=2).map(virtual_key).collect();
        let cols: Vec<FractionalKey> = (1..=5).map(virtual_key).collect();
        let (first, second) = (minted(&[0x20], 1), minted(&[0x30], 1));

        let root = Commit::new(1, PAST, genesis(&rows, &cols).patches);
        // A wide span from one replica, a narrower one from another, one HLC step later.
        let wide = Commit::new(
            1,
            same_ms(1),
            vec![
                Patch::SetColumnSpan {
                    sheet: SHEET,
                    span: (cols[0].clone(), cols[3].clone()),
                    props: vec![Property::Width(10.0)],
                    ts: None,
                    prev: Vec::new(),
                },
                Patch::SetColumnSpan {
                    sheet: SHEET,
                    span: (cols[0].clone(), cols[3].clone()),
                    props: vec![Property::Hidden(true)],
                    ts: None,
                    prev: Vec::new(),
                },
                Patch::AddConditionalFormat {
                    sheet: SHEET,
                    key: first.clone(),
                    rule: Box::new(cf_rule("A1>0")),
                    ranges: vec![],
                },
                Patch::AddConditionalFormat {
                    sheet: SHEET,
                    key: second.clone(),
                    rule: Box::new(cf_rule("A1>1")),
                    ranges: vec![],
                },
            ],
        );
        let narrow = Commit::new(
            2,
            same_ms(2),
            vec![
                Patch::SetColumnSpan {
                    sheet: SHEET,
                    span: (cols[1].clone(), cols[1].clone()),
                    props: vec![Property::Width(20.0)],
                    ts: None,
                    prev: Vec::new(),
                },
                // The second rule takes a position below the first one's identity key.
                Patch::SetConditionalFormat {
                    sheet: SHEET,
                    key: second.clone(),
                    property: CfProperty::Priority(minted(&[0x10], 2)),
                    prev: None,
                },
            ],
        );

        let mut a = CollabModel::new(1);
        let mut b = CollabModel::new(2);
        for rec in [&root, &wide, &narrow] {
            rec.deliver(&mut a);
        }
        for rec in [&root, &narrow, &wide] {
            rec.deliver(&mut b);
        }
        assert_eq!(a.workbook, b.workbook);

        // The newest span covering a position wins it, per position and per property kind. Columns
        // 1..4 are hidden — which a width read reports as 0 — so the register is what has to be
        // compared to see which span won the width.
        let width = |m: &CollabModel, column: i32| {
            (m.workbook.worksheets[0].cols.iter())
                .find(|col| (col.min..=col.max).contains(&column))
                .map(|col| col.width)
        };
        assert_eq!(width(&a, 1), width(&a, 3));
        assert_ne!(width(&a, 1), width(&a, 2));
        assert_eq!(a.get_column_width(0, 5).unwrap(), DEFAULT_COLUMN_WIDTH);
        for column in 1..=5 {
            assert_eq!(width(&a, column), width(&b, column));
            assert_eq!(
                a.is_column_hidden(0, column).unwrap(),
                b.is_column_hidden(0, column).unwrap()
            );
        }
        // The narrower span wrote no `Hidden` register, so the wide one still owns that property.
        assert!(a.is_column_hidden(0, 2).unwrap());
        assert!(!a.is_column_hidden(0, 5).unwrap());

        // Storage stays in creation order — a caller's index must not move — and only the
        // priorities follow the moved rule, which now sorts lowest.
        let sheet = &a.workbook.worksheets[0];
        assert_eq!(sheet.index.registers.cf_order, vec![first, second]);
        assert_eq!(sheet.conditional_formatting[0].cf_rule, cf_stored("A1>0"));
        let priorities: Vec<u32> = sheet
            .conditional_formatting
            .iter()
            .map(|cf| cf.priority)
            .collect();
        assert_eq!(priorities, vec![2, 1]);
        assert_eq!(
            b.workbook.worksheets[0].index.registers.cf_order,
            sheet.index.registers.cf_order
        );
    }

    #[test]
    fn snapshot_round_trip() {
        let rows: Vec<FractionalKey> = (1..=3).map(virtual_key).collect();
        let cols: Vec<FractionalKey> = (1..=2).map(virtual_key).collect();
        let mut model = CollabModel::new(1);
        genesis(&rows, &cols).deliver(&mut model);
        Commit::new(
            1,
            Hlc::now(),
            vec![
                Patch::SetCellValue {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    value: Some(CellInput::Text("kept".to_string())),
                    ts: None,
                    prev: Box::default(),
                },
                Patch::SetCellStyle {
                    sheet: SHEET,
                    at: (rows[0].clone(), cols[0].clone()),
                    props: vec![Property::QuotePrefix(true)],
                    ts: None,
                    prev: Vec::new(),
                },
            ],
        )
        .deliver(&mut model);

        // A third replica picks the snapshot up, so the keys it mints are its own.
        let restored = CollabModel::decode(&model.encode(), 3).unwrap();
        assert_eq!(restored.workbook, model.workbook);
        assert_eq!(restored.shared_strings, model.shared_strings);
        assert_eq!(
            restored.workbook.worksheets[0].index.rows.suffix,
            3u32.to_be_bytes()
        );

        // ...and it carries on from there.
        let next = Commit::new(
            3,
            Hlc::now(),
            vec![Patch::SetCellValue {
                sheet: SHEET,
                at: (rows[1].clone(), cols[1].clone()),
                value: Some(CellInput::Number(7.0)),
                ts: None,
                prev: Box::default(),
            }],
        );
        let mut restored = restored;
        next.deliver(&mut restored);
        next.deliver(&mut model);
        assert_eq!(restored.workbook, model.workbook);
    }
}
