//! The two conversions between a parsed formula and its stable form.
//!
//! A formula is stored and shipped as its R1C1 English text plus one slot per reference-shaped
//! leaf of its parse tree, in pre-order. Binding walks the parsed node and keys each leaf; lowering
//! parses the text for its shape and overwrites each leaf from its slot against the index.
//!
//! Both walks are iterative with an explicit stack: formula depth is author-controlled, so
//! recursing over a `Node` tree is a stack overflow waiting to happen.

use std::cell::OnceCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt;

use crate::collab::formula::{StableAxisRef, StableFormula, StableRef, StableSheetRef};
use crate::collab::fractional_index::FractionalIndex;
use crate::collab::fractional_key::FractionalKey;
use crate::collab::model::{CollabModel, Stable, StableIndexes};
use crate::collab::patch::{DefinedNameId, Patch, SheetId};
use crate::constants::{LAST_COLUMN, LAST_ROW};
use crate::expressions::lexer::LexerMode;
use crate::expressions::parser::stringify::to_rc_format;
use crate::expressions::parser::{Node, Parser};
use crate::expressions::token;
use crate::expressions::types::CellReferenceRC;
use crate::language::get_default_language;
use crate::locale::get_default_locale;

/// Per-lowering scratch: the defined-name display list, built lazily and reused across leaves.
type DisplayNameCache = OnceCell<Vec<(DefinedNameId, Option<SheetId>, String)>>;

/// Why a `Node` has no stable form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindError {
    /// A reference names a sheet that does not exist, or a row/column off the grid.
    UnboundReference,
    /// A name with no live defined-name entry to point at.
    UnresolvedDefinedName(String),
}

impl fmt::Display for BindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BindError::UnboundReference => write!(f, "reference does not resolve to a live cell"),
            BindError::UnresolvedDefinedName(name) => {
                write!(f, "defined name \"{name}\" not found")
            }
        }
    }
}

impl std::error::Error for BindError {}

/// What a `Wrong*` node's dead axis carries: absolute ordinal 0, which upstream both renders and
/// evaluates as `#REF!`.
const DEAD_AXIS: (bool, i32) = (true, 0);

/// The axis of an open range (`A:A`, `5:7`): no key, the grid's first or last row or column.
const OPEN_AXIS: StableAxisRef = StableAxisRef {
    key: FractionalKey::NULL,
    absolute: true,
};

/// Rows and columns that sheets have not materialized yet (but they were referenced by formulas).
/// Each `rows`/`cols` is a pair of (sheet-id, highest-referenced-row (or column)).
#[derive(Debug, Default)]
pub struct MintPlan {
    rows: BTreeMap<u32, i32>,
    cols: BTreeMap<u32, i32>,
}

impl MintPlan {
    fn note(axis: &mut BTreeMap<u32, i32>, at: u32, ordinal: i32) {
        let slot = axis.entry(at).or_default();
        *slot = (*slot).max(ordinal);
    }
}

/// The cell a formula is lowered against: relative references come back as offsets from it.
pub struct Host {
    pub sheet: u32,
    pub row: i32,
    pub column: i32,
}

impl Host {
    pub fn relative(sheet: u32, row: i32, column: i32) -> Self {
        Host { sheet, row, column }
    }
}

/// Whether `node` gets a slot. Whether a sheet or a name resolves only picks one of each pair, so a
/// text has the same leaves on every replica.
fn is_leaf(node: &Node) -> bool {
    matches!(
        node,
        Node::ReferenceKind { .. }
            | Node::WrongReferenceKind { .. }
            | Node::RangeKind { .. }
            | Node::WrongRangeKind { .. }
            | Node::DefinedNameKind(_)
            | Node::NamedVariableKind { .. }
    )
}

/// The reference-shaped leaves of `node`, in pre-order.
pub(crate) fn leaves(node: &Node) -> Vec<&Node> {
    let mut out = Vec::new();
    let mut stack = vec![node];
    // Children are pushed last-first so the stack pops them left to right.
    while let Some(node) = stack.pop() {
        match node {
            Node::OpRangeKind { left, right }
            | Node::OpConcatenateKind { left, right }
            | Node::OpSumKind { left, right, .. }
            | Node::OpProductKind { left, right, .. }
            | Node::OpPowerKind { left, right }
            | Node::CompareKind { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            Node::UnaryKind { right, .. } => stack.push(right),
            Node::ImplicitIntersection { child, .. } | Node::SpillRangeOperator { child } => {
                stack.push(child)
            }
            Node::LambdaDefKind { body, .. } => stack.push(body),
            Node::FunctionKind { args, .. } | Node::NamedFunctionKind { args, .. } => {
                stack.extend(args.iter().rev())
            }
            Node::LambdaCallKind { lambda, args } => {
                stack.extend(args.iter().rev());
                stack.push(lambda);
            }
            leaf if is_leaf(leaf) => out.push(leaf),
            _ => {}
        }
    }
    out
}

/// [`leaves`], for overwriting them.
pub(crate) fn leaves_mut(node: &mut Node) -> Vec<&mut Node> {
    let mut out = Vec::new();
    let mut stack = vec![node];
    while let Some(node) = stack.pop() {
        match node {
            Node::OpRangeKind { left, right }
            | Node::OpConcatenateKind { left, right }
            | Node::OpSumKind { left, right, .. }
            | Node::OpProductKind { left, right, .. }
            | Node::OpPowerKind { left, right }
            | Node::CompareKind { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            Node::UnaryKind { right, .. } => stack.push(right),
            Node::ImplicitIntersection { child, .. } | Node::SpillRangeOperator { child } => {
                stack.push(child)
            }
            Node::LambdaDefKind { body, .. } => stack.push(body),
            Node::FunctionKind { args, .. } | Node::NamedFunctionKind { args, .. } => {
                stack.extend(args.iter_mut().rev())
            }
            Node::LambdaCallKind { lambda, args } => {
                stack.extend(args.iter_mut().rev());
                stack.push(lambda);
            }
            leaf if is_leaf(leaf) => out.push(leaf),
            _ => {}
        }
    }
    out
}

/// Parses stored text — R1C1, English — for its shape only. A parser that knows the host sheet and
/// nothing else: the leaves are overwritten from their slots anyway, and a parse that read the
/// replica's sheet and name tables would give `LAMBDA(a, …)` a different shape wherever a name `a`
/// is defined.
pub(crate) fn parse_shape(text: &str, sheet: &str, row: i32, column: i32) -> Node {
    let mut parser = Parser::new(
        vec![sheet.to_string()],
        vec![],
        HashMap::new(),
        get_default_locale(),
        get_default_language(),
    );
    parser.set_lexer_mode(LexerMode::R1C1);
    let context = CellReferenceRC {
        sheet: sheet.to_string(),
        row,
        column,
    };
    parser.parse(text, &context)
}

/// An axis' `(absolute, value)` pair: an ordinal when absolute, else an offset from `host`. `None`
/// when the key has no active position.
fn lower_axis(index: &FractionalIndex, axis: &StableAxisRef, host: i32) -> Option<(bool, i32)> {
    let ordinal = index.position_of(&axis.key)? as i32 + 1;
    Some(match axis.absolute {
        true => (true, ordinal),
        false => (false, ordinal - host),
    })
}

fn lower_span(
    index: &FractionalIndex,
    last: i32,
    lo: &StableAxisRef,
    hi: &StableAxisRef,
    host: i32,
) -> [Option<(bool, i32)>; 2] {
    // A dead corner clamps inwards like `resolve_axis`: the low one up, the high one down.
    let corner = |axis: &StableAxisRef, open: i32, dead: i32| match axis.key.is_empty() {
        true => ((open, axis.absolute), true),
        false => match index.position_of(&axis.key) {
            Some(p) => ((p as i32 + 1, axis.absolute), true),
            None => (
                (index.active_index(&axis.key) as i32 + dead, axis.absolute),
                false,
            ),
        },
    };
    let ((mut first, live_lo), (mut second, live_hi)) = (corner(lo, 1, 1), corner(hi, last, 0));
    // Concurrent moves can invert the live corners; the span they bound is still the same one.
    if live_lo && live_hi && first.0 > second.0 {
        (first, second) = (second, first);
    }
    // Every cell of the span was deleted.
    if first.0 > second.0 {
        return [None, None];
    }
    let relative = |(ordinal, absolute): (i32, bool)| match absolute {
        true => (true, ordinal),
        false => (false, ordinal - host),
    };
    [Some(relative(first)), Some(relative(second))]
}

impl CollabModel<'_> {
    /// The ordering context of worksheet `at`, if it is live.
    fn indexes(&self, at: u32) -> Option<&StableIndexes> {
        self.workbook
            .worksheets
            .get(at as usize)
            .map(|ws| &ws.index)
    }

    fn sheet_id_at(&self, at: u32) -> Option<SheetId> {
        self.workbook
            .worksheets
            .get(at as usize)
            .map(|ws| ws.sheet_id)
    }

    fn position_of_sheet(&self, id: SheetId) -> Option<u32> {
        self.workbook
            .worksheets
            .iter()
            .position(|ws| ws.sheet_id == id)
            .map(|at| at as u32)
    }

    /// Binds a parsed formula authored in cell (`host_sheet`, `host_row`, `host_column`).
    ///
    /// If formula refers to row/column that doesn't exist yet, it will be recorded in `plan` and
    /// materialized later via [Patch::InsertRows]/[Patch::InsertColumns].
    pub fn bind_formula(
        &self,
        node: &Node,
        host_sheet: u32,
        host_row: i32,
        host_column: i32,
        plan: &mut MintPlan,
    ) -> Result<StableFormula, BindError> {
        // Unparseable text is stored verbatim, with nothing to key.
        if let Node::ParseErrorKind { formula, .. } = node {
            return Ok(StableFormula {
                text: formula.clone(),
                refs: Vec::new(),
            });
        }
        let refs = leaves(node)
            .into_iter()
            .map(|leaf| self.bind_leaf(leaf, host_sheet, host_row, host_column, plan))
            .collect::<Result<_, _>>()?;
        Ok(StableFormula {
            text: to_rc_format(node),
            refs,
        })
    }

    /// The `InsertRows`/`InsertColumns` to create rows/columns required by formula bind.
    pub(crate) fn mint_patches(&self, plan: &MintPlan) -> Vec<Patch> {
        let mut patches = Vec::new();
        for (&sheet_idx, &row_idx) in plan.rows.iter() {
            let (Some(index), Some(sheet)) = (self.indexes(sheet_idx), self.sheet_id_at(sheet_idx))
            else {
                continue;
            };
            let keys = index.rows.plan_virtual(row_idx as usize);
            if keys.is_empty() {
                continue;
            }
            patches.push(Patch::InsertRows { sheet, keys });
        }
        for (&sheet_idx, &col_idx) in plan.cols.iter() {
            let (Some(index), Some(sheet)) = (self.indexes(sheet_idx), self.sheet_id_at(sheet_idx))
            else {
                continue;
            };
            let keys = index.cols.plan_virtual(col_idx as usize);
            if keys.is_empty() {
                continue;
            }
            patches.push(Patch::InsertColumns { sheet, keys });
        }
        patches
    }

    /// The key naming the row/column at `ordinal` on sheet `at`, per axis. One on the grid that the
    /// index has not reached yet is minted, exactly as a write to that cell would mint it.
    fn bind_axis(
        &self,
        at: u32,
        is_row: bool,
        absolute: bool,
        offset: i32,
        host: i32,
        plan: &mut MintPlan,
    ) -> Result<StableAxisRef, BindError> {
        let index = self.indexes(at).ok_or(BindError::UnboundReference)?;
        let ordinal = if absolute { offset } else { host + offset };
        let stored = if is_row {
            Stable::row_at(index, ordinal)
        } else {
            Stable::col_at(index, ordinal)
        };
        let key = match stored {
            Some(key) => key,
            None => {
                let (axis, limit, planned) = match is_row {
                    true => (&mut plan.rows, LAST_ROW, &index.rows),
                    false => (&mut plan.cols, LAST_COLUMN, &index.cols),
                };
                if ordinal > limit || ordinal < 1 {
                    return Err(BindError::UnboundReference);
                }
                // Planning is deterministic, so the key an ordinal gets is the same however many
                // times, and from however far, the axis is planned out to it.
                let key = planned
                    .plan_virtual(ordinal as usize)
                    .pop()
                    .ok_or(BindError::UnboundReference)?;
                MintPlan::note(axis, at, ordinal);
                key
            }
        };
        Ok(StableAxisRef { key, absolute })
    }

    /// The sheet a reference targets: its position, and whether it keeps an explicit prefix.
    fn bind_sheet(
        &self,
        sheet_name: &Option<String>,
        sheet_index: u32,
        host_sheet: u32,
    ) -> Result<(StableSheetRef, u32), BindError> {
        match sheet_name {
            None => Ok((StableSheetRef::Current, host_sheet)),
            // The parser already resolved the name; an explicit prefix is kept even for the host
            // sheet, for display fidelity.
            Some(_) => {
                let id = self
                    .sheet_id_at(sheet_index)
                    .ok_or(BindError::UnboundReference)?;
                Ok((StableSheetRef::Sheet(id), sheet_index))
            }
        }
    }

    /// The slot of one reference-shaped leaf.
    pub(crate) fn bind_leaf(
        &self,
        leaf: &Node,
        host_sheet: u32,
        host_row: i32,
        host_column: i32,
        plan: &mut MintPlan,
    ) -> Result<StableRef, BindError> {
        Ok(match leaf {
            Node::ReferenceKind {
                sheet_name,
                sheet_index,
                absolute_row,
                absolute_column,
                row,
                column,
            } => {
                let (sheet, at) = self.bind_sheet(sheet_name, *sheet_index, host_sheet)?;
                StableRef::Cell {
                    sheet,
                    row: self.bind_axis(at, true, *absolute_row, *row, host_row, plan)?,
                    col: self.bind_axis(at, false, *absolute_column, *column, host_column, plan)?,
                }
            }
            Node::RangeKind {
                sheet_name,
                sheet_index,
                absolute_row1,
                absolute_column1,
                row1,
                column1,
                absolute_row2,
                absolute_column2,
                row2,
                column2,
            } => {
                let (sheet, at) = self.bind_sheet(sheet_name, *sheet_index, host_sheet)?;
                // `A:A` and `5:7` span the whole grid on one axis: open ends, not the last row's key.
                let (row1, row2) =
                    if *absolute_row1 && *absolute_row2 && *row1 == 1 && *row2 == LAST_ROW {
                        (OPEN_AXIS, OPEN_AXIS)
                    } else {
                        (
                            self.bind_axis(at, true, *absolute_row1, *row1, host_row, plan)?,
                            self.bind_axis(at, true, *absolute_row2, *row2, host_row, plan)?,
                        )
                    };
                let (col1, col2) = if *absolute_column1
                    && *absolute_column2
                    && *column1 == 1
                    && *column2 == LAST_COLUMN
                {
                    (OPEN_AXIS, OPEN_AXIS)
                } else {
                    (
                        self.bind_axis(at, false, *absolute_column1, *column1, host_column, plan)?,
                        self.bind_axis(at, false, *absolute_column2, *column2, host_column, plan)?,
                    )
                };
                StableRef::Range {
                    sheet,
                    row1,
                    col1,
                    row2,
                    col2,
                }
            }
            // No sheet to key against: the leaf keeps the parser's own fields in the text, and
            // lowering retries the name.
            Node::WrongReferenceKind { sheet_name, .. }
            | Node::WrongRangeKind { sheet_name, .. } => {
                StableRef::Unresolved(sheet_name.clone().unwrap_or_default())
            }
            Node::DefinedNameKind((name, scope, _)) => {
                let scope = match scope {
                    Some(at) => Some(
                        self.sheet_id_at(*at)
                            .ok_or_else(|| BindError::UnresolvedDefinedName(name.clone()))?,
                    ),
                    None => None,
                };
                let id = self
                    .defined_name_id_of(scope, name)
                    .ok_or_else(|| BindError::UnresolvedDefinedName(name.clone()))?;
                StableRef::Name(id)
            }
            Node::NamedVariableKind { name, .. } => StableRef::Unresolved(name.clone()),
            // `leaves` hands nothing else over.
            _ => return Err(BindError::UnboundReference),
        })
    }

    pub(crate) fn lower(&self, text: &str, refs: &[StableRef], host: &Host) -> Node {
        let sheet = self
            .workbook
            .worksheets
            .get(host.sheet as usize)
            .map(|ws| ws.get_name())
            .unwrap_or_default();
        let mut node = parse_shape(text, &sheet, host.row, host.column);
        // Raw text the full parser rejected has no slots: if the name-blind parse finds leaves in
        // it anyway, it stays a parse error, as in the ordinal model.
        if refs.is_empty() && !leaves(&node).is_empty() {
            return Node::ParseErrorKind {
                formula: text.to_string(),
                message: "Invalid formula".to_string(),
                position: 0,
                expecting: Vec::new(),
            };
        }
        self.overwrite_leaves(&mut node, refs, host);
        node
    }

    /// Overwrites every reference-shaped leaf of `node` from `refs`, resolved against the index,
    /// returning whether the node changed. A slot count that differs from the leaf count is
    /// corruption: the whole node becomes `#REF!`.
    ///
    /// References whose sheet or key no longer resolves come back as the `Wrong*` nodes upstream
    /// evaluates to `#REF!`: displacement happens here, not by rewriting stored slots.
    pub(crate) fn overwrite_leaves(
        &self,
        node: &mut Node,
        refs: &[StableRef],
        host: &Host,
    ) -> bool {
        // Built at most once per call, and only if a name slot asks for it.
        let names = DisplayNameCache::new();
        let mut targets = leaves_mut(node);
        if targets.len() == refs.len() {
            let mut changed = false;
            for (leaf, slot) in targets.iter_mut().zip(refs) {
                let lowered = self.lower_leaf(slot, leaf, host, &names);
                if **leaf != lowered {
                    **leaf = lowered;
                    changed = true;
                }
            }
            return changed;
        }
        let corrupt = Node::ErrorKind(token::Error::REF);
        if *node == corrupt {
            return false;
        }
        *node = corrupt;
        true
    }

    fn lower_leaf(
        &self,
        slot: &StableRef,
        leaf: &Node,
        host: &Host,
        names: &DisplayNameCache,
    ) -> Node {
        match slot {
            StableRef::Cell { sheet, row, col } => {
                let (sheet_name, at) = self.lower_sheet(sheet, host.sheet);
                let (r, c) = match at.and_then(|at| self.indexes(at)) {
                    Some(index) => (
                        lower_axis(&index.rows, row, host.row),
                        lower_axis(&index.cols, col, host.column),
                    ),
                    None => (None, None),
                };
                match (at, r, c) {
                    (
                        Some(sheet_index),
                        Some((absolute_row, row)),
                        Some((absolute_column, column)),
                    ) => Node::ReferenceKind {
                        sheet_name,
                        sheet_index,
                        absolute_row,
                        absolute_column,
                        row,
                        column,
                    },
                    (_, r, c) => {
                        let (absolute_row, row) = r.unwrap_or(DEAD_AXIS);
                        let (absolute_column, column) = c.unwrap_or(DEAD_AXIS);
                        Node::WrongReferenceKind {
                            sheet_name,
                            absolute_row,
                            absolute_column,
                            row,
                            column,
                        }
                    }
                }
            }
            StableRef::Range {
                sheet,
                row1,
                col1,
                row2,
                col2,
            } => {
                let (sheet_name, at) = self.lower_sheet(sheet, host.sheet);
                let [r1, r2, c1, c2] = match at.and_then(|at| self.indexes(at)) {
                    Some(index) => {
                        let [r1, r2] = lower_span(&index.rows, LAST_ROW, row1, row2, host.row);
                        let [c1, c2] =
                            lower_span(&index.cols, LAST_COLUMN, col1, col2, host.column);
                        [r1, r2, c1, c2]
                    }
                    None => [None; 4],
                };
                let (absolute_row1, row1) = r1.unwrap_or(DEAD_AXIS);
                let (absolute_column1, column1) = c1.unwrap_or(DEAD_AXIS);
                let (absolute_row2, row2) = r2.unwrap_or(DEAD_AXIS);
                let (absolute_column2, column2) = c2.unwrap_or(DEAD_AXIS);
                // A wholly deleted span, or a missing sheet, is `#REF!`.
                match (at, [r1, c1, r2, c2].iter().all(Option::is_some)) {
                    (Some(sheet_index), true) => Node::RangeKind {
                        sheet_name,
                        sheet_index,
                        absolute_row1,
                        absolute_column1,
                        row1,
                        column1,
                        absolute_row2,
                        absolute_column2,
                        row2,
                        column2,
                    },
                    _ => Node::WrongRangeKind {
                        sheet_name,
                        absolute_row1,
                        absolute_column1,
                        row1,
                        column1,
                        absolute_row2,
                        absolute_column2,
                        row2,
                        column2,
                    },
                }
            }
            StableRef::Name(id) => self.lower_defined_name(*id, names),
            StableRef::Unresolved(name) => self.retry_unbound(name, leaf, host, names),
        }
    }

    /// An unbound leaf keeps what the text says and resolves its name anew: a sheet by that name
    /// showing up later makes it a live reference, and a defined name a live name, the way the
    /// ordinal model's reparse does. One that goes again falls back.
    fn retry_unbound(
        &self,
        name: &str,
        leaf: &Node,
        host: &Host,
        names: &DisplayNameCache,
    ) -> Node {
        match leaf {
            Node::ReferenceKind {
                sheet_name,
                absolute_row,
                absolute_column,
                row,
                column,
                ..
            }
            | Node::WrongReferenceKind {
                sheet_name,
                absolute_row,
                absolute_column,
                row,
                column,
            } => match sheet_name
                .as_deref()
                .and_then(|n| self.get_sheet_index_by_name(n))
            {
                Some(sheet_index) => Node::ReferenceKind {
                    sheet_name: sheet_name.clone(),
                    sheet_index,
                    absolute_row: *absolute_row,
                    absolute_column: *absolute_column,
                    row: *row,
                    column: *column,
                },
                None => Node::WrongReferenceKind {
                    sheet_name: sheet_name.clone(),
                    absolute_row: *absolute_row,
                    absolute_column: *absolute_column,
                    row: *row,
                    column: *column,
                },
            },
            Node::RangeKind {
                sheet_name,
                absolute_row1,
                absolute_column1,
                row1,
                column1,
                absolute_row2,
                absolute_column2,
                row2,
                column2,
                ..
            }
            | Node::WrongRangeKind {
                sheet_name,
                absolute_row1,
                absolute_column1,
                row1,
                column1,
                absolute_row2,
                absolute_column2,
                row2,
                column2,
            } => match sheet_name
                .as_deref()
                .and_then(|n| self.get_sheet_index_by_name(n))
            {
                Some(sheet_index) => Node::RangeKind {
                    sheet_name: sheet_name.clone(),
                    sheet_index,
                    absolute_row1: *absolute_row1,
                    absolute_column1: *absolute_column1,
                    row1: *row1,
                    column1: *column1,
                    absolute_row2: *absolute_row2,
                    absolute_column2: *absolute_column2,
                    row2: *row2,
                    column2: *column2,
                },
                None => Node::WrongRangeKind {
                    sheet_name: sheet_name.clone(),
                    absolute_row1: *absolute_row1,
                    absolute_column1: *absolute_column1,
                    row1: *row1,
                    column1: *column1,
                    absolute_row2: *absolute_row2,
                    absolute_column2: *absolute_column2,
                    row2: *row2,
                    column2: *column2,
                },
            },
            _ => match self.named_variable_id(name, host, names) {
                Some(id) => self.lower_defined_name(id, names),
                None => Node::NamedVariableKind {
                    name: name.to_string(),
                    id: None,
                },
            },
        }
    }

    /// The sheet a reference names: how it renders, and where it sits — `None` once it is deleted,
    /// which leaves its keys with no index to resolve against.
    fn lower_sheet(
        &self,
        sheet: &StableSheetRef,
        host_sheet: u32,
    ) -> (Option<String>, Option<u32>) {
        let StableSheetRef::Sheet(id) = sheet else {
            return (None, Some(host_sheet));
        };
        match self.position_of_sheet(*id) {
            Some(at) => (
                Some(self.workbook.worksheets[at as usize].name.clone()),
                Some(at),
            ),
            // The name register outlives the sheet, so a revived id renders as it did before.
            None => (
                self.workbook
                    .meta
                    .sheet_names
                    .get(id)
                    .map(|name| name.value.clone()),
                None,
            ),
        }
    }

    /// The defined name a bare name in a formula stands for, looked up as the parser looks one up:
    /// the host sheet's own scope first, then the workbook scope. `None` if no live name matches.
    fn named_variable_id(
        &self,
        name: &str,
        host: &Host,
        names: &DisplayNameCache,
    ) -> Option<DefinedNameId> {
        let upper = name.to_uppercase();
        let display = names.get_or_init(|| self.defined_name_display());
        let find = |scope: Option<SheetId>| {
            display
                .iter()
                .find(|(_, s, shown)| *s == scope && shown.to_uppercase() == upper)
                .map(|(id, ..)| *id)
        };
        self.sheet_id_at(host.sheet)
            .and_then(|id| find(Some(id)))
            .or_else(|| find(None))
    }

    /// A live name lowers to its current display name and formula; a deleted one to the node the
    /// parser builds for a name it does not know, which evaluates to `#NAME?`.
    fn lower_defined_name(&self, id: DefinedNameId, names: &DisplayNameCache) -> Node {
        let unknown = || match self.workbook.meta.defined_names.get(&id) {
            Some(state) => Node::NamedVariableKind {
                name: state.name.value.1.clone(),
                id: None,
            },
            // No register ever held this id: there is not even a name left to render.
            None => Node::ErrorKind(token::Error::NAME),
        };
        // Only live names are listed, and a live name always has a formula.
        let Some((_, sheet_id, name)) = names
            .get_or_init(|| self.defined_name_display())
            .iter()
            .find(|(entry, ..)| *entry == id)
        else {
            return unknown();
        };
        let (sheet_id, name) = (*sheet_id, name.clone());
        let scope = match sheet_id {
            Some(sheet) => match self.position_of_sheet(sheet) {
                Some(at) => Some(at),
                None => return unknown(),
            },
            None => None,
        };
        // The body text is the projection `normalize_defined_names` already lowered, so lowering a
        // name never re-lowers another name's body.
        match self
            .workbook
            .defined_names
            .iter()
            .find(|dn| dn.sheet_id == sheet_id && dn.name == name)
        {
            Some(dn) => Node::DefinedNameKind((name, scope, dn.formula.clone())),
            None => unknown(),
        }
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;
    use crate::collab::log::Commit;
    use crate::collab::patch::invert_patches;
    use crate::expressions::token::OpUnary;
    use crate::model::Model;
    use crate::types::Cell;
    use std::collections::HashSet;

    /// A workbook with two sheets, each materialized out to `rows` x `columns`.
    fn model(rows: i32, columns: i32) -> CollabModel<'static> {
        let mut model = CollabModel::new(1);
        for sheet in 0..2 {
            model.new_sheet();
            model
                .set_user_input(sheet, rows, columns, "1".to_string())
                .unwrap();
        }
        model
    }

    /// The entry the formula cell at `(row, column)` points at.
    fn entry_at(model: &CollabModel<'_>, sheet: u32, row: i32, column: i32) -> usize {
        let ws = &model.workbook.worksheets[sheet as usize];
        match &*ws.sheet_data.cell(row, column).unwrap() {
            Cell::CellFormula { f, .. } | Cell::ArrayFormula { f, .. } => *f as usize,
            other => panic!("not a formula cell: {other:?}"),
        }
    }

    /// The parsed AST the model holds for the formula in a cell.
    fn node_at(model: &CollabModel<'_>, sheet: u32, row: i32, column: i32) -> Node {
        let f = entry_at(model, sheet, row, column);
        (*model.parsed_formulas[sheet as usize][f].0).clone()
    }

    /// Binds against a model whose grid is already materialized, so nothing needs minting.
    fn bind(
        model: &CollabModel<'_>,
        node: &Node,
        sheet: u32,
        row: i32,
        column: i32,
    ) -> Result<StableFormula, BindError> {
        model.bind_formula(node, sheet, row, column, &mut MintPlan::default())
    }

    /// Bind, ship through bitcode, lower again.
    fn round_trip(model: &CollabModel<'_>, node: &Node, sheet: u32, row: i32, column: i32) -> Node {
        let bound = bind(model, node, sheet, row, column).unwrap();
        let decoded: StableFormula = bitcode::decode(&bitcode::encode(&bound)).unwrap();
        assert_eq!(decoded, bound);
        model.lower(
            &decoded.text,
            &decoded.refs,
            &Host::relative(sheet, row, column),
        )
    }

    /// A slot's variant name, for coverage bookkeeping.
    fn kind_of(slot: &StableRef) -> String {
        let name = format!("{slot:?}");
        let end = name.find(['(', ' ']).unwrap_or(name.len());
        name[..end].to_string()
    }

    /// The commits of the last local edits, undone.
    fn undo(model: &mut CollabModel<'_>, commits: &[Commit]) {
        let undo: Vec<_> = commits
            .iter()
            .rev()
            .flat_map(|commit| invert_patches(&commit.patches))
            .collect();
        model.commit_local(undo);
    }

    /// Every formula a text can produce survives bind → bytes → lower unchanged, from any host
    /// cell, and every slot kind is produced.
    #[test]
    fn bind_lower_round_trip() {
        let mut model = model(30, 15);
        model
            .new_defined_name("MyName", None, "Sheet1!$A$1")
            .unwrap();
        let mut seen: HashSet<String> = HashSet::new();
        let formulas = [
            "=1+2*3-4/5",
            "=\"a\"&\"b\"",
            "=2^3%",
            "=-A1",
            "=TRUE",
            "=A1+$B$2",
            "=$A1+A$2",
            "=Sheet2!C3",
            "=Sheet1!C3",
            "=SUM(Sheet2!A1:B3)",
            "=SUM(A$1:$B2)",
            "=SUM(A:A)+SUM(2:3)",
            "=IF(A1>0,\"y\",-A1%)",
            "=IF(A1<>1,A1,)",
            "=#VALUE!",
            "={TRUE,1;\"s\",#REF!}",
            "=@A1",
            "=A1#",
            "=LAMBDA(a,b,a*b)(2,3)",
            "=LET(x,1,x+A1)",
            "=myLambda(1,A1)",
            "=MyName*2",
            "=notAName",
            "=Nope!A1+SUM(Nope!A1:B2)",
            "=SUM(A1:A5)*MyName",
        ];
        for (host_row, host_column) in [(1, 1), (5, 3), (12, 7)] {
            for text in formulas {
                model
                    .set_user_input(0, host_row, host_column, text.to_string())
                    .unwrap();
                let node = node_at(&model, 0, host_row, host_column);
                let bound = bind(&model, &node, 0, host_row, host_column).unwrap();
                seen.extend(bound.refs.iter().map(kind_of));
                let lowered = round_trip(&model, &node, 0, host_row, host_column);
                assert_eq!(lowered, node, "{text} at ({host_row}, {host_column})");
                // The stored text is the R1C1 rendering of the stored node.
                let f = entry_at(&model, 0, host_row, host_column);
                assert_eq!(
                    model.workbook.worksheets[0].shared_formulas[f],
                    to_rc_format(&node)
                );
            }
        }
        for kind in ["Cell", "Range", "Name", "Unresolved"] {
            assert!(seen.contains(kind), "no formula produced a {kind} slot");
        }
    }

    /// A bound reference names rows and columns, not positions: structural edits move what it
    /// lowers to with no rewrite of its slots, and deleting its target turns it into a `#REF!` node.
    #[test]
    fn references_follow_structural_ops() {
        let mut model = model(30, 15);
        let node = Node::OpSumKind {
            kind: crate::expressions::token::OpSum::Add,
            left: Box::new(Node::ReferenceKind {
                sheet_name: None,
                sheet_index: 0,
                absolute_row: false,
                absolute_column: false,
                row: 5 - 10,
                column: 1 - 2,
            }),
            right: Box::new(Node::ReferenceKind {
                sheet_name: None,
                sheet_index: 0,
                absolute_row: true,
                absolute_column: true,
                row: 6,
                column: 1,
            }),
        };
        let bound = bind(&model, &node, 0, 10, 2).unwrap();

        let refs = |model: &CollabModel<'_>, host_row: i32| match model.lower(
            &bound.text,
            &bound.refs,
            &Host::relative(0, host_row, 2),
        ) {
            Node::OpSumKind { left, right, .. } => (*left, *right),
            other => panic!("not a sum: {other:?}"),
        };

        // Two rows above everything: both targets and the host slide down, so the relative offset
        // is unchanged and the absolute ordinal is not.
        model.insert_rows(0, 1, 2).unwrap();
        let (left, right) = refs(&model, 12);
        assert!(matches!(left, Node::ReferenceKind { row: -5, .. }));
        assert!(matches!(
            right,
            Node::ReferenceKind {
                row: 8,
                absolute_row: true,
                ..
            }
        ));

        // A row between the target and the host: only the host moves, so the offset grows.
        model.insert_rows(0, 8, 1).unwrap();
        let (left, right) = refs(&model, 13);
        assert!(matches!(left, Node::ReferenceKind { row: -6, .. }));
        assert!(matches!(right, Node::ReferenceKind { row: 9, .. }));

        // Deleting the row the left reference names leaves it with nothing to point at.
        model.delete_rows(0, 7, 1).unwrap();
        let (left, right) = refs(&model, 12);
        assert!(matches!(
            left,
            Node::WrongReferenceKind {
                row: 0,
                absolute_row: true,
                ..
            }
        ));
        assert!(matches!(right, Node::ReferenceKind { row: 8, .. }));

        // Columns work the same way.
        model.insert_columns(0, 1, 3).unwrap();
        let (_, right) = refs(&model, 12);
        assert!(matches!(right, Node::ReferenceKind { column: 4, .. }));

        // A cross-sheet reference outlives its sheet: it renders under the name the register kept,
        // and comes back for real once the sheet does.
        // A restore brings back only the rows and columns the sheet's content named, so the target
        // is a cell that holds something.
        model.set_user_input(1, 1, 1, "7".to_string()).unwrap();
        let cross = Node::ReferenceKind {
            sheet_name: Some("Sheet2".to_string()),
            sheet_index: 1,
            absolute_row: true,
            absolute_column: true,
            row: 1,
            column: 1,
        };
        let bound = bind(&model, &cross, 0, 1, 1).unwrap();
        assert_eq!(
            model.lower(&bound.text, &bound.refs, &Host::relative(0, 1, 1)),
            cross
        );

        model.flush();
        model.delete_sheet(1).unwrap();
        assert_eq!(
            model.lower(&bound.text, &bound.refs, &Host::relative(0, 1, 1)),
            Node::WrongReferenceKind {
                sheet_name: Some("Sheet2".to_string()),
                absolute_row: true,
                absolute_column: true,
                row: 0,
                column: 0,
            }
        );

        let commits = model.flush();
        undo(&mut model, &commits);
        assert_eq!(
            model.lower(&bound.text, &bound.refs, &Host::relative(0, 1, 1)),
            cross
        );
    }

    /// What has no stable form at all, and what is stored verbatim instead.
    #[test]
    fn bind_rejects_and_rawtext() {
        let mut model = model(10, 5);
        model
            .new_defined_name("MyName", None, "Sheet1!$A$1")
            .unwrap();

        let unknown_sheet = Node::WrongReferenceKind {
            sheet_name: Some("Nope".to_string()),
            absolute_row: true,
            absolute_column: true,
            row: 1,
            column: 1,
        };
        assert_eq!(
            round_trip(&model, &unknown_sheet, 0, 1, 1),
            unknown_sheet.clone()
        );

        let relative = |row: i32, column: i32| Node::ReferenceKind {
            sheet_name: None,
            sheet_index: 0,
            absolute_row: false,
            absolute_column: false,
            row,
            column,
        };
        let cases = [
            // Offsets landing off the grid, above it and past its end.
            (relative(-1, 0), BindError::UnboundReference),
            (relative(0, -1), BindError::UnboundReference),
            // Past the grid itself, not merely past what the index has reached.
            (relative(LAST_ROW, 0), BindError::UnboundReference),
            (relative(0, LAST_COLUMN), BindError::UnboundReference),
            (
                Node::DefinedNameKind(("Nope".to_string(), None, "=1".to_string())),
                BindError::UnresolvedDefinedName("Nope".to_string()),
            ),
        ];
        for (node, expected) in cases {
            assert_eq!(bind(&model, &node, 0, 1, 1).unwrap_err(), expected);
        }

        // Unparseable text is the whole formula, with nothing to key, and comes back as it went in.
        let raw = Node::ParseErrorKind {
            formula: "=this is not a formula".to_string(),
            message: "boom".to_string(),
            position: 5,
            expecting: Vec::new(),
        };
        let bound = bind(&model, &raw, 0, 1, 1).unwrap();
        assert_eq!(
            bound,
            StableFormula {
                text: "=this is not a formula".to_string(),
                refs: Vec::new(),
            }
        );
        assert_eq!(
            to_rc_format(&round_trip(&model, &raw, 0, 1, 1)),
            to_rc_format(&raw)
        );

        // A deleted defined name lowers to the node the parser builds for a name it never heard
        // of, which evaluates to #NAME?.
        let name = Node::DefinedNameKind(("MyName".to_string(), None, "=Sheet1!$A$1".to_string()));
        let bound = bind(&model, &name, 0, 1, 1).unwrap();
        model.delete_defined_name("MyName", None).unwrap();
        assert_eq!(
            model.lower(&bound.text, &bound.refs, &Host::relative(0, 1, 1)),
            Node::NamedVariableKind {
                name: "MyName".to_string(),
                id: None,
            }
        );
        // An id no register ever held has not even a name left.
        let unknown = StableFormula {
            text: "MyName".to_string(),
            refs: vec![StableRef::Name(7)],
        };
        assert_eq!(
            model.lower(&unknown.text, &unknown.refs, &Host::relative(0, 1, 1)),
            Node::ErrorKind(token::Error::NAME)
        );
        // A slot count that differs from the leaf count is corruption.
        let corrupt = StableFormula {
            text: "R1C1+R2C2".to_string(),
            refs: vec![StableRef::Name(7)],
        };
        assert_eq!(
            model.lower(&corrupt.text, &corrupt.refs, &Host::relative(0, 1, 1)),
            Node::ErrorKind(token::Error::REF)
        );
    }

    /// Depth the recursive-descent parser could never produce from text: the walks that bind and
    /// re-lower a node are iterative, so depth is no limit for them.
    #[test]
    fn deep_formula_no_overflow() {
        let model = model(5, 5);
        let depth = 8_000;
        let mut node = Node::ReferenceKind {
            sheet_name: None,
            sheet_index: 0,
            absolute_row: true,
            absolute_column: true,
            row: 2,
            column: 3,
        };
        for _ in 0..depth {
            node = Node::UnaryKind {
                kind: OpUnary::Minus,
                right: Box::new(node),
            };
        }
        let refs = leaves(&node)
            .into_iter()
            .map(|leaf| model.bind_leaf(leaf, 0, 1, 1, &mut MintPlan::default()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(refs.len(), 1);
        // Lowered against the index as it is, the leaf is what it was.
        assert!(!model.overwrite_leaves(&mut node, &refs, &Host::relative(0, 1, 1)));
        // Comparing or dropping the tree recurses, so it is walked and dismantled iteratively.
        let mut cursor = &node;
        let mut seen = 0;
        while let Node::UnaryKind { right, .. } = cursor {
            cursor = right;
            seen += 1;
        }
        assert_eq!(seen, depth);
        assert!(matches!(cursor, Node::ReferenceKind { row: 2, .. }));
        let mut tree = node;
        while let Node::UnaryKind { right, .. } = tree {
            tree = *right;
        }
    }

    #[test]
    fn stable_ordinal_parity() {
        let mut o = Model::new_empty("model", "en", "UTC", "en").unwrap();
        let mut c = CollabModel::new(1);
        c.new_sheet();
        for model_sheet in [o.new_sheet().1, c.new_sheet().1] {
            assert_eq!(model_sheet, 1);
        }
        for row in 1..=6 {
            let value = format!("{row}");
            o.set_user_input(0, row, 1, value.clone()).unwrap();
            c.set_user_input(0, row, 1, value).unwrap();
        }
        for (row, column, value) in [(2, 2, "10"), (1, 3, "0.5")] {
            o.set_user_input(1, row, column, value.to_string()).unwrap();
            c.set_user_input(1, row, column, value.to_string()).unwrap();
        }
        o.new_defined_name("tax", None, "Sheet2!$C$1").unwrap();
        c.new_defined_name("tax", None, "Sheet2!$C$1").unwrap();
        let formula = "=SUM(A1:A4)+Sheet2!$B$2*tax";
        o.set_user_input(0, 5, 4, formula.to_string()).unwrap();
        c.set_user_input(0, 5, 4, formula.to_string()).unwrap();
        let same = |o: &mut Model, c: &mut CollabModel, row: i32, step: &str| {
            o.evaluate();
            c.evaluate();
            assert_eq!(
                c.get_cell_formula(0, row, 4),
                o.get_cell_formula(0, row, 4),
                "{step}"
            );
            assert_eq!(
                c.get_formatted_cell_value(0, row, 4),
                o.get_formatted_cell_value(0, row, 4),
                "{step}"
            );
        };
        same(&mut o, &mut c, 5, "seed");

        let (sheet1, sheet2) = (
            c.workbook.worksheets[0].sheet_id,
            c.workbook.worksheets[1].sheet_id,
        );
        let tax = c.defined_name_id_of(None, "tax").unwrap();
        let f = entry_at(&c, 0, 5, 4);
        let text = |c: &CollabModel<'_>| c.workbook.worksheets[0].shared_formulas[f].clone();
        assert_eq!(text(&c), "SUM(R[-4]C[-3]:R[-1]C[-3])+Sheet2!R2C2*tax");
        let index = &c.workbook.worksheets[0].index;
        let refs = &index.formulas[f].refs;
        assert!(matches!(
            refs.as_slice(),
            [
                StableRef::Range {
                    sheet: StableSheetRef::Current,
                    ..
                },
                StableRef::Cell {
                    sheet: StableSheetRef::Sheet(id),
                    row: StableAxisRef { absolute: true, .. },
                    col: StableAxisRef { absolute: true, .. },
                },
                StableRef::Name(name),
            ] if *id == sheet2 && *name == tax
        ));
        let users = HashSet::from([f as u32]);
        assert_eq!(index.referenced_by.get(&sheet1), Some(&users));
        assert_eq!(index.referenced_by.get(&sheet2), Some(&users));
        assert_eq!(index.names_referenced_by.get(&tax), Some(&users));

        // Two rows before row 3: the host is now D7, and A1:A4 rows 1..6.
        o.insert_rows(0, 3, 2).unwrap();
        c.insert_rows(0, 3, 2).unwrap();
        same(&mut o, &mut c, 7, "insert rows");
        assert_eq!(text(&c), "SUM(R[-6]C[-3]:R[-1]C[-3])+Sheet2!R2C2*tax");
        assert_eq!(
            c.get_cell_formula(0, 7, 4),
            Ok(Some("=SUM(A1:A6)+Sheet2!$B$2*tax".to_string()))
        );

        o.rename_sheet_by_index(1, "Data").unwrap();
        c.rename_sheet_by_index(1, "Data").unwrap();
        same(&mut o, &mut c, 7, "rename sheet");
        assert_eq!(text(&c), "SUM(R[-6]C[-3]:R[-1]C[-3])+Data!R2C2*tax");

        // The low corner's row goes: the range shrinks to the rows left, as in Excel. The ordinal
        // model's displacement still prints a `#REF!` corner here, so the two diverge.
        c.flush();
        o.delete_rows(0, 1, 1).unwrap();
        c.delete_rows(0, 1, 1).unwrap();
        o.evaluate();
        c.evaluate();
        assert_eq!(
            c.get_cell_formula(0, 6, 4),
            Ok(Some("=SUM(A1:A5)+Data!$B$2*tax".to_string()))
        );
        assert_eq!(
            o.get_cell_formula(0, 6, 4),
            Ok(Some("=SUM(#REF!:A5)+Data!$B$2*tax".to_string()))
        );

        // The slot kept the key, so the undo brings the range back whole.
        let commits = c.flush();
        undo(&mut c, &commits);
        c.evaluate();
        assert_eq!(
            c.get_cell_formula(0, 7, 4),
            Ok(Some("=SUM(A1:A6)+Data!$B$2*tax".to_string()))
        );
        // 1 + 2 + 3 + 4 over the six rows, plus 10 * 0.5.
        assert_eq!(c.get_formatted_cell_value(0, 7, 4), Ok("15".to_string()));
    }

    fn shape(leaf: &Node) -> &'static str {
        match leaf {
            Node::ReferenceKind { .. } | Node::WrongReferenceKind { .. } => "reference",
            Node::RangeKind { .. } | Node::WrongRangeKind { .. } => "range",
            _ => "name",
        }
    }

    /// The same text lowers to the same leaves on a replica that names its sheets and defined names
    /// differently, and to the same node once both replicas hold the same workbook.
    #[test]
    fn shape_is_stable_across_replicas() {
        let mut a = model(10, 5);
        a.new_defined_name("tax", None, "0.5").unwrap(); // A: tax=0.5
        let mut b = CollabModel::new(2);
        b.apply_batch(&a.flush()).unwrap();
        // `b` renames a sheet and defines names `a` would read differently.
        b.rename_sheet_by_index(1, "Other").unwrap();
        b.new_defined_name("a", None, "1").unwrap(); // B: a=1
        b.new_defined_name("Nope", None, "2").unwrap(); // B: Nope=2
        let formulas = [
            "=LAMBDA(a,b,a*b)(2,3)",
            "=Sheet2!A1+SUM(Sheet2!A1:B3)",
            "=tax*2",
            "=Nope!A1+Nope",
            "=SUM(A:A)+LET(x,1,x+A1)",
        ];
        let mut bound = Vec::new();
        for (row, text) in formulas.iter().enumerate() {
            let row = row as i32 + 1;
            a.set_user_input(0, row, 3, text.to_string()).unwrap();
            let node = node_at(&a, 0, row, 3);
            let formula = bind(&a, &node, 0, row, 3).unwrap();
            let on_b = b.lower(&formula.text, &formula.refs, &Host::relative(0, row, 3));
            assert_eq!(
                leaves(&on_b).into_iter().map(shape).collect::<Vec<_>>(),
                leaves(&node).into_iter().map(shape).collect::<Vec<_>>(),
                "{text}"
            );
            bound.push((row, formula));
        }
        // Once both hold the same workbook, the same slots lower to the same node.
        let (from_a, from_b) = (a.flush(), b.flush());
        a.apply_batch(&from_b).unwrap();
        b.apply_batch(&from_a).unwrap();
        for (row, formula) in bound {
            assert_eq!(
                a.lower(&formula.text, &formula.refs, &Host::relative(0, row, 3)),
                b.lower(&formula.text, &formula.refs, &Host::relative(0, row, 3)),
            );
            assert_eq!(node_at(&a, 0, row, 3), node_at(&b, 0, row, 3));
        }
        // ...and what the user sees agrees too: the same text, evaluating to the same value.
        a.evaluate();
        b.evaluate();
        for (row, text) in formulas.iter().enumerate() {
            let row = row as i32 + 1;
            let shown = a.get_cell_formula(0, row, 3).unwrap();
            assert!(shown.is_some(), "{text} shows no formula");
            assert_eq!(b.get_cell_formula(0, row, 3).unwrap(), shown, "{text}");
            assert_eq!(
                a.get_formatted_cell_value(0, row, 3),
                b.get_formatted_cell_value(0, row, 3),
                "{text}"
            );
        }
    }

    /// A LAMBDA parameter named like a defined name is a parse error to the full parser but not to
    /// the name-blind one: the text stays as typed and errors, as in the ordinal model and on a
    /// peer. So does a plain parse error.
    #[test]
    fn lambda_parameter_shadowing_a_name_keeps_the_text() {
        let mut o = Model::new_empty("model", "en", "UTC", "en").unwrap();
        let mut a = CollabModel::new(1);
        a.new_sheet();
        o.new_defined_name("a", None, "Sheet1!$F$2").unwrap();
        a.new_defined_name("a", None, "Sheet1!$F$2").unwrap();
        let cases = [(1, "=LAMBDA(a,b,a*b)(2,3)"), (2, "=1+")];
        for (row, text) in cases {
            o.set_user_input(0, row, 1, text.to_string()).unwrap();
            a.set_user_input(0, row, 1, text.to_string()).unwrap();
        }
        let mut b = CollabModel::new(2);
        b.apply_batch(&a.flush()).unwrap();
        o.evaluate();
        a.evaluate();
        b.evaluate();
        for (row, text) in cases {
            let formula = o.get_cell_formula(0, row, 1).unwrap();
            let value = o.get_formatted_cell_value(0, row, 1).unwrap();
            assert_eq!(formula.as_deref(), Some(text), "{text}");
            assert_eq!(value, "#ERROR!", "{text}");
            for c in [&a, &b] {
                assert_eq!(c.get_cell_formula(0, row, 1).unwrap(), formula, "{text}");
                assert_eq!(c.get_formatted_cell_value(0, row, 1).unwrap(), value);
            }
        }
        // The cell recovers once a valid formula replaces the text.
        a.cell_clear_contents(0, 1, 1).unwrap();
        a.set_user_input(0, 1, 1, "=LAMBDA(x,y,x*y)(2,3)".to_string())
            .unwrap();
        b.apply_batch(&a.flush()).unwrap();
        a.evaluate();
        b.evaluate();
        for c in [&a, &b] {
            assert_eq!(c.get_formatted_cell_value(0, 1, 1), Ok("6".to_string()));
        }
    }

    /// A single-cell reference to a deleted row is `#REF!`, as in the ordinal model, and the undo
    /// of the delete brings it back.
    #[test]
    fn deleted_row_reference_comes_back_on_undo() {
        let mut o = Model::new_empty("model", "en", "UTC", "en").unwrap();
        let mut c = CollabModel::new(1);
        c.new_sheet();
        for (row, column, value) in [(3, 1, "5"), (1, 3, "=A3")] {
            o.set_user_input(0, row, column, value.to_string()).unwrap();
            c.set_user_input(0, row, column, value.to_string()).unwrap();
        }
        c.flush();
        o.delete_rows(0, 3, 1).unwrap();
        c.delete_rows(0, 3, 1).unwrap();
        o.evaluate();
        c.evaluate();
        assert_eq!(c.get_cell_formula(0, 1, 3), o.get_cell_formula(0, 1, 3));
        assert_eq!(c.get_formatted_cell_value(0, 1, 3), Ok("#REF!".to_string()));

        let commits = c.flush();
        undo(&mut c, &commits);
        c.evaluate();
        assert_eq!(c.get_cell_formula(0, 1, 3), Ok(Some("=A3".to_string())));
        assert_eq!(c.get_formatted_cell_value(0, 1, 3), Ok("5".to_string()));
    }

    /// The model for the range-shrink tests: `A1:C1 = 1, 2, 3` and `formula` in E1.
    fn range_model(formula: &str) -> CollabModel<'static> {
        let mut c = CollabModel::new(1);
        c.new_sheet();
        for (column, value) in [(1, "1"), (2, "2"), (3, "3"), (5, formula)] {
            c.set_user_input(0, 1, column, value.to_string()).unwrap();
        }
        c.flush();
        c
    }

    /// Both corners die in two deletes, but the middle column survives: the range shrinks to it.
    #[test]
    fn range_with_both_corners_deleted_keeps_its_middle() {
        let mut c = range_model("=SUM(A1:C1)");
        c.delete_columns(0, 1, 1).unwrap();
        // The old C is now B.
        c.delete_columns(0, 2, 1).unwrap();
        c.evaluate();
        assert_eq!(
            c.get_cell_formula(0, 1, 3),
            Ok(Some("=SUM(A1:A1)".to_string()))
        );
        assert_eq!(c.get_formatted_cell_value(0, 1, 3), Ok("2".to_string()));
    }

    /// A range whose every cell is deleted is `#REF!`, and the undo brings it back whole.
    #[test]
    fn deleted_range_comes_back_on_undo() {
        let mut c = range_model("=SUM(B1:C1)");
        c.delete_columns(0, 2, 2).unwrap();
        c.evaluate();
        assert_eq!(c.get_formatted_cell_value(0, 1, 3), Ok("#REF!".to_string()));

        let commits = c.flush();
        undo(&mut c, &commits);
        c.evaluate();
        assert_eq!(
            c.get_cell_formula(0, 1, 5),
            Ok(Some("=SUM(B1:C1)".to_string()))
        );
        assert_eq!(c.get_formatted_cell_value(0, 1, 5), Ok("5".to_string()));
    }
}
