use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::{iter, slice};

use bitcode::{Decode, Encode};

use crate::collab::blocks::{self, retain_entries, At, Blocks};
use crate::collab::fractional_index::{FractionalIndex, FractionalKey};
use crate::collab::model::{SheetIndexes, Stable};
use crate::evaluation::KeyBuild;
use crate::types::{Cell, Position};
use crate::worksheet::WorksheetDimension;

/// Cells a row keeps in a sorted array; one more turns it into blocks.
const ROW_ARRAY_LEN: usize = 256;

/// The cells of a [`Stable`] sheet, filed under their row and column identity keys and iterated in
/// key order (rows by row key, cells by column key), which is not display order after a move. No
/// stored row is empty: replicas compare equal whether or not a losing write ever filed the row.
#[derive(Clone, Debug, Default, Encode, Decode)]
pub struct CellMap {
    rows: Blocks<Row>,
    /// Number of cells in each column.
    #[bitcode(skip)]
    col_counts: HashMap<FractionalKey, u32, KeyBuild>,
    /// Which rows hold `ArrayFormula` anchor.
    #[bitcode(skip)]
    anchor_rows: HashSet<FractionalKey, KeyBuild>,
    /// Where the last access landed; see `seek_row`. Not encoded, not compared.
    #[bitcode(skip)]
    cursor: std::cell::Cell<Cursor>,
}

impl PartialEq for CellMap {
    fn eq(&self, other: &Self) -> bool {
        self.rows == other.rows
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Cursor {
    row: Option<At>,
    col: u32, // a slot in an `Array` row
}

/// One row's cells, sorted by column key, never empty. `Array` if it holds at most
/// `ROW_ARRAY_LEN` cells, so equal contents have one representation.
#[derive(Clone, Debug, PartialEq, Encode, Decode)]
enum Row {
    Array {
        keys: Vec<FractionalKey>,
        cells: Vec<Cell>,
    },
    Wide(Blocks<Cell>),
}

/// Finds `col` at the cursor's slot, then the next one, else by search; the cursor keeps the slot
/// found or the insertion point.
fn col_slot(
    cursor: &std::cell::Cell<Cursor>,
    keys: &[FractionalKey],
    col: &FractionalKey,
) -> Result<usize, usize> {
    let mut at = cursor.get();
    let hint = at.col as usize;
    let found = if keys.get(hint) == Some(col) {
        Ok(hint)
    } else if keys.get(hint + 1) == Some(col) {
        Ok(hint + 1)
    } else {
        keys.binary_search(col)
    };
    at.col = match found {
        Ok(slot) | Err(slot) => slot as u32,
    };
    cursor.set(at);
    found
}

impl Row {
    fn single(col: FractionalKey, cell: Cell) -> Self {
        Row::Array {
            keys: vec![col],
            cells: vec![cell],
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Row::Array { keys, .. } => keys.is_empty(),
            Row::Wide(cells) => cells.is_empty(),
        }
    }

    fn get(&self, col: &FractionalKey, cursor: &std::cell::Cell<Cursor>) -> Option<&Cell> {
        match self {
            Row::Array { keys, cells } => col_slot(cursor, keys, col).ok().map(|i| &cells[i]),
            Row::Wide(cells) => cells.lookup(col),
        }
    }

    fn get_mut(
        &mut self,
        col: &FractionalKey,
        cursor: &std::cell::Cell<Cursor>,
    ) -> Option<&mut Cell> {
        match self {
            Row::Array { keys, cells } => col_slot(cursor, keys, col).ok().map(|i| &mut cells[i]),
            Row::Wide(cells) => {
                let at = cells.find(col).ok()?;
                Some(cells.get_mut(at))
            }
        }
    }

    fn insert(
        &mut self,
        col: FractionalKey,
        cell: Cell,
        cursor: &std::cell::Cell<Cursor>,
    ) -> Option<Cell> {
        match self {
            Row::Array { keys, cells } => match col_slot(cursor, keys, &col) {
                Ok(i) => Some(std::mem::replace(&mut cells[i], cell)),
                Err(_) if keys.len() == ROW_ARRAY_LEN => {
                    let mut wide = Blocks::from_sorted(keys.drain(..).zip(cells.drain(..)));
                    wide.insert(col, cell);
                    *self = Row::Wide(wide);
                    None
                }
                Err(i) => {
                    keys.reserve_exact(1);
                    cells.reserve_exact(1);
                    keys.insert(i, col);
                    cells.insert(i, cell);
                    None
                }
            },
            Row::Wide(cells) => cells.insert(col, cell),
        }
    }

    fn remove(&mut self, col: &FractionalKey, cursor: &std::cell::Cell<Cursor>) -> Option<Cell> {
        match self {
            Row::Array { keys, cells } => {
                let i = col_slot(cursor, keys, col).ok()?;
                keys.remove(i);
                Some(cells.remove(i))
            }
            Row::Wide(cells) => {
                let removed = cells.remove(col);
                self.shrink();
                removed
            }
        }
    }

    fn retain(&mut self, keep: impl FnMut(&FractionalKey, &mut Cell) -> bool) {
        match self {
            Row::Array { keys, cells } => retain_entries(keys, cells, keep),
            Row::Wide(cells) => {
                cells.retain(keep);
                self.shrink();
            }
        }
    }

    /// Turns a wide row that dropped to `ROW_ARRAY_LEN` cells back into an array.
    fn shrink(&mut self) {
        let Row::Wide(wide) = self else {
            return;
        };
        if wide.len() > ROW_ARRAY_LEN {
            return;
        }
        let mut keys = Vec::with_capacity(wide.len());
        let mut cells = Vec::with_capacity(wide.len());
        for (col, cell) in std::mem::take(wide).into_entries() {
            keys.push(col);
            cells.push(cell);
        }
        *self = Row::Array { keys, cells };
    }

    fn iter(&self) -> RowCells<'_> {
        match self {
            Row::Array { keys, cells } => RowCells::Array(keys.iter().zip(cells.iter())),
            Row::Wide(cells) => RowCells::Wide(cells.iter()),
        }
    }
}

fn is_anchor(cell: &Cell) -> bool {
    matches!(cell, Cell::ArrayFormula { .. })
}

fn uncount(counts: &mut HashMap<FractionalKey, u32, KeyBuild>, col: &FractionalKey) {
    match counts.get_mut(col) {
        Some(count) if *count > 1 => *count -= 1,
        Some(_) => {
            counts.remove(col);
        }
        None => debug_assert!(false, "column count underflow"),
    }
}

/// The first and last 1-based positions of `axis` whose key `held` accepts.
fn extent(axis: &FractionalIndex, held: impl Fn(&FractionalKey) -> bool) -> Option<(i32, i32)> {
    let held_at = |i: &usize| axis.key(*i).is_some_and(&held);
    let first = (0..axis.len()).find(held_at)?;
    let last = (first..axis.len()).rev().find(held_at)?;
    Some((first as i32 + 1, last as i32 + 1))
}

impl CellMap {
    /// The row `key`, or its insertion point. Steps from the cursor's row to the next one before
    /// searching. Leaves the cursor on the row found, or on the row before the insertion point.
    fn seek_row(&self, key: &FractionalKey) -> Result<At, At> {
        let mut cursor = self.cursor.get();
        if let Some(at) = cursor.row {
            match key.cmp(self.rows.key(at)) {
                Ordering::Equal => return Ok(at),
                Ordering::Greater => {
                    let Some(next) = self.rows.next(at) else {
                        return Err(self.rows.end());
                    };
                    match key.cmp(self.rows.key(next)) {
                        Ordering::Equal => {
                            cursor.row = Some(next);
                            self.cursor.set(cursor);
                            return Ok(next);
                        }
                        Ordering::Less => return Err(next),
                        Ordering::Greater => {}
                    }
                }
                Ordering::Less => {}
            }
        }
        let found = self.rows.find(key);
        cursor.row = match found {
            Ok(at) => Some(at),
            Err(at) => self.rows.prev(at),
        };
        self.cursor.set(cursor);
        found
    }

    pub fn cell(&self, row: &FractionalKey, col: &FractionalKey) -> Option<&Cell> {
        let at = self.seek_row(row).ok()?;
        self.rows.get(at).get(col, &self.cursor)
    }

    /// Must not turn a cell into an `ArrayFormula` anchor: anchors are tracked by `insert_cell`.
    pub fn cell_mut(&mut self, row: &FractionalKey, col: &FractionalKey) -> Option<&mut Cell> {
        let at = self.seek_row(row).ok()?;
        self.rows.get_mut(at).get_mut(col, &self.cursor)
    }

    /// Returns the cell it replaced.
    pub fn insert_cell(
        &mut self,
        row: FractionalKey,
        col: FractionalKey,
        cell: Cell,
    ) -> Option<Cell> {
        if is_anchor(&cell) {
            self.anchor_rows.insert(row.clone());
        }
        let replaced = match self.seek_row(&row) {
            Ok(at) => self
                .rows
                .get_mut(at)
                .insert(col.clone(), cell, &self.cursor),
            Err(at) => {
                let at = self.rows.insert_at(at, row, Row::single(col.clone(), cell));
                self.cursor.set(Cursor {
                    row: Some(at),
                    col: 0,
                });
                None
            }
        };
        if replaced.is_none() {
            *self.col_counts.entry(col).or_insert(0) += 1;
        }
        replaced
    }

    /// A row left without cells is dropped.
    pub fn remove_cell(&mut self, row: &FractionalKey, col: &FractionalKey) -> Option<Cell> {
        let at = self.seek_row(row).ok()?;
        let cells = self.rows.get_mut(at);
        let removed = cells.remove(col, &self.cursor)?;
        if cells.is_empty() {
            // The row before stays where it is.
            self.cursor.set(Cursor {
                row: self.rows.prev(at),
                col: 0,
            });
            self.rows.remove_at(at);
            self.anchor_rows.remove(row);
        }
        uncount(&mut self.col_counts, col);
        Some(removed)
    }

    /// Keeps the cells of `row` for which `keep` returns true; a row left without cells is dropped.
    pub fn retain_row(
        &mut self,
        row: &FractionalKey,
        mut keep: impl FnMut(&FractionalKey, &mut Cell) -> bool,
    ) {
        let Ok(at) = self.seek_row(row) else {
            return;
        };
        self.cursor.take();
        let cells = self.rows.get_mut(at);
        let (counts, mut anchor) = (&mut self.col_counts, false);
        cells.retain(|col, cell| {
            let kept = keep(col, cell);
            if kept {
                anchor |= is_anchor(cell);
            } else {
                uncount(counts, col);
            }
            kept
        });
        if cells.is_empty() {
            self.rows.remove_at(at);
            self.anchor_rows.remove(row);
        } else if anchor {
            self.anchor_rows.insert(row.clone());
        }
    }

    /// The same for the cells in `col`, across all rows.
    pub fn retain_col(
        &mut self,
        col: &FractionalKey,
        mut keep: impl FnMut(&FractionalKey, &mut Cell) -> bool,
    ) {
        let CellMap {
            rows,
            col_counts,
            anchor_rows,
            cursor,
        } = self;
        rows.retain(|row, cells| {
            let Some(cell) = cells.get_mut(col, cursor) else {
                return true;
            };
            if !keep(row, cell) {
                cells.remove(col, cursor);
                uncount(col_counts, col);
            } else if is_anchor(cell) {
                anchor_rows.insert(row.clone());
            }
            if cells.is_empty() {
                anchor_rows.remove(row);
                return false;
            }
            true
        });
        cursor.take();
    }

    /// Recomputes the derived column counts and anchor rows from the cells.
    pub fn rebuild_derived(&mut self) {
        self.cursor.take();
        self.col_counts.clear();
        self.anchor_rows.clear();
        for (row, cells) in self.rows.iter() {
            for (col, cell) in cells.iter() {
                *self.col_counts.entry(col.clone()).or_insert(0) += 1;
                if is_anchor(cell) {
                    self.anchor_rows.insert(row.clone());
                }
            }
        }
    }

    /// The 1-based extent of the stored cells, anchors' areas included; `None` when there are none.
    pub fn dimension(&self, index: &SheetIndexes) -> Option<WorksheetDimension> {
        let (min_row, mut max_row) = extent(&index.rows, |key| self.rows.find(key).is_ok())?;
        let (min_column, mut max_column) =
            extent(&index.cols, |key| self.col_counts.contains_key(key))?;
        for row_key in &self.anchor_rows {
            let (Some(cells), Some(row)) = (
                self.rows.lookup(row_key),
                Stable::row_ordinal(index, row_key),
            ) else {
                continue;
            };
            for (col_key, cell) in cells.iter() {
                let Cell::ArrayFormula { r, .. } = cell else {
                    continue;
                };
                if let Some(column) = Stable::col_ordinal(index, col_key) {
                    max_row = max_row.max(row + r.1.max(1) - 1);
                    max_column = max_column.max(column + r.0.max(1) - 1);
                }
            }
        }
        Some(WorksheetDimension {
            min_row,
            max_row,
            min_column,
            max_column,
        })
    }

    /// Rows holding at least one cell, each with its cells.
    pub fn rows(&self) -> impl Iterator<Item = (&FractionalKey, RowCells<'_>)> {
        self.rows.iter().map(|(row, cells)| (row, cells.iter()))
    }

    /// The cells of `row`; empty when it holds none.
    pub fn row_cells(&self, row: &FractionalKey) -> RowCells<'_> {
        match self.seek_row(row) {
            Ok(at) => self.rows.get(at).iter(),
            Err(_) => RowCells::Empty,
        }
    }

    /// `(row, cell)` for the cells in `col`.
    pub fn col_cells<'a>(
        &'a self,
        col: &'a FractionalKey,
    ) -> impl Iterator<Item = (&'a FractionalKey, &'a Cell)> {
        self.rows
            .iter()
            .filter_map(move |(row, cells)| Some((row, cells.get(col, &self.cursor)?)))
    }

    /// `(row, col, cell)` for every cell.
    pub fn cells(&self) -> impl Iterator<Item = (&FractionalKey, &FractionalKey, &Cell)> {
        self.rows
            .iter()
            .flat_map(|(row, cells)| cells.iter().map(move |(col, cell)| (row, col, cell)))
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// The cells of one row, as `(col, cell)`, in column key order.
pub enum RowCells<'a> {
    Empty,
    Array(iter::Zip<slice::Iter<'a, FractionalKey>, slice::Iter<'a, Cell>>),
    Wide(blocks::Iter<'a, Cell>),
}

impl<'a> Iterator for RowCells<'a> {
    type Item = (&'a FractionalKey, &'a Cell);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            RowCells::Empty => None,
            RowCells::Array(cells) => cells.next(),
            RowCells::Wide(cells) => cells.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            RowCells::Empty => (0, Some(0)),
            RowCells::Array(cells) => cells.size_hint(),
            RowCells::Wide(cells) => cells.size_hint(),
        }
    }
}

impl ExactSizeIterator for RowCells<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collab::fractional_index::{virtual_key, virtual_ordinal};
    use crate::types::{ArrayKind, FormulaValue};

    fn number(v: f64) -> Cell {
        Cell::NumberCell { v, s: 0 }
    }

    fn anchor(width: i32, height: i32) -> Cell {
        Cell::ArrayFormula {
            f: 0,
            s: 0,
            r: (width, height),
            kind: ArrayKind::Cse,
            v: FormulaValue::Unevaluated,
        }
    }

    fn count(map: &CellMap, col: u32) -> Option<u32> {
        map.col_counts.get(&virtual_key(col)).copied()
    }

    #[test]
    fn emptied_rows_are_dropped() {
        let (r1, r2, c1, c2) = (
            virtual_key(1),
            virtual_key(2),
            virtual_key(1),
            virtual_key(2),
        );
        let cell = Cell::EmptyCell { s: 0 };
        let mut map = CellMap::default();
        map.insert_cell(r1.clone(), c1.clone(), cell.clone());
        map.insert_cell(r1.clone(), c2.clone(), cell.clone());
        map.insert_cell(r2.clone(), c1.clone(), cell.clone());

        // `r2` holds only `c1`.
        map.retain_col(&c1, |_, _| false);
        let rows: Vec<_> = map.rows().map(|(row, _)| row).collect();
        assert_eq!(rows, vec![&r1]);
        assert_eq!(map.remove_cell(&r1, &c2), Some(cell.clone()));
        assert!(map.is_empty());

        map.insert_cell(r1.clone(), c1.clone(), cell.clone());
        map.retain_row(&r1, |_, _| false);
        assert!(map.is_empty());
    }

    #[test]
    fn a_row_turns_wide_past_the_array_length_and_back() {
        let row = virtual_key(1);
        let len = ROW_ARRAY_LEN as u32;
        let in_order = |map: &CellMap| {
            let cols: Vec<_> = map.row_cells(&row).map(|(col, _)| col.clone()).collect();
            let mut sorted = cols.clone();
            sorted.sort();
            cols == sorted && map.row_cells(&row).size_hint() == (cols.len(), Some(cols.len()))
        };
        let mut map = CellMap::default();
        let mut array = CellMap::default();
        for col in (1..=len).rev() {
            map.insert_cell(row.clone(), virtual_key(col), number(col as f64));
            array.insert_cell(row.clone(), virtual_key(col), number(col as f64));
        }
        assert!(matches!(map.rows.lookup(&row), Some(Row::Array { .. })));
        assert!(in_order(&map));

        map.insert_cell(row.clone(), virtual_key(len + 1), number(0.0));
        assert!(matches!(map.rows.lookup(&row), Some(Row::Wide(_))));
        assert_eq!(map.row_cells(&row).count(), ROW_ARRAY_LEN + 1);
        assert!(in_order(&map));
        assert_eq!(map.cell(&row, &virtual_key(7)), Some(&number(7.0)));

        assert_eq!(
            map.remove_cell(&row, &virtual_key(len + 1)),
            Some(number(0.0))
        );
        assert!(matches!(map.rows.lookup(&row), Some(Row::Array { .. })));
        assert!(in_order(&map));
        assert_eq!(map, array);
        let decoded: CellMap = bitcode::decode(&bitcode::encode(&map)).unwrap();
        assert_eq!(decoded, array);
        assert_eq!(bitcode::encode(&map), bitcode::encode(&array));

        // `retain_*` drops a wide row back to an array too.
        map.insert_cell(row.clone(), virtual_key(len + 1), number(0.0));
        map.retain_row(&row, |col, _| col != &virtual_key(len + 1));
        assert_eq!(map, array);
        assert!(matches!(map.rows.lookup(&row), Some(Row::Array { .. })));
    }

    #[test]
    fn derived_state_follows_the_cells() {
        let (r1, r2, c1, c2) = (
            virtual_key(1),
            virtual_key(2),
            virtual_key(1),
            virtual_key(2),
        );
        let mut map = CellMap::default();
        map.insert_cell(r1.clone(), c1.clone(), number(1.0));
        map.insert_cell(r2.clone(), c1.clone(), anchor(2, 2));
        map.insert_cell(r2.clone(), c2.clone(), number(2.0));
        assert_eq!((count(&map, 1), count(&map, 2)), (Some(2), Some(1)));
        assert!(map.anchor_rows.contains(&r2) && !map.anchor_rows.contains(&r1));

        // A replacing insert counts nothing new, and an anchor written into a row marks it.
        map.insert_cell(r1.clone(), c1.clone(), anchor(1, 1));
        assert_eq!(count(&map, 1), Some(2));
        assert!(map.anchor_rows.contains(&r1));

        assert_eq!(map.remove_cell(&r2, &c2), Some(number(2.0)));
        assert_eq!(count(&map, 2), None);
        assert!(map.anchor_rows.contains(&r2));

        map.retain_col(&c1, |row, _| row == &r1);
        assert_eq!(count(&map, 1), Some(1));
        assert!(!map.anchor_rows.contains(&r2)); // the row went
        assert!(map.anchor_rows.contains(&r1));

        map.insert_cell(r1.clone(), c2.clone(), number(3.0));
        map.retain_row(&r1, |col, _| col == &c2);
        assert_eq!((count(&map, 1), count(&map, 2)), (None, Some(1)));
        map.retain_row(&r1, |_, _| false);
        assert!(map.col_counts.is_empty() && map.anchor_rows.is_empty());
    }

    #[test]
    fn rebuilt_derived_state_gives_the_same_dimension() {
        let mut index = SheetIndexes::default();
        for i in 1..=6 {
            index.rows.insert_key(virtual_key(i));
            index.cols.insert_key(virtual_key(i));
        }
        let mut map = CellMap::default();
        map.insert_cell(virtual_key(2), virtual_key(3), number(1.0));
        map.insert_cell(virtual_key(4), virtual_key(2), anchor(3, 2));
        map.insert_cell(virtual_key(3), virtual_key(4), number(2.0));
        let expected = WorksheetDimension::new(2, 5, 2, 4);
        assert_eq!(map.dimension(&index), Some(expected));

        let mut decoded: CellMap = bitcode::decode(&bitcode::encode(&map)).unwrap();
        assert!(decoded.col_counts.is_empty());
        decoded.rebuild_derived();
        assert_eq!(decoded.col_counts, map.col_counts);
        assert_eq!(decoded.anchor_rows, map.anchor_rows);
        assert_eq!(decoded.dimension(&index), map.dimension(&index));
        assert_eq!(CellMap::default().dimension(&index), None);
    }

    type Model = std::collections::BTreeMap<(FractionalKey, FractionalKey), Cell>;

    /// A fixed-seed LCG.
    struct Lcg(u64);

    impl Lcg {
        fn below(&mut self, n: u32) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((self.0 >> 33) % u64::from(n)) as u32
        }
    }

    fn insert(map: &mut CellMap, model: &mut Model, row: u32, col: u32, cell: Cell) {
        let (row, col) = (virtual_key(row), virtual_key(col));
        let expected = model.insert((row.clone(), col.clone()), cell.clone());
        assert_eq!(map.insert_cell(row, col, cell), expected);
    }

    fn remove(map: &mut CellMap, model: &mut Model, row: u32, col: u32) {
        let (row, col) = (virtual_key(row), virtual_key(col));
        let expected = model.remove(&(row.clone(), col.clone()));
        assert_eq!(map.remove_cell(&row, &col), expected);
    }

    fn read(map: &mut CellMap, model: &Model, row: u32, col: u32) {
        let (row, col) = (virtual_key(row), virtual_key(col));
        let expected = model.get(&(row.clone(), col.clone()));
        assert_eq!(map.cell(&row, &col), expected, "{row:?} {col:?}");
        assert_eq!(map.cell_mut(&row, &col).map(|cell| &*cell), expected);
    }

    fn read_row(map: &CellMap, model: &Model, row: u32) {
        let row = virtual_key(row);
        let expected: Vec<_> = model
            .iter()
            .filter(|((r, _), _)| *r == row)
            .map(|((_, col), cell)| (col, cell))
            .collect();
        assert_eq!(map.row_cells(&row).collect::<Vec<_>>(), expected);
    }

    /// Cells, layout and derived counts all agree with `model`.
    fn check(map: &CellMap, model: &Model) {
        let cells: Vec<_> = map.cells().collect();
        let expected: Vec<_> = model.iter().map(|((r, c), cell)| (r, c, cell)).collect();
        assert_eq!(cells, expected);
        for (_, row) in map.rows.iter() {
            match row {
                Row::Array { keys, .. } => assert!(keys.len() <= ROW_ARRAY_LEN),
                Row::Wide(cells) => assert!(cells.len() > ROW_ARRAY_LEN),
            }
        }
        let mut rebuilt = map.clone();
        rebuilt.rebuild_derived();
        assert_eq!(rebuilt.col_counts, map.col_counts);
    }

    #[test]
    fn cursor_reads_agree_with_fresh_lookups() {
        let (rows, cols, sparse, wide) = (600, 6, 8, 300);
        let mut map = CellMap::default();
        let mut model = Model::new();
        for row in 1..=rows {
            for col in 1..=cols {
                if (row * 7 + col) % 5 != 0 {
                    insert(
                        &mut map,
                        &mut model,
                        row,
                        col,
                        number(f64::from(row * 10 + col)),
                    );
                }
            }
            if row % 9 == 0 {
                insert(&mut map, &mut model, row, sparse, number(0.0));
            }
        }
        for col in 10..=wide {
            insert(&mut map, &mut model, wide, col, number(f64::from(col)));
        }
        check(&map, &model);
        let all_rows = 0..=rows + 1;
        let all_cols = 0..=sparse + 1;

        for row in all_rows.clone() {
            for col in all_cols.clone() {
                read(&mut map, &model, row, col);
            }
        }
        for col in all_cols.clone() {
            for row in all_rows.clone() {
                read(&mut map, &model, row, col);
            }
        }
        for row in all_rows.clone().rev() {
            for col in all_cols.clone().rev() {
                read(&mut map, &model, row, col);
            }
        }
        for col in (0..=wide + 1).chain((0..=wide + 1).rev()) {
            read(&mut map, &model, wide, col);
        }
        let mut lcg = Lcg(7);
        for _ in 0..5000 {
            let (row, col) = (lcg.below(rows + 2), lcg.below(sparse + 2));
            read(&mut map, &model, row, col);
        }

        // Mutations between reads of a row-major scan.
        for row in all_rows.clone() {
            for col in all_cols.clone() {
                read(&mut map, &model, row, col);
                match (row + col) % 11 {
                    0 => insert(&mut map, &mut model, row + 1, col, number(-1.0)),
                    1 => remove(&mut map, &mut model, row, col + 1),
                    2 => remove(&mut map, &mut model, row + 1, col),
                    _ => {}
                }
                read(&mut map, &model, row, col + 1);
                read(&mut map, &model, row + 1, col);
            }
            read_row(&map, &model, row);
            if row % 50 == 0 {
                let key = virtual_key(row + 1);
                map.retain_row(&key, |col, _| col != &virtual_key(2));
                model.retain(|(r, c), _| *r != key || c != &virtual_key(2));
                read(&mut map, &model, row + 1, 1);
            }
            if row % 97 == 0 {
                let key = virtual_key(row % cols + 1);
                map.retain_col(&key, |r, _| r > &virtual_key(row));
                model.retain(|(r, c), _| *c != key || r > &virtual_key(row));
                read(&mut map, &model, row, row % cols + 1);
            }
        }
        check(&map, &model);
    }

    #[test]
    fn random_operations_agree_with_a_btree_model() {
        let mut lcg = Lcg(42);
        let mut map = CellMap::default();
        let mut model = Model::new();
        for step in 0..8000 {
            // Half the operations go to three rows spanning many columns, so they turn wide.
            let (row, col) = if lcg.below(2) == 0 {
                (lcg.below(3) + 1, lcg.below(700) + 1)
            } else {
                (lcg.below(700) + 1, lcg.below(6) + 1)
            };
            match lcg.below(200) {
                0..100 => insert(&mut map, &mut model, row, col, number(f64::from(step))),
                100..130 => remove(&mut map, &mut model, row, col),
                130..170 => {
                    for col in col..col + 3 {
                        read(&mut map, &model, row, col);
                    }
                }
                170..190 => read_row(&map, &model, row),
                190..195 => {
                    let (key, drop) = (virtual_key(row), lcg.below(50));
                    let keep = |c: &FractionalKey| virtual_ordinal(c).unwrap() % 50 != drop;
                    map.retain_row(&key, |c, _| keep(c));
                    model.retain(|(r, c), _| *r != key || keep(c));
                }
                _ => {
                    let (key, drop) = (virtual_key(col), lcg.below(50));
                    let keep = |r: &FractionalKey| virtual_ordinal(r).unwrap() % 50 != drop;
                    map.retain_col(&key, |r, _| keep(r));
                    model.retain(|(r, c), _| *c != key || keep(r));
                }
            }
            if step % 500 == 0 {
                check(&map, &model);
            }
        }
        check(&map, &model);
        // Rows span several blocks, and a row went wide.
        assert!(map.rows.len() > 2 * ROW_ARRAY_LEN);
        assert!(map.rows.iter().any(|(_, row)| matches!(row, Row::Wide(_))));

        let mut fresh = CellMap::default();
        for ((row, col), cell) in &model {
            fresh.insert_cell(row.clone(), col.clone(), cell.clone());
        }
        assert_eq!(map, fresh);
        assert_eq!(bitcode::encode(&map), bitcode::encode(&fresh));
        let decoded: CellMap = bitcode::decode(&bitcode::encode(&map)).unwrap();
        assert_eq!(decoded, map);
    }
}
