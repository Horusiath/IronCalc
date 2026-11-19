//! The rows of a sheet, by position: chunks of consecutive rows, allocated as
//! they are needed.

use std::borrow::Cow;

use bitcode::{Decode, Encode};

use super::row::Row;
use crate::constants::{LAST_COLUMN, LAST_ROW};
use crate::types::Cell;

const CHUNK_BITS: u32 = 10;
const CHUNK_ROWS: usize = 1 << CHUNK_BITS;
const CHUNK_MASK: usize = CHUNK_ROWS - 1;

/// The cells of a worksheet, by row and column. Both are 1-indexed.
///
/// A row can exist without cells: `set_row` with no cells creates one. The xlsx
/// importer does that for rows that carry a height or a style and nothing
/// else, and the exporter writes a `<row>` element for every row that exists
/// here, so such rows survive a round trip. Removing the last cell of a row
/// with `remove_cell` removes the row.
///
/// Rows outside the sheet, below 1 or beyond the last row, cannot hold cells:
/// writing to them does nothing and reading them finds nothing.
#[derive(Encode, Decode, Debug, Clone, Default)]
pub struct SheetData {
    /// `chunks[i]` holds rows `i * CHUNK_ROWS ..`, if any of them exists.
    chunks: Vec<Option<Box<Chunk>>>,
    /// How many rows exist.
    row_count: usize,
}

#[derive(Encode, Decode, Debug, Clone)]
struct Chunk {
    /// Always `CHUNK_ROWS` long.
    rows: Vec<Option<Row>>,
    /// How many of them exist. A chunk with none is freed.
    used: usize,
}

impl Chunk {
    fn new() -> Self {
        let mut rows = Vec::new();
        rows.resize_with(CHUNK_ROWS, || None);
        Chunk { rows, used: 0 }
    }
}

/// The chunk and the place in it of a row, if the row is within the sheet.
#[inline]
fn locate(row: i32) -> Option<(usize, usize)> {
    if !(1..=LAST_ROW).contains(&row) {
        return None;
    }
    let row = row as usize;
    Some((row >> CHUNK_BITS, row & CHUNK_MASK))
}

impl SheetData {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub(super) fn row(&self, row: i32) -> Option<&Row> {
        let (chunk, index) = locate(row)?;
        self.chunks.get(chunk)?.as_ref()?.rows[index].as_ref()
    }

    #[inline]
    fn row_mut(&mut self, row: i32) -> Option<&mut Row> {
        let (chunk, index) = locate(row)?;
        self.chunks.get_mut(chunk)?.as_mut()?.rows[index].as_mut()
    }

    /// The row, created if it does not exist. `None` outside the sheet.
    fn row_or_insert(&mut self, row: i32) -> Option<&mut Row> {
        let (chunk, index) = locate(row)?;
        if chunk >= self.chunks.len() {
            self.chunks.resize_with(chunk + 1, || None);
        }
        let chunk = self.chunks[chunk].get_or_insert_with(|| Box::new(Chunk::new()));
        if chunk.rows[index].is_none() {
            chunk.rows[index] = Some(Row::default());
            chunk.used += 1;
            self.row_count += 1;
        }
        chunk.rows[index].as_mut()
    }

    /// Every row that exists with its number, in ascending order.
    fn rows_in_order(&self) -> impl Iterator<Item = (i32, &Row)> {
        self.chunks
            .iter()
            .enumerate()
            .filter_map(|(chunk_index, chunk)| Some((chunk_index, chunk.as_ref()?)))
            .flat_map(|(chunk_index, chunk)| {
                chunk
                    .rows
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, row)| {
                        let number = (chunk_index << CHUNK_BITS) | index;
                        Some((number as i32, row.as_ref()?))
                    })
            })
    }

    /// The cell at a position, if there is one.
    #[inline]
    pub fn cell(&self, row: i32, column: i32) -> Option<Cow<'_, Cell>> {
        self.row(row)?.get(column)
    }

    /// The cell at a position, to be changed in place.
    pub fn cell_mut(&mut self, row: i32, column: i32) -> Option<&mut Cell> {
        self.row_mut(row)?.get_mut(column)
    }

    /// Puts a cell at a position and returns the one that was there.
    pub fn set_cell(&mut self, row: i32, column: i32, cell: Cell) -> Option<Cell> {
        self.row_or_insert(row)?.insert(column, cell)
    }

    /// Removes the cell at a position and returns it.
    pub fn remove_cell(&mut self, row: i32, column: i32) -> Option<Cell> {
        let row_data = self.row_mut(row)?;
        let cell = row_data.remove(column)?;
        if row_data.is_empty() {
            self.remove_row(row);
        }
        Some(cell)
    }

    /// True if the sheet has no rows.
    pub fn is_empty(&self) -> bool {
        self.row_count == 0
    }

    /// Every cell of the sheet with its row and column, in natural order:
    /// by row, and within a row by column.
    pub fn cells(&self) -> impl Iterator<Item = (i32, i32, Cow<'_, Cell>)> {
        self.rows_in_order().flat_map(|(row, row_data)| {
            row_data
                .iter()
                .map(move |(column, cell)| (row, column, cell))
        })
    }

    /// The rows that exist, in ascending order.
    pub fn rows(&self) -> Vec<i32> {
        self.rows_in_order().map(|(row, _)| row).collect()
    }

    /// The columns of a row that have cells, in ascending order.
    pub fn columns_in_row(&self, row: i32) -> Vec<i32> {
        match self.row(row) {
            Some(row_data) => row_data.iter().map(|(column, _)| column).collect(),
            None => Vec::new(),
        }
    }

    /// The cells of a row with their column, in ascending order of column.
    pub fn cells_in_row(&self, row: i32) -> Vec<(i32, Cow<'_, Cell>)> {
        match self.row(row) {
            Some(row_data) => row_data.iter().collect(),
            None => Vec::new(),
        }
    }

    /// The cells of a row from `first_column` to `last_column`, both included,
    /// with their column, in ascending order of column. Reading a stretch of a
    /// row this way finds the row once, not once per cell.
    pub fn cells_in_row_between(
        &self,
        row: i32,
        first_column: i32,
        last_column: i32,
    ) -> impl Iterator<Item = (i32, Cow<'_, Cell>)> {
        self.row(row)
            .map(|row_data| row_data.iter_from(first_column))
            .into_iter()
            .flatten()
            .take_while(move |(column, _)| *column <= last_column)
    }

    /// The numbers of a row from `first_column` to `last_column`, both
    /// included, if the row holds them as numbers and nothing else, with none
    /// missing. `None` is no news about the row: its cells say what it holds.
    #[inline]
    pub fn numbers_in_row_between(
        &self,
        row: i32,
        first_column: i32,
        last_column: i32,
    ) -> Option<&[f64]> {
        match self.row(row)? {
            Row::Numbers {
                first_column: row_first_column,
                values,
                ..
            } => {
                let first = Row::offset(*row_first_column, values, first_column)?;
                let last = Row::offset(*row_first_column, values, last_column)?;
                values.get(first..=last)
            }
            Row::Cells(_) => None,
        }
    }

    /// Removes every cell of a row, and the row.
    pub fn remove_row(&mut self, row: i32) {
        self.take_row(row);
    }

    /// Removes a row and returns it.
    fn take_row(&mut self, row: i32) -> Option<Row> {
        let (chunk_index, index) = locate(row)?;
        let chunk = self.chunks.get_mut(chunk_index)?.as_mut()?;
        let taken = chunk.rows[index].take()?;
        chunk.used -= 1;
        self.row_count -= 1;
        if chunk.used == 0 {
            self.chunks[chunk_index] = None;
        }
        Some(taken)
    }

    /// Moves a row, if it exists, into the place of one that does not. A row
    /// moved outside the sheet is gone.
    fn move_row_slot(&mut self, from: i32, to: i32) {
        if from == to || self.row(from).is_none() {
            return;
        }
        // The place is made before the row leaves, so that a chunk left
        // empty by one row and filled by the next is not freed in between.
        let inside = self.row_or_insert(to).is_some();
        let taken = self.take_row(from);
        if let (true, Some(taken)) = (inside, taken) {
            if let Some(slot) = self.row_mut(to) {
                *slot = taken;
            }
        }
    }

    /// The rows that exist from `first` to `last`, both included, ascending.
    fn rows_between(&self, first: i32, last: i32) -> Vec<i32> {
        self.rows_in_order()
            .map(|(row, _)| row)
            .skip_while(|row| *row < first)
            .take_while(|row| *row <= last)
            .collect()
    }

    /// Rows numbered `at` and up move down by `count`; rows pushed past the
    /// last row are dropped.
    pub fn insert_rows(&mut self, at: i32, count: i32) {
        if count <= 0 || locate(at).is_none() {
            return;
        }
        // From the bottom up, so that every row moves into a place already left
        for row in self.rows_between(at, LAST_ROW).into_iter().rev() {
            self.move_row_slot(row, row + count);
        }
    }

    /// Rows `at..at + count` are removed; the rows after them move up by
    /// `count`.
    pub fn remove_rows(&mut self, at: i32, count: i32) {
        if count <= 0 || locate(at).is_none() {
            return;
        }
        let end = at + count;
        // From the top down, so that every row moves into a place already left
        for row in self.rows_between(at, LAST_ROW) {
            if row < end {
                self.take_row(row);
            } else {
                self.move_row_slot(row, row - count);
            }
        }
    }

    /// The row at `from` ends up at `to`; the rows between shift by one
    /// towards `from`.
    pub fn move_row(&mut self, from: i32, to: i32) {
        if from == to || locate(from).is_none() || locate(to).is_none() {
            return;
        }
        let moving = self.take_row(from);
        if from < to {
            for row in self.rows_between(from + 1, to) {
                self.move_row_slot(row, row - 1);
            }
        } else {
            for row in self.rows_between(to, from - 1).into_iter().rev() {
                self.move_row_slot(row, row + 1);
            }
        }
        if let Some(moving) = moving {
            if let Some(slot) = self.row_or_insert(to) {
                *slot = moving;
            }
        }
    }

    /// Moves the cells of every row as `f` says, see [`Row::remap_columns`].
    /// A row left without cells goes, as it does with `remove_cell`; a row
    /// that had none stays.
    fn remap_columns(&mut self, f: impl Fn(i32) -> Option<i32>) {
        let SheetData { chunks, row_count } = self;
        for slot in chunks.iter_mut() {
            let Some(chunk) = slot else {
                continue;
            };
            for row_slot in chunk.rows.iter_mut() {
                let Some(row) = row_slot else {
                    continue;
                };
                let was_empty = row.is_empty();
                row.remap_columns(&f);
                if !was_empty && row.is_empty() {
                    *row_slot = None;
                    chunk.used -= 1;
                    *row_count -= 1;
                }
            }
            if chunk.used == 0 {
                *slot = None;
            }
        }
    }

    /// In every row, cells in columns `at` and up move right by `count`;
    /// cells pushed past the last column are dropped, and a row left without
    /// cells by that goes.
    pub fn insert_columns(&mut self, at: i32, count: i32) {
        if count <= 0 || !(1..=LAST_COLUMN).contains(&at) {
            return;
        }
        self.remap_columns(|column| {
            if column < at {
                Some(column)
            } else {
                column
                    .checked_add(count)
                    .filter(|column| *column <= LAST_COLUMN)
            }
        });
    }

    /// Cells in columns `at..at + count` are removed, and so is a row left
    /// without cells by that; cells after them move left by `count`.
    pub fn remove_columns(&mut self, at: i32, count: i32) {
        if count <= 0 || !(1..=LAST_COLUMN).contains(&at) {
            return;
        }
        let end = at.saturating_add(count);
        self.remap_columns(|column| {
            if column < at {
                Some(column)
            } else if column < end {
                None
            } else {
                Some(column - count)
            }
        });
    }

    /// The cell at column `from` of every row ends up at `to`; the cells
    /// between shift by one towards `from`.
    pub fn move_column(&mut self, from: i32, to: i32) {
        let columns = 1..=LAST_COLUMN;
        if from == to || !columns.contains(&from) || !columns.contains(&to) {
            return;
        }
        self.remap_columns(|column| {
            Some(if column == from {
                to
            } else if from < column && column <= to {
                column - 1
            } else if to <= column && column < from {
                column + 1
            } else {
                column
            })
        });
    }

    /// Replaces the cells of a row. The row exists afterwards, even with no
    /// cells. If a column is given twice the last one stays.
    pub fn set_row(&mut self, row: i32, cells: impl IntoIterator<Item = (i32, Cell)>) {
        let Some(row_data) = self.row_or_insert(row) else {
            return;
        };
        // Collected at its exact size: a row grown cell by cell from empty
        // starts with room for four, and a sheet with a million short rows
        // paid for that four times over.
        let mut cells: Vec<(i32, Cell)> = cells.into_iter().collect();
        // A file gives the cells of a row from left to right, and then there
        // is nothing to sort and no column given twice.
        if !cells.is_sorted_by(|earlier, later| earlier.0 < later.0) {
            cells.sort_by_key(|(column, _)| *column);
            // Of two cells in the same column the later one stays: it is moved
            // into the slot of the earlier one, which `dedup_by` then keeps.
            cells.dedup_by(|later, earlier| {
                if later.0 == earlier.0 {
                    std::mem::swap(&mut later.1, &mut earlier.1);
                    true
                } else {
                    false
                }
            });
        }
        cells.shrink_to_fit();
        *row_data = Row::from_cells(cells);
    }
}

/// Two sheets are equal when they have the same rows and the same cells.
/// Which chunks happen to be allocated is not part of that.
impl PartialEq for SheetData {
    fn eq(&self, other: &Self) -> bool {
        self.row_count == other.row_count && self.rows_in_order().eq(other.rows_in_order())
    }
}
