use std::collections::{hash_map, HashMap};

use bitcode::{Decode, Encode};

use crate::collab::fractional_index::FractionalKey;
use crate::types::Cell;

/// The cells of a [`Stable`](crate::collab::model::Stable) sheet, filed under their row and column
/// identity keys. Iteration order is unspecified. No stored row is empty: replicas compare equal
/// whether or not a losing write ever filed the row.
#[derive(Clone, Debug, Default, PartialEq, Encode, Decode)]
pub struct CellMap(HashMap<FractionalKey, HashMap<FractionalKey, Cell>>);

impl CellMap {
    pub fn cell(&self, row: &FractionalKey, col: &FractionalKey) -> Option<&Cell> {
        self.0.get(row)?.get(col)
    }

    pub fn cell_mut(&mut self, row: &FractionalKey, col: &FractionalKey) -> Option<&mut Cell> {
        self.0.get_mut(row)?.get_mut(col)
    }

    /// Returns the cell it replaced.
    pub fn insert_cell(
        &mut self,
        row: FractionalKey,
        col: FractionalKey,
        cell: Cell,
    ) -> Option<Cell> {
        self.0.entry(row).or_default().insert(col, cell)
    }

    /// A row left without cells is dropped.
    pub fn remove_cell(&mut self, row: &FractionalKey, col: &FractionalKey) -> Option<Cell> {
        let cells = self.0.get_mut(row)?;
        let removed = cells.remove(col);
        if cells.is_empty() {
            self.0.remove(row);
        }
        removed
    }

    /// Keeps the cells of `row` for which `keep` returns true; a row left without cells is dropped.
    pub fn retain_row(
        &mut self,
        row: &FractionalKey,
        mut keep: impl FnMut(&FractionalKey, &mut Cell) -> bool,
    ) {
        let Some(cells) = self.0.get_mut(row) else {
            return;
        };
        cells.retain(|col, cell| keep(col, cell));
        if cells.is_empty() {
            self.0.remove(row);
        }
    }

    /// The same for the cells in `col`, across all rows.
    pub fn retain_col(
        &mut self,
        col: &FractionalKey,
        mut keep: impl FnMut(&FractionalKey, &mut Cell) -> bool,
    ) {
        self.0.retain(|row, cells| {
            if let Some(cell) = cells.get_mut(col) {
                if !keep(row, cell) {
                    cells.remove(col);
                }
            }
            !cells.is_empty()
        });
    }

    /// Rows holding at least one cell, each with its cells.
    pub fn rows(&self) -> impl Iterator<Item = (&FractionalKey, RowCells<'_>)> {
        self.0
            .iter()
            .map(|(row, cells)| (row, RowCells(Some(cells.iter()))))
    }

    /// The cells of `row`; empty when it holds none.
    pub fn row_cells(&self, row: &FractionalKey) -> RowCells<'_> {
        RowCells(self.0.get(row).map(HashMap::iter))
    }

    /// `(row, cell)` for the cells in `col`.
    pub fn col_cells<'a>(
        &'a self,
        col: &'a FractionalKey,
    ) -> impl Iterator<Item = (&'a FractionalKey, &'a Cell)> {
        self.0
            .iter()
            .filter_map(move |(row, cells)| Some((row, cells.get(col)?)))
    }

    /// `(row, col, cell)` for every cell.
    pub fn cells(&self) -> impl Iterator<Item = (&FractionalKey, &FractionalKey, &Cell)> {
        self.0
            .iter()
            .flat_map(|(row, cells)| cells.iter().map(move |(col, cell)| (row, col, cell)))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// The cells of one row, as `(col, cell)`.
pub struct RowCells<'a>(Option<hash_map::Iter<'a, FractionalKey, Cell>>);

impl<'a> Iterator for RowCells<'a> {
    type Item = (&'a FractionalKey, &'a Cell);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut()?.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            None => (0, Some(0)),
            Some(cells) => cells.size_hint(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collab::fractional_index::virtual_key;

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
}
