#[cfg(test)]
pub(crate) mod test {
    #![allow(clippy::unwrap_used)]
    use crate::collab::apply::SNAPSHOT_FORMAT_VERSION;
    use crate::collab::formula::StableRef;
    use crate::collab::log::Snapshot;
    use crate::collab::model::{CollabModel, Stable};
    use crate::collab::patch::PropKind;
    use crate::expressions::parser::Node;
    use crate::types::{ArrayKind, Cell};
    use crate::user_model::CellArrayStructure;
    use crate::UserModel;

    pub(crate) type Peer = UserModel<'static, Stable>;

    pub(crate) fn peer(session: u32) -> Peer {
        UserModel::<Stable>::from_model(CollabModel::new(session))
    }

    pub(crate) fn deliver(from: &mut Peer, to: &mut Peer) {
        to.apply_external_diffs(&from.flush_send_queue()).unwrap();
    }

    pub(crate) fn converged(a: &mut Peer, b: &mut Peer) {
        a.evaluate();
        b.evaluate();
        let (ma, mb) = (a.get_model(), b.get_model());
        assert_eq!(mb.workbook.worksheets.len(), ma.workbook.worksheets.len());
        for (i, sheet) in ma.workbook.worksheets.iter().enumerate() {
            assert_eq!(
                mb.sheet_content(i),
                ma.sheet_content(i),
                "content of sheet {}",
                sheet.name
            );
            assert_eq!(cells(mb, i), cells(ma, i), "cells of sheet {}", sheet.name);
        }
        assert_image(ma);
        assert_image(mb);
        for row in 1..=6 {
            for col in 1..=4 {
                assert_eq!(
                    b.get_formatted_cell_value(0, row, col),
                    a.get_formatted_cell_value(0, row, col),
                    "value at row {row} column {col}"
                );
                assert_eq!(
                    b.get_cell_array_structure(0, row, col),
                    a.get_cell_array_structure(0, row, col),
                    "structure at row {row} column {col}"
                );
            }
        }
    }

    /// Every stored cell of the `i`-th sheet, in natural order, with what its shared string or its
    /// formula index names: both tables fill in arrival order, so the indices are per replica. A
    /// formula is its text, its slots and the node it lowered to.
    #[allow(clippy::type_complexity)]
    fn cells(
        model: &CollabModel<'_>,
        i: usize,
    ) -> Vec<(
        i32,
        i32,
        Cell,
        Option<String>,
        Option<(String, Vec<StableRef>, Node)>,
    )> {
        let sheet = &model.workbook.worksheets[i];
        let text = |si: &i32| model.workbook.shared_strings.get(*si as usize).cloned();
        let formula = |f: &i32| {
            let f = *f as usize;
            Some((
                sheet.shared_formulas.get(f)?.clone(),
                sheet.index.formulas.get(f)?.refs.clone(),
                (*model.parsed_formulas.get(i)?.get(f)?.0).clone(),
            ))
        };
        (sheet.sheet_data.cells())
            .map(|(row, column, cell)| match cell.into_owned() {
                Cell::SharedString { si, s } => (
                    row,
                    column,
                    Cell::SharedString { si: 0, s },
                    text(&si),
                    None,
                ),
                Cell::CellFormula { f, s, v } => {
                    let cell = Cell::CellFormula { f: 0, s, v };
                    (row, column, cell, None, formula(&f))
                }
                Cell::ArrayFormula { f, s, r, kind, v } => {
                    let cell = Cell::ArrayFormula {
                        f: 0,
                        s,
                        r,
                        kind,
                        v,
                    };
                    (row, column, cell, None, formula(&f))
                }
                cell => (row, column, cell, None, None),
            })
            .collect()
    }

    /// The image of `model` is its index's. A snapshot round trip, which re-derives the sparse
    /// records, the formula slots and the reverse sets from the index, gives the workbook back
    /// unchanged. Every stored cell that is not a spill sits under a row and a column the index has,
    /// and was written by a patch: its address has a value or a style register. Row records sit
    /// under visible rows, in order. What a spill covers is an authored style, under a spill.
    pub(crate) fn assert_image(model: &CollabModel<'_>) {
        // What `Snapshot::encode` writes; spelled out so a borrowed model can be checked too.
        let mut bytes = vec![SNAPSHOT_FORMAT_VERSION];
        bytes.extend_from_slice(&bitcode::encode(&model.workbook));
        let restored = CollabModel::decode(&bytes, 99).unwrap();
        assert_eq!(restored.workbook, model.workbook, "snapshot round trip");
        for sheet in &model.workbook.worksheets {
            let index = &sheet.index;
            for (row, column, cell) in sheet.sheet_data.cells() {
                if matches!(*cell, Cell::SpillCell { .. }) {
                    let listed = index.spills.0.contains(&(row, column));
                    assert!(listed, "spill at ({row}, {column}) is not listed");
                    continue;
                }
                let keys = (
                    index.rows.key(row as usize - 1),
                    index.cols.key(column as usize - 1),
                );
                let (Some(r), Some(c)) = keys else {
                    unreachable!("{cell:?} at ({row}, {column}) is outside the index");
                };
                let at = (r.clone(), c.clone());
                let registers = &index.registers;
                let written = registers.cell_values.contains_key(&at)
                    || (PropKind::ALL.into_iter())
                        .any(|kind| registers.cell_styles.contains_key(&(at.clone(), kind)));
                assert!(written, "{cell:?} at ({row}, {column}) has no register");
            }
            // Row records sit under a visible row, in order, and a hidden row's record waits in
            // `hidden_rows` only while the row is hidden.
            let len = index.rows.len() as i32;
            for row in &sheet.rows {
                assert!(
                    (1..=len).contains(&row.r),
                    "row record {row:?} is outside the index"
                );
            }
            assert!(
                sheet.rows.windows(2).all(|w| w[0].r < w[1].r),
                "row records out of order"
            );
            for key in index.hidden_rows.keys() {
                assert!(
                    index.rows.position_of(key).is_none(),
                    "row {key:?} is visible and has a hidden record"
                );
            }
            // What a spill covers is an authored style, under a spill.
            for (&(row, column), s) in &index.covered {
                let cell = sheet.sheet_data.cell(row, column);
                assert!(
                    matches!(cell.as_deref(), Some(Cell::SpillCell { .. })),
                    "covered style {s} at ({row}, {column}) is under {cell:?}"
                );
                let keys = (
                    index.rows.key(row as usize - 1),
                    index.cols.key(column as usize - 1),
                );
                let (Some(r), Some(c)) = keys else {
                    unreachable!("covered style {s} at ({row}, {column}) is outside the index");
                };
                let at = (r.clone(), c.clone());
                let styled = (PropKind::ALL.into_iter()).any(|kind| {
                    index
                        .registers
                        .cell_styles
                        .contains_key(&(at.clone(), kind))
                });
                assert!(
                    styled,
                    "covered style {s} at ({row}, {column}) has no register"
                );
            }
        }
    }

    fn structure(model: &Peer, row: i32, column: i32) -> CellArrayStructure {
        model.get_cell_array_structure(0, row, column).unwrap()
    }

    #[test]
    fn spill_and_block_round_trip() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        // Only row 1 is materialized: A2 and A3 have no keys of their own.
        a.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A1=1, A2=2, A3=3
        a.set_user_input(0, 1, 3, "=SUM(A1#)").unwrap(); // C1=6
        deliver(&mut a, &mut b);

        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "1"); // A1=1
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "2"); // A2=2 (spill)
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "3"); // A3=3 (spill)
            assert_eq!(model.get_formatted_cell_value(0, 1, 3).unwrap(), "6"); // C1=SUM(A1#)
            assert_eq!(
                structure(model, 1, 1),
                CellArrayStructure::DynamicAnchor(1, 3)
            );
            assert_eq!(
                structure(model, 2, 1),
                CellArrayStructure::DynamicChild(1, 1, 1, 3)
            );
            let inner = model.get_model();
            assert!(inner.get_cell_formula(0, 1, 1).unwrap().is_some());
            assert_eq!(inner.get_cell_formula(0, 2, 1).unwrap(), None);
        }
        converged(&mut a, &mut b);

        b.set_user_input(0, 3, 1, "x").unwrap(); // Peer B: A3=x
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            // spill blocked by B's A3=x write
            assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "#SPILL!");
            // A2 contents are results of A1 spill - they have no value on their own
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "");
            // A3 was written by peer B
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "x");
        }
        converged(&mut a, &mut b);

        b.set_user_input(0, 3, 1, "").unwrap(); // unblock A1 spill
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "3"); // A3=3
        }
        converged(&mut a, &mut b);

        a.set_user_input(0, 1, 1, "42").unwrap(); // A1=42
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "42");
            // A2 and A3 values were results of A1 spill, once it's gone they're empty
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "");
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "");
            assert_eq!(structure(model, 2, 1), CellArrayStructure::SingleCell);
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn markup_is_the_same_on_every_replica() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        a.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A: A1:A3=1,2,3
        a.set_user_input(0, 1, 3, "=SUM(A:A)").unwrap(); // A: C1
        deliver(&mut a, &mut b);
        b.set_user_array_formula(0, 5, 1, 2, 2, "=1+1").unwrap(); // B: A5:B6=2
        deliver(&mut b, &mut a);

        let expected = "=SEQUENCE(3)||=SUM(A:A)\n2||\n3||\n||\n=1+1|2|\n2|2|";
        for model in [&a, &b] {
            assert_eq!(model.get_model().get_sheet_markup(0).unwrap(), expected);
        }

        // Blocked, an array is its anchor alone: what blocks it shows instead.
        a.set_user_input(0, 2, 1, "x").unwrap(); // A: A2=x (blocks sequence)
        deliver(&mut a, &mut b);
        let expected = "=SEQUENCE(3)||=SUM(A:A)\nx||\n||\n||\n=1+1|2|\n2|2|";
        for model in [&a, &b] {
            assert_eq!(model.get_model().get_sheet_markup(0).unwrap(), expected);
        }
    }

    #[test]
    fn dimension_covers_spilled_cells() {
        use crate::worksheet::WorksheetDimension;

        fn dimension(model: &Peer) -> WorksheetDimension {
            model.get_model().workbook.worksheets[0].dimension()
        }
        fn rows_and_columns(max_row: i32, max_column: i32) -> WorksheetDimension {
            WorksheetDimension {
                min_row: 1,
                min_column: 1,
                max_row,
                max_column,
            }
        }
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        a.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A1:A3=1,2,3 (3x1)
        a.set_user_input(0, 1, 3, "=SUM(A:A)").unwrap(); // C1 (3x3)
        a.set_user_input(0, 2, 3, "=COUNT(A:A)").unwrap(); // C2 (3x3)
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(dimension(model), rows_and_columns(3, 3));
            assert_eq!(model.get_formatted_cell_value(0, 1, 3).unwrap(), "6");
            assert_eq!(model.get_formatted_cell_value(0, 2, 3).unwrap(), "3");
        }

        b.set_user_array_formula(0, 5, 4, 2, 3, "=1+1").unwrap(); // D5:E7=2 (7x5)
        b.set_user_input(0, 3, 3, "=SUM(E:E)").unwrap(); // C3
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            assert_eq!(dimension(model), rows_and_columns(7, 5));
            assert_eq!(model.get_formatted_cell_value(0, 3, 3).unwrap(), "6");
        }

        // Blocked, the dynamic array draws its anchor alone. Freed, it reaches as far again.
        b.set_user_input(0, 2, 1, "7").unwrap(); // A2=7
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "#SPILL!");
            assert_eq!(model.get_formatted_cell_value(0, 1, 3).unwrap(), "#SPILL!");
        }
        b.set_user_input(0, 2, 1, "").unwrap();
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            assert_eq!(dimension(model), rows_and_columns(7, 5));
            assert_eq!(model.get_formatted_cell_value(0, 1, 3).unwrap(), "6");
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn concurrent_edit_versus_spill_both_orders() {
        fn execute(anchor_first: bool) {
            let (mut a, mut b) = (peer(1), peer(2));
            a.new_sheet().unwrap();
            deliver(&mut a, &mut b);

            a.set_user_input(0, 1, 1, "=SEQUENCE(2)").unwrap(); // A: A1=1, A2=2
            b.set_user_input(0, 2, 1, "5").unwrap(); // B: A2=5 (interferes with spill)
            let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
            if anchor_first {
                b.apply_external_diffs(&from_a).unwrap();
                a.apply_external_diffs(&from_b).unwrap();
            } else {
                a.apply_external_diffs(&from_b).unwrap();
                b.apply_external_diffs(&from_a).unwrap();
            }

            for model in [&a, &b] {
                // regardless of order of exchange, spill area is blocked by B's write
                assert_eq!(
                    model.get_formatted_cell_value(0, 1, 1).unwrap(),
                    "#SPILL!",
                    "anchor first: {anchor_first}"
                );
                assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "5");
            }
            converged(&mut a, &mut b);
        }

        execute(true);
        execute(false);
    }

    #[test]
    fn structural_moves_carry_the_spill() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        a.set_user_input(0, 2, 1, "=SEQUENCE(3)").unwrap(); // A2=1, A3=2, A4=3
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);

        b.insert_rows(0, 1, 1).unwrap(); // insert row before A1 (which holds array formula)
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            // after B's row insert, spills should shift down together with their array formula
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "1"); // A3=1
            assert_eq!(model.get_formatted_cell_value(0, 4, 1).unwrap(), "2"); // A4=2
            assert_eq!(model.get_formatted_cell_value(0, 5, 1).unwrap(), "3"); // A5=3
            assert_eq!(
                structure(model, 3, 1),
                CellArrayStructure::DynamicAnchor(1, 3)
            );
        }
        converged(&mut a, &mut b);

        b.delete_rows(0, 3, 1).unwrap(); // delete row which has array formula
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            // after deleting their anchor, spill cells should return to regular behavior
            for row in 1..=6 {
                assert_eq!(
                    structure(model, row, 1),
                    CellArrayStructure::SingleCell,
                    "row {row}"
                );
            }
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn snapshot_rebuilds_the_spill() {
        let mut author = UserModel::new_empty_with_session("book", "en", "UTC", "en", 1).unwrap();
        author.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A1=1, A2=2, A3=3
        assert_eq!(author.get_formatted_cell_value(0, 3, 1).unwrap(), "3"); // A3=3

        let mut restored =
            UserModel::<Stable>::from_bytes_with_session(&author.to_bytes(), 2).unwrap();
        // The overlay is not in the payload; only an evaluation can put the spill back.
        restored.evaluate();
        assert_eq!(restored.get_formatted_cell_value(0, 1, 1).unwrap(), "1"); // A1=1
        assert_eq!(restored.get_formatted_cell_value(0, 3, 1).unwrap(), "3"); // A3=3
        let sheet = &restored.get_model().workbook.worksheets[0];
        // row 3 was never got explicit key, so it was not materialized
        // the only reason why it shows value, is because we track spill overlays
        assert_eq!(Stable::row_at(&sheet.index, 3), None);
    }

    /// B1:B3 = 5, 10, 15 and the CSE array A1:A3 = B1:B3*2 on `a`, flushed.
    fn cse_init(a: &mut Peer) {
        for row in 1..=3 {
            a.set_user_input(0, row, 2, &format!("{}", row * 5))
                .unwrap();
        }
        a.set_user_array_formula(0, 1, 1, 1, 3, "=B1:B3*2").unwrap(); // A1:A3 = B1:B3*2
    }

    #[test]
    fn cse_replicates() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        cse_init(&mut a);
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "10"); // A1=10
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "20"); // A2=20
            assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "30"); // A3=30
            assert_eq!(model.get_cell_content(0, 1, 1).unwrap(), "=B1:B3*2");
            assert_eq!(
                structure(model, 1, 1),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            assert_eq!(
                structure(model, 3, 1),
                CellArrayStructure::ArrayChild(1, 1, 1, 3)
            );
        }
        converged(&mut a, &mut b);
        b.flush_send_queue();

        assert!(b.set_user_input(0, 2, 1, "7").is_err()); // A2=7 (denied)
        assert!(b.get_model().local.pending.is_empty()); // write denied, no updates

        // A scalar formula over a range is still an array: it fills the range.
        a.set_user_array_formula(0, 5, 3, 2, 2, "=1+1").unwrap(); // C5:D6

        // Read before the anchor in sheet order: the covered cell is there all the same.
        a.set_user_input(0, 1, 3, "=D6*3").unwrap(); // C1=6
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            for (row, col) in [(5, 3), (5, 4), (6, 3), (6, 4)] {
                assert_eq!(model.get_formatted_cell_value(0, row, col).unwrap(), "2");
            }
            assert_eq!(model.get_formatted_cell_value(0, 1, 3).unwrap(), "6");
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn cse_blocked_by_concurrent_write() {
        fn execute(clear_on_author: bool) {
            let (mut a, mut b) = (peer(1), peer(2));
            a.new_sheet().unwrap();
            deliver(&mut a, &mut b);

            cse_init(&mut a); // A: A1:A3=B1:B3*2
            b.set_user_input(0, 2, 1, "7").unwrap(); // B: A2=7, before A's array arrives
            let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
            b.apply_external_diffs(&from_a).unwrap();
            a.apply_external_diffs(&from_b).unwrap();
            for model in [&a, &b] {
                // on collab, CSE conflict works like dynamic array
                assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "#SPILL!");
                assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "7");
                assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "");
            }
            converged(&mut a, &mut b);

            let (from, to) = if clear_on_author {
                (&mut a, &mut b)
            } else {
                (&mut b, &mut a)
            };
            from.set_user_input(0, 2, 1, "").unwrap(); // unblock the array
            deliver(from, to);
            for model in [&a, &b] {
                assert_eq!(model.get_formatted_cell_value(0, 1, 1).unwrap(), "10");
                assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "20");
                assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "30");
            }
            converged(&mut a, &mut b);
        }

        execute(true);
        execute(false);
    }

    /// An array against a plain value written to its anchor concurrently. The anchor is one
    /// register: the later write stands, and nothing of the other is left.
    #[test]
    fn cse_anchor_is_one_register() {
        fn execute(array_last: bool) {
            let (mut a, mut b) = (peer(1), peer(2));
            a.new_sheet().unwrap();
            deliver(&mut a, &mut b);

            // The peers share this process's clock: the later call carries the later stamp.
            if array_last {
                b.set_user_input(0, 1, 1, "x").unwrap(); // B: A1=x
                a.set_user_array_formula(0, 1, 1, 1, 2, "=1+1").unwrap(); // A: A1:A2=1+1 (CSE)
            } else {
                a.set_user_array_formula(0, 1, 1, 1, 2, "=1+1").unwrap(); // A: A1:A2=1+1 (CSE)
                b.set_user_input(0, 1, 1, "x").unwrap(); // B: A1=x
            }
            let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
            b.apply_external_diffs(&from_a).unwrap();
            a.apply_external_diffs(&from_b).unwrap();

            let (values, anchor, below) = if array_last {
                (
                    ["2", "2"],
                    CellArrayStructure::ArrayAnchor(1, 2),
                    CellArrayStructure::ArrayChild(1, 1, 1, 2),
                )
            } else {
                (
                    ["x", ""],
                    CellArrayStructure::SingleCell,
                    CellArrayStructure::SingleCell,
                )
            };
            for model in [&a, &b] {
                let shown = [
                    model.get_formatted_cell_value(0, 1, 1).unwrap(),
                    model.get_formatted_cell_value(0, 2, 1).unwrap(),
                ];
                assert_eq!(shown, values, "array last: {array_last}");
                assert_eq!(structure(model, 1, 1), anchor, "array last: {array_last}");
                assert_eq!(structure(model, 2, 1), below, "array last: {array_last}");
            }
            converged(&mut a, &mut b);
        }

        execute(true);
        execute(false);
    }

    #[test]
    fn cse_undo() {
        use crate::collab::patch::{invert_patches, Patch};

        let mut model = CollabModel::new(1);
        model.new_sheet();
        for row in 1..=3 {
            model.set_user_input(0, row, 1, format!("{row}")).unwrap(); // Ax=x
        }
        model.evaluate();
        model.flush();

        model.set_user_array_formula(0, 1, 1, 1, 3, "=10").unwrap(); // A1:A3=10
        model.evaluate();
        assert_eq!(model.get_formatted_cell_value(0, 3, 1).unwrap(), "10"); // A3=10
        let commits = model.flush();
        assert_eq!(commits.len(), 1);

        let inverse: Vec<Patch> = commits
            .iter()
            .rev()
            .flat_map(|commit| invert_patches(&commit.patches))
            .collect();
        model.commit_local(inverse);
        model.evaluate();
        for row in 1..=3 {
            assert_eq!(
                model.get_formatted_cell_value(0, row, 1).unwrap(),
                format!("{row}")
            ); // Ax == x
            assert!(matches!(
                model.workbook.worksheets[0].cell(row, 1).as_deref(),
                Some(Cell::NumberCell { .. })
            ));
        }
    }

    #[test]
    fn cse_survives_structural_edits() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        cse_init(&mut a);
        deliver(&mut a, &mut b);

        // Concurrently: A inserts a row inside the array, B deletes one.
        a.insert_rows(0, 2, 1).unwrap();
        b.delete_rows(0, 3, 1).unwrap();
        let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
        b.apply_external_diffs(&from_a).unwrap();
        a.apply_external_diffs(&from_b).unwrap();
        a.evaluate();
        b.evaluate();
        converged(&mut a, &mut b);
        for model in [&a, &b] {
            // The array is `height` rows from wherever its anchor sits now.
            assert_eq!(
                structure(model, 1, 1),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            for row in 2..=3 {
                assert_eq!(
                    structure(model, row, 1),
                    CellArrayStructure::ArrayChild(1, 1, 1, 3)
                );
            }
            assert_eq!(structure(model, 4, 1), CellArrayStructure::SingleCell);
        }
    }

    #[test]
    fn cse_survives_snapshot_and_sheet_copy() {
        let mut author = UserModel::new_empty_with_session("book", "en", "UTC", "en", 1).unwrap();
        cse_init(&mut author);
        author.duplicate_sheet(0).unwrap();
        for sheet in 0..2 {
            assert_eq!(
                author.get_cell_array_structure(sheet, 1, 1).unwrap(),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            assert_eq!(author.get_formatted_cell_value(sheet, 3, 1).unwrap(), "30");
        }

        let mut restored =
            UserModel::<Stable>::from_bytes_with_session(&author.to_bytes(), 2).unwrap();
        restored.evaluate();
        for sheet in 0..2 {
            assert!(matches!(
                restored.get_model().workbook.worksheets[sheet as usize]
                    .cell(1, 1)
                    .as_deref(),
                Some(Cell::ArrayFormula {
                    kind: ArrayKind::Cse,
                    r: (1, 3),
                    ..
                })
            ));
            assert_eq!(
                restored.get_formatted_cell_value(sheet, 3, 1).unwrap(),
                "30"
            );
        }
    }

    #[test]
    fn cse_extent_from_the_wire_is_clamped() {
        use crate::collab::patch::{CellInput, Patch};

        let mut a = CollabModel::new(1);
        a.new_sheet();
        a.set_user_array_formula(0, 1, 1, 1, 2, "=1+1").unwrap(); // A1:A2=1+1
        let mut commits = a.flush();
        for commit in &mut commits {
            for patch in &mut commit.patches {
                if let Patch::SetCellValue {
                    value: Some(CellInput::Cse { width, height, .. }),
                    ..
                } = patch
                {
                    (*width, *height) = (0, -3);
                }
            }
        }
        let mut b = CollabModel::new(2);
        b.apply_batch(&commits).unwrap();
        b.evaluate();
        assert!(matches!(
            b.workbook.worksheets[0].cell(1, 1).as_deref(),
            Some(Cell::ArrayFormula {
                kind: ArrayKind::Cse,
                r: (1, 1),
                ..
            })
        ));
        assert_eq!(b.get_formatted_cell_value(0, 1, 1).unwrap(), "2"); // A1 == 2
    }

    /// The values of A1..A4, as shown.
    fn a1_to_a4(model: &Peer) -> Vec<String> {
        (1..=4)
            .map(|row| model.get_formatted_cell_value(0, row, 1).unwrap())
            .collect()
    }

    /// Exchanges what both peers did concurrently: each applies its own work first.
    fn exchange(a: &mut Peer, b: &mut Peer) {
        let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
        b.apply_external_diffs(&from_a).unwrap();
        a.apply_external_diffs(&from_b).unwrap();
    }

    #[test]
    fn cse_undo_redo_converges() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        for row in 1..=3 {
            a.set_user_input(0, row, 1, &format!("{row}")).unwrap(); // A1:A3=1,2,3
        }
        cse_init(&mut a); // over what A1:A3 held
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["10", "20", "30", ""]);
        }

        // One step takes the array away and puts back what it covered, on both.
        a.undo().unwrap();
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["1", "2", "3", ""]);
            for row in 1..=3 {
                assert_eq!(structure(model, row, 1), CellArrayStructure::SingleCell);
            }
            // Nothing is locked any more.
            assert_eq!(model.get_cell_content(0, 1, 1).unwrap(), "1");
        }
        converged(&mut a, &mut b);

        a.redo().unwrap();
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["10", "20", "30", ""]);
            assert_eq!(
                structure(model, 1, 1),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            assert_eq!(
                structure(model, 2, 1),
                CellArrayStructure::ArrayChild(1, 1, 1, 3)
            );
        }
        converged(&mut a, &mut b);
        assert!(b.set_user_input(0, 2, 1, "7").is_err()); // locked again

        a.undo().unwrap();
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["1", "2", "3", ""]);
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn cse_undo_keeps_a_concurrent_write_into_the_range() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        deliver(&mut a, &mut b);

        cse_init(&mut a); // A: A1:A3=B1:B3*2
        b.set_user_input(0, 2, 1, "7").unwrap(); // B: A2=7, before the array arrives
        exchange(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["#SPILL!", "7", "", ""]);
        }

        a.undo().unwrap();
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["", "7", "", ""]);
            assert_eq!(structure(model, 1, 1), CellArrayStructure::SingleCell);
        }
        converged(&mut a, &mut b);

        // Redone, the array is back and blocked by the same cell.
        a.redo().unwrap();
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["#SPILL!", "7", "", ""]);
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn undo_of_the_blocking_write_restores_the_cse() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        deliver(&mut a, &mut b);

        cse_init(&mut a);
        b.set_user_input(0, 2, 1, "7").unwrap(); // A2=7
        exchange(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["#SPILL!", "7", "", ""]);
        }

        b.undo().unwrap(); // undo A2=7, unlocks CSE
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            // CSE works back
            assert_eq!(a1_to_a4(model), ["10", "20", "30", ""]);
            assert_eq!(
                structure(model, 2, 1),
                CellArrayStructure::ArrayChild(1, 1, 1, 3)
            );
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn cse_undo_after_a_peer_cleared_the_range() {
        use crate::expressions::types::Area;

        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        for row in 1..=3 {
            a.set_user_input(0, row, 1, &format!("{row}")).unwrap(); // A1,A2,A3=1,2,3
        }
        cse_init(&mut a);
        deliver(&mut a, &mut b);

        let area = Area {
            sheet: 0,
            row: 1,
            column: 1,
            width: 1,
            height: 3,
        };
        b.range_clear_contents(&area).unwrap(); // clear A1:A3 (wins)
        deliver(&mut b, &mut a);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["", "", "", ""]);
            assert_eq!(structure(model, 1, 1), CellArrayStructure::SingleCell);
        }

        a.undo().unwrap(); // undo CSE, brings back A1,A2,A3=1,2,3
        deliver(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(a1_to_a4(model), ["1", "2", "3", ""]);
            assert_eq!(structure(model, 1, 1), CellArrayStructure::SingleCell);
        }
        converged(&mut a, &mut b);
    }

    #[test]
    fn cse_overlapping_arrays_converge() {
        let (mut a, mut b, mut c) = (peer(1), peer(2), peer(3));
        a.new_sheet().unwrap();
        let sheet = a.flush_send_queue();
        b.apply_external_diffs(&sheet).unwrap();
        c.apply_external_diffs(&sheet).unwrap();

        a.set_user_array_formula(0, 1, 1, 1, 3, "=1+1").unwrap(); // A: A1:A3=1+1
        b.set_user_array_formula(0, 2, 1, 1, 3, "=2+2").unwrap(); // B: A2:A4=2+2
        let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
        b.apply_external_diffs(&from_a).unwrap();
        a.apply_external_diffs(&from_b).unwrap();
        // The third peer sees B's first.
        c.apply_external_diffs(&from_b).unwrap();
        c.apply_external_diffs(&from_a).unwrap();

        for model in [&a, &b, &c] {
            // A1:A3 is locked by A2:A4, since A2 (anchor) is in A1's spill range
            assert_eq!(a1_to_a4(model), ["#SPILL!", "4", "4", "4"]);
            assert_eq!(
                structure(model, 1, 1),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            assert_eq!(
                structure(model, 2, 1),
                CellArrayStructure::ArrayAnchor(1, 3)
            );
            assert_eq!(
                structure(model, 4, 1),
                CellArrayStructure::ArrayChild(2, 1, 1, 3)
            );
        }
        converged(&mut a, &mut b);
        converged(&mut a, &mut c);
    }

    #[test]
    fn cse_same_anchor_converges_on_one_extent() {
        fn execute(vertical_last: bool) {
            let (mut a, mut b, mut c) = (peer(1), peer(2), peer(3));
            a.new_sheet().unwrap();
            let sheet = a.flush_send_queue();
            b.apply_external_diffs(&sheet).unwrap();
            c.apply_external_diffs(&sheet).unwrap();

            // The peers share this process's clock: the later call carries the later stamp.
            if vertical_last {
                b.set_user_array_formula(0, 1, 1, 3, 1, "=2+2").unwrap(); // B: A1:C1, across
                a.set_user_array_formula(0, 1, 1, 1, 3, "=1+1").unwrap(); // A: A1:A3, down
            } else {
                a.set_user_array_formula(0, 1, 1, 1, 3, "=1+1").unwrap(); // A: A1:A3, down
                b.set_user_array_formula(0, 1, 1, 3, 1, "=2+2").unwrap(); // B: A1:C1, across
            }
            let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
            b.apply_external_diffs(&from_a).unwrap();
            a.apply_external_diffs(&from_b).unwrap();
            // The third peer sees B's first.
            c.apply_external_diffs(&from_b).unwrap();
            c.apply_external_diffs(&from_a).unwrap();

            let (anchor, down, across, below, beside) = if vertical_last {
                (
                    CellArrayStructure::ArrayAnchor(1, 3),
                    ["2", "2", "2", ""],
                    ["2", "", ""],
                    CellArrayStructure::ArrayChild(1, 1, 1, 3),
                    CellArrayStructure::SingleCell,
                )
            } else {
                (
                    CellArrayStructure::ArrayAnchor(3, 1),
                    ["4", "", "", ""],
                    ["4", "4", "4"],
                    CellArrayStructure::SingleCell,
                    CellArrayStructure::ArrayChild(1, 1, 3, 1),
                )
            };
            for model in [&a, &b, &c] {
                let a1_to_c1: Vec<String> = (1..=3)
                    .map(|column| model.get_formatted_cell_value(0, 1, column).unwrap())
                    .collect();
                assert_eq!(structure(model, 1, 1), anchor, "down last: {vertical_last}");
                assert_eq!(a1_to_a4(model), down, "down last: {vertical_last}");
                assert_eq!(a1_to_c1, across, "down last: {vertical_last}");
                assert_eq!(structure(model, 2, 1), below, "down last: {vertical_last}");
                assert_eq!(structure(model, 1, 2), beside, "down last: {vertical_last}");
            }
            converged(&mut a, &mut b);
            converged(&mut a, &mut c);
        }

        execute(true);
        execute(false);
    }

    #[test]
    fn cse_versus_dynamic_spill_converges() {
        let (mut a, mut b, mut c) = (peer(1), peer(2), peer(3));
        a.new_sheet().unwrap();
        for row in 1..=3 {
            a.set_user_input(0, row, 4, &format!("{row}")).unwrap(); // D1,D2,D3=1,2,3
        }
        let seed = a.flush_send_queue();
        b.apply_external_diffs(&seed).unwrap();
        c.apply_external_diffs(&seed).unwrap();

        a.set_user_array_formula(0, 2, 1, 2, 1, "=1+1").unwrap(); // A: A2:B2=1+1
        b.set_user_input(0, 1, 2, "=D1:D3").unwrap(); // B: B1 spills over B1:B3
        let (from_a, from_b) = (a.flush_send_queue(), b.flush_send_queue());
        b.apply_external_diffs(&from_a).unwrap();
        a.apply_external_diffs(&from_b).unwrap();
        c.apply_external_diffs(&from_b).unwrap();
        c.apply_external_diffs(&from_a).unwrap();
        converged(&mut a, &mut b);
        converged(&mut a, &mut c);
        // Neither holds the other's anchor, so which one gives way is evaluation order — the same
        // on every replica — and exactly one of them does.
        for model in [&a, &b, &c] {
            let cse = model.get_formatted_cell_value(0, 2, 1).unwrap();
            let dynamic = model.get_formatted_cell_value(0, 1, 2).unwrap();
            assert!(
                (cse == "#SPILL!") != (dynamic == "#SPILL!"),
                "A2 = {cse}, B1 = {dynamic}"
            );
        }
    }

    fn a2(sheet: u32) -> crate::expressions::types::Area {
        crate::expressions::types::Area {
            sheet,
            row: 2,
            column: 1,
            width: 1,
            height: 1,
        }
    }

    #[test]
    fn spill_over_a_styled_empty_cell_keeps_its_style() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        a.update_range_style(&a2(0), "font.b", "true").unwrap(); // A: A2 bold, empty
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);

        a.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A: A1:A3=1,2,3
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);
        for model in [&a, &b] {
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "2");
            assert!(model.get_cell_style(0, 2, 1).unwrap().font.b);
        }

        b.update_range_style(&a2(0), "font.i", "true").unwrap(); // B: A2 italic, spilled
        deliver(&mut b, &mut a);
        converged(&mut a, &mut b);

        a.set_user_input(0, 1, 1, "").unwrap(); // A: the spill goes
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);
        for model in [&a, &b] {
            let style = model.get_cell_style(0, 2, 1).unwrap();
            assert!(style.font.b && style.font.i, "A2 is bold and italic");
            assert_eq!(model.get_formatted_cell_value(0, 2, 1).unwrap(), "");
        }
    }

    /// A spill in a styled row shows the row's style, and leaves no cell behind when it goes.
    #[test]
    fn spill_in_a_styled_row_leaves_no_cell() {
        let (mut a, mut b) = (peer(1), peer(2));
        a.new_sheet().unwrap();
        let row_2 = crate::expressions::types::Area {
            sheet: 0,
            row: 2,
            column: 1,
            width: crate::constants::LAST_COLUMN,
            height: 1,
        };
        a.update_range_style(&row_2, "font.b", "true").unwrap(); // A: row 2 bold
        a.set_user_input(0, 1, 1, "=SEQUENCE(3)").unwrap(); // A: A1:A3=1,2,3
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);
        for model in [&a, &b] {
            assert!(model.get_cell_style(0, 2, 1).unwrap().font.b);
        }

        a.set_user_input(0, 1, 1, "").unwrap(); // A: the spill goes
        deliver(&mut a, &mut b);
        converged(&mut a, &mut b);
        for model in [&a, &b] {
            let sheet = &model.get_model().workbook.worksheets[0];
            assert_eq!(sheet.sheet_data.cell(2, 1), None);
            assert!(model.get_cell_style(0, 2, 1).unwrap().font.b);
        }
    }
}
