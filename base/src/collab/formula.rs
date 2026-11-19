use bitcode::{Decode, Encode};

use crate::collab::fractional_key::FractionalKey;
use crate::collab::model::StableCellAddress;
use crate::collab::patch::{DefinedNameId, SheetId};

/// Which sheet a reference points at.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
pub enum StableSheetRef {
    /// Ref without explicit sheet prefix: resolves to the host cell's sheet.
    Current,
    Sheet(SheetId),
}

/// One axis (row or column) of a reference.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
pub struct StableAxisRef {
    /// [`FractionalKey::NULL`] is an open end: the first or last row or column of the grid.
    pub key: FractionalKey,
    /// Whether the axis is shown with a `$` and lowered to an ordinal rather than an offset from
    /// the host.
    pub absolute: bool,
}

/// What one reference-shaped leaf of a formula names.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
pub enum StableRef {
    Cell {
        sheet: StableSheetRef,
        row: StableAxisRef,
        col: StableAxisRef,
    },
    Range {
        sheet: StableSheetRef,
        row1: StableAxisRef,
        col1: StableAxisRef,
        row2: StableAxisRef,
        col2: StableAxisRef,
    },
    Name(DefinedNameId),
    /// A sheet name or bare name the author could not resolve: the leaf stays as parsed, and
    /// lowering retries the name. Carries the name so `unresolved` can index it.
    Unresolved(String),
}

pub(crate) fn unresolved_names(refs: &[StableRef]) -> impl Iterator<Item = &str> {
    refs.iter().filter_map(|slot| match slot {
        StableRef::Unresolved(name) => Some(name.as_str()),
        _ => None,
    })
}

/// R1C1 addressed formula string + [StableRef] trackers used to lower into formula string whenever
/// row/column reorder affects the formula.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
pub struct StableFormula {
    pub text: String,
    pub refs: Vec<StableRef>,
}

impl StableFormula {
    pub fn unresolved_names(&self) -> impl Iterator<Item = &str> {
        unresolved_names(&self.refs)
    }

    /// Points every reference naming `source` at `target` instead, returning whether anything
    /// changed. A reference with no sheet prefix stays as it is. The text is left alone: lowering
    /// takes the sheet from the slot.
    pub(crate) fn retarget_sheet(&mut self, source: SheetId, target: SheetId) -> bool {
        let mut changed = false;
        for slot in &mut self.refs {
            let sheet = match slot {
                StableRef::Cell { sheet, .. } | StableRef::Range { sheet, .. } => sheet,
                _ => continue,
            };
            if *sheet == StableSheetRef::Sheet(source) {
                *sheet = StableSheetRef::Sheet(target);
                changed = true;
            }
        }
        changed
    }
}

/// What `shared_formulas[f]` of a sheet is relative to, and what its leaves name.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
pub struct FormulaRefs {
    /// The cell the text is relative to.
    pub host: StableCellAddress,
    /// One per reference-shaped leaf of the parsed node, in pre-order.
    pub refs: Vec<StableRef>,
}

impl FormulaRefs {
    /// The sheets a reorder or a rename of which can change how the entry lowers: every sheet a
    /// cell or range slot names, and the host's own (`host`) whenever there is one, since relative
    /// offsets are measured from the host.
    pub(crate) fn sheets(&self, host: SheetId) -> impl Iterator<Item = SheetId> + '_ {
        let named = self.refs.iter().filter_map(|slot| match slot {
            StableRef::Cell {
                sheet: StableSheetRef::Sheet(id),
                ..
            }
            | StableRef::Range {
                sheet: StableSheetRef::Sheet(id),
                ..
            } => Some(*id),
            _ => None,
        });
        let any = (self.refs.iter())
            .any(|slot| matches!(slot, StableRef::Cell { .. } | StableRef::Range { .. }));
        any.then_some(host).into_iter().chain(named)
    }

    pub(crate) fn names(&self) -> impl Iterator<Item = DefinedNameId> + '_ {
        self.refs.iter().filter_map(|slot| match slot {
            StableRef::Name(id) => Some(*id),
            _ => None,
        })
    }

    pub(crate) fn unresolved(&self) -> bool {
        self.refs
            .iter()
            .any(|slot| matches!(slot, StableRef::Unresolved(_)))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]
    use super::*;
    use crate::collab::fractional_index::virtual_key;

    fn axis(ordinal: u32, absolute: bool) -> StableAxisRef {
        StableAxisRef {
            key: virtual_key(ordinal),
            absolute,
        }
    }

    /// Every `StableRef` and `StableSheetRef` variant survives bitcode, open ends included.
    #[test]
    fn round_trip() {
        let formulas = vec![
            // =A1+$B$2
            StableFormula {
                text: "R[0]C[0]+R2C2".to_string(),
                refs: vec![
                    StableRef::Cell {
                        sheet: StableSheetRef::Current,
                        row: axis(1, false),
                        col: axis(1, false),
                    },
                    StableRef::Cell {
                        sheet: StableSheetRef::Current,
                        row: axis(2, true),
                        col: axis(2, true),
                    },
                ],
            },
            // =SUM(Sheet2!A1:B3)+SUM(C:C)
            StableFormula {
                text: "SUM(Sheet2!R[0]C[0]:R3C2)+SUM(R1C[2]:R1048576C[2])".to_string(),
                refs: vec![
                    StableRef::Range {
                        sheet: StableSheetRef::Sheet(7),
                        row1: axis(1, false),
                        col1: axis(1, false),
                        row2: axis(3, true),
                        col2: axis(2, true),
                    },
                    StableRef::Range {
                        sheet: StableSheetRef::Current,
                        row1: StableAxisRef {
                            key: FractionalKey::NULL,
                            absolute: true,
                        },
                        col1: axis(3, false),
                        row2: StableAxisRef {
                            key: FractionalKey::NULL,
                            absolute: true,
                        },
                        col2: axis(3, false),
                    },
                ],
            },
            // =MyName*Nope!A1+notAName
            StableFormula {
                text: "MyName*Nope!R[0]C[0]+notAName".to_string(),
                refs: vec![
                    StableRef::Name(42),
                    StableRef::Unresolved("Nope".to_string()),
                    StableRef::Unresolved("notAName".to_string()),
                ],
            },
            // An unparseable text carries no slots.
            StableFormula {
                text: "=this is not a formula".to_string(),
                refs: vec![],
            },
        ];
        for formula in formulas {
            let decoded: StableFormula = bitcode::decode(&bitcode::encode(&formula)).unwrap();
            assert_eq!(decoded, formula);
        }
        let entry = FormulaRefs {
            host: (virtual_key(5), virtual_key(4)),
            refs: vec![StableRef::Name(3), StableRef::Unresolved("x".to_string())],
        };
        let decoded: FormulaRefs = bitcode::decode(&bitcode::encode(&entry)).unwrap();
        assert_eq!(decoded, entry);
    }

    /// The names a formula still holds as text are its unbound slots, and a retarget touches only
    /// the slots naming the source by id.
    #[test]
    fn text_names_and_retarget() {
        let mut formula = StableFormula {
            text: String::new(),
            refs: vec![
                StableRef::Cell {
                    sheet: StableSheetRef::Sheet(7),
                    row: axis(1, true),
                    col: axis(1, true),
                },
                StableRef::Cell {
                    sheet: StableSheetRef::Current,
                    row: axis(1, true),
                    col: axis(1, true),
                },
                StableRef::Unresolved("Nope".to_string()),
                StableRef::Name(1),
            ],
        };
        assert_eq!(formula.unresolved_names().collect::<Vec<_>>(), vec!["Nope"]);
        assert!(formula.retarget_sheet(7, 9));
        assert!(!formula.retarget_sheet(7, 9));
        assert!(matches!(
            formula.refs[0],
            StableRef::Cell {
                sheet: StableSheetRef::Sheet(9),
                ..
            }
        ));
        assert!(matches!(
            formula.refs[1],
            StableRef::Cell {
                sheet: StableSheetRef::Current,
                ..
            }
        ));
    }
}
