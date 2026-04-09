use std::collections::{BTreeMap, BTreeSet};

use crate::term;
use crate::typ;
use crate::VarMap;
use crate::absadt::enc::{Enc, Approx, Encoder};
use crate::errors::Res;
use crate::info::VarInfo;
use crate::term::typ::{RTyp, Typ};

pub enum Category {
    Static, Dynamic
}

/// Struct to manage all the type dependencies.
///
/// It introduces the concept of *statically simplifiable* and *dynamically
/// simplifiable* for a given type.
/// # Definitions
/// ## Statically simplifiable
/// An ADT is said statically simplifiable when it is not recursive and the
/// only dependencies are:
/// - None or
/// - A SMT primitive type (Int) or
/// - Another statically simplifiable ADT
///
/// Its approximation is fixed before the CEGAR loop and remains the same
/// throughout the whole execution.
/// ## Dynamically simplifiable
/// An ADT is said dynamically simplifiable:
/// - There is no loop (even with size > 1) into itself and
/// - It is not statically simplifiable
///
/// If an ADT is *dynamically simplifiable* then its approximation degree and
/// its arguments are adjusted during the CEGAR loop according to the dependency
/// approximation degree.
/// # Examples
/// ## Statically simplifiable
/// ```text
/// (declare-datatypes
///  ( (Color 0) )
///  ( ( (Red) (Green) (Blue) (Yellow) ) ))
/// ```
/// Is statically simplified to:
/// ```text
/// Red    -> 1
/// Green  -> 2
/// Blue   -> 3
/// Yellow -> 4
/// ```
/// ## Dynamically simplifiable
/// ```text
/// (declare-datatypes
///  ( (Tuple 0) )
///  ( ( (TupColor  (first Color) (second Color)) ) ))
/// ```
/// Is statically simplified to:
/// ```text
/// TupColor (first, second) -> (first, second)
/// ```
/// If the approximation degree for `Color` was 2 then, the simplification for
/// `Tuple` would have been:
/// ```text
/// TupColor (first_1, first_2, second_1, second_2) -> (first_1, first_2, second_1, second_2)
/// ```
#[derive(Default)]
pub struct ADTDependencyGraph {
    dependencies: BTreeMap<Typ, BTreeSet<Typ>>,
    statically_simplifiable: BTreeSet<Typ>,
    dynamically_simplifiable: BTreeSet<Typ>,
    initial_approx_degrees: BTreeMap<RTyp, usize>,
}

impl ADTDependencyGraph {
    pub fn new(adts: &BTreeMap<Typ, Encoder>) -> Res<Self> {
        let all_adts: BTreeSet<Typ> = adts.keys().map(|item| item.clone()).collect();
        let mut dependencies = BTreeMap::new();

        for adt_rtyp in all_adts.iter() {
            if adt_rtyp.dtyp_inspect().is_some() {
                dependencies.insert(adt_rtyp.clone(), adt_rtyp.dtyp_dependencies(&all_adts)?);
            }
        }

        let statically_simplifiable = Self::init_statically_simplifiable(&dependencies);
        let dynamically_simplifiable =
            Self::init_dynamically_simplifiable(&dependencies, &statically_simplifiable);
        let initial_approx_degrees = Self::init_approx_degrees(&all_adts)?;

        Ok(Self {
            dependencies,
            statically_simplifiable,
            dynamically_simplifiable,
            initial_approx_degrees,
        })
    }

    fn init_statically_simplifiable(dependencies: &BTreeMap<Typ, BTreeSet<Typ>>) -> BTreeSet<Typ> {
        let mut return_vec = BTreeSet::new();
        let mut changed = true;

        while changed {
            changed = false;
            for (typ, deps) in dependencies.iter() {
                if !return_vec.contains(typ) {
                    if deps
                        .iter()
                        .all(|dep| matches!(dep.get(), RTyp::Int) || return_vec.contains(dep))
                    {
                        return_vec.insert(typ.clone());
                        changed = true;
                    }
                }
            }
        }
        return_vec
    }

    fn init_dynamically_simplifiable(
        dependencies: &BTreeMap<Typ, BTreeSet<Typ>>,
        statically_simplifiable: &BTreeSet<Typ>,
    ) -> BTreeSet<Typ> {
        let is_self_recursive = |start: &Typ| -> bool {
            let mut visited = BTreeSet::new();
            let mut stack = vec![start];
            while let Some(typ) = stack.pop() {
                for dep_set in dependencies.get(typ).iter() {
                    for dep in dep_set.iter() {
                        if visited.insert(dep) {
                            stack.push(dep);
                        }
                        if dep == start {
                            return true;
                        }
                    }
                }
            }
            false
        };

        dependencies
            .keys()
            .filter(|t| !(is_self_recursive(t) || statically_simplifiable.contains(t)))
            .map(|t| t.clone())
            .collect()
    }

    fn init_approx_degrees(all_adt: &BTreeSet<Typ>) -> Res<BTreeMap<RTyp, usize>> {
        let mut degree_map = BTreeMap::new();
        for typ in all_adt.iter() {
            typ.get().compute_approximation_degree(all_adt, &mut degree_map)?;
        }
        Ok(degree_map)
    }

    fn get_simplifiable(&self, category_to_flatten: &Category) -> BTreeMap<Typ, usize> {
        let list = match category_to_flatten {
            Category::Dynamic => &self.dynamically_simplifiable,
            Category::Static => &self.statically_simplifiable,
        };
        list
            .iter()
            .map(|typ| {
                (
                    typ.clone(),
                    *self.initial_approx_degrees.get(typ).unwrap(),
                )
            })
            .collect()
    }

    fn get_dependant_on(&self, category_to_flatten: &Category) -> BTreeSet<Typ> {
        let criterion = match category_to_flatten {
            Category::Dynamic => &self.dynamically_simplifiable,
            Category::Static => &self.statically_simplifiable,
        };
        self.dependencies
            .iter()
            .filter(|(_, deps)| {
                deps.iter()
                    .any(|typ| criterion.contains(typ))
            })
            .map(|(key, _)| key.clone())
            .collect()
    }

    pub fn flatten_adt(&self, encs: &mut BTreeMap<Typ, Enc<Approx>>, category_to_flatten: Category) -> Res<()> {
        let simplifiable: BTreeMap<Typ, usize> = self.get_simplifiable(&category_to_flatten);
        let typs: BTreeSet<Typ> = self.get_dependant_on(&category_to_flatten);
        // Expand the signature of types dependant on simplifiable ADTs
        for dep_typ in typs {
            let (rdtyp, parameter) = dep_typ.dtyp_inspect().unwrap();
            let enc = &mut encs.get_mut(&dep_typ).unwrap();
            for (constructor_name, constructor_args) in rdtyp.news.iter() {
                let mut new_signature = VarMap::<VarInfo>::new();
                for (arg_name, arg_typ) in constructor_args.iter() {
                    if let Ok(argument_concrete_typ) = arg_typ.to_type(Some(parameter)) {
                        for idx in 0..*self.initial_approx_degrees.get(&argument_concrete_typ).unwrap_or(&1) {
                            new_signature.push(VarInfo {
                                name: format!("{arg_name}_{idx}",),
                                typ: typ::int(),
                                idx: new_signature.next_index(),
                                active: true,
                            });
                        }
                    }
                    else{
                        new_signature.push(VarInfo {
                            name: format!("{arg_name}",),
                            typ: typ::int(),
                            idx: new_signature.next_index(),
                            active: true,
                        });
                    }
                }
                enc.approxs.get_mut(constructor_name).unwrap().args = new_signature;
            }
        }

        // Expanding the approximation body
        for (typ, approx_deg) in simplifiable.iter() {
            let enc = encs.get_mut(&typ).unwrap();
            enc.n_params = *approx_deg;
            if matches!(category_to_flatten, Category::Dynamic) {
                enc.dynamically_simplified = true;
            }
            else {
                enc.statically_simplified = true;
            }
            let n_constr = enc.approxs.keys().len();
            let approximations = &mut enc.approxs;
            for (idx, (_, approx)) in approximations.iter_mut().enumerate() {
                approx.expand_signature(&simplifiable);
                approx.terms = vec![];
                if n_constr > 1 {
                    //Discriminate the constructor
                    approx.terms.push(term::int(idx));
                }

                for arg in approx.args.iter() {
                    approx.terms.push(term::int_var(arg.idx));
                }
                // Final padding
                if approx.terms.len() < enc.n_params {
                    for _ in approx.terms.len()..enc.n_params {
                        approx.terms.push(term::int_zero());
                    }
                }
                debug_assert_eq!(approx.terms.len(), *approx_deg);
            }
        }
        Ok(())
    }
}

impl std::fmt::Display for ADTDependencyGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "digraph G {{\n",)?;
        for (node, neighbors) in self.dependencies.iter() {
            let color = if self.statically_simplifiable.contains(&node) {
                " [color=red]"
            } else if self.dynamically_simplifiable.contains(&node) {
                " [color=blue]"
            } else {
                ""
            };
            write!(f, "    \"{}\" {};\n", node, color)?;
            for neighbor in neighbors {
                write!(f, "    \"{}\" -> \"{}\";\n", node, neighbor)?;
            }
        }
        write!(f, "}}",)
    }
}

#[test]
fn test_static_adt_detection() {
    use crate::dtyp::DTyp;
    use crate::dtyp::PartialTyp;
    use crate::dtyp::TPrmIdx;
    use crate::dtyp::RDTyp;
    use crate::parse::Pos;

    let dummy_pos = Pos::default();
    let param_0: TPrmIdx = 0.into();
    let ptyp = PartialTyp::DTyp (
        "List".into(), dummy_pos, vec![ PartialTyp::Param(param_0) ].into()
    );
    let mut boolean = RDTyp::new("Bool");
    let _ = boolean.add_constructor("True", vec![]);
    let _ = boolean.add_constructor("False", vec![]);
    let boolean = typ::dtyp(DTyp::new(boolean), vec![].into());
    let b_list = typ::dtyp(crate::dtyp::get("List").unwrap(), vec![boolean.clone()].into());
    let mut adts_encs: BTreeMap<Typ, Encoder> = BTreeMap::new();
    let fake_enc: Enc<Approx> = Enc { typ: typ::int(), n_params: 1, approxs: BTreeMap::new(), statically_simplified: false, dynamically_simplified: false };
    adts_encs.insert(boolean.clone(), fake_enc.clone());
    adts_encs.insert(b_list.clone(), fake_enc.clone());
    let graph = ADTDependencyGraph::new(&adts_encs).unwrap();
    let mut expected: BTreeSet<Typ> = BTreeSet::new();
    expected.insert(boolean);
    assert_eq!(graph.statically_simplifiable, expected);
}

#[test]
fn test_dynamic_adt_detection() {
    use crate::dtyp::DTyp;
    use crate::dtyp::PartialTyp;
    use crate::dtyp::TPrmIdx;
    use crate::dtyp::RDTyp;
    use crate::parse::Pos;

    let dummy_pos = Pos::default();
    let param_0: TPrmIdx = 0.into();
    let ptyp = PartialTyp::DTyp (
        "List".into(), dummy_pos, vec![ PartialTyp::Param(param_0) ].into()
    );
    let int_list = typ::dtyp(crate::dtyp::get("List").unwrap(), vec![typ::int()].into());

    let mut tuple = RDTyp::new("Tuple");
    let _ = tuple.add_constructor("tuple", vec![("first".to_string(), PartialTyp::Typ(int_list.clone())), ("second".to_string(), PartialTyp::Typ(int_list.clone()))]);
    let tuple = typ::dtyp(DTyp::new(tuple), vec![].into());
    let mut adts_encs: BTreeMap<Typ, Encoder> = BTreeMap::new();
    let fake_enc: Enc<Approx> = Enc { typ: typ::int(), n_params: 1, approxs: BTreeMap::new(), statically_simplified: false, dynamically_simplified: false };
    adts_encs.insert(int_list.clone(), fake_enc.clone());
    adts_encs.insert(tuple.clone(), fake_enc.clone());
    let graph = ADTDependencyGraph::new(&adts_encs).unwrap();
    let mut expected: BTreeSet<Typ> = BTreeSet::new();
    expected.insert(tuple);
    assert_eq!(graph.dynamically_simplifiable, expected);
}
