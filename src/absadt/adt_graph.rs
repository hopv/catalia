use std::collections::{BTreeMap, BTreeSet};

use crate::conf;
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

#[derive(Default)]
pub struct ADTDependencyGraph {
    dependencies: BTreeMap<Typ, BTreeSet<Typ>>,
    // An ADT is said statically simplifiable when it is not recursive and the
    // only dependencies are:
    // - None or
    // - A SMT primitive type (Int) or
    // - Another statically simplifiable ADT
    statically_simplifiable: BTreeSet<Typ>,
    // An ADT is said dynamically simplifiable when there is no loop (any loop size)
    // into itself and it is not statically simplifiable
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
        let initial_approx_degrees = Self::init_approx_degrees(&all_adts);

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

    fn init_approx_degrees(all_adt: &BTreeSet<Typ>) -> BTreeMap<RTyp, usize> {
        let mut degree_map = BTreeMap::new();
        for typ in all_adt.iter() {
            typ.get().compute_approximation_degree(all_adt, &mut degree_map);
        }
        degree_map
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
                enc.dinamically_simplified = true;
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
