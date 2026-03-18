use std::collections::{BTreeMap, BTreeSet};

use crate::term;
use crate::typ;
use crate::VarMap;
use crate::absadt::enc::{Enc, Approx, Encoder};
use crate::errors::Res;
use crate::info::VarInfo;
use crate::term::typ::{RTyp, Typ};

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

        Ok(Self {
            dependencies,
            statically_simplifiable,
            dynamically_simplifiable,
        })
    }

    fn init_statically_simplifiable(dependencies: &BTreeMap<Typ, BTreeSet<Typ>>) -> BTreeSet<Typ> {
        //let mut simplifiable: BTreeSet<&Typ> = BTreeSet::new();
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
                        //simplifiable.insert(&typ);
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

        let eligible: BTreeSet<_> = dependencies
            .keys()
            .filter(|t| !(is_self_recursive(t) || statically_simplifiable.contains(t)))
            .collect();

        let mut done = BTreeSet::new();
        let mut changed = true;
        //let mut dynamically_simplifiable = Vec::new();
        while changed {
            changed = false;
            for typ in eligible.iter() {
                if !done.contains(*typ) && dependencies[typ]
                        .iter()
                        .any(|dep| !eligible.contains(dep) || !done.contains(dep))
                {
                    done.insert((*typ).clone());
                    changed = true;
                }
            }
        }
        done
    }

    pub fn flatten_static_adt(&self, encs: &mut BTreeMap<Typ, Enc<Approx>>) -> Res<()> {
        let statically_simplifiable = self.get_statically_simplifiable();
        
        // Expand all the signatures and approximations for statically simplifibale ADTs
        for (typ, approx_deg) in statically_simplifiable.iter() {
            let enc = encs.get_mut(&typ).unwrap();
            enc.n_params = *approx_deg;
            enc.statically_simplified = true;
            let approximations = &mut enc.approxs;
            for (idx, (_, approx)) in approximations.iter_mut().enumerate() {
                approx.expand_signature(&statically_simplifiable);
                //Discriminate the constructor
                approx.terms = vec![term::int(idx)];
                for arg in approx.args.iter() {
                    approx.terms.push(term::int_var(arg.idx));
                }
                // Final padding
                for _ in approx.terms.len()..enc.n_params {
                    approx.terms.push(term::int_zero());
                }
            }
        }

        // Expand all the signatures for ADTs that depends on static approx ADTs
        for typ in self
            .get_dependant_on_statically_simplifiable()
        {
            let (rdtyp, parameter) = typ.dtyp_inspect().unwrap();
            let enc = &mut encs.get_mut(&typ).unwrap();
            for (constructor_name, constructor_args) in rdtyp.news.iter() {
                let mut new_signature = VarMap::<VarInfo>::new();
                for (arg_name, arg_typ) in constructor_args.iter() {
                    if let Ok(argument_concrete_typ) = arg_typ.to_type(Some(parameter)) {
                        for idx in 0..*statically_simplifiable.get(&argument_concrete_typ).unwrap_or(&1) {
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
        Ok(())
    }

    fn get_statically_simplifiable(&self) -> BTreeMap<Typ, usize> {
        self.statically_simplifiable
            .iter()
            .map(|typ| {
                (
                    typ.clone(),
                    typ.get_approximation_degree(&self.dependencies.keys().collect()),
                )
            })
            .collect()
    }

    fn get_dependant_on_statically_simplifiable(&self) -> BTreeSet<Typ> {
        self.dependencies
            .iter()
            .filter(|(key, deps)| {
                !self.statically_simplifiable.contains(key) &&
                deps.iter()
                    .any(|typ| self.statically_simplifiable.contains(typ))
            })
            .map(|(key, _)| key.clone())
            .collect()
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
