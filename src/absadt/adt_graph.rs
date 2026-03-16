use std::collections::{BTreeMap, BTreeSet};

use crate::absadt::enc::Encoder;
use crate::errors::Res;
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

    pub fn get_statically_simplifiable(&self) -> BTreeMap<Typ, usize> {
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

    pub fn get_dependant_on_statically_simplifiable(&self) -> BTreeSet<Typ> {
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
