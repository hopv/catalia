use std::collections::{BTreeMap, BTreeSet};

use crate::absadt::enc::Encoder;
use crate::errors::Res;
use crate::term::typ::{RTyp, Typ};

pub struct ADTDependencyGraph<'depgraph> {
    dependencies: BTreeMap<&'depgraph RTyp, BTreeSet<&'depgraph RTyp>>,
    all_adts: BTreeSet<&'depgraph Typ>,
    // An ADT is said statically simplifiable when it is not recursive and the
    // only dependencies are:
    // - None or
    // - A SMT primitive type (Int) or
    // - Another statically simplifiable ADT
    pub statically_simplifiable: Vec<&'depgraph RTyp>,
    // An ADT is said dynamically simplifiable when there is no loop (any loop size)
    // into itself and it is not statically simplifiable
    pub dynamically_simplifiable: Vec<&'depgraph RTyp>,
}

impl<'depgraph> ADTDependencyGraph<'depgraph> {
    pub fn new(adts: &'depgraph BTreeMap<Typ, Encoder>) -> Res<Self> {
        let mut dep_graph = Self {
            dependencies: BTreeMap::new(),
            all_adts: adts.keys().collect(),
            statically_simplifiable: Vec::new(),
            dynamically_simplifiable: Vec::new(),
        };
        for (adt_rtyp, _) in adts.iter() {
            if adt_rtyp.dtyp_inspect().is_some() {
                dep_graph
                    .dependencies
                    .insert(adt_rtyp.get(), adt_rtyp.dtyp_dependencies(&dep_graph.all_adts)?);
            }
        }

        dep_graph.init_statically_simplifiable();
        dep_graph.init_dynamically_simplifiable();

        Ok(dep_graph)
    }

    fn init_statically_simplifiable(&mut self) {
        let mut simplifiable: BTreeSet<&'depgraph RTyp> = BTreeSet::new();
        let mut changed = true;

        while changed {
            changed = false;
            for (&typ, deps) in &self.dependencies {
                if !simplifiable.contains(typ) {
                    let all_deps_resolved = deps
                        .iter()
                        .all(|dep| matches!(dep, RTyp::Int) || simplifiable.contains(dep));
                    if all_deps_resolved {
                        simplifiable.insert(typ);
                        self.statically_simplifiable.push(typ);
                        changed = true;
                    }
                }
            }
        }
    }

    pub fn init_dynamically_simplifiable(&mut self) {
        let is_self_recursive = |start: &'depgraph RTyp| -> bool {
            let mut visited = BTreeSet::new();
            let mut stack = vec![start];
            while let Some(typ) = stack.pop() {
                for dep_set in self.dependencies.get(typ).iter() {
                    for dep in dep_set.iter() {
                        if visited.insert(*dep) {
                            stack.push(dep);
                        }
                        if *dep == start {
                            log!("{dep} == {start}");
                            return true;
                        }
                    }
                }
            }
            false
        };

        let eligible: BTreeSet<_> = self
            .dependencies
            .keys()
            .filter(|t| !(is_self_recursive(t) || self.statically_simplifiable.contains(t)))
            .collect();

        let mut done = BTreeSet::new();
        let mut changed = true;
        while changed {
            changed = false;
            for typ in eligible.iter() {
                if !done.contains(typ)
                    && self.dependencies[*typ]
                        .iter()
                        .all(|dep| eligible.contains(dep) || !done.contains(&dep))
                {
                    done.insert(typ);
                    self.dynamically_simplifiable.push(typ);
                    changed = true;
                }
            }
        }
    }

    /// Returns the approximation degree required by the corresponding element in
    /// `self.statically_simplifiable`
    pub fn get_appoximation_degrees(&self,) -> Vec<usize> {
        let mut approximations = Vec::new();
        for typ in self.statically_simplifiable.iter() {
            let (adt_rdtyp, _) = typ.dtyp_inspect().unwrap();
            let n_news = (adt_rdtyp.news.len() as f64).log2().ceil() as usize;
            approximations.push(n_news + typ.get_approximation_degree(&self.all_adts));
        }
        approximations
    }
}

impl<'a> std::fmt::Display for ADTDependencyGraph<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "digraph G {{\n",)?;
        for (node, neighbors) in self.dependencies.iter() {
            let color = if self.statically_simplifiable.contains(node) {
                " [color=red]"
            } else if self.dynamically_simplifiable.contains(node) {
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
