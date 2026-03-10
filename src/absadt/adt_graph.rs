use petgraph::{
    dot::Dot,
    graph::{DiGraph, NodeIndex},
};
use std::collections::{BTreeSet, HashMap};

use crate::conf;
use crate::dtyp;
use crate::dtyp::PartialTyp;
use crate::errors::{Error, ErrorKind, Res};
use crate::term::typ::RTyp;

pub struct ADTDependencyGraph {
    graph: DiGraph<String, ()>,
    name_to_idx_map: HashMap<String, NodeIndex>,
    idx_to_name_map: HashMap<NodeIndex, String>,
}

impl ADTDependencyGraph {
    pub fn new() -> Res<Self> {
        let adts = dtyp::get_all();
        let mut dep_graph = Self {
            graph: DiGraph::<String, ()>::new(),
            name_to_idx_map: HashMap::<String, NodeIndex>::new(),
            idx_to_name_map: HashMap::<NodeIndex, String>::new(),
        };
        if adts.is_empty() {
            return Ok(dep_graph);
        }
        for (adt_name, adt_typ) in adts.iter() {
            log_debug!("Detected adt {adt_name}");
            dep_graph.safe_add_node(adt_name);
            for (_, constr_args) in adt_typ.news.iter() {
                for (_, arg_partial_typ) in constr_args.iter() {
                    dep_graph.add_arguments(adt_name, arg_partial_typ)?;
                }
            }
        }
        Ok(dep_graph)
    }

    pub fn get_simplifiable_adt(&mut self) -> Res<BTreeSet<String>> {
        let mut any_change = true;
        let mut simplifiable_adt = BTreeSet::new();
        // If any_change is false then we reached a fix-point,we do not need
        // to proceed any further
        while any_change {
            any_change = false;
            for node_idx in self.graph.node_indices() {
                let node_name = self.idx_to_name_map.get(&node_idx).unwrap();
                if !simplifiable_adt.contains(node_name)
                    && self.can_be_simplified(node_idx, |neg_node_idx| {
                        simplifiable_adt.contains(self.idx_to_name_map.get(&neg_node_idx).unwrap())
                    })
                {
                    simplifiable_adt
                        .insert(self.idx_to_name_map.get(&node_idx).unwrap().to_string());
                    any_change = true;
                }
            }
        }
        Ok(simplifiable_adt)
    }

    fn can_be_simplified<F>(&self, node_idx: NodeIndex, pred: F) -> bool
    where
        F: Fn(NodeIndex) -> bool,
    {
        self.graph.edges(node_idx).count() == 0 || self.graph.neighbors(node_idx).all(pred)
    }

    fn add_arguments(&mut self, starting_typ: &str, arg: &PartialTyp) -> Res<()> {
        match arg {
            PartialTyp::DTyp(dep_name, _, partial_params) => {
                // constructorArgument: anotherADT
                self.safe_add_node(dep_name);
                self.safe_add_edge(starting_typ, dep_name)?;
                // Recursive call in the args, we are only interested in the
                // ADT case
                for partial_typ_arg in partial_params.iter() {
                    if matches!(partial_typ_arg, PartialTyp::DTyp(_, _, _)) {
                        let arg_name = partial_typ_arg.get_adt_name().unwrap();
                        let arg_params = partial_typ_arg.get_adt_args().unwrap();
                        for arg_param in arg_params.iter() {
                            self.add_arguments(&arg_name, arg_param)?;
                        }
                    }
                }
            }
            PartialTyp::Typ(concrete_typ) => {
                // constructorArgument: Int
                // Since an ADT is defined over ADTs or integer the only
                // primitive type supported is Int.
                // For the sake of simplicity it is better to avoid adding the
                // Int node.
                match concrete_typ.get() {
                    RTyp::Int => {}
                    _ => {
                        return Err(Error::from_kind(ErrorKind::Msg(format!(
                            "I should only have ADT and Int in argument, found {concrete_typ}"
                        ))))
                    }
                }
            }
            PartialTyp::Param(_) => {
                // constructorArgument: T
                // Here we should do nothing, we are analysing a generic
                // hopefully we will eventually see a concrete instance of this
                // argument
            }
            _ => {
                return Err(Error::from_kind(ErrorKind::Msg(format!(
                    "I cannot have any other thing that DTyp or partial types, found {arg}"
                ))))
            }
        }
        Ok(())
    }

    fn safe_add_node(&mut self, new_node: &str) {
        if self.name_to_idx_map.contains_key(new_node) {
            return;
        }
        let idx = self.graph.add_node(new_node.to_string());
        self.idx_to_name_map.insert(idx, new_node.to_string());
        self.name_to_idx_map.insert(new_node.to_string(), idx);
    }

    fn safe_add_edge(&mut self, start_node: &str, end_node: &str) -> Res<()> {
        if !self.name_to_idx_map.contains_key(start_node) {
            return Err(Error::from_kind(ErrorKind::Msg(format!(
                "Type {start_node} not present"
            ))));
        }
        if !self.name_to_idx_map.contains_key(end_node) {
            return Err(Error::from_kind(ErrorKind::Msg(format!(
                "Type {end_node} not present"
            ))));
        }
        let start_idx = self.name_to_idx_map.get(start_node).unwrap();
        let end_idx = self.name_to_idx_map.get(end_node).unwrap();
        if self.graph.find_edge(*start_idx, *end_idx).is_some() {
            return Ok(());
        }
        self.graph.add_edge(*start_idx, *end_idx, ());
        Ok(())
    }
}

impl std::fmt::Display for ADTDependencyGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{:?}",
            Dot::with_config(&self.graph, &[petgraph::dot::Config::EdgeNoLabel])
        )
    }
}
