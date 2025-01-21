//! Inline tuple types
//!
//! We inline tuple of basic types.
//! If the tuple appears in a dtype, then we reconstruct the tuple

use crate::common::*;
use crate::info;
use crate::instance::*;
use crate::preproc::RedStrat;

/// Calls `PredInstance::simplify_all`.
pub struct InlineADT;

struct Trans<'a, 'b> {
    instance: &'a mut PreInstance<'b>,
    typ2tuple: HashMap<DTyp, Vec<Typ>>,
}

/// Check if the given type is a tuple.
///
/// Currently, very conservative. A tuple is composed of multiple items of base types.
fn tuple_opt(typ: &DTyp) -> Option<Vec<Typ>> {
    let mut itr = typ.news.iter();
    let types = if let Some((_, t)) = itr.next() {
        if itr.next().is_some() {
            return None;
        }
        t
    } else {
        return None;
    };
    let mut vec = Vec::with_capacity(types.len());
    for (_, t) in types.iter() {
        match t {
            dtyp::PartialTyp::Typ(t) if t.is_bool() || t.is_arith() => vec.push(t.clone()),
            _ => return None,
        }
    }
    Some(vec)
}

impl<'a, 'b> Trans<'a, 'b> {
    fn new(instance: &'a mut PreInstance<'b>) -> Self {
        let mut typ2tup = HashMap::new(); // O(n) is OK
        let mut n_types = 0; // count number of types for generating unique names later
        for (name, typ) in dtyp::get_all().iter() {
            n_types += 1;
            match tuple_opt(typ) {
                Some(types) => {
                    println!("name: {}", name);
                    println!("typ: {}", typ);
                    println!("types: {:?}", types);
                    typ2tup.insert(typ.clone(), types);
                }
                None => {}
            }
        }
        Self {
            instance,
            typ2tuple: typ2tup,
        }
    }
    fn get_tuple(&self, typ: &Typ) -> Option<&Vec<Typ>> {
        match typ.get() {
            typ::RTyp::DTyp { dtyp, prms } => match self.typ2tuple.get(dtyp) {
                Some(ts) => Some(ts),
                None => None,
            },
            _ => None,
        }
    }
    fn work_on(&self, c: &Clause) -> Clause {
        // 2. if a variable is a tuple, then introduce new variables
        // 3. replace the tuple access with the new variables
        // 3.1 constructor is removed and inlined
        // 3.2 tester is always true
        // 3.3 accessor is replaced with the corresponding variable
        // 3.4 if a variable appears as an argument of type tuple for a function, then we reconstruct it (e.g., a constructor for another dtype).
        let mut new_vars = VarMap::new();
        for v in c.vars() {
            match self.get_tuple(&v.typ) {
                Some(ts) => {
                    for (idx, t) in ts.iter().enumerate() {
                        let info = info::VarInfo::new(
                            format!("{}-{}", v.name, idx),
                            t.clone(),
                            new_vars.next_index(),
                        );
                        new_vars.push(info);
                    }
                }
                None => {
                    new_vars.push(v.clone());
                }
            }
        }
        unimplemented!()
    }
    fn expand_tuple(&mut self) {
        // 0. redefine each predicate
        let mut new_preds = VarMap::new();
        for p in self.instance.preds() {
            let mut new_sigs = VarMap::new();
            for s in &p.sig {
                match self.get_tuple(s) {
                    Some(ts) => {
                        for t in ts.iter() {
                            new_sigs.push(t.clone());
                        }
                    }
                    None => {
                        new_sigs.push(s.clone());
                    }
                }
            }
            let p = crate::info::Pred::new(p.name.clone(), p.idx, new_sigs);
            new_preds.push(p);
        }
        // 1. iter all the clauses
        for c in self.instance.clauses() {
            let c = self.work_on(c);
        }
        self.instance.rm_args(to_keep)
    }
}

#[test]
fn test_is_tuple() {
    // gen list
    // check list is tuple -> no
}

impl RedStrat for InlineADT {
    fn name(&self) -> &'static str {
        "inline_adt"
    }

    fn new(_: &Instance) -> Self {
        InlineADT
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        // expand the tuple
        let mut trans = Trans::new(instance);
        trans.expand_tuple();
        unimplemented!()
    }
}
