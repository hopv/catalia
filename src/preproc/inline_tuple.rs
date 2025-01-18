//! Inline tuple types
//!
//! We inline tuple of basic types.
//! If the tuple appears in a dtype, then we reconstruct the tuple

use crate::common::*;
use crate::instance::*;
use crate::preproc::RedStrat;

/// Calls `PredInstance::simplify_all`.
pub struct InlineADT;

/// Check if the given type is a tuple.
///
/// Currently, very conservative. A tuple is composed of multiple items of base types.
fn tuple_opt(typ: &DTyp) -> Option<Vec<Typ>> {
    let mut itr = typ.news.iter();
    let types = if let Some((name, t)) = itr.next() {
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

fn expand_tuple(instance: &mut PreInstance, typ2tuple: &HashMap<Typ, Vec<Typ>>) {
    // 0. redefine each predicate
    // 1. iter all the clauses
    // 2. if a variable is a tuple, then introduce new variables
    // 3. replace the tuple access with the new variables
    // 3.1 constructor is removed and inlined
    // 3.2 tester is always true
    // 3.3 accessor is replaced with the corresponding variable
    // 3.4 if a variable appears as an argument of type tuple for a function, then we reconstruct it (e.g., a constructor for another dtype).
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
        let mut typ2tup = HashMap::new(); // O(n) is OK
        let mut n_types = 0; // count number of types for generating unique names later
        for (name, typ) in dtyp::get_all().iter() {
            n_types += 1;
            match tuple_opt(typ) {
                Some(types) => {
                    println!("name: {}", name);
                    println!("typ: {}", typ);
                    println!("types: {:?}", types);
                    typ2tup.insert(typ, types);
                }
                None => {}
            }
        }

        // expand the tuple
        unimplemented!()
    }
}
