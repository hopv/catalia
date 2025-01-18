//! preprocess [Kostyukov+ PLDI21]
//!
//!  - remove all the selectors and testers
//!    - by introducing additional temporary variables
//!  - replace dis-equality on data types with true (temporary solution)
//!     - better solution: introduce a new predicate that expresses the dis-equality on each data type,
//!       which is introduced by Kostyukov et al.
//!
use super::chc::{self, *};
use crate::common::*;
use crate::info::VarInfo;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Polarity {
    Pos,
    Neg,
}

impl Polarity {
    fn pos() -> Self {
        Polarity::Pos
    }
    fn flip(&self) -> Self {
        match self {
            Polarity::Pos => Polarity::Neg,
            Polarity::Neg => Polarity::Pos,
        }
    }
}

/// Remove dis-equality on data types and replace equality with AdtEql
fn handle_equality(t: &term::Term, pol: Polarity) -> Term {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
        RTerm::CArray { typ, term, .. } => {
            let term = handle_equality(term, pol);
            term::cst_array(typ.clone(), term)
        }
        RTerm::App { op, args, .. } => {
            let pol = match op {
                Op::Not => pol.flip(),
                _ => pol,
            };
            let args: Vec<_> = args.iter().map(|t| handle_equality(t, pol)).collect();
            assert!(args.len() > 0);
            let arg = &args[0];
            match op {
                Op::Eql if arg.typ().is_dtyp() => {
                    // replace this to AdtEql if pol = Pos
                    if pol == Polarity::Pos {
                        term::adteq(args[0].clone(), args[1].clone())
                    } else {
                        warn!("Dis-equality on data types is approximated as true");
                        term::bool(false)
                    }
                }
                Op::AdtEql => panic!("AdtEql should not appear in the preprocessed term"),
                _ => term::app(op.clone(), args),
            }
        }
        RTerm::DTypNew {
            typ, name, args, ..
        } => {
            let args = args.iter().map(|t| handle_equality(t, pol)).collect();
            term::dtyp_new(typ.clone(), name, args)
        }
        RTerm::DTypSlc { .. } => todo!(),
        RTerm::DTypTst { .. } => todo!(),
        RTerm::Fun { name, args, .. } => {
            let args = args.iter().map(|t| handle_equality(t, pol)).collect();
            term::fun(name.clone(), args)
        }
    }
}

fn slcs_to_args(
    prms: &dtyp::TPrmMap<Typ>,
    slcs: &[(String, dtyp::PartialTyp)],
    varinfos: &mut VarInfos,
) -> Vec<(VarIdx, Typ)> {
    let mut args = Vec::new();
    // return the index of the selected variable
    for (_, sel_ty) in slcs.iter() {
        let new_var = varinfos.next_index();
        let sel_ty = sel_ty.to_type(Some(prms)).unwrap();
        let new_var_info = VarInfo::new(format!("tmp_{}", new_var), sel_ty.clone(), new_var);
        varinfos.push(new_var_info);
        args.push((new_var, sel_ty));
    }
    args
}

fn find_other_selectors<'a>(dty: &'a DTyp, selector: &str) -> Res<(&'a String, &'a dtyp::CArgs)> {
    for (constr_name, slcs) in dty.news.iter() {
        for (sel, _) in slcs.iter() {
            if sel == selector {
                return Ok((constr_name, slcs));
            }
        }
    }
    bail!("Selector {} is not found in the type {}", selector, dty)
}

/// Remove all the selectors and testers
fn remove_slc_tst_inner(
    t: &Term,
    varinfos: &mut VarInfos,
    cache: &mut HashMap<Term, (String, Vec<(VarIdx, Typ)>)>,
) -> Term {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
        RTerm::CArray { typ, term, .. } => {
            let term = remove_slc_tst_inner(term, varinfos, cache);
            term::cst_array(typ.clone(), term)
        }
        RTerm::App { op, args, .. } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, cache))
                .collect();
            term::app(op.clone(), args)
        }
        RTerm::DTypNew {
            typ, name, args, ..
        } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, cache))
                .collect();
            term::dtyp_new(typ.clone(), name, args)
        }
        RTerm::DTypSlc { name, term, .. } => {
            let term = remove_slc_tst_inner(term, varinfos, cache);
            let term_typ = term.typ();
            let (dty, prms) = term_typ.dtyp_inspect().unwrap();
            let (constructor_name, slcs) = find_other_selectors(dty, name).unwrap();
            let args = match cache.get(&term) {
                Some(args) => args,
                None => {
                    let args = slcs_to_args(prms, slcs, varinfos);
                    cache.insert(term.clone(), (constructor_name.clone(), args));
                    cache.get(&term).unwrap()
                }
            };

            let idx = slcs
                .iter()
                .enumerate()
                .find_map(|(idx, (sel, _))| if sel == name { Some(idx) } else { None })
                .unwrap();
            let target_arg = args.1[idx].clone();

            term::var(target_arg.0, target_arg.1)
        }
        RTerm::DTypTst { name, term, .. } => {
            let term = remove_slc_tst_inner(term, varinfos, cache);
            let term_typ = term.typ();
            let (ty, prms) = term_typ.dtyp_inspect().unwrap();
            let slcs = ty.selectors_of(name).unwrap();
            let args = slcs_to_args(prms, slcs, varinfos)
                .into_iter()
                .map(|(v, t)| term::var(v, t))
                .collect();
            let lhs = term::dtyp_new(term.typ(), name, args);
            let eq = term::eq(lhs.clone(), term.clone());
            eq
        }
        RTerm::Fun { name, args, .. } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, cache))
                .collect();
            term::fun(name.clone(), args)
        }
    }
}

fn remove_slc_tst(c: &mut AbsClause) {
    let mut cache = HashMap::new();
    let t = remove_slc_tst_inner(&c.lhs_term, &mut c.vars, &mut cache);
    for p in c.lhs_preds.iter_mut() {
        let args: Vec<_> = p
            .args
            .iter()
            .map(|t| remove_slc_tst_inner(t, &mut c.vars, &mut cache))
            .collect();
        let args: VarMap<_> = args.into();
        p.args = args.into();
    }
    let mut constrs: Vec<_> = cache
        .into_iter()
        .map(|(term, (constructor_name, args))| {
            let args = args.into_iter().map(|(v, t)| term::var(v, t)).collect();
            let lhs = term::dtyp_new(term.typ(), constructor_name, args);
            term::eq(lhs.clone(), term.clone())
        })
        .collect();
    constrs.push(t);
    c.lhs_term = term::and(constrs);
}

fn handle_clause(c: &mut AbsClause) {
    remove_slc_tst(c);
    c.lhs_term = handle_equality(&c.lhs_term, Polarity::pos());
}

/*
pub struct AbsClause {
    pub vars: VarInfos,
    pub rhs: Option<(PrdIdx, Vec<VarIdx>)>,
    pub lhs_preds: Vec<PredApp>,
    pub lhs_term: Term,
}
     */
#[test]
fn test_remove_slc_tst() {
    use crate::info::VarInfo;
    let preds = Preds::new();
    let p = preds.next_index();
    let rhs = None;

    // List<T> = nil | insert (head T) (tail List<T>)
    dtyp::create_list_dtyp();

    // ilist
    let ilist = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());

    // P(tail l, head l) /\ is-cons l /\ z = head l => false
    let mut vars = VarInfos::new();
    let l = vars.next_index();
    let li = VarInfo::new("l", ilist.clone(), l);
    vars.push(li);
    let z = vars.next_index();
    let zi = VarInfo::new("z", typ::int(), z);
    vars.push(zi);

    let arg1 = term::dtyp_slc(ilist.clone(), "tail", term::var(l, ilist.clone()));
    let arg2 = term::dtyp_slc(typ::int(), "head", term::var(l, ilist.clone()));
    let args: VarMap<_> = vec![arg1, arg2].into();
    let p = super::chc::PredApp {
        pred: p,
        args: args.into(),
    };

    let term1 = term::dtyp_tst("insert", term::var(l, ilist.clone()));
    let term2 = term::eq(
        term::var(z, typ::int()),
        term::dtyp_slc(typ::int(), "head", term::var(l, ilist.clone())),
    );
    let lhs_term = term::and(vec![term1, term2]);
    let mut c = AbsClause {
        vars,
        rhs,
        lhs_preds: vec![p],
        lhs_term,
    };
    println!("clause: {}", c);
    remove_slc_tst(&mut c);
    println!("transformed: {}", c);

    // check if all the selectors and testers are removed from lhs_term and lhs_preds
    fn check_no_slc_tst(t: &Term) {
        match t.get() {
            RTerm::Var(_, _) | RTerm::Cst(_) => {}
            RTerm::CArray { term, .. } => check_no_slc_tst(term),
            RTerm::App { args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
            RTerm::DTypNew { args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
            RTerm::DTypSlc { .. } => panic!("DTypSlc should not appear"),
            RTerm::DTypTst { .. } => panic!("DTypTst should not appear"),
            RTerm::Fun { args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
        }
    }
    for p in c.lhs_preds.iter() {
        for arg in p.args.iter() {
            check_no_slc_tst(arg);
        }
    }
    check_no_slc_tst(&c.lhs_term);
}

fn remove_neg_src_tst<'a>(instance: &mut AbsInstance<'a>) {
    for c in instance.clauses.iter_mut() {
        handle_clause(c);
    }
}

fn check_not_boolean_use_inner(t: &Term) -> bool {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => false,
        RTerm::App { op, args, .. } if *op == Op::Not => {
            debug_assert_eq!(args.len(), 1);
            let a = &args[0];
            match a.get() {
                RTerm::App { op, .. } if *op == Op::Eql => false,
                _ => true,
            }
        }
        RTerm::App { args, .. } => args.iter().any(|x| check_not_boolean_use_inner(x)),
        RTerm::CArray { term, .. } => check_not_boolean_use_inner(term),
        RTerm::DTypSlc { .. } => panic!("DTypSlc should not appear"),
        RTerm::DTypTst { .. } => panic!("DTypTst should not appear"),
        RTerm::DTypNew { args, .. } => args.iter().any(|x| check_not_boolean_use_inner(x)),
        RTerm::Fun { args, .. } => args.iter().any(|x| check_not_boolean_use_inner(x)),
    }
}
/// Checks if the given instance require to apply `remove_not_bool` pass
///
/// If there is a use of (not X), returns true
fn check_not_boolean_use<'a>(instance: &AbsInstance<'a>) -> bool {
    instance.clauses.iter().any(|x| {
        check_not_boolean_use_inner(&x.lhs_term)
            || x.lhs_preds
                .iter()
                .any(|x| x.args.iter().any(|x| check_not_boolean_use_inner(x)))
    })
}

#[cfg(test)]
fn gen_term_for_test() -> (term::Term, term::Term) {
    /*
    (and (= (insert 1 D) nil)
     (not G)
     (= v_7 false))
     */
    // List<T> = nil | insert (head T) (tail List<T>)
    dtyp::create_list_dtyp();

    // ilist
    let ilist = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());

    let mut vars = VarInfos::new();
    let c = VarInfo::new("C", ilist.clone(), vars.next_index());
    let c_idx = c.idx;
    vars.push(c);
    let g = VarInfo::new("G", typ::bool(), vars.next_index());
    let g_idx = g.idx;
    vars.push(g);
    let v7 = VarInfo::new("v_7", typ::bool(), vars.next_index());
    let v7_idx = v7.idx;
    vars.push(v7);

    // (= (insert C) nil)
    let arg1 = term::dtyp_new(ilist.clone(), "nil", vec![]);
    let arg2 = term::dtyp_new(
        ilist.clone(),
        "insert",
        vec![term::int(1), term::var(c_idx, ilist.clone())],
    );
    let t1 = term::eq(arg2, arg1);
    // (not G)
    let t2 = term::app(Op::Not, vec![term::var(g_idx, typ::bool())]);
    // (= v_7 false)
    let t3 = term::eq(term::var(v7_idx, typ::bool()), term::bool(false));
    let lhs_term = term::and(vec![t1.clone(), t2, t3]);
    (lhs_term, t1)
}

#[test]
fn test_check_not_boolean_use() {
    let (pos, neg) = gen_term_for_test();

    assert!(check_not_boolean_use_inner(&pos));
    assert!(!check_not_boolean_use_inner(&neg));
}

fn introduce_dual<'a>(instance: &mut AbsInstance<'a>) -> Vec<HashMap<VarIdx, VarIdx>> {
    let mut dual_var_map = Vec::new();
    for c in instance.clauses.iter_mut() {
        let mut var_map = HashMap::new();
        for v in c.vars.iter() {
            if v.typ.is_bool() {
                var_map.insert(v.idx, c.vars.next_index() + var_map.len());
            }
        }
        for (k, v) in var_map.iter() {
            let name = format!("dual-{}", k);
            let info = VarInfo::new(name, typ::bool(), *v);
            c.vars.push(info)
        }
        dual_var_map.push(var_map)
    }
    for p in instance.preds.iter_mut() {
        let mut new_sig = VarMap::new();
        for x in p.sig.iter() {
            new_sig.push(x.clone());
            if x.is_bool() {
                new_sig.push(x.clone())
            }
        }
        p.sig = new_sig.into();
    }
    dual_var_map
}

fn remove_not_bool_var<'a>(instance: &mut AbsInstance<'a>, varmap: &Vec<HashMap<VarIdx, VarIdx>>) {
    assert_eq!(varmap.len(), instance.clauses.len());
    // Takes a negation of a given term using mapping of dual variables
    fn neg(t: &term::Term, env: &HashMap<VarIdx, VarIdx>) -> term::Term {
        match t.get() {
            RTerm::Var(typ, v) => {
                let dual = env.get(v).unwrap();
                term::var(*dual, typ.clone())
            }
            RTerm::Cst(_) => term::app(Op::Not, vec![t.clone()]),
            RTerm::CArray { typ, term, .. } => {
                let term = neg(term, env);
                term::cst_array(typ.clone(), term)
            }
            RTerm::App { op, args, .. } => match op {
                Op::Not => {
                    assert!(args.len() > 0 && args[0].typ().is_bool());
                    debug_assert!(args.len() == 1);
                    let arg = &args[0];
                    arg.clone()
                }
                Op::And => {
                    debug_assert!(args.len() > 0 && args[0].typ().is_bool());
                    let args = args.iter().map(|t| neg(t, env)).collect();
                    term::app(Op::Or, args)
                }
                Op::Or => {
                    debug_assert!(args.len() > 0 && args[0].typ().is_bool());
                    let args = args.iter().map(|t| neg(t, env)).collect();
                    term::app(Op::And, args)
                }
                Op::Eql => term::app(Op::Not, vec![term::app(Op::Eql, args.clone())]),
                Op::Impl => todo!(),
                Op::AdtEql => todo!(),
                Op::Ite => todo!(),
                Op::Distinct => todo!(),
                Op::Add
                | Op::Sub
                | Op::Mul
                | Op::CMul
                | Op::IDiv
                | Op::Div
                | Op::Rem
                | Op::Mod
                | Op::Gt
                | Op::Ge
                | Op::Le
                | Op::Lt
                | Op::ToInt
                | Op::ToReal
                | Op::Store
                | Op::Select => panic!("program error: unreachable expression for negation: {}", t),
            },
            RTerm::DTypNew { .. } => {
                panic!("program error: type")
            }
            RTerm::DTypSlc { .. } | RTerm::DTypTst { .. } => {
                panic!("Assumption: slc&testers are already removed")
            }
            RTerm::Fun { name, args, .. } => {
                let args = args.iter().map(|t| neg(t, env)).collect();
                let t = term::fun(name.clone(), args);
                term::app(Op::Not, vec![t])
            }
        }
    }

    // remove (not t) where t is a boolean term
    // for each occurrence, neg(t) is applied
    fn go(t: &term::Term, env: &HashMap<VarIdx, VarIdx>) -> term::Term {
        match t.get() {
            RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
            RTerm::CArray { typ, term, .. } => {
                let term = go(term, env);
                term::cst_array(typ.clone(), term)
            }
            RTerm::App { op, args, .. } => {
                let args: Vec<_> = args.iter().map(|t| go(t, env)).collect();
                if *op == Op::Not {
                    assert!(args.len() == 1);
                    if args[0].typ().is_bool() {
                        neg(&args[0], env)
                    } else {
                        term::app(op.clone(), args)
                    }
                } else {
                    term::app(op.clone(), args)
                }
            }
            RTerm::DTypNew {
                typ, name, args, ..
            } => {
                let args = args.iter().map(|t| go(t, env)).collect();
                term::dtyp_new(typ.clone(), name, args)
            }
            RTerm::DTypSlc {
                typ, name, term, ..
            } => {
                let term = go(term, env);
                term::dtyp_slc(typ.clone(), name, term)
            }
            RTerm::DTypTst { name, term, .. } => {
                let term = go(term, env);
                term::dtyp_tst(name, term)
            }
            RTerm::Fun { name, args, .. } => {
                let args = args.iter().map(|t| go(t, env)).collect();
                term::fun(name.clone(), args)
            }
        }
    }

    let clauses: Vec<_> = instance
        .clauses
        .iter()
        .zip(varmap.iter())
        .map(|(c, env)| {
            let lhs_term = go(&c.lhs_term, env);
            let lhs_preds = c
                .lhs_preds
                .iter()
                .map(|lhs_pred| {
                    let mut args = Vec::new();
                    for term in lhs_pred.args.iter() {
                        args.push(go(term, env));
                        // all the term of bool is passed with its dual
                        if term.typ().is_bool() {
                            args.push(neg(term, env));
                        }
                    }
                    let args: VarMap<_> = args.into();
                    chc::PredApp {
                        pred: lhs_pred.pred,
                        args: args.into(),
                    }
                })
                .collect();
            let rhs = c.rhs.as_ref().map(|(p, old_args)| {
                let mut args = Vec::new();
                for arg in old_args.iter() {
                    args.push(*arg);
                    match env.get(arg) {
                        Some(dual) => {
                            args.push(*dual);
                        }
                        None => {}
                    }
                }

                (*p, args)
            });
            AbsClause {
                lhs_preds,
                lhs_term,
                rhs,
                vars: c.vars.clone(),
            }
        })
        .collect();
    instance.clauses = clauses;
}

fn remove_not_bool<'a>(instance: &mut AbsInstance<'a>) {
    if !check_not_boolean_use(instance) {
        log_info!("(not X) does not appear in the instance");
        return;
    }
    let varmap = introduce_dual(instance);
    remove_not_bool_var(instance, &varmap);
}

#[test]
fn test_remove_not_bool() {}

fn inline_adts<'a>(instance: &mut AbsInstance<'a>) {
    for (name, dt) in dtyp::get_all().iter() {}
    unimplemented!()
}

pub fn work<'a>(instance: &mut AbsInstance<'a>) {
    remove_neg_src_tst(instance);
    remove_not_bool(instance);
}
