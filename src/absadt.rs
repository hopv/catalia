//! Overall Design of AbsADT
//!
//! ## Data Structure
//!
//! - Enc: enc
//!   - The encoding is a map from ADT terms to integer expressions.
//! - Model: model
//!   - A model of SMT modulo ADT
//!
//! ## Main Algorithm
//! 1. Solve the CHC over LIA using Spacer with the current approximation `enc`.
//!   - If sat, then the original problem is also sat, and the algorithm
//!     terminates.
//! 2. From the counterexample, extract a non-recursive counterexample C (SMT
//! constraints over ADT but not with RDF) for the original CHC, and add to
//! cexs: Vec<Constraint>.
//!   - This forms an underapproximation original CHC.
//!   - If C is sat → the original problem is unsatisfiable.
//! 3. Apply the current encode to the extracted constraints and obtain the
//! resulting counterexample model (over ADT) by a SMT solver. Then add to
//! pseudo_cexs: Vec<Model>.
//! 4. Generate a new approximation enc’ that can refute all cexs: (GenEnc).
//!   - If C is sat with enc’, go back to step 2.
//!   - If C is unsat with enc’, update enc to enc’ and return to step 1.
//!
//! ## GenEnc
//!
//! - Input: pseudo_cexs
//! - Output: new encoding enc’
//!
//! ### Algorithm:
//!
//! 1. Find a good abstraction from a set of templates
//! 2. TBD
//!
//!
//! ## Some Assumptions
//! - set of ADT does not change from start to end during `work`
//!   - they are defined as the global hashconsed objects
use chc::AbsInstance;
use enc::Encoder;

use crate::common::{smt::FullParser as Parser, *};
use crate::info::{Pred, VarInfo};

use crate::unsat_core::UnsatRes;

mod chc;
mod chc_solver;
mod enc;
mod hyper_res;
mod learn;
mod preproc;

pub struct AbsConf<'original> {
    pub cexs: Vec<chc::CEX>,
    pub instance: AbsInstance<'original>,
    pub solver: Solver<Parser>,
    pub encs: BTreeMap<Typ, Encoder>,
    epoch: usize,
    profiler: &'original Profiler,
}

fn initialize_dtyp(typ: Typ, encs: &mut BTreeMap<Typ, Encoder>) -> Res<()> {
    let (ty, _) = typ.dtyp_inspect().unwrap();
    let mut approxs = BTreeMap::new();
    for (constr_name, sels) in ty.news.iter() {
        let mut args = VarInfos::new();

        for (sel, _) in sels.iter() {
            let info = VarInfo::new(sel, typ::int(), args.next_index());
            args.push(info);
        }
        let terms = vec![term::int_zero()];
        let approx = enc::Approx { args, terms };
        approxs.insert(constr_name.to_string(), approx);
    }
    let typ = typ.clone();
    let n_params = 1;
    let enc = enc::Enc {
        typ: typ.clone(),
        n_params,
        approxs,
    };
    let r = encs.insert(typ, enc);
    debug_assert!(r.is_none());
    Ok(())
}

fn initialize_encs_for_term(t: &Term, encs: &mut BTreeMap<Typ, Encoder>) -> Res<()> {
    let typ = t.typ();
    if typ.is_dtyp() && !encs.contains_key(&typ) {
        initialize_dtyp(typ, encs)?;
    }
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => (),
        RTerm::CArray { term, .. } | RTerm::DTypSlc { term, .. } | RTerm::DTypTst { term, .. } => {
            initialize_encs_for_term(term, encs)?;
        }
        RTerm::App { args, .. } | RTerm::DTypNew { args, .. } | RTerm::Fun { args, .. } => {
            for arg in args.iter() {
                initialize_encs_for_term(arg, encs)?;
            }
        }
    }
    Ok(())
}

impl<'original> AbsConf<'original> {
    fn new(original: &'original Instance, profiler: &'original Profiler) -> Res<Self> {
        let mut instance = AbsInstance::new(original)?;
        preproc::work(&mut instance);
        let cexs = Vec::new();
        let solver = conf.solver.spawn("absadt", Parser, original)?;
        let encs = BTreeMap::new();

        Ok(AbsConf {
            instance,
            cexs,
            solver,
            encs,
            epoch: 0,
            profiler,
        })
    }

    fn initialize_encs(&mut self) -> Res<()> {
        let instance = &self.instance;
        for c in instance.clauses.iter() {
            for v in c.vars.iter() {
                if v.typ.is_dtyp() && !self.encs.contains_key(&v.typ) {
                    initialize_dtyp(v.typ.clone(), &mut self.encs)?;
                }
            }
            for p in c.lhs_preds.iter() {
                for t in p.args.iter() {
                    initialize_encs_for_term(t, &mut self.encs)?;
                }
            }
            initialize_encs_for_term(&c.lhs_term, &mut self.encs)?;
        }
        Ok(())
    }

    fn log_epoch(&self, e: &AbsInstance) -> Res<()> {
        let mut encoder_s = "[encoders]\n".to_string();
        for (tag, e) in self.encs.iter() {
            encoder_s += &format!("[{}]", tag);
            encoder_s += &e.to_string();
        }
        let mut file = self
            .instance
            .instance_log_files(format!("encoded-epoch-{}", self.epoch))?;
        e.dump_as_smt2(&mut file, &encoder_s, false)?;
        Ok(())
    }

    fn refine_encs(&mut self) -> Res<()> {
        // TODO: discard unnecessary encoders
        Ok(())
    }

    fn get_combined_cex(&self) -> chc::CEX {
        let mut varmap = VarMap::new();
        let mut form = Vec::new();
        for cex in self.cexs.iter() {
            let mut subst = Vec::new();
            for v in cex.vars.iter() {
                let mut new_v = v.clone();
                new_v.idx = varmap.next_index();
                subst.push((v.idx, term::var(new_v.idx, new_v.typ.clone())));
                varmap.push(new_v);
            }
            let subst: VarHMap<_> = subst.into_iter().collect();
            let t = cex.term.subst_total(&subst).unwrap().0;
            form.push(t);
        }

        chc::CEX {
            vars: varmap,
            term: term::or(form),
        }
    }

    fn run(&mut self) -> Res<either::Either<(), ()>> {
        //self.playground()?;
        self.initialize_encs()?;
        let r = loop {
            self.epoch += 1;
            log_info!("epoch: {}", self.epoch);
            if conf.split_step {
                pause("go?", &self.profiler);
            }
            let encoded = self.encode();
            self.log_epoch(&encoded)?;
            match encoded.check_sat()? {
                either::Left(()) => {
                    break either::Left(());
                }
                either::Right(x) => {
                    let cex = self.instance.get_cex(&x);
                    log_debug!("cex: {}", cex);
                    if let Some(b) = cex.check_sat_opt(&mut self.solver)? {
                        // unsat
                        if b {
                            break either::Right(());
                        }
                    }
                    self.cexs.push(cex);
                    let cex = self.get_combined_cex();

                    log_debug!("combined_cex: {}", cex);
                    learn::work(&mut self.encs, &cex, &mut self.solver, &self.profiler)?;
                    log_info!("encs are updated");
                    for (tag, enc) in self.encs.iter() {
                        log_debug!("{}: {}", tag, enc);
                    }
                    self.refine_encs()?;
                }
            }
        };
        Ok(r)
    }
}

impl<'a> AbsConf<'a> {
    pub fn encode_clause(&self, c: &chc::AbsClause) -> chc::AbsClause {
        let ctx = enc::EncodeCtx::new(&self.encs);
        let (new_vars, introduced) = enc::tr_varinfos(&self.encs, &c.vars);
        let encode_var = |_, var| {
            let x = introduced.get(var).unwrap();
            let mut res = Vec::new();
            for y in x.iter() {
                res.push(term::var(*y.idx, y.typ.clone()));
            }
            res
        };
        let r = ctx.encode(&c.lhs_term, &encode_var);
        let lhs_term = term::and(r);
        let mut lhs_preds = Vec::with_capacity(c.lhs_preds.len());
        for lhs_app in c.lhs_preds.iter() {
            let mut new_args = VarMap::new();
            for arg in lhs_app.args.iter() {
                for encoded in ctx.encode(arg, &encode_var) {
                    new_args.push(encoded);
                }
            }
            lhs_preds.push(chc::PredApp {
                pred: lhs_app.pred,
                args: new_args.into(),
            });
        }
        let rhs = c.rhs.as_ref().map(|(pred, args)| {
            let mut new_args = Vec::new();
            for arg in args.iter() {
                if let Some(approx) = introduced.get(arg) {
                    for approx_arg in approx.iter() {
                        new_args.push(approx_arg.idx);
                    }
                } else {
                    new_args.push(arg.clone());
                }
            }
            (*pred, new_args)
        });
        let res = chc::AbsClause {
            vars: new_vars,
            lhs_term,
            lhs_preds,
            rhs,
        };
        res
    }
    fn encode_sig(&self, sig: &VarMap<Typ>) -> VarMap<Typ> {
        let mut new_sig = VarMap::new();
        for ty in sig.iter() {
            if let Some(enc) = self.encs.get(&ty) {
                enc.push_approx_typs(&mut new_sig)
            } else {
                new_sig.push(ty.clone());
            }
        }
        new_sig
    }

    fn encode_pred(&self, p: &Pred) -> Pred {
        let mut pred = p.clone();
        pred.sig = self.encode_sig(&pred.sig);
        pred
    }
    pub fn encode(&self) -> chc::AbsInstance {
        let clauses = self
            .instance
            .clauses
            .iter()
            .map(|c| self.encode_clause(c))
            .collect();
        let preds = self
            .instance
            .preds
            .iter()
            .map(|p| self.encode_pred(p))
            .collect();
        self.instance.clone_with_clauses(clauses, preds)
    }
}

/// Abstract ADT terms with integer expressions, and solve the instance by an external solver.
///
/// Returns
///
/// - a model if the instance is sat,
/// - `None` if not in `infer` mode,
/// - an [`UnsatRes`] if unsat.
///
/// Assumes the instance is **already pre-processed**.
///
/// [`UnsatRes`]: ../unsat_core/enum.UnsatRes.html (UnsatRes struct)
pub fn work(
    instance: &Arc<Instance>,
    profiler: &Profiler,
) -> Res<Option<Either<ConjCandidates, UnsatRes>>> {
    log_info!("ABS ADT is enabled");
    //playground(instance);

    let mut absconf = AbsConf::new(instance, profiler)?;
    let r = match absconf.run()? {
        either::Left(()) => either::Left(ConjCandidates::new()),
        either::Right(_) => either::Right(UnsatRes::None),
    };
    Ok(Some(r))
}
