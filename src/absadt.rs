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

mod catamorphism_parser;
mod chc;
mod chc_solver;
mod eld_cex;
mod enc;
mod hyper_res;
mod learn;
mod preproc;

/// Number of expansion depth for synthesizing the initial catamorphism
const INIT_EXPANSION_DEPTH: usize = 0;
const BMC_DEPTH: usize = 3;

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
        let mut file = instance.instance_log_files("target")?;
        instance.dump_as_smt2(&mut file, "", false)?;
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
        e.dump_as_smt2(&mut file, &encoder_s, true)?;
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

    /// Handles a counterexample
    ///
    /// `handle_cex` takes a cex and
    /// 1. checks if it is feasible.
    /// 2. if yes, returns true
    /// 3. if no, updates the encoders and returns false
    fn handle_cex(&mut self, cex: chc::CEX, return_timeout: bool) -> Res<bool> {
        log_debug!("cex: {}", cex);
        if let Some(b) = cex.check_sat_opt(&mut self.solver)? {
            // unsat
            if b {
                return Ok(true);
            }
        } else {
            if return_timeout {
                bail!("timeout");
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
        Ok(false)
    }

    /// Synthesize the initial catamorphism
    ///
    /// returns true if the instance is unsatisfiable
    fn synthesize_initial_encs(&mut self) -> Res<bool> {
        for n in (0..INIT_EXPANSION_DEPTH).rev() {
            log_info!("initializing encs: {}", n);
            let cex = self.instance.get_n_expansion(n);
            match self.handle_cex(cex, true) {
                Ok(x) => return Ok(x),
                Err(_) => (),
            }
        }
        Ok(false)
    }

    /// Bounded model checking
    ///
    /// returns true if the instance is unsatisfiable
    fn bmc(&mut self) -> Res<bool> {
        for n in (1..BMC_DEPTH).rev() {
            log_info!("trying bmc with: {}", n);
            let cex = self.instance.get_n_expansion(n);
            match cex.check_sat_opt(&mut self.solver)? {
                Some(x) => return Ok(x),
                // timeout
                None => continue,
            }
        }
        Ok(false)
    }

    /// Main CEGAR loop of Catalia
    fn run(&mut self, approximation_file: Option<&str>) -> Res<either::Either<(), ()>> {
        //self.playground()?;
        self.initialize_encs()?;
        let mut file = self.instance.instance_log_files("preprocessed")?;
        self.instance.dump_as_smt2(&mut file, "", false)?;

        if self.bmc()? {
            return Ok(either::Right(()));
        }

        // Bounded model checking
        if self.synthesize_initial_encs()? {
            return Ok(either::Right(()));
        }

        // The approximation map
        if let Some(catamorphism_str) = approximation_file {
            let parsed_approximations =  catamorphism_parser::parse_catamorphism(catamorphism_str)?;
			log_info!("Testing the input approximations");
            self.encs =
                catamorphism_parser::build_encoding_from_approx(parsed_approximations, &self.encs)?;
            let encoded = self.encode();
            self.log_epoch(&encoded)?;
            log_debug!("I produced the abstracted file");
            match encoded.check_sat()? {
                either::Left(()) => {
                    return Ok(either::Left(()));
                }
                either::Right(x) => {
                    let cex = self.instance.get_cex(&x);
                    log_debug!("Found a counter-example {cex}");
                    return Ok(either::Right(()));
                }
            }
        }

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
                    if self.handle_cex(cex, false)? {
                        break either::Right(());
                    }
                }
            }
        };
        Ok(r)
    }
}

impl<'a> AbsConf<'a> {
    pub fn encode_clause(
        &self,
        c: &chc::AbsClause
    ) -> chc::AbsClause {
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

    fn generate_approx_constraint(
        &self,
        pidx: &PrdIdx,
        typ: &Typ,
        constr_name: &str,
        enc_map: &BTreeMap<Typ, PrdIdx>,
        arg_typs: impl Iterator<Item = Typ>,
    ) -> chc::AbsClause {
        let mut lhs_preds = Vec::new();

        // P(y) <= y == constr_name(x1, ..., xn) /\ P1(x1) /\ ... /\ Pn(xn)
        //              ^^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^
        //                  head_argument              constraints

        // 1. generate arguments for the constructor
        let mut vars = VarMap::new();
        for (i, ty) in arg_typs.enumerate() {
            let idx = vars.next_index();
            let var = VarInfo::new(format!("!arg_{}", i), ty.clone(), idx);
            vars.push(var);
        }
        // 2. generate head argument
        let head_argument = term::dtyp_new(
            typ.clone(),
            constr_name,
            vars
                .iter()
                .map(|v| term::var(v.idx, v.typ.clone()))
                .collect(),
        );

        // 3. generate constraints for each dtyp argument
        for var in vars.iter() {
            match enc_map.get(&var.typ) {
                Some(p) => {
                    let args: VarMap<_> = vec![term::var(var.idx, var.typ.clone())].into();
                    let app = chc::PredApp {
                        pred: *p,
                        args: args.into(),
                    };
                    lhs_preds.push(app);
                },
                None => {
                    assert!(!var.typ.is_dtyp());
                }
            }
        }

        let res_var = VarInfo::new("res", typ.clone(), vars.next_index());
        vars.push(res_var.clone());
        let constr_for_head = term::adteq(
            term::var(vars.last().unwrap().idx, typ.clone()),
            head_argument,
        );
        let head_args = vec![res_var.idx];
        chc::AbsClause {
            vars,
            lhs_term: constr_for_head,
            lhs_preds,
            rhs: Some((*pidx, head_args)),
        }
    }

    /// Generate a predicate that represents the encoder's possible outputs
    ///
    /// P_ilist(nil) <= true
    /// P_ilist(cons(x, l)) <= P_ilist(l)
    ///
    /// This will be transformed to the following clauses after the abstraction:
    /// Ex) ilist where nil |-> 0, cons(x, l) |-> l + 1
    /// P_ilist_0(r) <= r = 0
    /// P_ilist_0(r) <= r = l + 1 /\ P_ilist_0(l)
    fn generate_admissibility_preds(
        &self,
        preds: &mut PrdMap<Pred>,
    ) -> (BTreeMap<Typ, PrdIdx>, Vec<chc::AbsClause>) {
        let mut enc_map = BTreeMap::new();

        // prepare preds
        for (typ, _) in self.encs.iter() {
            let pi = preds.next_index();
            let p = Pred::new(
                format!(
                    "encoder_pred_{}",
                    enc::to_valid_symbol(typ.to_string()),
                ),
                pi,
                vec![typ.clone()].into(),
            );
            enc_map.insert(typ.clone(), p.idx);
            preds.push(p);
        }

        // generate clauses
        let mut clauses = Vec::new();
        for (typ, _) in self.encs.iter() {
            let (dt, prms) = typ.dtyp_inspect().unwrap();
            let pidx = enc_map.get(typ).unwrap();
            // for each constructor, we generate a different clause
            for (constructor_name, sels) in dt.news.iter() {
                let types = sels.iter().map(|(_, ty)| ty.to_type(Some(prms)).unwrap());
                let clause =
                    self.generate_approx_constraint(pidx, typ, constructor_name, &enc_map, types);
                clauses.push(clause);
            }
        }
        (enc_map, clauses)
    }

    fn append_admissibility_check(
        &self,
        clauses: &[chc::AbsClause],
        enc_map: &BTreeMap<Typ, PrdIdx>,
    ) -> Vec<chc::AbsClause> {
        let mut res = Vec::new();
        for c in clauses.iter() {
            let mut lhs_preds = c.lhs_preds.clone();
            // for each dtyp variable, we add the admissibility predicate
            for var in c.vars.iter() {
                if !var.typ.is_dtyp() {
                    continue;
                }
                let approx_pred = enc_map.get(&var.typ).unwrap();
                let args: VarMap<_> = vec![term::var(var.idx, var.typ.clone())].into();
                let app = chc::PredApp {
                    pred: *approx_pred,
                    args: args.into(),
                    };
                lhs_preds.push(app);
            }
            res.push(chc::AbsClause {
                vars: c.vars.clone(),
                lhs_term: c.lhs_term.clone(),
                lhs_preds,
                rhs: c.rhs.clone(),
            });
        }
        res
    }

    pub fn encode(&self) -> chc::AbsInstance {
        // 1. append admissibility predicates and clauses
        let mut preds = self.instance.preds.clone();
        let (enc_map, clauses2) = self.generate_admissibility_preds(&mut preds);
        let mut clauses = self.append_admissibility_check(&self.instance.clauses, &enc_map);
        clauses.extend(clauses2);

        // 2. encode the clauses by using the current catamorphism
        let preds = preds
            .iter()
            .map(|p| self.encode_pred(p))
            .collect();

        let clauses: Vec<_> = clauses.iter()
            .map(|c| self.encode_clause(c))
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
    approximation_to_test: Option<&str>,
) -> Res<Option<Either<ConjCandidates, UnsatRes>>> {
    log_info!("ABS ADT is enabled");
    //playground(instance);

    let mut absconf = AbsConf::new(instance, profiler)?;
    let r = match absconf.run(approximation_to_test)? {
        either::Left(()) => either::Left(ConjCandidates::new()),
        either::Right(_) => either::Right(UnsatRes::None),
    };
    Ok(Some(r))
}
