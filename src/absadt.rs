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
use enc::Enc;
use hyper_res::ResolutionProof;

use crate::common::*;
use crate::term::Term;
use crate::unsat_core::UnsatRes;
use std::path::PathBuf;

mod chc;
mod enc;
mod hyper_res;
mod spacer;

/// To be removed. Just for checking some behaviors
fn playground(instance: &Arc<Instance>) {
    // ~~~playground~~~
    let decs = dtyp::get_all();
    assert!(!decs.is_empty(), "no ADT is defined");

    for (name, dtyp) in decs.iter() {
        println!("dtype name: {}\n{:#?}", name, dtyp);
    }

    let ty = dtyp::of_constructor("nil").unwrap();
    println!("ty: {}", ty.name);
    let idx = dtyp::TPrmIdx::from(0);
    let ty = &ty.prms[idx];
    println!("ty: {}", ty);
    for c in instance.clauses().into_iter() {
        println!("clause: {:#?}", c.vars);
    }
}

pub struct AbsConf<'original> {
    pub cexs: Vec<chc::CEX>,
    pub instance: AbsInstance<'original>,
}

impl<'original> AbsConf<'original> {
    fn new(original: &'original Instance) -> Res<Self> {
        let instance = AbsInstance::new(original)?;
        let cexs = Vec::new();
        Ok(AbsConf { instance, cexs })
    }
    /// To be removed.
    fn playground(&mut self) -> Res<()> {
        let instance = &mut self.instance;
        let mut file = instance.instance_log_files("hoge")?;
        let last = &instance.clauses[0];
        let ty = last
            .vars
            .iter()
            .find_map(|x| if x.typ.is_dtyp() { Some(&x.typ) } else { None })
            .unwrap()
            .clone();
        instance.encs.insert(ty.clone(), Enc::len_ilist(ty));

        instance.dump_as_smt2(&mut file, "before", "", false)?;
        let encoded = instance.encode();
        encoded.dump_as_smt2(&mut file, "after", "", false)?;

        encoded.dump_as_smt2(&mut file, "w/ tag", "", true)?;

        match encoded.check_sat() {
            Ok(either::Left(())) => {
                println!("sat: {:#?}", ());
            }
            Ok(either::Right(x)) => {
                println!("unsat: {x}");
                let cex = instance.get_cex(&x);
                println!("cex: {cex}");
            }
            Err(e) => {
                println!("error: {:#?}", e);
            }
        }
        //chc::test_check_sat();
        Ok(())
    }
    fn run(&mut self) -> Res<()> {
        self.playground()?;

        loop {}

        Ok(())
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
    _profiler: &Profiler,
) -> Res<Option<Either<ConjCandidates, UnsatRes>>> {
    println!("hello");
    playground(instance);

    let mut absconf = AbsConf::new(instance)?;
    absconf.run()?;
    unimplemented!()
}
