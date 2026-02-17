//! Wrapper for Spacer
//!
//! This module takes an instance, executes Spacer, and returns a model or
//! unsat-core. This module is intended to be temporary; we should move the
//! functionality to rsmt2 or some other place.

use super::Instance as InstanceT;
use crate::absadt::hyper_res;
use crate::common::*;
use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};

const OPTION: [&str; 14] = [
    // Disable inlining for obtaining resolution proofs appropriately
    // see https://github.com/Z3Prover/z3/issues/2430#issuecomment-514351694
    // and https://github.com/Z3Prover/z3/issues/6848
    // in my understanding, slice also should be false
    // which prevents spacer from generating proofs such as
    // ((set-logic HORN)
    // (declare-fun query!1 () Bool)
    // (declare-fun query!0 () Bool)
    // (declare-fun lt_0!slice!2 () Bool)  <- this can be removed
    // (proof
    // (let ((@x2101 ((_ hyper-res 0 0 0 1) (asserted (=> lt_0!slice!2 query!0)) ((_ hyper-res 0 0) (asserted lt_0!slice!2) lt_0!slice!2) query!0)))
    // (mp ((_ hyper-res 0 0 0 1) (asserted (=> query!0 query!1)) @x2101 query!1) (asserted (=> query!1 false)) false))))
    "fp.xform.slice=false",
    "fp.xform.inline_linear=false",
    "fp.xform.inline_eager=false",
    "fp.xform.subsumption_checker=false",
    // Spacer configuration taken from CHC-COMP
    "fp.xform.tail_simplifier_pve=false",
    "fp.validate=true",
    "fp.spacer.mbqi=false",
    "fp.spacer.use_iuc=true",
    "fp.spacer.global=true",
    "fp.spacer.expand_bnd=true",
    "fp.spacer.q3.use_qgen=true",
    "fp.spacer.q3.instantiate=true",
    "fp.spacer.q3=true",
    "fp.spacer.ground_pobs=false",
];

pub struct Spacer {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

impl Drop for Spacer {
    fn drop(&mut self) {
        self.child.kill().unwrap();
    }
}

impl Spacer {
    fn write_all<S>(&mut self, s: S) -> Res<()>
    where
        S: AsRef<[u8]>,
    {
        let s = s.as_ref();
        self.stdin.write_all(s)?;
        Ok(())
    }

    fn dump_instance<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        let options = "(set-option :produce-proofs true)\n(set-option :pp.pretty_proof true)\n(set-option :produce-unsat-cores true)";
        instance.dump_as_smt2(&mut self.stdin, options, encode_tag)?;
        Ok(())
    }
    fn check_sat(&mut self) -> Res<bool> {
        let mut line = String::new();
        self.stdout.read_line(&mut line)?;
        if line.starts_with("sat") {
            Ok(true)
        } else if line.starts_with("unsat") {
            Ok(false)
        } else {
            bail!("Unexpected output (spacer): {}", line)
        }
    }
}
impl Spacer {
    fn new() -> Res<Spacer> {
        let mut args = OPTION.to_vec();
        let path = conf.spacer.clone().unwrap_or("z3".to_string());
        args.push("-in");
        let mut child = Command::new(path)
            .args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("no stdin");
        let stdout = child.stdout.take().expect("no stdout");
        let stdout = BufReader::new(stdout);
        Ok(Spacer {
            child,
            stdin,
            stdout,
        })
    }
    fn get_proof(&mut self) -> Res<hyper_res::ResolutionProof> {
        self.write_all(b"(get-proof)\n")?;
        self.write_all(b"(exit)\n")?;
        let mut output = String::new();
        self.stdout.read_to_string(&mut output)?;
        parse_proof(&output)
    }
    #[allow(dead_code)]
    fn get_model(&mut self) -> Res<CHCModel> {
        self.write_all(b"(get-model)\n")?;
        self.write_all(b"(exit)\n")?;
        let mut output = String::new();
        self.stdout.read_to_string(&mut output)?;
        parse_model(&output)
    }
    #[allow(dead_code)]
    fn set_timeout(&mut self, sec: usize) -> Res<()> {
        self.write_all(format!("(set-option :timeout {}000)\n", sec))?;
        Ok(())
    }
}

fn parse_proof(output: &str) -> Res<hyper_res::ResolutionProof> {
    log_debug!("{output}");
    let mut p = hyper_res::HyperResolutionParser::new();
    p.parse_spacer(output)
}

pub struct CHCModel {}

fn parse_model(_output: &str) -> Res<CHCModel> {
    unimplemented!()
}

pub fn run_spacer<I>(instance: &I) -> Res<either::Either<(), hyper_res::ResolutionProof>>
where
    I: InstanceT,
{
    let mut spacer = Spacer::new()?;
    spacer.dump_instance(instance, true)?;

    let is_sat = spacer.check_sat()?;

    if is_sat {
        //let model = spacer.get_model()?;
        Ok(either::Left(()))
    } else {
        let proof = spacer.get_proof()?;
        Ok(either::Right(proof))
    }
}
