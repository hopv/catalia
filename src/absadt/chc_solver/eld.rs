use super::Instance as InstanceT;
use crate::absadt::eld_cex;
use crate::absadt::hyper_res;
use crate::common::*;
use std::borrow::Cow;
use std::io::BufReader;
use std::process::{Command, Stdio};

pub struct Eldarica {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

const OPTION: [&str; 0] = [];

impl Eldarica {
    fn new(timeout: Option<usize>, cex_mode: bool) -> Res<Self> {
        let mut args = OPTION.iter().map(|s| Cow::from(*s)).collect::<Vec<_>>();
        args.push(Cow::from("-in"));
        if cex_mode {
            args.push(Cow::from("-cex"));
        }
        if let Some(timeout) = timeout {
            args.push(Cow::from(format!("-t:{}", timeout)));
        }

        let mut child = Command::new("eld")
            .args(args.iter().map(|s| s.as_ref()))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("no stdin");
        let stdout = child.stdout.take().expect("no stdout");
        let stdout = BufReader::new(stdout);
        Ok(Self {
            child,
            stdin,
            stdout,
        })
    }
}

impl Eldarica {
    fn dump_instance<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        instance.dump_as_smt2(&mut self.stdin, "", encode_tag)?;
        Ok(())
    }

    fn check_sat(self) -> Res<bool> {
        let Self {
            stdin,
            stdout,
            mut child,
            ..
        } = self;
        fn inner(
            stdin: std::process::ChildStdin,
            mut stdout: BufReader<std::process::ChildStdout>,
        ) -> Res<String> {
            stdin.discard();

            let mut line = String::new();
            stdout.read_to_string(&mut line)?;
            Ok(line)
        }

        let res = inner(stdin, stdout);
        // kill child process before returning
        child.kill().unwrap();

        let line = res?;

        if line.starts_with("sat") {
            Ok(true)
        } else if line.starts_with("unsat") {
            Ok(false)
        } else {
            bail!("Unexpected output: {}", line)
        }
    }

    /// Check satisfiability and return counterexample if unsat
    fn check_sat_with_cex(self) -> Res<either::Either<(), hyper_res::ResolutionProof>> {
        let Self {
            stdin,
            stdout,
            mut child,
            ..
        } = self;

        fn inner(
            stdin: std::process::ChildStdin,
            mut stdout: BufReader<std::process::ChildStdout>,
        ) -> Res<String> {
            stdin.discard();

            let mut output = String::new();
            stdout.read_to_string(&mut output)?;
            Ok(output)
        }

        let res = inner(stdin, stdout);
        // kill child process before returning
        child.kill().unwrap();

        let output = res?;

        if output.starts_with("sat") {
            Ok(either::Left(()))
        } else if output.starts_with("unsat") {
            // Parse the counterexample
            let proof = eld_cex::parse_eldarica_cex(&output)?;
            Ok(either::Right(proof))
        } else {
            bail!("Unexpected output from Eldarica: {}", output)
        }
    }
}

pub fn run_eldarica<I>(instance: &I, timeout: Option<usize>, encode_tag: bool) -> Res<bool>
where
    I: InstanceT,
{
    let mut eld = Eldarica::new(timeout, false)?;
    eld.dump_instance(instance, encode_tag)?;
    eld.check_sat()
}

/// Run Eldarica with counterexample generation
///
/// Returns `Left(())` if sat, `Right(proof)` if unsat with counterexample
pub fn run_eldarica_cex<I>(
    instance: &I,
    timeout: Option<usize>,
) -> Res<either::Either<(), hyper_res::ResolutionProof>>
where
    I: InstanceT,
{
    let mut eld = Eldarica::new(timeout, true)?;
    // encode_tag must be true for counterexample generation
    eld.dump_instance(instance, true)?;
    eld.check_sat_with_cex()
}
