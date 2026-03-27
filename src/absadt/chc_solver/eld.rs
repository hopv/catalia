use super::CancelGroup;
use super::Instance as InstanceT;
use crate::absadt::eld_cex;
use crate::absadt::hyper_res;
use crate::common::*;
use std::borrow::Cow;
use std::io::BufReader;
use command_group::CommandGroup;
use std::process::{Command, Stdio};

pub struct Eldarica {
    child: command_group::GroupChild,
    stdin: Option<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
}

impl Drop for Eldarica {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
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
            .group_spawn()?;
        let stdin = child.inner().stdin.take().expect("no stdin");
        let stdout = child.inner().stdout.take().expect("no stdout");
        let stdout = BufReader::new(stdout);
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout,
        })
    }
}

impl Eldarica {
    fn dump_instance<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        instance.dump_as_smt2(self.stdin.as_mut().expect("stdin already closed"), "", encode_tag)?;
        Ok(())
    }

    fn check_sat(&mut self) -> Res<bool> {
        // Close stdin to signal EOF to the child.
        drop(self.stdin.take());

        let mut line = String::new();
        self.stdout.read_to_string(&mut line)?;

        if line.starts_with("sat") {
            Ok(true)
        } else if line.starts_with("unsat") {
            Ok(false)
        } else {
            bail!("Unexpected output: {}", line)
        }
    }

    /// Check satisfiability and return counterexample if unsat
    fn check_sat_with_cex(&mut self) -> Res<either::Either<(), hyper_res::ResolutionProof>> {
        // Close stdin to signal EOF to the child.
        drop(self.stdin.take());

        let mut output = String::new();
        self.stdout.read_to_string(&mut output)?;

        if output.starts_with("sat") {
            Ok(either::Left(()))
        } else if output.starts_with("unsat") {
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

/// Like [`run_eldarica`] but registers the child's process-group ID (pgid)
/// with `cancel` before blocking on I/O so that the caller can signal the
/// entire process group for prompt cancellation.
pub fn run_eldarica_cancellable<I>(
    instance: &I,
    timeout: Option<usize>,
    encode_tag: bool,
    cancel: &CancelGroup,
) -> super::WorkerResult
where
    I: InstanceT,
{
    let eld = match Eldarica::new(timeout, false) {
        Ok(e) => e,
        Err(e) => return super::WorkerResult::Failed(format!("{}", e)),
    };
    let pgid = eld.child.id();
    cancel.register(pgid);
    let mut eld = eld;
    let result = eld.dump_instance(instance, encode_tag).and_then(|_| eld.check_sat());
    match result {
        Ok(true)  => super::WorkerResult::Sat,
        Ok(false) => super::WorkerResult::Unsat,
        Err(e) if cancel.was_killed(pgid) => {
            log_info!("Eldarica cancelled: {}", e);
            super::WorkerResult::Cancelled
        }
        Err(e) => super::WorkerResult::Failed(format!("{}", e)),
    }
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
