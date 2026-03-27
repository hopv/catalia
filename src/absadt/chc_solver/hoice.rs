use super::CancelGroup;
use super::CHCSolver;
use super::Instance as InstanceT;
use crate::common::*;
use std::borrow::Cow;
use std::io::BufReader;
use command_group::CommandGroup;
use std::process::{Command, Stdio};

pub struct Hoice {
    child: command_group::GroupChild,
    stdin: Option<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
}

impl Drop for Hoice {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

const OPTION: [&str; 0] = [];

impl Hoice {
    fn new(timeout: Option<usize>) -> Res<Self> {
        let mut args = OPTION.iter().map(|s| Cow::from(*s)).collect::<Vec<_>>();
        if let Some(timeout) = timeout {
            args.push(Cow::from("--timeout"));
            args.push(Cow::from(timeout.to_string()));
        }

        let mut child = Command::new("hoice")
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

impl CHCSolver for Hoice {
    fn dump_instance_with_encode_tag<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        instance.dump_as_smt2(self.stdin.as_mut().expect("stdin already closed"), "", encode_tag)?;
        Ok(())
    }

    fn check_sat(mut self) -> Res<bool> {
        let mut line = String::new();
        writeln!(self.stdin.as_mut().expect("stdin already closed"), "(exit)").discard();
        // Close stdin so the child sees EOF after "(exit)".
        drop(self.stdin.take());

        self.stdout.read_to_string(&mut line)?;

        if line.starts_with("sat") {
            Ok(true)
        } else if line.starts_with("unsat") {
            Ok(false)
        } else {
            bail!("Unexpected output: {}", line)
        }
    }

    fn write_all<S>(&mut self, s: S) -> Res<()>
    where
        S: AsRef<[u8]>,
    {
        let s = s.as_ref();
        self.stdin.as_mut().expect("stdin already closed").write_all(s)?;
        Ok(())
    }
}

pub fn run_hoice<I>(instance: &I, timeout: Option<usize>, encode_tag: bool) -> Res<bool>
where
    I: InstanceT,
{
    let mut hoice = Hoice::new(timeout)?;
    hoice.dump_instance_with_encode_tag(instance, encode_tag)?;
    hoice.check_sat()
}

/// Like [`run_hoice`] but registers the child's process-group ID (pgid)
/// with `cancel` before blocking on I/O so that the caller can signal the
/// entire process group for prompt cancellation.
pub fn run_hoice_cancellable<I>(
    instance: &I,
    timeout: Option<usize>,
    encode_tag: bool,
    cancel: &CancelGroup,
) -> super::WorkerResult
where
    I: InstanceT,
{
    let mut hoice = match Hoice::new(timeout) {
        Ok(h) => h,
        Err(e) => return super::WorkerResult::Failed(format!("HoIce: {}", e)),
    };
    cancel.register(hoice.child.id());
    let result = hoice.dump_instance_with_encode_tag(instance, encode_tag)
        .and_then(|_| hoice.check_sat());
    match result {
        Ok(true)  => super::WorkerResult::Sat,
        Ok(false) => super::WorkerResult::Unsat,
        Err(e) => super::WorkerResult::Failed(format!("HoIce: {}", e)),
    }
}
