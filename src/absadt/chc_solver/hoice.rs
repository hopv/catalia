use super::CHCSolver;
use super::Instance as InstanceT;
use crate::common::*;
use std::borrow::Cow;
use std::io::BufReader;
use std::process::{Command, Stdio};

pub struct Hoice {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
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

impl CHCSolver for Hoice {
    fn dump_instance_with_encode_tag<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        instance.dump_as_smt2(&mut self.stdin, "", encode_tag)?;
        Ok(())
    }

    fn check_sat(mut self) -> Res<bool> {
        let mut line = String::new();
        writeln!(&mut self.stdin, "(exit)").discard();

        self.stdout.read_to_string(&mut line)?;

        self.child.kill().unwrap();

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
        self.stdin.write_all(s)?;
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

/// Like [`run_hoice`] but registers the child PID in `pids` before blocking
/// on I/O so that the caller can SIGTERM the process for prompt cancellation.
pub fn run_hoice_cancellable<I>(
    instance: &I,
    timeout: Option<usize>,
    encode_tag: bool,
    pids: &std::sync::Mutex<Vec<u32>>,
) -> Res<bool>
where
    I: InstanceT,
{
    let mut hoice = Hoice::new(timeout)?;
    pids.lock().expect("pid mutex poisoned").push(hoice.child.id());
    hoice.dump_instance_with_encode_tag(instance, encode_tag)?;
    hoice.check_sat()
}
