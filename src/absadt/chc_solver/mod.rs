mod eld;
mod hoice;
mod spacer;

use crate::absadt::hyper_res;
use crate::common::*;
pub use eld::{run_eldarica, run_eldarica_cex};
pub use hoice::run_hoice;
pub use spacer::{run_spacer, run_spacer_portfolio};

const CHECK_CHC_TIMEOUT: usize = 60;

pub trait Instance {
    fn dump_as_smt2<File, Option>(
        &self,
        w: &mut File,
        options: Option,
        encode_tag: bool,
    ) -> Res<()>
    where
        File: Write,
        Option: AsRef<str>;
}

pub trait CHCSolver {
    fn write_all<S>(&mut self, s: S) -> Res<()>
    where
        S: AsRef<[u8]>;

    fn dump_instance<I>(&mut self, instance: &I) -> Res<()>
    where
        I: Instance,
    {
        self.dump_instance_with_encode_tag(instance, true)
    }

    fn dump_instance_with_encode_tag<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: Instance;

    fn check_sat(self) -> Res<bool>;
}

/// Dispatch to sequential or parallel portfolio depending on configuration.
pub fn portfolio<I>(instance: &I) -> Res<either::Either<(), (hyper_res::ResolutionProof, bool)>>
where
    I: Instance + Sync,
{
    if conf.parallel_portfolio {
        portfolio_parallel(instance)
    } else {
        portfolio_sequential(instance)
    }
}

/// Try each enabled solver in order and return the first conclusive result.
///
/// The `eldarica_error` flag in the `Right` variant signals that Eldarica
/// encountered a problem during this phase; when `use_eldarica_cex` is set,
/// the caller uses this flag to decide whether to attempt Eldarica for CEX
/// generation.
fn portfolio_sequential<I>(
    instance: &I,
) -> Res<either::Either<(), (hyper_res::ResolutionProof, bool)>>
where
    I: Instance,
{
    if !conf.no_eldarica {
        match run_eldarica(instance, Some(CHECK_CHC_TIMEOUT), false, None) {
            // Eldarica determined SAT
            Ok(true) => return Ok(either::Left(())),
            // Eldarica determined UNSAT
            Ok(false) =>
                return Ok(either::Right((hyper_res::ResolutionProof::new(), false))),
            Err(err) => {
                log_info!("Eldarica failed with {}", err);
                return Ok(either::Right((hyper_res::ResolutionProof::new(), true)));
            },
        }
    }

    if !conf.no_hoice {
        let b = run_hoice(instance, Some(CHECK_CHC_TIMEOUT), false, None)
            .map_err(|e| log_info!("Hoice failed with {}", e))
            .unwrap_or(false);
        if b {
            return Ok(either::Left(()));
        }
    }

    if !conf.no_spacer {
        match run_spacer_portfolio(instance, Some(CHECK_CHC_TIMEOUT), false, None) {
            Ok(true) => return Ok(either::Left(())),
            Ok(false) => {},
            Err(e) => log_info!("Spacer (portfolio) failed with {}", e),
        }
    }

    Ok(either::Right((hyper_res::ResolutionProof::new(), false)))
}

/// Coordinates SIGKILL cancellation of solver process groups.
///
/// Each solver is spawned with `group_spawn()`, which calls `setpgid(0, 0)`
/// so the process group leader's PID equals the pgid. Registering that PID
/// via `GroupChild::id()` is therefore equivalent to registering the pgid,
/// and `kill(-pgid, SIGKILL)` terminates the entire group (including any
/// grandchild processes such as the JVM launched by the Eldarica shell script).
///
/// `register` and `cancel` share a mutex so they are fully serialised:
/// a pgid registered concurrently with `cancel` is either in the pending list
/// and killed by `cancel`, or it arrives after `cancelled` is set and is
/// killed immediately inside `register`. No late-registering solver can escape.
struct CancelGroup {
    inner: std::sync::Mutex<CancelGroupInner>,
}

struct CancelGroupInner {
    cancelled: bool,
    pending: Vec<u32>,
}

impl CancelGroup {
    fn new() -> std::sync::Arc<Self> {
        std::sync::Arc::new(Self {
            inner: std::sync::Mutex::new(CancelGroupInner {
                cancelled: false,
                pending: Vec::new(),
            }),
        })
    }

    /// Register a pgid (== `GroupChild::id()`). Kills immediately if already cancelled.
    fn register(&self, pgid: u32) {
        let mut g = self.inner.lock().expect("cancel group poisoned");
        if g.cancelled {
            kill_group(pgid);
        } else {
            g.pending.push(pgid);
        }
    }

    /// SIGKILL all registered process groups.
    fn cancel(&self) {
        let mut g = self.inner.lock().expect("cancel group poisoned");
        g.cancelled = true;
        for &pgid in &g.pending { kill_group(pgid); }
    }
}

/// SIGKILL the process group identified by `pgid` (`kill(-pgid, SIGKILL)`).
/// Parallel portfolio is Unix-only, so the non-Unix stub just panics.
#[cfg(unix)]
fn kill_group(pgid: u32) {
    unsafe { libc::kill(-(pgid as libc::pid_t), libc::SIGKILL); }
}

#[cfg(not(unix))]
fn kill_group(_: u32) {
    unreachable!("--parallel-portfolio is not supported on this platform");
}

/// Run all enabled solvers in parallel and return the first conclusive result.
///
/// Each solver thread registers its child's process-group ID (pgid) with a
/// `CancelGroup` before blocking on I/O.  Once the first result arrives,
/// `cancel()` signals every registered process group so its thread unblocks
/// immediately (killed process → stdout EOF → I/O call returns).
/// `std::thread::scope` then joins the now-quick-to-exit threads before
/// returning.
///
/// The `eldarica_error` flag in the returned `Right` is only set when
/// Eldarica fails for a genuine reason (not because we killed it ourselves).
/// Attribution is per-pgid, so a genuine Eldarica failure racing with another
/// solver's win is correctly classified.
fn portfolio_parallel<I>(
    instance: &I,
) -> Res<either::Either<(), (hyper_res::ResolutionProof, bool)>>
where
    I: Instance + Sync,
{
    use std::sync::{mpsc, Arc};

    let (tx, rx) = mpsc::channel::<Res<bool>>();
    let cancel = CancelGroup::new();

    let result = std::thread::scope(|s| {
        if !conf.no_eldarica {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || { let _ = tx.send(eld::run_eldarica(instance, Some(CHECK_CHC_TIMEOUT), false, Some(&cancel))); });
        }
        if !conf.no_hoice {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || { let _ = tx.send(hoice::run_hoice(instance, Some(CHECK_CHC_TIMEOUT), false, Some(&cancel))); });
        }
        if !conf.no_spacer {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || { let _ = tx.send(spacer::run_spacer_portfolio(instance, Some(CHECK_CHC_TIMEOUT), false, Some(&cancel))); });
        }

        drop(tx);

        let result = loop {
            match rx.recv() {
                Ok(Ok(sat)) => break Some(sat),
                Ok(Err(e)) => log_info!("solver failed: {}", e),
                Err(_) => break None, // all solvers done, none conclusive
            }
        };
        cancel.cancel();
        result
    });

    Ok(match result {
        Some(true) => either::Left(()),
        _ => either::Right((hyper_res::ResolutionProof::new(), false)),
    })
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use command_group::CommandGroup;
    use std::io::BufRead;

    fn pid_exists(pid: i32) -> bool {
        unsafe { libc::kill(pid, 0) == 0 }
    }

    /// Verify that `CancelGroup::cancel()` kills the entire process group,
    /// including grandchild processes spawned by the group leader.
    #[test]
    fn cancel_kills_entire_process_group() {
        // Shell: spawn a grandchild (sleep), print its PID, then loop forever.
        let mut child = std::process::Command::new("sh")
            .args(["-c", "sleep 10000 & echo $!; sleep 10000"])
            .stdout(std::process::Stdio::piped())
            .group_spawn()
            .unwrap();

        let pgid = child.id() as i32;

        // Read the grandchild PID printed by the shell.
        let grandchild_pid: i32 = {
            let stdout = child.inner().stdout.take().unwrap();
            let mut line = String::new();
            std::io::BufReader::new(stdout).read_line(&mut line).unwrap();
            line.trim().parse().unwrap()
        };

        assert!(pid_exists(pgid), "process group leader should be alive");
        assert!(pid_exists(grandchild_pid), "grandchild should be alive");

        let cancel = CancelGroup::new();
        cancel.register(child.id());
        cancel.cancel();

        // Reap the direct child so it doesn't stay a zombie.
        let _ = child.wait();

        // Grandchild is adopted by init after the shell dies; poll until reaped.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while pid_exists(grandchild_pid) && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        assert!(!pid_exists(pgid), "process group leader should be dead");
        assert!(!pid_exists(grandchild_pid), "grandchild should be dead");
    }
}
