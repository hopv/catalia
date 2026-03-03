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
        match run_eldarica(instance, Some(CHECK_CHC_TIMEOUT), false) {
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
        let b = run_hoice(instance, Some(CHECK_CHC_TIMEOUT), false)
            .map_err(|e| log_info!("Hoice failed with {}", e))
            .unwrap_or(false);
        if b {
            return Ok(either::Left(()));
        }
    }

    if !conf.no_spacer {
        match run_spacer_portfolio(instance, Some(CHECK_CHC_TIMEOUT), false) {
            Ok(true) => return Ok(either::Left(())),
            Ok(false) => {},
            Err(e) => log_info!("Spacer (portfolio) failed with {}", e),
        }
    }

    Ok(either::Right((hyper_res::ResolutionProof::new(), false)))
}

/// Race-free cancellation group for parallel solver execution.
///
/// Each registered value is a process-group ID (pgid).  On Unix, signals are
/// sent to the entire group (via `kill(-pgid, sig)`) so subprocesses such as
/// the JVM launched by the Eldarica shell script are also included.
///
/// `register` and `cancel` both hold the same mutex, so they are fully
/// serialised: a pgid registered concurrently with a `cancel` call is
/// either found in the vec and killed by `cancel`, or it sees the
/// `cancelled` flag and is killed immediately inside `register`.
/// There is therefore no window in which a late-registering thread can
/// escape cancellation.
struct CancelGroup(std::sync::Mutex<(bool, Vec<u32>)>);

impl CancelGroup {
    fn new() -> std::sync::Arc<Self> {
        std::sync::Arc::new(Self(std::sync::Mutex::new((false, Vec::new()))))
    }

    /// Register `pgid`.  If already cancelled, kills it immediately.
    fn register(&self, pgid: u32) {
        let mut g = self.0.lock().expect("cancel group poisoned");
        if g.0 { kill_group_now(pgid); } else { g.1.push(pgid); }
    }

    /// Mark as cancelled and kill every registered process group.
    ///
    /// Sends SIGTERM to all groups simultaneously, polls for up to 500 ms,
    /// then sends SIGKILL to any survivors.
    fn cancel(&self) {
        // Drain vec and set flag under lock; release before sleeping.
        let pgids: Vec<u32> = {
            let mut g = self.0.lock().expect("cancel group poisoned");
            g.0 = true;
            g.1.drain(..).collect()
        };

        // Send SIGTERM to all groups simultaneously.
        #[cfg(unix)]
        for &pgid in &pgids { signal_group(pgid, libc::SIGTERM); }

        // Poll for up to 500 ms, checking all groups together.
        #[cfg(unix)] {
            let deadline = std::time::Instant::now()
                + std::time::Duration::from_millis(500);
            let mut alive: Vec<u32> = pgids.clone();
            while !alive.is_empty() && std::time::Instant::now() < deadline {
                std::thread::sleep(std::time::Duration::from_millis(10));
                // kill(-pgid, 0) returns -1/ESRCH when the group is gone.
                alive.retain(|&pgid| unsafe {
                    libc::kill(-(pgid as libc::pid_t), 0) == 0
                });
            }
            // SIGKILL any survivors.
            for &pgid in &alive { signal_group(pgid, libc::SIGKILL); }
        }
        #[cfg(not(unix))] let _ = pgids;
    }

    /// True after `cancel()` has been called.
    fn is_cancelled(&self) -> bool {
        self.0.lock().expect("cancel group poisoned").0
    }
}

/// Send `sig` to the process group identified by `pgid`.
///
/// `libc::kill` treats a negative first argument as `-(pgid)`, which
/// targets every process in the group — including subprocesses such as
/// the JVM launched by the Eldarica shell script.
#[cfg(unix)]
fn signal_group(pgid: u32, sig: libc::c_int) -> libc::c_int {
    // SAFETY: Sending a signal to a process group we own is safe.
    // Sending to a group that has already exited returns -1/ESRCH, which we ignore.
    unsafe { libc::kill(-(pgid as libc::pid_t), sig) }
}
#[cfg(not(unix))]
fn signal_group(_: u32, _: i32) -> i32 { 0 }

/// Immediate SIGKILL to a process group (no grace period).
fn kill_group_now(pgid: u32) {
    #[cfg(unix)] { signal_group(pgid, libc::SIGKILL); }
    #[cfg(not(unix))] let _ = pgid;
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
/// Latency after the winning solver finishes is bounded by process teardown
/// time (typically milliseconds), not by `CHECK_CHC_TIMEOUT`.
///
/// **Unix only.** Process-group signalling requires Unix; this function
/// returns an error immediately on other platforms.
///
/// The `eldarica_error` flag in the returned `Right` is only set when
/// Eldarica fails for a genuine reason (not because we killed it ourselves).
fn portfolio_parallel<I>(
    instance: &I,
) -> Res<either::Either<(), (hyper_res::ResolutionProof, bool)>>
where
    I: Instance + Sync,
{
    #[cfg(not(unix))]
    bail!("--parallel-portfolio is not supported on this platform: \
           process-group cancellation requires Unix");

    use std::sync::{mpsc, Arc};
    use std::sync::atomic::{AtomicBool, Ordering};

    // Channel carries Left(()) = SAT or Right(()) = UNSAT.
    // eldarica_error is tracked separately to avoid conflating it with
    // which solver happened to win the race.
    let (tx, rx) = mpsc::channel::<either::Either<(), ()>>();
    let cancel = CancelGroup::new();
    let eldarica_errored = Arc::new(AtomicBool::new(false));

    let result = std::thread::scope(|s| {
        if !conf.no_eldarica {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            let eldarica_errored = Arc::clone(&eldarica_errored);
            s.spawn(move || {
                match eld::run_eldarica_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel) {
                    Ok(true)  => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(())); },
                    Err(e)    => {
                        log_info!("Eldarica failed with {}", e);
                        // Only flag a genuine failure; an error caused by
                        // our own SIGKILL is expected and benign.
                        if !cancel.is_cancelled() {
                            eldarica_errored.store(true, Ordering::SeqCst);
                        }
                    },
                }
            });
        }

        if !conf.no_hoice {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || {
                match hoice::run_hoice_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel) {
                    Ok(true)  => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(())); },
                    Err(e)    => { log_info!("HoIce failed with {}", e); },
                }
            });
        }

        if !conf.no_spacer {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || {
                match spacer::run_spacer_portfolio_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel) {
                    Ok(true)  => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(())); },
                    Err(e)    => { log_info!("Spacer (portfolio) failed with {}", e); },
                }
            });
        }

        // Drop the main sender so the channel closes once all threads finish.
        drop(tx);

        // Block until the first conclusive result (or channel close if all fail).
        let result = match rx.recv() {
            Ok(r)  => r,
            Err(_) => either::Right(()),
        };

        // Signal every remaining solver process group; threads unblock immediately.
        cancel.cancel();

        result
    });

    let eldarica_error = eldarica_errored.load(Ordering::SeqCst);
    Ok(match result {
        either::Left(())  => either::Left(()),
        either::Right(()) => either::Right((hyper_res::ResolutionProof::new(), eldarica_error)),
    })
}
