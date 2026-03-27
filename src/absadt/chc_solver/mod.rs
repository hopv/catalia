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

/// Result from a parallel solver worker.
enum WorkerResult {
    Sat,
    Unsat,
    Failed(String),
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

    /// Register `pgid`.  If already cancelled, kills it immediately.
    fn register(&self, pgid: u32) {
        let mut g = self.inner.lock().expect("cancel group poisoned");
        if g.cancelled {
            kill_group(pgid);
        } else {
            g.pending.push(pgid);
        }
    }

    /// Mark as cancelled and immediately SIGKILL every registered process group.
    fn cancel(&self) {
        let mut g = self.inner.lock().expect("cancel group poisoned");
        g.cancelled = true;
        for &pgid in &g.pending { kill_group(pgid); }
    }
}

/// SIGKILL a process group. Parallel portfolio is Unix-only (rejected at
/// arg-parse time on other platforms), so this is unconditionally Unix.
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
    use std::sync::atomic::{AtomicBool, Ordering};

    // Channel carries the solver outcome (only Sat/Unsat are sent).
    let (tx, rx) = mpsc::channel::<WorkerResult>();
    let cancel = CancelGroup::new();
    let eldarica_errored = Arc::new(AtomicBool::new(false));

    let result = std::thread::scope(|s| {
        if !conf.no_eldarica {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            let eldarica_errored = Arc::clone(&eldarica_errored);
            s.spawn(move || {
                let r = eld::run_eldarica_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel);
                match r {
                    WorkerResult::Sat | WorkerResult::Unsat => { let _ = tx.send(r); },
                    WorkerResult::Failed(ref e) => {
                        log_info!("Eldarica failed with {}", e);
                        eldarica_errored.store(true, Ordering::SeqCst);
                    },
                }
            });
        }

        if !conf.no_hoice {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || {
                let r = hoice::run_hoice_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel);
                match r {
                    WorkerResult::Sat | WorkerResult::Unsat => { let _ = tx.send(r); },
                    WorkerResult::Failed(ref e) => { log_info!("HoIce failed with {}", e); },
                }
            });
        }

        if !conf.no_spacer {
            let tx = tx.clone();
            let cancel = Arc::clone(&cancel);
            s.spawn(move || {
                let r = spacer::run_spacer_portfolio_cancellable(instance, Some(CHECK_CHC_TIMEOUT), false, &cancel);
                match r {
                    WorkerResult::Sat | WorkerResult::Unsat => { let _ = tx.send(r); },
                    WorkerResult::Failed(ref e) => { log_info!("Spacer (portfolio) failed with {}", e); },
                }
            });
        }

        drop(tx);

        let result = rx.recv().ok();

        // Signal every remaining solver process group; threads unblock immediately.
        cancel.cancel();

        result
    });

    let eldarica_error = eldarica_errored.load(Ordering::SeqCst);
    Ok(match result {
        Some(WorkerResult::Sat) => either::Left(()),
        _ => either::Right((hyper_res::ResolutionProof::new(), eldarica_error)),
    })
}
