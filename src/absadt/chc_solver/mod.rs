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

/// Run all enabled solvers in parallel and return the first conclusive result.
///
/// All solvers share the same per-solver timeout (`CHECK_CHC_TIMEOUT`), so the
/// total wall-clock time is bounded by a single timeout regardless of how many
/// solvers are active.  `std::thread::scope` guarantees every spawned thread
/// finishes before this function returns.
fn portfolio_parallel<I>(
    instance: &I,
) -> Res<either::Either<(), (hyper_res::ResolutionProof, bool)>>
where
    I: Instance + Sync,
{
    use std::sync::mpsc;

    // Each thread sends `Left(())` for SAT or `Right(eldarica_error)` for UNSAT.
    let (tx, rx) = mpsc::channel::<either::Either<(), bool>>();

    std::thread::scope(|s| {
        if !conf.no_eldarica {
            let tx = tx.clone();
            s.spawn(move || {
                match run_eldarica(instance, Some(CHECK_CHC_TIMEOUT), false) {
                    Ok(true) => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(false)); },
                    Err(e) => { log_info!("Eldarica failed with {}", e); },
                }
            });
        }

        if !conf.no_hoice {
            let tx = tx.clone();
            s.spawn(move || {
                match run_hoice(instance, Some(CHECK_CHC_TIMEOUT), false) {
                    Ok(true) => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(true)); },
                    Err(e) => { log_info!("HoIce failed with {}", e); },
                }
            });
        }

        if !conf.no_spacer {
            let tx = tx.clone();
            s.spawn(move || {
                match run_spacer_portfolio(instance, Some(CHECK_CHC_TIMEOUT)) {
                    Ok(true) => { let _ = tx.send(either::Left(())); },
                    Ok(false) => { let _ = tx.send(either::Right(true)); },
                    Err(e) => { log_info!("Spacer (portfolio) failed with {}", e); },
                }
            });
        }

        // Drop the main sender so the channel closes once all threads finish.
        drop(tx);

        match rx.recv() {
            Ok(either::Left(())) => Ok(either::Left(())),
            Ok(either::Right(eldarica_error)) =>
                Ok(either::Right((hyper_res::ResolutionProof::new(), eldarica_error))),
            // All solvers failed without a result.
            Err(_) => Ok(either::Right((hyper_res::ResolutionProof::new(), true))),
        }
    })
}
