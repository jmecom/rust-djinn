//! Exercise the actual optimizer loop with deterministic provider, verifier,
//! and timing boundaries. These tests never launch a paid agent or Lean.
#![allow(dead_code)]

use std::cell::RefCell;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

mod config {
    pub use cargo_djinn::config::*;
}
mod status {
    pub use cargo_djinn::status::*;
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Mode {
    Accept,
    BenchmarkError,
    AgentError,
    AgentExit,
    VerifyReject,
    VerifyCancel,
    BenchmarkCancel,
    CheckpointError,
    CheckpointSymlink,
}
struct State {
    mode: Mode,
    measurements: usize,
    stop: Arc<AtomicBool>,
}
thread_local! {
    static STATE: RefCell<Option<State>> = const { RefCell::new(None) };
}
fn mode() -> Mode {
    STATE.with(|s| s.borrow().as_ref().unwrap().mode)
}
fn cancel() {
    STATE.with(|s| s.borrow().as_ref().unwrap().stop.store(true, Ordering::SeqCst));
}

mod bench {
    use crate::{config::Config, Mode, STATE};
    pub use cargo_djinn::bench::{fmt_ns, validate_options, workload_path, workload_source, Measurement, Point};

    pub fn measure(cfg: &Config, _: f64, _: usize, _: usize, _: &mut dyn FnMut(&str)) -> Result<Measurement, String> {
        let call = STATE.with(|s| {
            let mut s = s.borrow_mut();
            let s = s.as_mut().unwrap();
            let n = s.measurements;
            s.measurements += 1;
            n
        });
        if call > 0 {
            match crate::mode() {
                Mode::BenchmarkError => return Err("benchmark panic".into()),
                Mode::BenchmarkCancel => crate::cancel(),
                Mode::CheckpointError => std::fs::remove_file(cfg.lean_dir().join("Proofs.lean")).unwrap(),
                Mode::CheckpointSymlink => {
                    std::fs::remove_file(cfg.lean_dir().join("Proofs.lean")).unwrap();
                    std::os::unix::fs::symlink(cfg.crate_dir.join("outside.txt"), cfg.lean_dir().join("Proofs.lean")).unwrap();
                }
                _ => {}
            }
        }
        let ns = if call == 0 { 100.0 } else { 50.0 };
        Ok(Measurement {
            ns_per_iter: vec![ns; 5],
            median_ns: ns,
            min_ns: ns,
            max_ns: ns,
            iters_per_batch: 1,
            total_secs: 1.0,
            points: vec![],
        })
    }
}
mod verify {
    pub use cargo_djinn::verify::Log;
    pub struct Report {
        pub pass: bool,
        pub stage: String,
    }
    pub fn verify(cfg: &crate::config::Config, jail: Option<&std::path::Path>, _: &mut Log) -> Report {
        if let Some(j) = jail {
            std::fs::copy(j.join("candidate.rs"), cfg.solution_dir().join("mod.rs")).unwrap();
            if crate::mode() == crate::Mode::VerifyCancel {
                crate::cancel();
            }
        }
        Report {
            pass: jail.is_none() || crate::mode() != crate::Mode::VerifyReject,
            stage: "done".into(),
        }
    }
}
mod agent {
    use crate::{
        config::Config,
        status::{Job, Usage},
    };
    pub use cargo_djinn::agent::{Agent, AgentRun, Opts};
    use std::{fs, path::Path, sync::atomic::AtomicBool};

    pub fn ensure_no_running_job(_: &Config) -> Result<(), String> {
        Ok(())
    }
    pub fn run_foreground(cfg: &Config, _: &Opts, _: &str, _: &Path, _: &AtomicBool, _: &str) -> Result<AgentRun, String> {
        let jail = cfg.state_dir().join("mock-jail");
        fs::create_dir_all(&jail).unwrap();
        fs::write(jail.join("candidate.rs"), "candidate\n").unwrap();
        // Agents can request synchronization before their process finishes.
        fs::write(cfg.solution_dir().join("mod.rs"), "candidate\n").unwrap();
        if crate::mode() == crate::Mode::AgentError {
            return Err("agent failed after sync".into());
        }
        let job = Job {
            id: "mock-job".into(),
            agent: "mock".into(),
            pid: 0,
            started: crate::config::now(),
            jail: jail.clone(),
            log: jail.join("agent.log"),
            background: false,
            model: None,
            limit_usd: None,
        };
        let usage = Usage {
            cost_usd: Some(0.25),
            ..Default::default()
        };
        Ok(AgentRun {
            job,
            exit_ok: crate::mode() != crate::Mode::AgentExit,
            interrupted: false,
            usage,
        })
    }
}
#[path = "../src/optimize.rs"]
mod optimize;

fn run_case(mode: Mode, expected_error: bool, interrupted: bool) {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!("djinn-optimizer-test-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    fs::create_dir(&root).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname=\"optimizer-test\"\nversion=\"0.1.0\"\n[package.metadata.djinn]\nbench=\"workload\"\n",
    )
    .unwrap();
    let cfg = config::load_config(&root.join("Cargo.toml")).unwrap();
    fs::create_dir_all(cfg.solution_dir()).unwrap();
    fs::create_dir_all(cfg.lean_dir()).unwrap();
    fs::write(cfg.solution_dir().join("mod.rs"), "known good\n").unwrap();
    fs::write(cfg.lean_dir().join("Proofs.lean"), "known proof\n").unwrap();
    fs::write(cfg.crate_dir.join("outside.txt"), "unrelated\n").unwrap();
    let stop = Arc::new(AtomicBool::new(false));
    STATE.with(|s| {
        *s.borrow_mut() = Some(State {
            mode,
            measurements: 0,
            stop: stop.clone(),
        })
    });
    let opts = optimize::OptOpts {
        cycles: Some(1),
        min_time: 0.01,
        batches: 5,
        jobs: 1,
        threshold: 0.03,
        agent: agent::Opts {
            agent: agent::Agent::Codex,
            model: None,
            yolo: false,
            background: false,
            extra_prompt: None,
            max_budget_usd: None,
            effort: None,
            extra_args: vec![],
            limit_usd: None,
            from_scratch: false,
        },
    };
    let result = optimize::optimize_with_stop(&cfg, opts, Path::new("never-used"), &stop);
    assert_eq!(result.is_err(), expected_error, "{result:?}");
    let accepted = mode == Mode::Accept;
    let expected = if accepted { "candidate\n" } else { "known good\n" };
    assert_eq!(fs::read_to_string(cfg.solution_dir().join("mod.rs")).unwrap(), expected);
    assert_eq!(fs::read_to_string(cfg.state_dir().join("optimize/checkpoint/solution/mod.rs")).unwrap(), expected);
    assert_eq!(fs::read_to_string(cfg.lean_dir().join("Proofs.lean")).unwrap(), "known proof\n");
    assert_eq!(fs::read_to_string(cfg.crate_dir.join("outside.txt")).unwrap(), "unrelated\n");
    let log = optimize::OptimizeLog::load(&cfg).unwrap();
    assert_eq!(log.accepted, usize::from(accepted));
    assert_eq!(log.interrupted, interrupted);
    assert_eq!(log.attempts.len(), 1);
    assert!(log.finished.is_some());
    if mode != Mode::AgentError {
        assert_eq!(log.spent_usd, 0.25);
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn attempts_restore_checkpoint_unless_accepted() {
    for (mode, error, interrupted) in [
        (Mode::Accept, false, false),
        (Mode::BenchmarkError, true, false),
        (Mode::AgentError, true, false),
        (Mode::AgentExit, false, false),
        (Mode::VerifyReject, false, false),
        (Mode::VerifyCancel, false, true),
        (Mode::BenchmarkCancel, false, true),
        (Mode::CheckpointError, true, false),
        (Mode::CheckpointSymlink, true, false),
    ] {
        eprintln!("optimizer scenario: {mode:?}");
        run_case(mode, error, interrupted);
    }
}
