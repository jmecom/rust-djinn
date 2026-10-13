//! `cargo djinn optimize`: hill-climb on performance with an LLM, under the
//! verifier.
//!
//! 1. `verify` must pass (there is nothing to optimize otherwise).
//! 2. Baseline: time the workload (`bench`).
//! 3. Per cycle: checkpoint the verified solution and proofs; run an agent in
//!    a jail with the workload, the current timing, the acceptance rule and
//!    the history of earlier attempts; then `verify` — a failure reverts —
//!    and re-measure — not faster beyond noise and threshold reverts. An
//!    accepted attempt becomes the new baseline and checkpoint.
//! 4. Stop after `--cycles`, when the estimated spend reaches `--limit`, or
//!    on Ctrl-C, which kills the agent and restores the last known-good
//!    checkpoint.

use crate::agent::{self, Opts};
use crate::bench::{self, fmt_ns, Measurement};
use crate::config::*;
use crate::status;
use crate::verify::{self, Log};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub struct OptOpts {
    pub cycles: Option<usize>,
    pub min_time: f64,
    pub batches: usize,
    /// points measured concurrently (multi-point workloads)
    pub jobs: usize,
    /// required relative improvement, e.g. 0.03
    pub threshold: f64,
    pub agent: Opts,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Attempt {
    pub cycle: usize,
    pub job: String,
    /// accepted | not faster | did not verify (<stage>) | interrupted | agent failed
    pub verdict: String,
    pub ns: Option<f64>,
    /// multi-point workloads: (point, size, median ns) per point
    #[serde(default)]
    pub points: Vec<(u64, Option<u64>, f64)>,
    pub summary: String,
    pub cost_usd: Option<f64>,
    pub cost_is_estimate: bool,
    pub tokens_in: u64,
    pub tokens_out: u64,
    pub elapsed_secs: u64,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct OptimizeLog {
    pub started: u64,
    pub finished: Option<u64>,
    pub baseline_ns: f64,
    pub current_ns: f64,
    #[serde(default)]
    pub baseline_points: Vec<(u64, Option<u64>, f64)>,
    #[serde(default)]
    pub current_points: Vec<(u64, Option<u64>, f64)>,
    pub attempts: Vec<Attempt>,
    pub accepted: usize,
    pub spent_usd: f64,
    pub interrupted: bool,
}

impl OptimizeLog {
    pub fn path(cfg: &Config) -> PathBuf {
        cfg.state_dir().join("optimize.json")
    }
    pub fn load(cfg: &Config) -> Option<OptimizeLog> {
        serde_json::from_str(&fs::read_to_string(Self::path(cfg)).ok()?).ok()
    }
    fn save(&self, cfg: &Config) {
        let _ = fs::create_dir_all(cfg.state_dir());
        if let Ok(s) = serde_json::to_string_pretty(self) {
            let _ = fs::write(Self::path(cfg), s);
        }
    }
    pub fn speedup(&self) -> f64 {
        if self.current_ns > 0.0 {
            self.baseline_ns / self.current_ns
        } else {
            1.0
        }
    }
    pub fn summary_line(&self) -> String {
        format!(
            "optimize: {} → {} per iteration ({:.2}×), {} attempt(s), {} accepted, spent ~${:.2}{}",
            fmt_ns(self.baseline_ns),
            fmt_ns(self.current_ns),
            self.speedup(),
            self.attempts.len(),
            self.accepted,
            self.spent_usd,
            if self.interrupted { ", interrupted" } else { "" }
        )
    }
}

// ------------------------------------------------------------- frontier
//
// A multi-point workload (a compression level per point) is judged as lean-zip
// judges codecs: by the trade-off curve, not by any one point. Each point is
// (size, time); the achievable frontier is the lower convex hull — blending
// two adjacent points reaches every point on the segment between them — and
// a version is better when its frontier is nowhere above the old one and
// below it somewhere. Point labels carry no meaning: a level may change what
// it does, as long as the curve improves.

/// The lower-left convex hull of (size, time) points, sorted by size: the
/// trade-off curve, with dominated points dropped.
pub fn frontier(points: &[(f64, f64)]) -> Vec<(f64, f64)> {
    let mut ps: Vec<(f64, f64)> = points.iter().copied().filter(|p| p.0.is_finite() && p.1.is_finite()).collect();
    ps.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.partial_cmp(&b.1).unwrap()));
    // dominated: not strictly faster than a smaller-or-equal point
    let mut best = f64::INFINITY;
    let mut kept = Vec::new();
    for p in ps {
        if p.1 < best {
            best = p.1;
            kept.push(p);
        }
    }
    // lower hull (monotone chain)
    let cross = |o: (f64, f64), a: (f64, f64), b: (f64, f64)| (a.0 - o.0) * (b.1 - o.1) - (a.1 - o.1) * (b.0 - o.0);
    let mut hull: Vec<(f64, f64)> = Vec::new();
    for p in kept {
        while hull.len() >= 2 && cross(hull[hull.len() - 2], hull[hull.len() - 1], p) <= 0.0 {
            hull.pop();
        }
        hull.push(p);
    }
    hull
}

/// The frontier's time at a size: interpolated between vertices; its last
/// time beyond the largest size; `None` below the smallest (unreachable).
pub fn time_at(hull: &[(f64, f64)], size: f64) -> Option<f64> {
    let first = hull.first()?;
    if size < first.0 {
        return None;
    }
    for w in hull.windows(2) {
        if size <= w[1].0 {
            let t = if w[1].0 > w[0].0 { (size - w[0].0) / (w[1].0 - w[0].0) } else { 1.0 };
            return Some(w[0].1 + t * (w[1].1 - w[0].1));
        }
    }
    hull.last().map(|p| p.1)
}

/// The frontier's size at a time, by the same interpolation; `None` if no
/// point is that fast.
pub fn size_at(hull: &[(f64, f64)], time: f64) -> Option<f64> {
    let last = hull.last()?;
    if time < last.1 {
        return None;
    }
    for w in hull.windows(2) {
        if time >= w[1].1 {
            let t = if w[0].1 > w[1].1 { (w[0].1 - time) / (w[0].1 - w[1].1) } else { 0.0 };
            return Some(w[0].0 + t.clamp(0.0, 1.0) * (w[1].0 - w[0].0));
        }
    }
    hull.first().map(|p| p.0)
}

/// The verdict on a new measurement against the current one, by the frontier
/// rule: `Ok(improvement)` (the largest relative gain at a matched size or a
/// matched time, at least `required`), or `Err(why)`.
pub fn frontier_verdict(old: &Measurement, new: &Measurement, required: f64, size_required: f64) -> Result<f64, String> {
    let pts = |m: &Measurement| m.points.iter().map(|p| (p.size.unwrap_or(0) as f64, p.median_ns)).collect::<Vec<_>>();
    let (oh, nh) = (frontier(&pts(old)), frontier(&pts(new)));
    let (Some(of), Some(nf)) = (oh.first(), nh.first()) else { return Err("no points".into()) };
    if nf.0 > of.0 {
        return Err(format!("the densest point grew: {} → {} bytes (the frontier must still reach the old smallest size)", of.0, nf.0));
    }
    let mut best = f64::NEG_INFINITY;
    for &(s, t) in &oh {
        let nt = time_at(&nh, s).unwrap_or(f64::INFINITY);
        if nt > t * (1.0 + required) {
            return Err(format!("slower at size {}: {} → {} ({:+.1}%)", s, fmt_ns(t), fmt_ns(nt), (nt / t - 1.0) * 100.0));
        }
        best = best.max(1.0 - nt / t);
        if let Some(ns) = size_at(&nh, t) {
            // sizes are exact: a density gain needs only the threshold, not the noise
            let gain = 1.0 - ns / s;
            if gain >= size_required {
                best = best.max(gain.max(required));
            }
        }
    }
    // the new fastest point must not be slower than the old fastest
    if let (Some(ol), Some(nl)) = (oh.last(), nh.last()) {
        if nl.1 > ol.1 * (1.0 + required) {
            return Err(format!("the fastest point slowed: {} → {}", fmt_ns(ol.1), fmt_ns(nl.1)));
        }
    }
    if best >= required {
        Ok(best)
    } else {
        Err(format!("not better: best gain at a matched size or time {:+.1}%, needed {:.1}%", best * 100.0, required * 100.0))
    }
}

fn point_list(m: &Measurement) -> Vec<(u64, Option<u64>, f64)> {
    m.points.iter().map(|p| (p.id, p.size, p.median_ns)).collect()
}

#[cfg(test)]
mod frontier_tests {
    use super::*;
    use crate::bench::Point;
    fn m(pts: &[(u64, u64, f64)]) -> Measurement {
        let points: Vec<Point> = pts.iter().map(|&(id, size, ns)| Point { id, ns_per_iter: vec![ns], median_ns: ns, min_ns: ns, max_ns: ns, iters_per_batch: 1, size: Some(size) }).collect();
        Measurement { ns_per_iter: vec![], median_ns: points.iter().map(|p| p.median_ns).sum(), min_ns: 0.0, max_ns: 0.0, iters_per_batch: 1, total_secs: 0.0, points }
    }
    #[test]
    fn hull_drops_dominated() {
        let h = frontier(&[(100.0, 10.0), (90.0, 20.0), (95.0, 25.0), (80.0, 40.0)]);
        assert_eq!(h, vec![(80.0, 40.0), (90.0, 20.0), (100.0, 10.0)]);
    }
    #[test]
    fn faster_everywhere_is_accepted() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(1, 100, 9.0), (2, 90, 18.0), (3, 80, 36.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).unwrap() > 0.09);
    }
    #[test]
    fn relabelled_levels_are_fine() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(3, 100, 9.0), (1, 90, 18.0), (2, 80, 36.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_ok());
    }
    #[test]
    fn losing_density_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 100, 5.0), (2, 85, 20.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
    #[test]
    fn slower_at_matched_size_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(1, 100, 10.0), (2, 90, 30.0), (3, 80, 40.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
    #[test]
    fn denser_at_same_speed_is_accepted() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 98, 10.0), (2, 78, 40.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_ok());
    }
    #[test]
    fn noise_level_change_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 100, 9.9), (2, 80, 39.8)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
}

// ----------------------------------------------------------- checkpoints

fn checkpoint_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("optimize").join("checkpoint")
}

fn copy_tree(src: &Path, dst: &Path) -> Result<(), String> {
    if src.is_dir() {
        fs::create_dir_all(dst).map_err(|e| e.to_string())?;
        for e in fs::read_dir(src).map_err(|e| e.to_string())?.flatten() {
            copy_tree(&e.path(), &dst.join(e.file_name()))?;
        }
    } else {
        if let Some(p) = dst.parent() {
            fs::create_dir_all(p).map_err(|e| e.to_string())?;
        }
        fs::copy(src, dst).map_err(|e| format!("{}: {e}", src.display()))?;
    }
    Ok(())
}

/// Save the (verified) solution and proofs as the last known-good state.
fn checkpoint(cfg: &Config) -> Result<(), String> {
    let d = checkpoint_dir(cfg);
    let _ = fs::remove_dir_all(&d);
    copy_tree(&cfg.solution_dir(), &d.join("solution"))?;
    let proofs = cfg.lean_dir();
    copy_tree(&proofs.join("Proofs.lean"), &d.join("Proofs.lean"))?;
    if proofs.join("Proofs").is_dir() {
        copy_tree(&proofs.join("Proofs"), &d.join("Proofs"))?;
    }
    Ok(())
}

/// Restore the last known-good state and re-run the verifier so the report
/// and the generated code match it again.
fn revert(cfg: &Config, why: &str) -> Result<(), String> {
    eprintln!("== reverting to the last known-good checkpoint ({why})");
    let d = checkpoint_dir(cfg);
    if !d.join("solution").exists() {
        return Err("no checkpoint to revert to".into());
    }
    let _ = fs::remove_dir_all(cfg.solution_dir());
    copy_tree(&d.join("solution"), &cfg.solution_dir())?;
    let proofs = cfg.lean_dir();
    copy_tree(&d.join("Proofs.lean"), &proofs.join("Proofs.lean"))?;
    let _ = fs::remove_dir_all(proofs.join("Proofs"));
    if d.join("Proofs").is_dir() {
        copy_tree(&d.join("Proofs"), &proofs.join("Proofs"))?;
    }
    let r = verify::verify(cfg, None, &mut Log::new(false));
    if !r.pass {
        return Err(format!("the restored checkpoint no longer verifies (stage {}) — this should not happen", r.stage));
    }
    Ok(())
}

// ------------------------------------------------------------------ prompt

fn prompt(cfg: &Config, opts: &OptOpts, current: &Measurement, log: &OptimizeLog, extra: Option<&str>) -> String {
    let (_, w) = bench::workload_path(cfg).unwrap_or_default();
    let source = bench::workload_source(cfg).unwrap_or_else(|| "(source not found)".into());
    let required = opts.threshold.max(current.noise());
    let size_required = size_threshold(opts);
    let mut p = format!(
        "You are the OPTIMIZER in a Djinn-on-Aeneas project. The implementation in `{sol}/` is \
already verified against the specification in `{spec}` (read-only). Your job is to make it {goal} on \
the performance workload below while keeping it verified. Nothing else counts.\n\n\
Read `GUIDE.md` (in this directory) first; the editing rules are the same as for implementing: edit only \
`{sol}/` and `{proofs}/{ns}/Proofs.lean` (helpers under `{proofs}/{ns}/Proofs/`). The specification, \
`Cargo.toml`, and the workload are read-only; edits to them are discarded.\n\n\
## The workload (`{w}`)\n\n```rust\n{source}\n```\n\n\
## Current timing\n\n{timing}\n\n\
## Acceptance\n\n\
Your version is kept only if (1) the `verify` tool prints PASS — so when you change the Rust, re-prove \
`impl_correct` for whatever changed (the Aeneas model of your new code appears in `{proofs}/{ns}/Code/` \
after a `verify`) — and (2) {rule} Otherwise your \
changes are reverted. Measure your jail copy with `./bench` (same method: release build, at least \
{min:.0} s of iterations per point){tableinfo}.\n\n\
Approach: profile mentally first — what dominates the workload? Prefer algorithmic improvements \
(better complexity, fewer passes, no redundant work) over micro-tuning; keep to safe Rust that Aeneas \
can model (index loops, scalars; see the guide's Rust section). A faster algorithm usually needs a new \
loop invariant: budget for the proof.\n\n\
When `verify` prints PASS and `./bench` shows a gain, stop. Your FINAL message must summarize exactly what \
you changed and why, and the timing you observed: it becomes the history shown to later attempts.\n",
        spec = cfg.specs_display(),
        ns = cfg.ns,
        sol = cfg.sol_rel(),
        proofs = cfg.proofs_rel(),
        goal = if current.is_multi() { "BETTER — faster at every compression ratio, or denser at every speed" } else { "FASTER" },
        timing = if current.is_multi() { format!("{}\n\n```\n{}```", current.line(), current.table()) } else { current.line() },
        rule = if current.is_multi() {
            format!(
                "the trade-off curve improves, judged as lean-zip judges codecs: every point is (size, time); \
the achievable frontier is the lower convex hull of the points (mixing two adjacent points reaches the \
segment between them); your frontier must be nowhere above the current one — at every current size, your \
time at that size (interpolated) is not more than {pct:.1}% worse, the smallest size is still reached, the \
fastest point is not slower — and better somewhere: at least {pct:.1}% faster at some current size, or at \
least {spct:.1}% smaller at some current time. Sizes are exact; times carry noise ({thr:.0}% threshold, or \
the measured noise if larger). The point labels mean nothing to the rule: a level may change what it does, \
as long as the curve improves. Making a level faster by compressing less is accepted only if the curve as \
a whole does not suffer.",
                pct = required * 100.0,
                spct = size_required * 100.0,
                thr = opts.threshold * 100.0
            )
        } else {
            format!(
                "the workload runs at least {pct:.1}% faster than the current timing on a re-measurement by the \
harness ({thr:.0}% threshold, or the measured noise if larger).",
                pct = required * 100.0,
                thr = opts.threshold * 100.0
            )
        },
        tableinfo = if current.is_multi() { "; it prints the per-point table (size and time per point)" } else { "; it prints nanoseconds per workload iteration" },
        min = opts.min_time,
    );
    if !log.attempts.is_empty() {
        p.push_str("\n## Earlier attempts (do not repeat what failed)\n\n");
        for a in &log.attempts {
            let t = a.ns.map(|n| format!(" — measured {}", fmt_ns(n))).unwrap_or_default();
            p.push_str(&format!("- attempt {}: {}{}\n  tried: {}\n", a.cycle, a.verdict, t, a.summary.replace('\n', " ")));
        }
        p.push_str(&format!("\nBaseline before any attempt: {}.\n", fmt_ns(log.baseline_ns)));
    }
    if let Some(e) = extra {
        p.push_str("\nAdditional instructions from the human:\n");
        p.push_str(e);
        p.push('\n');
    }
    p
}

/// The relative size gain that counts as an improvement on its own: sizes are
/// exact, so a sixth of the time threshold (0.5% at the default 3%).
fn size_threshold(opts: &OptOpts) -> f64 {
    (opts.threshold / 6.0).max(0.001)
}

// -------------------------------------------------------------------- loop

pub fn optimize(cfg: &Config, opts: OptOpts, bin: &Path) -> Result<bool, String> {
    crate::agent::ensure_no_running_job(cfg)?;
    bench::workload_path(cfg)?;
    // Ctrl-C: stop the agent, restore the checkpoint
    let stop = Arc::new(AtomicBool::new(false));
    {
        let stop = stop.clone();
        ctrlc::set_handler(move || {
            eprintln!("\n^C — finishing the current step, then reverting to the last known-good checkpoint");
            stop.store(true, Ordering::SeqCst);
        })
        .map_err(|e| format!("cannot install the Ctrl-C handler: {e}"))?;
    }
    let mut say = |s: &str| eprintln!("{s}");

    // 1. the gate
    eprintln!("== optimize: confirming the implementation and proofs");
    let r = verify::verify(cfg, None, &mut Log::new(false));
    if !r.pass {
        return Err(format!("nothing to optimize: verify FAILs at {} — run `cargo djinn implement` first", r.stage));
    }
    checkpoint(cfg)?;
    // 2. baseline
    let baseline = bench::measure(cfg, opts.min_time, opts.batches, opts.jobs, &mut say)?;
    let mut log = OptimizeLog {
        started: now(),
        baseline_ns: baseline.median_ns,
        current_ns: baseline.median_ns,
        baseline_points: point_list(&baseline),
        current_points: point_list(&baseline),
        ..Default::default()
    };
    log.save(cfg);
    let mut current = baseline.clone();
    eprintln!("baseline: {}", current.line());

    let mut cycle = 0usize;
    loop {
        if stop.load(Ordering::SeqCst) {
            log.interrupted = true;
            break;
        }
        if let Some(n) = opts.cycles {
            if cycle >= n {
                break;
            }
        }
        if let Some(limit) = opts.agent.limit_usd {
            if log.spent_usd >= limit {
                eprintln!("== spending limit reached (${:.2} of ${limit:.2})", log.spent_usd);
                break;
            }
        }
        if opts.cycles.is_none() && opts.agent.limit_usd.is_none() {
            return Err("give --cycles N and/or --limit USD".into());
        }
        cycle += 1;
        eprintln!("\n== cycle {cycle}{}: current {}", opts.cycles.map(|n| format!(" of {n}")).unwrap_or_default(), fmt_ns(current.median_ns));
        let mut agent_opts = Opts {
            agent: opts.agent.agent,
            model: opts.agent.model.clone(),
            yolo: opts.agent.yolo,
            background: false,
            extra_prompt: None,
            max_budget_usd: None,
            effort: opts.agent.effort.clone(),
            extra_args: opts.agent.extra_args.clone(),
            limit_usd: opts.agent.limit_usd.map(|l| (l - log.spent_usd).max(0.5)),
            from_scratch: false,
        };
        if agent_opts.limit_usd.is_some() {
            agent_opts.max_budget_usd = agent_opts.limit_usd.map(|l| format!("{l:.2}"));
        }
        let text = prompt(cfg, &opts, &current, &log, opts.agent.extra_prompt.as_deref());
        let run = agent::run_foreground(cfg, &agent_opts, &text, bin, &stop, &format!("opt{cycle}"))?;
        let cost = run.usage.cost_usd.or(run.usage.est_cost_usd);
        log.spent_usd += cost.unwrap_or(0.0);
        let mut attempt = Attempt {
            cycle,
            job: run.job.id.clone(),
            verdict: String::new(),
            ns: None,
            points: Vec::new(),
            summary: run.usage.last_message.chars().take(1200).collect(),
            cost_usd: cost,
            cost_is_estimate: run.usage.cost_usd.is_none(),
            tokens_in: run.usage.input_tokens,
            tokens_out: run.usage.output_tokens,
            elapsed_secs: status::job_elapsed(&run.job),
        };
        if run.interrupted {
            attempt.verdict = "interrupted".into();
            log.attempts.push(attempt);
            log.interrupted = true;
            revert(cfg, "interrupted")?;
            break;
        }
        // (1) it must verify, with the agent's files synced from its jail
        let r = verify::verify(cfg, Some(&run.job.jail), &mut Log::new(false));
        if !r.pass {
            attempt.verdict = format!("did not verify (stage: {})", r.stage);
            eprintln!("cycle {cycle}: {}", attempt.verdict);
            log.attempts.push(attempt);
            log.save(cfg);
            revert(cfg, "verification failed")?;
            continue;
        }
        // (2) it must be better beyond noise and threshold: faster, or for a
        // multi-point workload a better trade-off curve
        let m = bench::measure(cfg, opts.min_time, opts.batches, opts.jobs, &mut say)?;
        attempt.ns = Some(m.median_ns);
        attempt.points = point_list(&m);
        let required = opts.threshold.max(current.noise()).max(m.noise());
        let verdict = if m.is_multi() {
            frontier_verdict(&current, &m, required, size_threshold(&opts))
        } else {
            let improvement = 1.0 - m.median_ns / current.median_ns;
            if improvement >= required {
                Ok(improvement)
            } else {
                Err(format!("not faster ({:+.1}%, needed {:.1}%)", improvement * 100.0, required * 100.0))
            }
        };
        match verdict {
            Ok(improvement) => {
                attempt.verdict = format!("accepted ({:.1}% better)", improvement * 100.0);
                eprintln!("cycle {cycle}: ACCEPTED — {} → {} ({:.1}% better)", fmt_ns(current.median_ns), fmt_ns(m.median_ns), improvement * 100.0);
                current = m;
                log.current_ns = current.median_ns;
                log.current_points = point_list(&current);
                log.accepted += 1;
                log.attempts.push(attempt);
                log.save(cfg);
                checkpoint(cfg)?;
            }
            Err(why) => {
                attempt.verdict = why;
                eprintln!("cycle {cycle}: {} — reverting", attempt.verdict);
                log.attempts.push(attempt);
                log.save(cfg);
                revert(cfg, "not better")?;
            }
        }
    }
    log.finished = Some(now());
    log.save(cfg);
    // report
    eprintln!("\n{:<6} {:<34} {:>12} {:>9} {:>10} {:>8}", "cycle", "verdict", "time/iter", "speedup", "cost", "wall");
    for a in &log.attempts {
        eprintln!(
            "{:<6} {:<34} {:>12} {:>9} {:>10} {:>8}",
            a.cycle,
            a.verdict.chars().take(34).collect::<String>(),
            a.ns.map(fmt_ns).unwrap_or("—".into()),
            a.ns.map(|n| format!("{:.2}×", log.baseline_ns / n)).unwrap_or("—".into()),
            a.cost_usd.map(|c| format!("{}${c:.2}", if a.cost_is_estimate { "~" } else { "" })).unwrap_or("n/a".into()),
            format!("{}m{:02}s", a.elapsed_secs / 60, a.elapsed_secs % 60)
        );
    }
    eprintln!("{}", log.summary_line());
    Ok(log.accepted > 0)
}
