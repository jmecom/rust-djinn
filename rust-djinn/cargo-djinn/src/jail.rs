//! The jail: a working copy of the crate for an agent, in which only the
//! LLM-owned paths are ever taken back into the real crate.
//!
//! Owned paths: `<work_dir>/solution/**`, `<proofs>/<NS>/Proofs.lean`,
//! `<proofs>/<NS>/Proofs/**`. The jail mirrors the crate's layout (so that
//! `#[path = "../djinn/solution/mod.rs"]` resolves in it too). Everything
//! else in the jail is a convenience copy;
//! the verifier regenerates the trusted files from the real specification and
//! pushes them into the jail after every run.

use crate::config::*;
use std::fs;
use std::path::{Path, PathBuf};

pub fn jails_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("jails")
}

/// The jail's copy of the solution directory (same relative path as in the crate).
pub fn sol_in(cfg: &Config, jail: &Path) -> PathBuf {
    jail.join(cfg.sol_rel())
}

/// The jail's copy of the Lean project.
pub fn proofs_in(cfg: &Config, jail: &Path) -> PathBuf {
    jail.join(cfg.proofs_rel())
}

mod safe_fs;
use safe_fs::Dir;

fn relative(cfg: &Config, path: &Path) -> Result<PathBuf, String> {
    let rel = path.strip_prefix(&cfg.crate_dir).map_err(|_| format!("mirrored path must be inside the crate: {}", path.display()))?;
    validate_relative_path(rel, "mirrored path")?;
    Ok(rel.to_owned())
}

fn validate_layout(cfg: &Config) -> Result<(), String> {
    relative(cfg, &cfg.solution_dir())?;
    relative(cfg, &cfg.proofs)?;
    validate_relative_path(Path::new(&cfg.ns), "namespace")?;
    if Path::new(&cfg.ns).components().count() != 1 {
        return Err("namespace must be a single path component".into());
    }
    let sol = cfg.solution_dir();
    if sol.starts_with(&cfg.proofs) || cfg.proofs.starts_with(&sol)
        || sol.starts_with(cfg.state_dir()) || cfg.proofs.starts_with(cfg.state_dir()) {
        return Err("solution, proofs, and scratch directories must not overlap".into());
    }
    for spec in cfg.specs() { relative(cfg, &spec.path)?; }
    Ok(())
}

fn roots(cfg: &Config, jail: &Path) -> Result<(Dir, Dir), String> {
    validate_layout(cfg)?;
    let jail = jail.canonicalize().map_err(|e| format!("{}: {e}", jail.display()))?;
    let real = cfg.crate_dir.canonicalize().map_err(|e| e.to_string())?;
    if real.starts_with(&jail) || jail.starts_with(cfg.solution_dir()) || jail.starts_with(&cfg.proofs) {
        return Err("jail must be distinct from the crate and its solution/proofs directories".into());
    }
    Ok((Dir::open(&real).map_err(|e| e.to_string())?, Dir::open(&jail).map_err(|e| e.to_string())?))
}

fn sh_quote(path: &Path) -> String {
    crate::agent::sh_quote(&path.to_string_lossy())
}

/// Reserve an archive atomically, and move all owned paths before creating a
/// fresh stub. If any move fails, undo the preceding moves in reverse order.
pub(crate) fn archive_work(cfg: &Config) -> Result<PathBuf, String> {
    validate_layout(cfg)?;
    let root = Dir::open(&cfg.crate_dir).map_err(|e| e.to_string())?;
    let backup_root = relative(cfg, &cfg.state_dir().join("backup"))?;
    let backup = (0u64..).find_map(|n| {
        let time = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
        let path = backup_root.join(format!("{}-{:09}-{}-{n:020}", id_time(time.as_secs()), time.subsec_nanos(), std::process::id()));
        match root.create_dir(&path) {
            Ok(()) => Some(Ok(path)),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => None,
            Err(e) => Some(Err(e.to_string())),
        }
    }).unwrap()?;
    let sol = relative(cfg, &cfg.solution_dir())?;
    let lean = relative(cfg, &cfg.lean_dir())?;
    let paths = [(sol.clone(), "solution"), (lean.join("Proofs.lean"), "Proofs.lean"), (lean.join("Proofs"), "Proofs")];
    let mut moved: Vec<(PathBuf, PathBuf)> = Vec::new();
    let result = (|| {
        for (path, name) in paths {
            if root.exists(&path).map_err(|e| e.to_string())? {
                let dest = backup.join(name);
                root.move_path(&path, &dest).map_err(|e| format!("cannot archive {}: {e}", path.display()))?;
                moved.push((path, dest));
            }
        }
        root.write(&sol.join("mod.rs"), b"//! LLM-owned.\n".as_slice(), 0o644).map_err(|e| e.to_string())
    })();
    if let Err(error) = result {
        let mut failures = Vec::new();
        // Only a newly created stub directory may be removed here. If the
        // solution move itself failed, the original is still in place.
        if moved.iter().any(|(path, _)| path == &sol) {
            if let Err(e) = root.remove(&sol) { failures.push(e.to_string()); }
        }
        for (path, dest) in moved.into_iter().rev() {
            if let Err(e) = root.move_path(&dest, &path) { failures.push(format!("{}: {e}", path.display())); }
        }
        if failures.is_empty() {
            let _ = root.remove(&backup);
            return Err(error);
        }
        return Err(format!("{error}; rollback failed: {}; retained archive: {}", failures.join("; "), cfg.crate_dir.join(&backup).display()));
    }
    for path in [lean.join("Code"), relative(cfg, &cfg.translation_path())?, relative(cfg, &crate::verify::Report::path(cfg))?] {
        root.remove(&path).map_err(|e| format!("archived work to {}, but cannot remove {}: {e}", cfg.crate_dir.join(&backup).display(), path.display()))?;
    }
    Ok(cfg.crate_dir.join(backup))
}

/// Cargo.toml for the jail: path dependencies and tool paths made absolute.
fn jail_cargo_toml(cfg: &Config) -> Result<String, String> {
    let text = fs::read_to_string(cfg.crate_dir.join("Cargo.toml")).map_err(|e| e.to_string())?;
    let mut doc: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    fn absolutize(v: &mut toml::Value, base: &Path) {
        if let Some(s) = v.as_str() {
            if !s.starts_with('/') {
                if let Ok(p) = base.join(s).canonicalize() {
                    *v = toml::Value::String(p.to_string_lossy().into_owned());
                }
            }
        } else if let Some(a) = v.as_array_mut() {
            // `spec = ["src/a.rs", …]`
            a.iter_mut().for_each(|x| absolutize(x, base));
        }
    }
    for sec in ["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(deps) = doc.get_mut(sec).and_then(|d| d.as_table_mut()) {
            for (_, dep) in deps.iter_mut() {
                if let Some(p) = dep.get_mut("path") {
                    absolutize(p, &cfg.crate_dir);
                }
            }
        }
    }
    if let Some(meta) = doc.get_mut("package").and_then(|p| p.get_mut("metadata")).and_then(|m| m.get_mut("djinn")).and_then(|d| d.as_table_mut()) {
        for k in ["charon", "aeneas", "spec", "lake_packages"] {
            if let Some(v) = meta.get_mut(k) {
                absolutize(v, &cfg.crate_dir);
            }
        }
        if let Some(v) = meta.get_mut("aeneas_lean") {
            absolutize(v, &cfg.proofs);
        }
        // the agent's own `cargo build` is exempt from the compile-time gate
        meta.insert("in_jail".into(), toml::Value::Boolean(true));
    }
    toml::to_string(&doc).map_err(|e| e.to_string())
}

/// Create a fresh jail for an agent run. Returns its directory.
pub fn create(cfg: &Config, id: &str, bin: &Path) -> Result<PathBuf, String> {
    validate_layout(cfg)?;
    validate_relative_path(Path::new(id), "jail identifier")?;
    if Path::new(id).components().count() != 1 {
        return Err("jail identifier must be a single path component".into());
    }
    let dir = jails_dir(cfg).join(id);
    let real = Dir::open(&cfg.crate_dir).map_err(|e| e.to_string())?;
    real.create_dir(&relative(cfg, &dir)?).map_err(|e| format!("{}: {e}", dir.display()))?;
    let jail = real.subdir(&relative(cfg, &dir)?, false).map_err(|e| e.to_string())?;
    jail.write(Path::new("Cargo.toml"), jail_cargo_toml(cfg)?.as_bytes(), 0o644).map_err(|e| e.to_string())?;
    jail.copy_tree(&real, Path::new("src")).map_err(|e| e.to_string())?;
    let sol = relative(cfg, &cfg.solution_dir())?;
    if real.exists(&sol).map_err(|e| e.to_string())? {
        jail.copy_tree(&real, &sol).map_err(|e| e.to_string())?;
    }
    jail.subdir(&sol, true).map_err(|e| e.to_string())?;
    let proofs = relative(cfg, &cfg.proofs)?;
    jail.copy_tree(&real, &proofs).map_err(|e| e.to_string())?;
    let packages = cfg.proofs.join(".lake/packages");
    if let Ok(packages) = packages.canonicalize() {
        jail.symlink(&packages, &proofs.join(".lake/packages")).map_err(|e| e.to_string())?;
    }
    if let Some(al) = &cfg.aeneas_lean {
        if let Ok(abs) = cfg.proofs.join(al).canonicalize() {
            for name in ["lakefile.lean", "lake-manifest.json"] {
                let path = proofs.join(name);
                if let Ok(bytes) = jail.read(&path) {
                    let text = String::from_utf8(bytes).map_err(|e| e.to_string())?;
                    let text = text.replace(&format!("\"{al}\""), &format!("\"{}\"", abs.display()));
                    jail.write(&path, text.as_bytes(), 0o644).map_err(|e| e.to_string())?;
                }
            }
        }
    }
    // tools for the agent
    let bin = bin.canonicalize().map_err(|e| e.to_string())?;
    let manifest = cfg.crate_dir.join("Cargo.toml");
    let script = |cmd: &str| {
        format!(
            "#!/bin/sh\n# {cmd} the real crate from this jail (only the solution directory and Proofs.lean are taken back).\nexec {} {cmd} --jail {} --manifest-path {} \"$@\"\n",
            sh_quote(&bin),
            sh_quote(&dir),
            sh_quote(&manifest)
        )
    };
    for cmd in ["verify", "status"] {
        jail.write(Path::new(cmd), script(cmd).as_bytes(), 0o755).map_err(|e| e.to_string())?;
    }
    let bench = format!("#!/bin/sh\n# time this jail's performance workload\nexec {} bench --manifest-path {} \"$@\"\n", sh_quote(&bin), sh_quote(&dir.join("Cargo.toml")));
    jail.write(Path::new("bench"), bench.as_bytes(), 0o755).map_err(|e| e.to_string())?;
    let mcp = serde_json::json!({
        "mcpServers": {
            "djinn": {
                "command": bin.to_string_lossy(),
                "args": ["mcp", "--jail", dir.to_string_lossy(), "--manifest-path", manifest.to_string_lossy()]
            }
        }
    });
    jail.write(Path::new(".mcp.json"), serde_json::to_string_pretty(&mcp).unwrap().as_bytes(), 0o644).map_err(|e| e.to_string())?;
    let pointer = format!(
        "# Djinn jail\n\nRead `GUIDE.md` (this directory) before doing anything else. You may edit only\n`{sol}/` and `{p}/{ns}/Proofs.lean` (plus helper files under\n`{p}/{ns}/Proofs/`). Everything else is regenerated by the verifier and\nedits to it are discarded. Judge your work with the `verify` tool\n(MCP server `djinn`), or `./verify` from this directory.\n",
        ns = cfg.ns,
        sol = cfg.sol_rel(),
        p = cfg.proofs_rel()
    );
    for name in ["CLAUDE.md", "AGENTS.md"] {
        jail.write(Path::new(name), pointer.as_bytes(), 0o444).map_err(|e| e.to_string())?;
    }
    sync_forward(cfg, &dir)?;
    Ok(dir)
}

/// Take the LLM-owned paths from the jail into the real crate.
pub fn sync_back(cfg: &Config, jail: &Path) -> Result<Vec<String>, String> {
    let (real, jailed) = roots(cfg, jail)?;
    let mut notes = Vec::new();
    let sol = relative(cfg, &cfg.solution_dir())?;
    if jailed.exists(&sol).map_err(|e| e.to_string())? {
        real.mirror_tree(&jailed, &sol, false).map_err(|e| format!("cannot sync solution: {e}"))?;
        notes.push(format!("synced {} from the jail", cfg.sol_rel()));
    }
    let lean = relative(cfg, &cfg.lean_dir())?;
    let proofs = lean.join("Proofs.lean");
    if jailed.exists(&proofs).map_err(|e| e.to_string())? {
        real.copy_file(&jailed, &proofs, &proofs, false).map_err(|e| e.to_string())?;
        notes.push(format!("synced {}/{}/Proofs.lean from the jail", cfg.proofs_rel(), cfg.ns));
    }
    let helpers = lean.join("Proofs");
    if jailed.exists(&helpers).map_err(|e| e.to_string())? {
        real.mirror_tree(&jailed, &helpers, false).map_err(|e| e.to_string())?;
        notes.push(format!("synced {}/{}/Proofs/ from the jail", cfg.proofs_rel(), cfg.ns));
    }
    // anything else the agent touched is ignored; say so for the spec
    for f in cfg.specs() {
        let path = relative(cfg, &f.path)?;
        if let (Ok(a), Ok(b)) = (jailed.read(&path), real.read(&path)) {
            if a != b {
                notes.push(format!("WARNING: the specification file {} in the jail was modified; the change is ignored and the file restored", cfg.rel(&f.path)));
            }
        }
    }
    Ok(notes)
}

/// Push the trusted, regenerated files into the jail.
pub fn sync_forward(cfg: &Config, jail: &Path) -> Result<(), String> {
    let (real, jailed) = roots(cfg, jail)?;
    let lean = relative(cfg, &cfg.lean_dir())?;
    for name in ["Spec.lean", "Obligations.lean", "Audit.lean"] {
        let path = lean.join(name);
        if real.exists(&path).map_err(|e| e.to_string())? {
            jailed.copy_file(&real, &path, &path, true).map_err(|e| format!("cannot refresh {}: {e}", path.display()))?;
        }
    }
    let code = lean.join("Code");
    if real.exists(&code).map_err(|e| e.to_string())? {
        jailed.mirror_tree(&real, &code, true).map_err(|e| e.to_string())?;
    }
    for (source, dest) in [(cfg.guide_path(), "GUIDE.md"), (cfg.translation_path(), "translation.json")] {
        let source = relative(cfg, &source)?;
        if real.exists(&source).map_err(|e| e.to_string())? {
            jailed.copy_file(&real, &source, Path::new(dest), true).map_err(|e| e.to_string())?;
        } else {
            jailed.remove(Path::new(dest)).map_err(|e| e.to_string())?;
        }
    }
    let build = relative(cfg, &cfg.proofs)?.join(".lake/build");
    if real.exists(&build).map_err(|e| e.to_string())? {
        jailed.mirror_tree(&real, &build, false).map_err(|e| e.to_string())?;
    }
    for f in cfg.specs() {
        let path = relative(cfg, &f.path)?;
        jailed.copy_file(&real, &path, &path, true).map_err(|e| e.to_string())?;
    }
    Ok(())
}
