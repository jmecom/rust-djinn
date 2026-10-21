//! Compile proof inputs in isolation, then check declaration data in a process
//! which never executes candidate initializers, elaborators or native plugins.

use crate::config::Config;
use crate::verify::Log;
use djinn_syntax::emit::{self, EmitCx};
use djinn_syntax::lower::Lowered;
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const CHECKER: &str = include_str!("ProofChecker.lean");
static NEXT_RUN: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Result<Self, String> {
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "djinn-proof-{}-{}-{}", std::process::id(), crate::config::now(),
                NEXT_RUN.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => {
                    #[cfg(unix)] {
                        use std::os::unix::fs::PermissionsExt;
                        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
                    }
                    return Ok(Self(path.canonicalize().map_err(|e| e.to_string())?));
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(format!("cannot create isolated proof directory: {e}")),
            }
        }
        Err("cannot allocate isolated proof directory".into())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); }
}

fn run(cmd: &mut Command, what: &str, log: &mut Log) -> Result<String, String> {
    let out = cmd.output().map_err(|e| format!("{what}: {e}"))?;
    let stdout = String::from_utf8(out.stdout).map_err(|e| format!("{what}: invalid UTF-8: {e}"))?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        return Err(format!("{what} failed ({}):\n{stdout}{stderr}", out.status));
    }
    if !stderr.trim().is_empty() { log.line(stderr.trim_end()); }
    Ok(stdout)
}

/// Every child inherits the confinement. No fallback runs untrusted Lean on
/// the host if the OS facility is missing or the policy cannot be installed.
fn confined(cmd: &Command, reads: &[PathBuf], writes: &[PathBuf], children: bool) -> Result<Command, String> {
    #[cfg(target_os = "macos")]
    let mut sandbox = {
        let quoted = |p: &Path| -> Result<String, String> {
            let s = p.to_str().ok_or("sandbox paths must be UTF-8")?;
            Ok(format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
        };
        let mut policy = String::from("(version 1) (deny default) (allow process-exec) (allow sysctl-read) (allow file-read-metadata) ");
        if children { policy.push_str("(allow process-fork) "); }
        policy.push_str("(allow file-read* (literal \"/\") ");
        for p in reads {
            policy.push_str(&format!("(subpath {}) ", quoted(p)?));
        }
        for p in ["/System", "/usr", "/bin", "/sbin", "/dev", "/private/var/db/dyld"] {
            policy.push_str(&format!("(subpath \"{p}\") "));
        }
        policy.push_str(") (allow file-write* (literal \"/dev/null\") ");
        for p in writes { policy.push_str(&format!("(subpath {}) ", quoted(p)?)); }
        policy.push(')');
        let mut c = Command::new("/usr/bin/sandbox-exec");
        c.args(["-p", &policy]);
        c
    };
    #[cfg(target_os = "linux")]
    let mut sandbox = {
        let _ = children;
        let mut c = Command::new("bwrap");
        c.args(["--unshare-all", "--die-with-parent", "--new-session"]);
        for p in ["/usr", "/bin", "/sbin", "/lib", "/lib64", "/etc/ld.so.cache"] {
            if Path::new(p).exists() { c.args(["--ro-bind", p, p]); }
        }
        c.args(["--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]);
        for p in reads { c.arg("--ro-bind").arg(p).arg(p); }
        for p in writes { c.arg("--bind").arg(p).arg(p); }
        c.arg("--");
        c
    };
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    return Err("proof verification requires macOS sandbox-exec or Linux bubblewrap; refusing unconfined execution".into());
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        // Candidate code must not inherit host credentials through environment
        // variables. Only trusted toolchain configuration needs the caller's
        // environment; direct Lean compilation/checking gets a small explicit one.
        sandbox.env_clear();
        if children { sandbox.envs(std::env::vars_os()); }
        else { sandbox.env("PATH", "/usr/bin:/bin"); }
        sandbox.arg(cmd.get_program()).args(cmd.get_args());
        if let Some(dir) = cmd.get_current_dir() { sandbox.current_dir(dir); }
        for (k, v) in cmd.get_envs() {
            match v { Some(v) => { sandbox.env(k, v); }, None => { sandbox.env_remove(k); } }
        }
        Ok(sandbox)
    }
}

fn copy_sources(from: &Path, to: &Path) -> Result<(), String> {
    fs::create_dir_all(to).map_err(|e| e.to_string())?;
    for entry in fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))? {
        let entry = entry.map_err(|e| e.to_string())?;
        let kind = entry.file_type().map_err(|e| e.to_string())?;
        if kind.is_symlink() { return Err(format!("proof sources must not contain symlinks: {}", entry.path().display())); }
        if kind.is_dir() {
            copy_sources(&entry.path(), &to.join(entry.file_name()))?;
        } else if kind.is_file() && entry.path().extension().is_some_and(|e| e == "lean") {
            fs::copy(entry.path(), to.join(entry.file_name())).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

fn expected_source(cx: &EmitCx, lowered: &[Lowered]) -> (String, Vec<String>) {
    let mut source = format!("import {}.Spec\n{}\nopen Aeneas Std\nopen {}.Spec\nnamespace {}.Expected\n", cx.ns, emit::code_import(cx), cx.ns, cx.ns);
    let mut names = Vec::new();
    for d in lowered {
        for o in emit::obligations(cx, d) {
            source.push_str(&format!("axiom {} :\n  {}\n", o.name, o.statement));
            names.push(o.name);
        }
    }
    source.push_str(&format!("end {}.Expected\n", cx.ns));
    (source, names)
}

struct Builder<'a> {
    namespace: String,
    lean: PathBuf,
    source: PathBuf,
    artifacts: PathBuf,
    outputs: PathBuf,
    temp: PathBuf,
    search: std::ffi::OsString,
    reads: Vec<PathBuf>,
    built: BTreeSet<PathBuf>,
    visiting: BTreeSet<PathBuf>,
    trusted: bool,
    log: &'a mut Log,
}

impl Builder<'_> {
    fn command(&self) -> Command {
        let mut c = Command::new(&self.lean);
        c.current_dir(&self.source).env("LEAN_PATH", &self.search).env("TMPDIR", &self.temp).env("TMP", &self.temp).env("TEMP", &self.temp).env("HOME", &self.temp);
        c
    }

    fn build(&mut self, relative: &Path) -> Result<(), String> {
        if self.built.contains(relative) { return Ok(()); }
        if !self.visiting.insert(relative.to_path_buf()) { return Err(format!("cyclic Lean imports: {}", relative.display())); }
        let namespace = Path::new(&self.namespace);
        let generated = ["Expected.lean", "Spec.lean", "Vocab.lean"].iter().any(|file| relative == namespace.join(file))
            || relative.starts_with(namespace.join("Code"));
        if self.trusted && !generated {
            return Err(format!("trusted specification imports an untrusted module: {}", relative.display()));
        }
        let source = self.source.join(relative);
        if !source.is_file() { return Err(format!("missing Lean source: {}", relative.display())); }
        let mut deps = self.command();
        deps.arg("--deps").arg(&source);
        let output = run(&mut confined(&deps, &self.reads, &[], false)?, "Lean dependency discovery", self.log)?;
        for line in output.lines().filter(|s| !s.trim().is_empty()) {
            let dependency = Path::new(line);
            if let Ok(rel) = dependency.strip_prefix(&self.artifacts) {
                self.build(&rel.with_extension("lean"))?;
            } else if !dependency.is_file() {
                return Err(format!("missing compiled Lean dependency {line}; build the trusted Lean dependencies first"));
            }
        }
        // Only this disposable output directory is writable. Imported artifacts
        // and source snapshots remain read-only, even to #eval and initializers.
        let output = self.outputs.join(self.built.len().to_string());
        fs::create_dir(&output).map_err(|e| e.to_string())?;
        let mut command = self.command();
        command.arg("-o").arg(output.join("module.olean")).arg(&source);
        let text = run(&mut confined(&command, &self.reads, &[output.clone(), self.temp.clone()], false)?, &format!("Lean {}", relative.display()), self.log)?;
        if !text.trim().is_empty() { self.log.line(text.trim_end()); }
        let target = self.artifacts.join(relative).with_extension("olean");
        fs::create_dir_all(target.parent().unwrap()).map_err(|e| e.to_string())?;
        for extension in ["olean", "olean.server", "olean.private", "ir"] {
            let produced = output.join(format!("module.{extension}"));
            if let Ok(metadata) = fs::symlink_metadata(&produced) {
                if !metadata.is_file() { return Err("Lean output is not a regular file".into()); }
                fs::copy(&produced, self.artifacts.join(relative).with_extension(extension)).map_err(|e| e.to_string())?;
            } else if extension == "olean" { return Err("Lean succeeded without producing its required artifact".into()); }
        }
        self.visiting.remove(relative);
        self.built.insert(relative.to_path_buf());
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuditRow { name: String, axioms: Vec<String> }

fn audit_results(text: &str, expected: &[String]) -> Result<BTreeMap<String, String>, String> {
    let rows: Vec<AuditRow> = serde_json::from_str(text).map_err(|e| format!("invalid trusted checker output: {e}"))?;
    let mut results = BTreeMap::new();
    for row in rows {
        if !expected.contains(&row.name) || results.contains_key(&row.name) { return Err(format!("unexpected or repeated audit declaration {}", row.name)); }
        let extra: Vec<_> = row.axioms.iter().filter(|a| !["propext", "Classical.choice", "Quot.sound"].contains(&a.as_str())).cloned().collect();
        let status = if extra.is_empty() { "proved".to_string() } else if extra.iter().any(|a| a == "sorryAx") { "sorry".to_string() } else { format!("axiom:{}", extra.join(",")) };
        results.insert(row.name, status);
    }
    if results.len() != expected.len() { return Err("trusted checker omitted a required obligation".into()); }
    Ok(results)
}

pub fn check(cfg: &Config, cx: &EmitCx, lowered: &[Lowered], log: &mut Log) -> Result<BTreeMap<String, String>, String> {
    let scratch = Scratch::new()?;
    let source = scratch.0.join("source");
    let artifacts = scratch.0.join("artifacts");
    let outputs = scratch.0.join("outputs");
    let temp = scratch.0.join("tmp");
    for dir in [&source, &artifacts, &outputs, &temp] { fs::create_dir(dir).map_err(|e| e.to_string())?; }
    copy_sources(&cfg.lean_dir(), &source.join(&cfg.ns))?;
    fs::create_dir(artifacts.join(&cfg.ns)).map_err(|e| e.to_string())?;
    let (expected, names) = expected_source(cx, lowered);
    fs::write(source.join(&cfg.ns).join("Expected.lean"), expected).map_err(|e| e.to_string())?;
    let checker = scratch.0.join("ProofChecker.lean");
    fs::write(&checker, CHECKER).map_err(|e| e.to_string())?;
    // Only the configured, trusted Aeneas installation supplies dependencies.
    // A project lakefile is executable code and cannot choose the audit's TCB.
    let backend = cfg.aeneas_lean.as_ref().ok_or("secure verification requires aeneas_lean or DJINN_AENEAS_LEAN naming the built, trusted Aeneas Lean backend")?;
    let backend = cfg.proofs.join(backend).canonicalize().map_err(|e| format!("trusted Aeneas Lean backend: {e}"))?;
    if !backend.join("Aeneas.lean").is_file() { return Err("configured Aeneas Lean backend has no Aeneas.lean".into()); }
    let mut env_command = Command::new("lake");
    env_command.args(["env", "printenv", "LEAN_PATH"]).current_dir(&backend).env_remove("LEAN_PATH").env_remove("LEAN_SRC_PATH");
    // Toolchain configuration may reference packages anywhere, but is executed
    // with no filesystem writes. Bootstrap dependencies outside verification.
    let env = run(&mut confined(&env_command, &[PathBuf::from("/")], &[], true)?, "trusted Lean dependency environment (build the Aeneas backend first if its cache is missing)", log)?;
    if env.trim().contains('\n') { return Err("Lake returned an ambiguous Lean search path".into()); }
    let prefix = run(Command::new("lean").arg("--print-prefix").current_dir(&backend), "Lean toolchain", log)?;
    let prefix = PathBuf::from(prefix.trim()).canonicalize().map_err(|e| format!("Lean toolchain: {e}"))?;
    let mut dependency_paths = Vec::new();
    for path in std::env::split_paths(env.trim()) {
        let path = if path.is_absolute() { path } else { backend.join(path) };
        if let Ok(path) = path.canonicalize() {
            // Never import stale or forged object files from the project cache.
            if !path.starts_with(&cfg.proofs) { dependency_paths.push(path); }
        }
    }
    let mut search_paths = vec![artifacts.clone()];
    search_paths.extend(dependency_paths.iter().cloned());
    let search = std::env::join_paths(&search_paths).map_err(|e| e.to_string())?;
    let mut reads = vec![scratch.0.clone(), prefix.clone()];
    reads.extend(dependency_paths.iter().map(|p| p.parent().unwrap_or(p).to_path_buf()));
    let mut builder = Builder { namespace: cfg.ns.clone(), lean: prefix.join("bin/lean"), source, artifacts, outputs, temp, search, reads, built: BTreeSet::new(), visiting: BTreeSet::new(), trusted: true, log };
    builder.log.line("== isolated Lean build and kernel audit");
    builder.build(&PathBuf::from(&cfg.ns).join("Expected.lean"))?;
    builder.trusted = false;
    builder.build(&PathBuf::from(&cfg.ns).join("Obligations.lean"))?;
    // The checker source sees only installed Lean during elaboration. Candidate
    // modules are loaded later as inert data by its main function.
    let mut command = Command::new(&builder.lean);
    command.env_remove("LEAN_PATH").current_dir(&scratch.0).arg("--run").arg(&checker).arg(&cfg.ns).arg(&builder.search).args(&names);
    let checked = run(&mut confined(&command, &builder.reads, &[], false)?, "trusted kernel audit", builder.log)?;
    audit_results(&checked, &names)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn audit_requires_exact_set_and_rejects_printing_tricks() {
        let names = vec!["f.impl_correct".to_string()];
        assert!(audit_results("[]", &names).is_err());
        assert!(audit_results(r#"[{"name":"f.impl_correct","axioms":[]},{"name":"f.impl_correct","axioms":[]}]"#, &names).is_err());
        assert!(audit_results(r#"[{"name":"wrong","axioms":[]}]"#, &names).is_err());
        let result = audit_results(r#"[{"name":"f.impl_correct","axioms":["does not depend on any axioms"]}]"#, &names).unwrap();
        assert_eq!(result[&names[0]], "axiom:does not depend on any axioms");
    }

    #[test]
    fn sandbox_allows_its_output_and_denies_host_writes() {
        if !cfg!(target_os = "macos") { return; }
        let scratch = Scratch::new().unwrap();
        let output = scratch.0.join("output");
        fs::create_dir(&output).unwrap();
        let outside = scratch.0.join("protected");
        let mut allowed = Command::new("/bin/sh");
        allowed.args(["-c", "printf ok > \"$1\"", "test"]).arg(output.join("ok")).current_dir(&scratch.0);
        assert!(confined(&allowed, std::slice::from_ref(&scratch.0), std::slice::from_ref(&output), false).unwrap().status().unwrap().success());
        let mut forbidden = Command::new("/bin/sh");
        forbidden.args(["-c", "printf wrong > \"$1\"", "test"]).arg(&outside).current_dir(&scratch.0);
        assert!(!confined(&forbidden, std::slice::from_ref(&scratch.0), &[output], false).unwrap().status().unwrap().success());
        assert!(!outside.exists());
        let private = Scratch::new().unwrap();
        fs::write(private.0.join("secret"), "not a proof input").unwrap();
        let mut read = Command::new("/bin/cat");
        read.arg(private.0.join("secret")).current_dir(&scratch.0);
        assert!(!confined(&read, std::slice::from_ref(&scratch.0), &[], false).unwrap().output().unwrap().status.success());
        let mut environment = Command::new("/usr/bin/printenv");
        environment.arg("HOME").current_dir(&scratch.0);
        assert!(!confined(&environment, &[scratch.0.clone()], &[], false).unwrap().output().unwrap().status.success());
    }
}
