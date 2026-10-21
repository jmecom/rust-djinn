//! `translate` and `verify`, producing a machine-readable report.

use crate::config::*;
use crate::jail;
use djinn_syntax::emit::{self, EmitCx};
use djinn_syntax::lower::Lowered;
use djinn_syntax::project::SpecFile;
use djinn_syntax::types::TypeNames;
use djinn_syntax::{Kind, Program};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::Path;
use std::process::Command;


/// Collects the verifier's output; echoes to stderr when running from a terminal.
pub struct Log {
    pub text: String,
    pub echo: bool,
}

impl Log {
    pub fn new(echo: bool) -> Self {
        Log { text: String::new(), echo }
    }
    pub fn line(&mut self, s: &str) {
        if self.echo {
            eprintln!("{s}");
        }
        self.text.push_str(s);
        self.text.push('\n');
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct DeclStatus {
    pub name: String,
    pub kind: String,
    pub implemented: bool,
    /// Full obligation names (`f.unambiguous`, …).
    pub obligations: Vec<String>,
    /// The declaration's tokens as verified (canonical text, see `project::canonical`).
    pub tokens: String,
    /// Declarations it mentions.
    pub uses: Vec<String>,
    /// Implemented (if a func) and every obligation of it and of what it uses proved.
    pub ok: bool,
    /// `#[weakly_specified]`: leaves choices to the implementer (or inherits
    /// them from a callee) — flagged for human review.
    #[serde(default)]
    pub weak: bool,
}

pub use djinn_syntax::project::solution_fns_in;

/// Names of functions defined in the crate's solution directory.
pub fn solution_fns(cfg: &Config) -> Vec<String> {
    solution_fns_in(&cfg.solution_dir())
}

/// The report file as written: `[run]` plus one `[[decl]]` per declaration.
#[derive(Serialize, Deserialize)]
struct ReportFile {
    run: RunEntry,
    #[serde(default)]
    certificate: Option<djinn_syntax::certificate::Certificate>,
    #[serde(default)]
    decl: Vec<DeclEntry>,
}

#[derive(Serialize, Deserialize)]
struct RunEntry {
    time: String,
    unix_time: u64,
    duration_secs: u64,
    pass: bool,
    stage: String,
    #[serde(default)]
    errors: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct DeclEntry {
    name: String,
    kind: String,
    implemented: bool,
    ok: bool,
    uses: Vec<String>,
    tokens: String,
    /// short obligation name → status
    obligations: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    weakly_specified: bool,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Report {
    /// Exact local inputs certified by this run; old reports are deliberately stale.
    #[serde(default)]
    pub certificate: Option<djinn_syntax::certificate::Certificate>,
    pub time: u64,
    pub duration_secs: u64,
    pub pass: bool,
    /// The stage that failed, or "done".
    pub stage: String,
    /// obligation name → proved | sorry | axiom:<name> | error | unverified
    pub obligations: BTreeMap<String, String>,
    pub declarations: Vec<DeclStatus>,
    pub errors: Vec<String>,
    pub log_tail: Vec<String>,
}

impl Report {
    /// `<work_dir>/report.toml`: next to `solution/` and `proofs/`, which it
    /// certifies; committed with them. The `djinn!` macro reads it.
    pub fn path(cfg: &Config) -> std::path::PathBuf {
        cfg.work_dir.join("report.toml")
    }
    pub fn log_path(cfg: &Config) -> std::path::PathBuf {
        cfg.state_dir().join("verify.log")
    }
    pub fn load(cfg: &Config) -> Option<Report> {
        let t = fs::read_to_string(Report::path(cfg)).ok()?;
        let f: ReportFile = toml::from_str(&t).ok()?;
        let mut obligations = BTreeMap::new();
        let mut declarations = Vec::new();
        for d in f.decl {
            let mut names = Vec::new();
            for (short, st) in d.obligations {
                let full = format!("{}.{short}", d.name);
                obligations.insert(full.clone(), st);
                names.push(full);
            }
            declarations.push(DeclStatus { name: d.name, kind: d.kind, implemented: d.implemented, obligations: names, tokens: d.tokens, uses: d.uses, ok: d.ok, weak: d.weakly_specified });
        }
        let log_tail = fs::read_to_string(Report::log_path(cfg)).map(|t| t.lines().map(|s| s.to_string()).collect()).unwrap_or_default();
        Some(Report { certificate: f.certificate, time: f.run.unix_time, duration_secs: f.run.duration_secs, pass: f.run.pass, stage: f.run.stage, obligations, declarations, errors: f.run.errors, log_tail })
    }
    /// Decide `ok` per declaration: implemented (funcs), and every obligation
    /// of it and of the declarations it uses, transitively, proved.
    pub fn finalize(&mut self) {
        let uses: HashMap<String, Vec<String>> = self.declarations.iter().map(|d| (d.name.clone(), d.uses.clone())).collect();
        let by_name: HashMap<String, DeclStatus> = self.declarations.iter().map(|d| (d.name.clone(), d.clone())).collect();
        let proved = |d: &DeclStatus| d.obligations.iter().all(|o| self.obligations.get(o).map(|s| s == "proved").unwrap_or(false));
        let oks: Vec<bool> = self
            .declarations
            .iter()
            .map(|d| d.implemented && djinn_syntax::project::closure(&d.name, &[&uses]).iter().all(|n| by_name.get(n).map(|x| proved(x)).unwrap_or(false)))
            .collect();
        for (d, ok) in self.declarations.iter_mut().zip(oks) {
            d.ok = ok;
        }
    }
    pub fn save(&self, cfg: &Config) {
        let _ = fs::create_dir_all(cfg.state_dir());
        let _ = fs::create_dir_all(&cfg.work_dir);
        let decl = self
            .declarations
            .iter()
            .map(|d| DeclEntry {
                name: d.name.clone(),
                kind: d.kind.clone(),
                implemented: d.implemented,
                ok: d.ok,
                uses: d.uses.clone(),
                tokens: d.tokens.clone(),
                obligations: d
                    .obligations
                    .iter()
                    .map(|o| (o.rsplit('.').next().unwrap_or(o).to_string(), self.obligations.get(o).cloned().unwrap_or_else(|| "unverified".into())))
                    .collect(),
                weakly_specified: d.weak,
            })
            .collect();
        let f = ReportFile {
            certificate: self.certificate.clone(),
            run: RunEntry { time: format!("{} UTC", fmt_time(self.time)), unix_time: self.time, duration_secs: self.duration_secs, pass: self.pass, stage: self.stage.clone(), errors: self.errors.clone() },
            decl,
        };
        if let Ok(s) = toml::to_string_pretty(&f) {
            let header = "# Written by `cargo djinn` after every verify. Per declaration: its tokens as\n# verified, what it uses, and the status of each obligation. The `djinn!`\n# macro refuses to compile a `fn` that is not `ok` here or whose tokens (or a\n# used declaration's) differ from this file. Commit it with solution/ and proofs/.\n\n";
            let _ = fs::write(Report::path(cfg), format!("{header}{s}"));
        }
        let _ = fs::write(Report::log_path(cfg), self.log_tail.join("\n"));
    }
    /// One-paragraph summary for humans and agents.
    pub fn summary(&self) -> String {
        let mut s = String::new();
        if self.pass {
            s.push_str("PASS: every obligation is proved and the axiom audit is clean.\n");
        } else {
            s.push_str(&format!("FAIL at stage: {}\n", self.stage));
        }
        let proved = self.obligations.values().filter(|v| v.as_str() == "proved").count();
        s.push_str(&format!("obligations proved: {proved}/{}\n", self.obligations.len()));
        for (k, v) in &self.obligations {
            if v != "proved" {
                s.push_str(&format!("  {k}: {v}\n"));
            }
        }
        if !self.errors.is_empty() {
            s.push_str("errors:\n");
            for e in self.errors.iter().take(30) {
                s.push_str(&format!("  {e}\n"));
            }
        }
        s
    }
}

fn fail_at(cfg: &Config, e: djinn_syntax::Error) -> String {
    let s = e.span.start();
    let file = cfg.specs().get(e.file).map(|f| f.path.display().to_string()).unwrap_or_else(|| cfg.specs_display());
    format!("{file}:{}:{}: error: {}", s.line, s.column + 1, e.msg)
}

/// The Rust module (`a::b`; `None` at the crate root) of a name of the
/// specification: the module of the file defining it.
pub fn module_of(specs: &[SpecFile], prog: &Program, name: &str) -> Option<String> {
    prog.origin.get(name).and_then(|&i| specs.get(i)).and_then(|f| f.module.clone())
}

/// Rust name → Lean name, from Aeneas's `translation.json` when present,
/// otherwise predicted from the module the stubs live in.
pub fn impl_names(cfg: &Config) -> HashMap<String, String> {
    let mut m = impl_names_from_json(cfg);
    // without any Aeneas output there is no implementation to name: the
    // `impl_correct` obligations appear after the first verify
    if !cfg.lean_dir().join("Code").join("Funs.lean").exists() {
        return m;
    }
    // an unimplemented func compiles to a panicking stub, which Aeneas models
    // too; its `impl_correct` would be unprovable noise, so only implemented
    // funcs get the implementation-dependent obligations
    let implemented = solution_fns(cfg);
    m.retain(|name, _| implemented.contains(name));
    let specs = cfg.specs();
    if let Ok(prog) = parse_spec(cfg) {
        for d in prog.decls.iter().filter(|d| d.kind == Kind::Func && implemented.contains(&d.name)) {
            m.entry(d.name.clone()).or_insert_with(|| cfg.lean_name(module_of(&specs, &prog, &d.name).as_deref(), &d.name));
        }
    }
    m
}

/// Rust type name → Lean name of its Aeneas inductive: from `translation.json`
/// when Aeneas has run, else predicted from the namespace and the spec module
/// (`Lz77.spec.Token`).
pub fn type_names(cfg: &Config, prog: &Program) -> TypeNames {
    let mut m = TypeNames::new();
    let specs = cfg.specs();
    let predict = |n: &str| cfg.lean_name(module_of(&specs, prog, n).as_deref(), n);
    for n in prog.types.enums.keys().chain(prog.types.structs.keys()) {
        m.insert(n.clone(), predict(n));
    }
    // ambient functions: `fn:<name>` → the Lean name of their Aeneas model
    for n in prog.types.ambient.keys() {
        m.insert(format!("fn:{n}"), predict(n));
    }
    if let Ok(text) = fs::read_to_string(cfg.translation_path()) {
        if let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) {
            for t in json["types"].as_array().into_iter().flatten() {
                if let (Some(rust), Some(lean)) = (t["rust_name"].as_str(), t["lean_name"].as_str()) {
                    let short = rust.rsplit("::").next().unwrap_or(rust);
                    if m.contains_key(short) {
                        m.insert(short.to_string(), lean.to_string());
                    }
                }
            }
            let paths = rust_paths(cfg, &specs, prog);
            for f in json["functions"].as_array().into_iter().flatten() {
                if f.get("loop").is_some() {
                    continue;
                }
                if let (Some(rust), Some(lean)) = (f["rust_name"].as_str(), f["lean_name"].as_str()) {
                    if let Some(short) = paths.get(rust) {
                        if prog.types.ambient.contains_key(short) {
                            m.insert(format!("fn:{short}"), lean.to_string());
                        }
                    }
                }
            }
        }
    }
    m
}

/// The ambient functions the specification's constraints call.
pub fn ambient_used(prog: &Program) -> Vec<String> {
    let mut v: Vec<String> = prog.types.ambient.keys().filter(|f| prog.decls.iter().any(|d| d.requires.iter().chain(d.ensures.iter()).chain(d.decreases.iter()).any(|e| e.calls(f)) || d.body.iter().any(|s| s.calls(f)))).cloned().collect();
    v.sort();
    v
}

/// Has Aeneas translated every ambient function the specification calls?
pub fn ambient_available(cfg: &Config, prog: &Program) -> bool {
    let used = ambient_used(prog);
    if used.is_empty() {
        return true;
    }
    let Ok(text) = fs::read_to_string(cfg.translation_path()) else { return false };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { return false };
    let paths = rust_paths(cfg, &cfg.specs(), prog);
    let have: Vec<String> = json["functions"].as_array().into_iter().flatten().filter_map(|f| f["rust_name"].as_str()).filter_map(|r| paths.get(r)).cloned().collect();
    used.iter().all(|f| have.contains(f)) && cfg.lean_dir().join("Code").join("Funs.lean").exists()
}

fn impl_names_from_json(cfg: &Config) -> HashMap<String, String> {
    let mut m = HashMap::new();
    let p = cfg.translation_path();
    let Ok(text) = fs::read_to_string(&p) else { return m };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { return m };
    let Ok(prog) = parse_spec(cfg) else { return m };
    let paths = rust_paths(cfg, &cfg.specs(), &prog);
    for f in json["functions"].as_array().into_iter().flatten() {
        if f.get("loop").is_some() {
            continue;
        }
        let (Some(rust), Some(lean)) = (f["rust_name"].as_str(), f["lean_name"].as_str()) else { continue };
        if let Some(short) = paths.get(rust) {
            m.insert(short.clone(), lean.to_string());
        }
    }
    m
}

/// `translation.json`'s Rust path (`my_crate::a::b::f`) of every name of
/// the specification → the name.
fn rust_paths(cfg: &Config, specs: &[SpecFile], prog: &Program) -> HashMap<String, String> {
    let krate = cfg.crate_name.replace('-', "_");
    prog.origin.keys().map(|n| (format!("{}::{n}", cfg.rust_module(&krate, module_of(specs, prog, n).as_deref())), n.clone())).collect()
}

/// Parse the specification files into one program.
pub fn parse_spec(cfg: &Config) -> Result<Program, String> {
    let texts = cfg.spec_texts()?;
    let srcs: Vec<String> = texts.into_iter().map(|(_, t)| t).collect();
    let prog = djinn_syntax::parse_sources(&srcs).map_err(|e| fail_at(cfg, e))?;
    if prog.decls.is_empty() {
        return Err(format!("{}: no `djinn! {{ … }}` declarations found", cfg.specs_display()));
    }
    Ok(prog)
}

/// The report's entries of the specification (empty if it does not parse).
pub fn spec_entries(cfg: &Config) -> Vec<djinn_syntax::project::Entry> {
    cfg.spec_texts().map(|t| djinn_syntax::project::index_texts(&t.into_iter().map(|(_, s)| s).collect::<Vec<_>>())).unwrap_or_default()
}

/// Parse and lower the specification.
pub fn lower_spec(cfg: &Config) -> Result<Vec<Lowered>, String> {
    let prog = parse_spec(cfg)?;
    let names = type_names(cfg, &prog);
    djinn_syntax::lower_program_named(&prog, &names).map_err(|e| fail_at(cfg, e))
}

/// The emitter's context for this crate.
pub fn emit_cx<'a>(cfg: &'a Config, lowered: &[Lowered], impl_names: &'a HashMap<String, String>, type_names: &'a TypeNames) -> EmitCx<'a> {
    EmitCx {
        ns: &cfg.ns,
        impl_names,
        type_names,
        has_types: cfg.lean_dir().join("Code").join("Types.lean").exists(),
        has_funs: cfg.lean_dir().join("Code").join("Funs.lean").exists(),
        unfoldable: lowered
            .iter()
            .flat_map(|d| {
                let mut v = vec![format!("{}_pre", d.name)];
                // `_spec` of a declaration with choices is a non-recursive
                // wrapper of `_body`; `_body` recurses when the declaration does
                if d.decreases.is_empty() || !d.choices.is_empty() {
                    v.push(format!("{}_spec", d.name));
                }
                if d.decreases.is_empty() && !d.choices.is_empty() {
                    v.push(format!("{}_body", d.name));
                }
                v
            })
            .collect(),
    }
}

/// Does `Code/Types.lean` define every user type the specification mentions?
pub fn types_available(cfg: &Config, prog: &Program) -> bool {
    let Ok(text) = fs::read_to_string(cfg.lean_dir().join("Code").join("Types.lean")) else { return false };
    let defined = |n: &str| text.contains(&format!(".{n} where")) || text.contains(&format!(" {n} where")) || text.contains(&format!("inductive {n}")) || text.contains(&format!("structure {n}"));
    let user_ok = prog.types.enums.keys().chain(prog.types.structs.keys()).all(|n| defined(n));
    // a `HashMap` in a signature needs the modeled type from `TypesExternal.lean`
    let uses_map = prog.decls.iter().any(|d| d.params.iter().any(|p| has_map(&p.ty)) || d.ret.as_ref().map(|(_, t)| has_map(t)).unwrap_or(false));
    let map_ok = !uses_map || fs::read_to_string(cfg.lean_dir().join("Code").join("TypesExternal.lean")).map(|t| t.contains("structure std.collections.hash.map.HashMap")).unwrap_or(false);
    user_ok && map_ok
}

fn has_map(t: &djinn_syntax::RType) -> bool {
    use djinn_syntax::RType;
    match t {
        RType::Map(..) => true,
        RType::Seq(e, _) | RType::Option(e) => has_map(e),
        RType::Result(a, b) => has_map(a) || has_map(b),
        _ => false,
    }
}

/// Does the specification need Aeneas's `Types` module (user types)?
pub fn needs_types(lowered: &[Lowered]) -> bool {
    lowered.iter().any(|d| d.uses_types)
}


pub fn decl_statuses(cfg: &Config, lowered: &[Lowered], names: &HashMap<String, String>) -> Vec<DeclStatus> {
    let fns = solution_fns(cfg);
    let tn = parse_spec(cfg).map(|p| type_names(cfg, &p)).unwrap_or_default();
    let cx = emit_cx(cfg, lowered, names, &tn);
    let entries: HashMap<String, djinn_syntax::project::Entry> = spec_entries(cfg)
        .into_iter()
        .map(|e| (e.name.clone(), e))
        .collect();
    let mut v: Vec<DeclStatus> = lowered
        .iter()
        .map(|d| DeclStatus {
            name: d.name.clone(),
            kind: d.kind.word().into(),
            implemented: d.kind == Kind::Rel || fns.contains(&d.name),
            obligations: emit::obligations(&cx, d).into_iter().map(|o| o.name).collect(),
            tokens: entries.get(&d.name).map(|e| e.tokens.clone()).unwrap_or_default(),
            uses: entries.get(&d.name).map(|e| e.uses.clone()).unwrap_or_default(),
            ok: false,
            weak: d.weakly_specified,
        })
        .collect();
    // the ambient functions the constraints call: trusted, no obligations,
    // recorded so that editing one marks its callers as changed
    let uses: HashMap<String, Vec<String>> = entries.iter().map(|(name, entry)| (name.clone(), entry.uses.clone())).collect();
    let mut referenced = std::collections::BTreeSet::new();
    for d in &v {
        referenced.extend(djinn_syntax::project::closure(&d.name, &[&uses]));
    }
    for name in referenced {
        if let Some(e) = entries.get(&name).filter(|e| !matches!(e.kind.as_str(), "func" | "rel")) {
            v.push(DeclStatus { name: e.name.clone(), kind: e.kind.clone(), implemented: true, obligations: vec![], tokens: e.tokens.clone(), uses: e.uses.clone(), ok: true, weak: false });
        }
    }
    v
}


/// Does a Lean segment (a top-level command with its attributes and doc
/// comment) mention one of the removed declarations: its `_spec`/`_pre`,
/// its obligations `name.…`, helpers named `name_…`, or its Aeneas model
/// `….name`?
fn mentions(segment: &str, removed: &[String]) -> Option<String> {
    for word in segment.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\'')) {
        for n in removed {
            let w = word.trim_matches('.');
            if w == format!("{n}_spec") || w == format!("{n}_pre") || w.starts_with(&format!("{n}.")) || w.starts_with(&format!("{n}_")) || w.ends_with(&format!(".{n}")) || w.contains(&format!(".{n}.")) {
                return Some(n.clone());
            }
        }
    }
    None
}

/// Split a Lean file into top-level segments: each command (`theorem`, `def`,
/// …) with the attributes and doc comment that precede it. `import`, `open`,
/// `namespace`, `end`, `set_option` and comments form segments of their own.
fn lean_segments(text: &str) -> Vec<String> {
    const STARTS: &[&str] = &["theorem ", "lemma ", "def ", "abbrev ", "instance ", "example ", "noncomputable ", "private ", "protected ", "structure ", "inductive ", "@[", "/--", "/-!", "/-", "import ", "open ", "namespace ", "end ", "section ", "set_option ", "attribute ", "variable ", "#"];
    const PREFIX: &[&str] = &["@[", "/--"];
    let mut segs: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut cur_is_prefix_only = false;
    for line in text.split_inclusive('\n') {
        let starts = STARTS.iter().any(|k| line.starts_with(k));
        if starts && !cur.is_empty() && !cur_is_prefix_only {
            segs.push(std::mem::take(&mut cur));
        }
        if starts {
            // an attribute or a doc comment opens a segment that the next command completes
            cur_is_prefix_only = PREFIX.iter().any(|k| line.starts_with(k));
        }
        cur.push_str(line);
    }
    if !cur.is_empty() {
        segs.push(cur);
    }
    segs
}

fn removable(segment: &str) -> bool {
    let first_cmd = segment.lines().find(|l| !(l.starts_with("@[") || l.starts_with("/--") || l.trim().is_empty() || l.starts_with("    ") || l.starts_with("--") || l.starts_with(" ")));
    matches!(first_cmd, Some(l) if ["theorem ", "lemma ", "def ", "abbrev ", "instance ", "example ", "noncomputable ", "private ", "protected ", "structure ", "inductive "].iter().any(|k| l.starts_with(k)))
}

/// Declarations that left the specification since the last report, and
/// obligations that no longer exist: move their theorems (and helper lemmas
/// mentioning them) and their Rust implementations out of the way into
/// `.djinnscratch/backup/<time>-stale/`, so the crate keeps building.
fn archive_stale(cfg: &Config, lowered: &[Lowered], cx: &EmitCx, log: &mut Log, archive_rust: bool) -> Result<(), String> {
    let current: std::collections::HashSet<&str> = lowered.iter().map(|d| d.name.as_str()).collect();
    let report = Report::load(cfg);
    // removed declarations: known to the last report but gone, or — if the
    // report was already rewritten — still owning obligation theorems
    // (`name.unambiguous`, `name.impl_correct`, …) in Proofs.lean
    let mut removed: Vec<String> = Vec::new();
    let mut removed_funcs: Vec<String> = Vec::new();
    if let Some(r) = &report {
        for d in &r.declarations {
            // Dependency entries record freshness, not declarations that own
            // obligations or implementations in the generated Lean files.
            if !matches!(d.kind.as_str(), "func" | "rel") {
                continue;
            }
            if !current.contains(d.name.as_str()) {
                removed.push(d.name.clone());
                if d.kind == "func" {
                    removed_funcs.push(d.name.clone());
                }
            }
        }
    }
    let proofs_path = cfg.lean_dir().join("Proofs.lean");
    if let Ok(text) = fs::read_to_string(&proofs_path) {
        for l in text.lines() {
            if let Some(rest) = l.strip_prefix("theorem ") {
                let name = rest.split(|c: char| c.is_whitespace() || c == ':').next().unwrap_or("");
                if let Some((decl, ob)) = name.rsplit_once('.') {
                    let known = emit::is_obligation_kind(ob);
                    if known && !current.contains(decl) && !removed.iter().any(|r| r == decl) {
                        removed.push(decl.to_string());
                        if ob == "impl_correct" || ob == "unambiguous" {
                            removed_funcs.push(decl.to_string());
                        }
                    }
                }
            }
        }
    }
    if removed.is_empty() {
        return Ok(());
    }
    let current_obligations: std::collections::HashSet<String> = lowered.iter().flat_map(|d| emit::obligations(cx, d).into_iter().map(|o| o.name)).collect();
    let mut stale_lean = String::new();
    let mut stale_rust = String::new();
    let mut notes = Vec::new();
    // Lean: segments about removed declarations, and theorems of vanished obligations
    if let Ok(text) = fs::read_to_string(&proofs_path) {
        let mut kept = String::new();
        let mut n_removed = 0usize;
        let mut n_vanished = 0usize;
        for seg in lean_segments(&text) {
            let mut drop = false;
            if removable(&seg) {
                if let Some(n) = mentions(&seg, &removed) {
                    drop = true;
                    n_removed += 1;
                    stale_lean.push_str(&format!("-- stale: mentions removed declaration `{n}`\n"));
                } else if let Some(name) = seg.lines().find_map(|l| l.strip_prefix("theorem ").map(|r| r.split(|c: char| c.is_whitespace() || c == ':').next().unwrap_or("").to_string())) {
                    // an obligation theorem (`decl.kind`) for a declaration that still exists
                    if let Some((decl, ob)) = name.rsplit_once('.') {
                        let known = emit::is_obligation_kind(ob);
                        if known && current.contains(decl) && !current_obligations.contains(&name) {
                            drop = true;
                            n_vanished += 1;
                            stale_lean.push_str(&format!("-- stale: obligation `{name}` no longer exists\n"));
                        }
                    }
                }
            }
            if drop {
                stale_lean.push_str(&seg);
                stale_lean.push('\n');
            } else {
                kept.push_str(&seg);
            }
        }
        if n_removed + n_vanished > 0 {
            fs::write(&proofs_path, kept).map_err(|e| e.to_string())?;
            if n_removed > 0 {
                notes.push(format!("{n_removed} Lean declaration(s) about removed {}", removed.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")));
            }
            if n_vanished > 0 {
                notes.push(format!("{n_vanished} theorem(s) of obligations that no longer exist"));
            }
        }
    }
    // Rust: `pub fn` items of removed funcs — unless other solution code still
    // calls them, in which case they have become helpers and stay
    let (removed_funcs, kept): (Vec<String>, Vec<String>) = removed_funcs.into_iter().partition(|n| !djinn_syntax::project::rust_fn_referenced(&cfg.solution_dir(), n));
    for k in &kept {
        log.line(&format!("kept `{k}` in the solution as a helper: the specification no longer declares it, but other solution code calls it"));
    }
    if !removed_funcs.is_empty() && archive_rust {
        let mut n = 0usize;
        for file in rust_files(&cfg.solution_dir()) {
            let Ok(src) = fs::read_to_string(&file) else { continue };
            let Ok(ast) = syn::parse_file(&src) else { continue };
            let mut cut: Vec<(usize, usize)> = Vec::new(); // 1-based inclusive line ranges
            for item in &ast.items {
                if let syn::Item::Fn(f) = item {
                    if removed_funcs.contains(&f.sig.ident.to_string()) {
                        use syn::spanned::Spanned;
                        let sp = item.span();
                        cut.push((sp.start().line, sp.end().line));
                    }
                }
            }
            if cut.is_empty() {
                continue;
            }
            let lines: Vec<&str> = src.split_inclusive('\n').collect();
            let mut kept = String::new();
            for (i, l) in lines.iter().enumerate() {
                let ln = i + 1;
                if cut.iter().any(|(a, b)| ln >= *a && ln <= *b) {
                    stale_rust.push_str(l);
                } else {
                    kept.push_str(l);
                }
            }
            stale_rust.push('\n');
            n += cut.len();
            fs::write(&file, kept).map_err(|e| e.to_string())?;
        }
        if n > 0 {
            notes.push(format!("{n} Rust function(s) implementing removed {}", removed_funcs.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")));
        }
    }
    if notes.is_empty() {
        return Ok(());
    }
    let dir = cfg.state_dir().join("backup").join(format!("{}-stale", id_time(now())));
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    if !stale_lean.is_empty() {
        fs::write(dir.join("Proofs.stale.lean"), format!("-- Removed from Proofs.lean by `cargo djinn translate` because the specification\n-- no longer has the declarations or obligations they concern.\n\n{stale_lean}")).map_err(|e| e.to_string())?;
    }
    if !stale_rust.is_empty() {
        fs::write(dir.join("solution.stale.rs"), format!("//! Removed from the solution by `cargo djinn translate`: implementations of\n//! functions the specification no longer declares.\n\n{stale_rust}")).map_err(|e| e.to_string())?;
    }
    log.line(&format!("archived to {}: {}", cfg.rel(&dir), notes.join("; ")));
    Ok(())
}

/// The solution is safe Rust: `src/lib.rs` (or `main.rs`) includes it as a
/// module under `#[forbid(unsafe_code)]` (or forbids it crate-wide), and no
/// solution file contains the `unsafe` keyword. Aeneas only models safe Rust,
/// so this is what makes "the verifier never sees `unsafe`" true.
pub fn check_safe(cfg: &Config) -> Result<(), String> {
    use quote::ToTokens;
    fn forbids(attrs: &[syn::Attribute]) -> bool {
        attrs.iter().any(|a| a.path().is_ident("forbid") && a.meta.to_token_stream().to_string().contains("unsafe_code"))
    }
    let root = ["src/lib.rs", "src/main.rs"].iter().map(|f| cfg.crate_dir.join(f)).find(|p| p.exists()).ok_or("no src/lib.rs or src/main.rs")?;
    let src = fs::read_to_string(&root).map_err(|e| format!("{}: {e}", root.display()))?;
    let file = syn::parse_file(&src).map_err(|e| format!("{}: {e}", root.display()))?;
    let crate_wide = forbids(&file.attrs);
    let module_level = file.items.iter().any(|it| matches!(it, syn::Item::Mod(m) if m.ident == "solution" && forbids(&m.attrs)));
    if !crate_wide && !module_level {
        return Err(format!(
            "FAIL: {} must include the solution under `#[forbid(unsafe_code)]`:\n  #[forbid(unsafe_code)]\n  #[path = \"../{}/mod.rs\"]\n  pub mod solution;\n(or forbid unsafe_code crate-wide with `#![forbid(unsafe_code)]`)",
            cfg.rel(&root),
            cfg.sol_rel()
        ));
    }
    fn has_unsafe(ts: proc_macro2::TokenStream) -> bool {
        ts.into_iter().any(|t| match t {
            proc_macro2::TokenTree::Ident(i) => i == "unsafe",
            proc_macro2::TokenTree::Group(g) => has_unsafe(g.stream()),
            _ => false,
        })
    }
    for f in rust_files(&cfg.solution_dir()) {
        let Ok(src) = fs::read_to_string(&f) else { continue };
        if let Ok(ts) = src.parse::<proc_macro2::TokenStream>() {
            if has_unsafe(ts) {
                return Err(format!("FAIL: {} contains `unsafe`; the solution must be safe Rust (Aeneas models only safe code)", cfg.rel(&f)));
            }
        }
    }
    Ok(())
}

fn rust_files(dir: &Path) -> Vec<std::path::PathBuf> {
    let mut v = Vec::new();
    fn walk(d: &Path, v: &mut Vec<std::path::PathBuf>) {
        for e in fs::read_dir(d).into_iter().flatten().flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, v);
            } else if p.extension().map(|x| x == "rs").unwrap_or(false) {
                v.push(p);
            }
        }
    }
    walk(dir, &mut v);
    v.sort();
    v
}

/// Emit the trusted Lean files (and the proof skeleton / project scaffolding once).
pub fn translate(cfg: &Config, log: &mut Log) -> Result<Vec<Lowered>, String> {
    translate_opts(cfg, log, true)
}

/// `archive_rust = false` while verifying from a jail: the jail would push the
/// removed function back on its next verify, so the human's own `translate`
/// does that archiving.
pub fn translate_opts(cfg: &Config, log: &mut Log, archive_rust: bool) -> Result<Vec<Lowered>, String> {
    let prog = parse_spec(cfg)?;
    let tn = type_names(cfg, &prog);
    let lowered = djinn_syntax::lower_program_named(&prog, &tn).map_err(|e| fail_at(cfg, e))?;
    let dir = cfg.lean_dir();
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    // the work directory: a placeholder solution so the crate builds and the
    // layout is visible
    fs::create_dir_all(cfg.solution_dir()).map_err(|e| e.to_string())?;
    if !cfg.solution_dir().join("mod.rs").exists() {
        fs::write(cfg.solution_dir().join("mod.rs"), "//! LLM-owned: the implementation of the `func`s of the specification.\n").map_err(|e| e.to_string())?;
    }
    // user types are Rust enums and structs, and ambient functions are Rust
    // code: `Spec.lean` needs their Aeneas translation, so the pipeline runs
    // once before the first translate
    if (needs_types(&lowered) && !types_available(cfg, &prog)) || !ambient_available(cfg, &prog) {
        log.line("the specification mentions user types or ambient functions whose Lean translation Aeneas has not produced yet: running Charon and Aeneas once");
        aeneas_pipeline(cfg, log).map_err(|(_, e)| e)?;
    }
    let tn = type_names(cfg, &prog);
    let lowered = djinn_syntax::lower_program_named(&prog, &tn).map_err(|e| fail_at(cfg, e))?;
    let names = impl_names(cfg);
    let cx = emit_cx(cfg, &lowered, &names, &tn);
    archive_stale(cfg, &lowered, &cx, log, archive_rust)?;
    let w = |name: &str, text: String| -> Result<(), String> {
        fs::write(dir.join(name), text).map_err(|e| format!("{name}: {e}"))
    };
    w("Vocab.lean", emit::vocab_lean())?;
    w("Spec.lean", emit::spec_lean(&cx, &lowered))?;
    w("Obligations.lean", emit::obligations_lean(&cx, &lowered))?;
    w("Audit.lean", emit::audit_lean(&cx, &lowered))?;
    if !dir.join("Proofs.lean").exists() {
        w("Proofs.lean", emit::proofs_skeleton(&cx, &lowered))?;
        log.line(&format!("wrote initial {}/Proofs.lean (never overwritten)", dir.display()));
    } else {
        // the specification may have grown: append stubs for obligations
        // that have no theorem yet, so existing work is reused
        let path = dir.join("Proofs.lean");
        let mut text = fs::read_to_string(&path).map_err(|e| e.to_string())?;
        // the Aeneas model has appeared since the skeleton was written
        let ci = emit::code_import(&cx);
        if !ci.is_empty() && !text.contains(ci.trim_end()) {
            let spec_import = format!("import {}.Spec\n", cfg.ns);
            text = match text.find(&spec_import) {
                Some(i) => format!("{}{}{}", &text[..i + spec_import.len()], ci, &text[i + spec_import.len()..]),
                None => format!("{ci}{text}"),
            };
            fs::write(&path, &text).map_err(|e| e.to_string())?;
            log.line(&format!("added `{}` to Proofs.lean", ci.trim_end()));
        }
        let mut missing = Vec::new();
        for d in &lowered {
            for o in emit::obligations(&cx, d) {
                if o.generated_proof.is_some() {
                    continue;
                }
                let decl = format!("theorem {} ", o.name);
                let decl2 = format!("theorem {}\n", o.name);
                if !text.contains(&decl) && !text.contains(&decl2) {
                    missing.push(o);
                }
            }
        }
        if !missing.is_empty() {
            let end_marker = format!("end {}.Proofs", cfg.ns);
            let mut add = String::new();
            add.push_str("/-! ## obligations added by a later `translate` (specification changed) -/\n\n");
            for o in &missing {
                add.push_str(&emit::stub_text(o));
            }
            let new_text = if let Some(i) = text.rfind(&end_marker) {
                format!("{}{}{}", &text[..i], add, &text[i..])
            } else {
                format!("{text}\n{add}")
            };
            fs::write(&path, new_text).map_err(|e| e.to_string())?;
            log.line(&format!("added {} stub(s) to Proofs.lean for new obligations: {}", missing.len(), missing.iter().map(|o| o.name.clone()).collect::<Vec<_>>().join(", ")));
        }
    }
    let root = cfg.proofs.join(format!("{}.lean", cfg.ns));
    if !root.exists() {
        fs::write(&root, format!("import {0}.Spec\nimport {0}.Obligations\n", cfg.ns)).map_err(|e| e.to_string())?;
    }
    // an initial report, so that `cargo build` can say "never attempted"
    // precisely and the macro has a file to track
    if !Report::path(cfg).exists() {
        let mut r = Report { certificate: None, time: now(), duration_secs: 0, pass: false, stage: "not run".into(), obligations: BTreeMap::new(), declarations: decl_statuses(cfg, &lowered, &names), errors: Vec::new(), log_tail: Vec::new() };
        for d in &r.declarations {
            for o in &d.obligations {
                r.obligations.insert(o.clone(), "unverified".into());
            }
        }
        r.save(cfg);
        log.line(&format!("wrote initial {}", cfg.rel(&Report::path(cfg))));
    }
    // the shared Lean package cache
    let pk = cfg.proofs.join(".lake").join("packages");
    // a dangling link (a crate copied from another machine) counts as missing
    let dangling = fs::symlink_metadata(&pk).map(|m| m.file_type().is_symlink()).unwrap_or(false) && !pk.exists();
    if dangling {
        let _ = fs::remove_file(&pk);
    }
    if !pk.exists() && cfg.lake_packages.is_dir() {
        fs::create_dir_all(cfg.proofs.join(".lake")).map_err(|e| e.to_string())?;
        let _ = std::os::unix::fs::symlink(&cfg.lake_packages, &pk);
        log.line(&format!("linked {} to the shared package cache {}", cfg.rel(&pk), cfg.lake_packages.display()));
    }
    let lakefile = cfg.proofs.join("lakefile.lean");
    if !lakefile.exists() {
        let aeneas_lean = cfg.aeneas_lean.clone().ok_or(
            "no lakefile.lean yet and no Aeneas Lean backend path: set [package.metadata.djinn] aeneas_lean or DJINN_AENEAS_LEAN",
        )?;
        fs::write(
            &lakefile,
            format!(
                "import Lake\nopen Lake DSL\n\nrequire aeneas from \"{aeneas_lean}\"\n\npackage «{0}» {{}}\n\n@[default_target] lean_lib «{1}» {{}}\n",
                cfg.crate_name, cfg.ns
            ),
        )
        .map_err(|e| e.to_string())?;
        let tc = cfg.proofs.join(&aeneas_lean).join("lean-toolchain");
        if let Ok(t) = fs::read_to_string(&tc) {
            fs::write(cfg.proofs.join("lean-toolchain"), t).map_err(|e| e.to_string())?;
        }
    }
    // the harness guide, always refreshed (the scratch directory may not exist yet on a crate
    // that has never been run)
    fs::create_dir_all(cfg.state_dir()).map_err(|e| format!("{}: {e}", cfg.state_dir().display()))?;
    fs::write(cfg.guide_path(), crate::guide::guide(cfg, &lowered, &names)).map_err(|e| format!("{}: {e}", cfg.guide_path().display()))?;
    log.line(&format!("translated {} declarations into {}", lowered.len(), dir.display()));
    Ok(lowered)
}

fn run(cmd: &mut Command, what: &str, log: &mut Log) -> Result<String, String> {
    log.line(&format!("== {what}"));
    let out = cmd.output().map_err(|e| format!("{what}: cannot run: {e}"))?;
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    if !out.status.success() {
        let tail: Vec<&str> = text.lines().rev().take(60).collect::<Vec<_>>().into_iter().rev().collect();
        return Err(format!("FAIL: {what}\n{}", tail.join("\n")));
    }
    Ok(text)
}

fn noise(line: &str) -> bool {
    line.starts_with('⚠')
        || line.contains("linter")
        || line.starts_with("Note:")
        || line.trim().is_empty()
        || line.contains("unusedVariables")
        || line.contains("binding can be removed")
        || line.contains("not explicitly referenced")
        || line.contains("dupNamespace")
        || line.contains("duplicated in the declaration")
        || line.starts_with("trace:")
        || line.starts_with("  • ")
}

/// The whole gate. With `jail`, the LLM-owned files are first synced back
/// from the jail into the crate, and the trusted files are pushed to the jail
/// afterwards.
pub fn verify(cfg: &Config, jail: Option<&Path>, log: &mut Log) -> Report {
    let start = now();
    let mut report = Report {
        certificate: None,
        time: start,
        duration_secs: 0,
        pass: false,
        stage: String::new(),
        obligations: BTreeMap::new(),
        declarations: Vec::new(),
        errors: Vec::new(),
        log_tail: Vec::new(),
    };
    let result = verify_inner(cfg, jail, log, &mut report);
    match result {
        Ok(()) => {
            report.pass = true;
            report.stage = "done".into();
            log.line("PASS");
        }
        Err((stage, msg)) => {
            report.pass = false;
            report.stage = stage;
            for l in msg.lines() {
                log.line(l);
            }
            if report.errors.is_empty() {
                report.errors = msg.lines().filter(|l| l.contains("error")).map(|s| s.to_string()).collect();
            }
        }
    }
    report.duration_secs = now() - start;
    report.log_tail = log.text.lines().rev().take(80).map(|s| s.to_string()).collect::<Vec<_>>().into_iter().rev().collect();
    report.finalize();
    if !report.pass { report.certificate = None; }
    report.save(cfg);
    if let Some(j) = jail {
        if let Err(e) = jail::sync_forward(cfg, j) {
            log.line(&format!("warning: could not refresh the jail: {e}"));
        }
    }
    report
}

/// Stages 1–4 of the gate: `cargo build`, the safe-Rust check, Charon, Aeneas
/// (regenerating `Code/`), and the audit of `translation.json`.
pub fn aeneas_pipeline(cfg: &Config, log: &mut Log) -> Result<(), (String, String)> {
    aeneas_pipeline_bound(cfg, log).map(|_| ())
}

fn aeneas_pipeline_bound(cfg: &Config, log: &mut Log) -> Result<djinn_syntax::certificate::Certificate, (String, String)> {
    let stage = |s: &str, e: String| (s.to_string(), e);
    // 1. the crate builds: signatures of spec and solution agree
    // the verifier is the one party allowed to compile an unverified crate
    run(Command::new("cargo").args(["build", "--quiet"]).env("DJINN_VERIFYING", "1").current_dir(&cfg.crate_dir), "cargo build", log)
        .map_err(|e| stage("cargo build", e))?;
    // Cargo may create Cargo.lock on the first build. Bind the complete input
    // only after that, and before extraction sees any implementation.
    let certificate = djinn_syntax::certificate::capture(&cfg.crate_dir).map_err(|e| stage("source snapshot", e))?;
    // 1b. only safe Rust: the solution must be included under
    // `#[forbid(unsafe_code)]`, and must not spell `unsafe` at all
    check_safe(cfg).map_err(|e| stage("unsafe", e))?;
    // 2. charon
    // Charon's intermediate output belongs to the disposable state, not the crate root
    let _ = fs::create_dir_all(cfg.state_dir());
    let llbc = cfg.state_dir().join(format!("{}.llbc", cfg.crate_name));
    let mut charon = Command::new(&cfg.charon);
    charon.args(["cargo", "--preset=aeneas", "--no-dedup-serialized-ast", "--dest-file"]).arg(&llbc).env("DJINN_VERIFYING", "1").current_dir(&cfg.crate_dir);
    // the verified program is what the specification names: translation
    // starts from the `fn` stubs and follows their calls (the solution and its
    // helpers); drivers, the workload and any other module of the crate are
    // never seen
    let prog = parse_spec(cfg).map_err(|e| stage("specification", e))?;
    let specs = cfg.specs();
    let path = |n: &str| format!("--start-from={}::{n}", cfg.rust_module("crate", module_of(&specs, &prog, n).as_deref()));
    for d in prog.decls.iter().filter(|d| d.kind == Kind::Func) {
        charon.arg(path(&d.name));
    }
    // and the ambient functions the constraints call: their Aeneas model is
    // their meaning in `Spec.lean`
    for f in ambient_used(&prog) {
        charon.arg(path(&f));
    }
    // and the specification's own types: a `struct` or `enum` that only the
    // relations mention is reached by no `fn`, yet `Spec.lean` names its
    // Aeneas inductive
    for t in prog.types.enums.keys().chain(prog.types.structs.keys()) {
        charon.arg(path(t));
    }
    // and only the library target: binaries (`src/main.rs`, `src/bin/`) are
    // drivers, which Charon must not even compile
    charon.args(["--", "--lib"]);
    run(&mut charon, "charon", log).map_err(|e| stage("charon", e))?;
    let llbc_json: serde_json::Value = serde_json::from_slice(&fs::read(&llbc).map_err(|e| stage("trusted models", e.to_string()))?).map_err(|e| stage("trusted models", e.to_string()))?;
    crate::models::validate_usage(&llbc_json).map_err(|e| stage("trusted models", e))?;
    // 3. aeneas, regenerating Code/ from scratch
    let code_dir = cfg.lean_dir().join("Code");
    let _ = fs::remove_dir_all(&code_dir);
    run(
        Command::new(&cfg.aeneas)
            .args(["-backend", "lean"])
            .arg(&llbc)
            .arg("-dest")
            .arg(&cfg.proofs)
            .args(["-subdir", &format!("{}/Code", cfg.ns), "-split-files", "-namespace", &cfg.ns, "-emit-json"]),
        "aeneas",
        log,
    )
    .map_err(|e| stage("aeneas", e))?;
    // 4. audit translation.json: no local opaque items, no unknown externals
    // (Aeneas writes it next to its output; it belongs to the scratch space)
    let _ = fs::rename(cfg.proofs.join("translation.json"), cfg.translation_path());
    let tj = fs::read_to_string(cfg.translation_path()).map_err(|e| stage("aeneas", format!("translation.json: {e}")))?;
    let json: serde_json::Value = serde_json::from_str(&tj).map_err(|e| stage("aeneas", e.to_string()))?;
    for f in json["functions"].as_array().into_iter().flatten() {
        if f["is_local"].as_bool() == Some(true) && f["is_opaque"].as_bool() == Some(true) {
            return Err(stage("escape hatch", format!("FAIL: local function {} is opaque (no escape hatches)", f["rust_name"])));
        }
    }
    if code_dir.join("FunsExternal_Template.lean").exists() || code_dir.join("TypesExternal_Template.lean").exists() {
        // externals with a model in the library are written as definitions
        // (trusted); any other is a failure with an explanation
        let patterns = external_patterns(&code_dir);
        match crate::models::cover(&cfg.ns, &patterns) {
            Ok((funs, types)) => {
                fs::write(code_dir.join("FunsExternal.lean"), funs).map_err(|e| stage("externals", e.to_string()))?;
                fs::write(code_dir.join("TypesExternal.lean"), types).map_err(|e| stage("externals", e.to_string()))?;
                log.line(&format!("modeled {} standard-library item(s) the solution uses (String / HashMap and their helpers), from the trusted model library", patterns.len()));
            }
            Err(uncovered) => return Err(stage("externals", explain_externals(cfg, &uncovered))),
        }
    }
    Ok(certificate)
}

/// The `Name pattern`s of the items Aeneas could not model.
fn external_patterns(code_dir: &Path) -> Vec<String> {
    let mut patterns: Vec<String> = Vec::new();
    for f in ["TypesExternal_Template.lean", "FunsExternal_Template.lean"] {
        if let Ok(text) = fs::read_to_string(code_dir.join(f)) {
            for l in text.lines() {
                if let Some(rest) = l.trim().strip_prefix("Name pattern: [") {
                    let pat = rest.trim_end_matches(']').to_string();
                    if !patterns.contains(&pat) {
                        patterns.push(pat);
                    }
                }
            }
        }
    }
    patterns
}

/// What the solution used that Aeneas has no model for, read from the
/// `*External_Template.lean` files Aeneas writes (one `Name pattern` per
/// missing item), grouped by what it is about, each with the places in the
/// solution that use it and a hint. Only safe, modeled Rust can be verified;
/// anything else belongs in a driver (DESIGN.md §7).
fn explain_externals(cfg: &Config, patterns: &[String]) -> String {
    let patterns: Vec<String> = patterns.to_vec();
    // (what to look for in the pattern, the words that betray it in the solution, the hint)
    const GROUPS: &[(&[&str], &[&str], &str, &str)] = &[
        (&["core::fmt", "std::io", "_print", "alloc::fmt::format", "core::hint::must_use"], &["println!", "print!", "eprintln!", "eprint!", "format!", "write!", "writeln!", "dbg!", "std::io", "to_string"], "printing and formatting", "there is no model of I/O or formatting: return data from the function and print it in a driver (DESIGN.md §7)"),
        (&["alloc::string", "str::"], &["String", "to_string", "to_owned", "&str", "as_str", "chars()"], "strings", "`String` is modeled for `new`, `push`, `push_str`, `len`, `is_empty`, `as_bytes`, `as_str`, `into_bytes`, `from_utf8`, `from(&str)`, `clone` and `==`; this method is not: work on the bytes (`as_bytes`) or with `Vec<u8>`"),
        (&["std::collections", "alloc::collections", "core::hash", "hashbrown"], &["HashMap", "HashSet", "BTreeMap", "BTreeSet", "VecDeque", "BinaryHeap", "collections::"], "collections", "`HashMap` is modeled for `new`, `insert`, `get`, `contains_key`, `remove`, `len` and `is_empty` with scalar keys; other collections and methods are not: use those, or a `Vec`"),
        (&["f32", "f64", "core::f32", "core::f64"], &["f32", "f64"], "floating point", "Aeneas has no model of floats; use integers"),
        (&["alloc::rc", "alloc::sync", "core::cell", "alloc::boxed::Box<dyn"], &["Rc<", "Arc<", "RefCell", "Cell<", "Box<dyn", "dyn "], "shared ownership and trait objects", "no model: use plain values and `&`/`&mut`"),
        (&["core::iter", "core::slice::iter"], &["iter()", ".map(", ".filter(", ".fold(", ".sum()", ".collect", "for_each", "into_iter"], "iterator adaptors", "iterate with an index and a `while`/`for` over `0..len` instead"),
        (&["core::slice::{", "alloc::slice", "sort"], &[".sort", ".swap(", ".reverse(", ".contains(", ".binary_search"], "slice methods without a model", "write the loop yourself with index reads and writes"),
    ];
    let mut out = String::from("FAIL: the solution uses Rust that Aeneas cannot model, so it cannot be verified:\n");
    let sol_files = rust_files(&cfg.solution_dir());
    let sources: Vec<(String, String)> = sol_files.iter().filter_map(|f| fs::read_to_string(f).ok().map(|t| (cfg.rel(f), t))).collect();
    let mut used: Vec<usize> = Vec::new();
    let mut explained: Vec<&String> = Vec::new();
    for (gi, (keys, words, what, hint)) in GROUPS.iter().enumerate() {
        let hits: Vec<&String> = patterns.iter().filter(|p| keys.iter().any(|k| p.contains(k))).collect();
        if hits.is_empty() {
            continue;
        }
        used.push(gi);
        explained.extend(hits.iter().copied());
        let mut where_: Vec<String> = Vec::new();
        for (name, text) in &sources {
            for (i, l) in text.lines().enumerate() {
                if words.iter().any(|w| l.contains(w)) {
                    where_.push(format!("{name}:{}: {}", i + 1, l.trim()));
                }
            }
        }
        out.push_str(&format!("  * {what} — {hint}\n"));
        for h in hits.iter().take(4) {
            out.push_str(&format!("      missing model: {h}\n"));
        }
        for w in where_.iter().take(6) {
            out.push_str(&format!("      used at {w}\n"));
        }
    }
    let rest: Vec<&String> = patterns.iter().filter(|p| !explained.contains(p)).collect();
    if !rest.is_empty() {
        out.push_str("  * other items without a model — avoid them, or move the work to a driver:\n");
        for p in rest.iter().take(8) {
            out.push_str(&format!("      {p}\n"));
        }
    }
    out.push_str("  (the full list is in the *External_Template.lean files under the generated Code/ directory)");
    out
}

fn verify_inner(cfg: &Config, jail: Option<&Path>, log: &mut Log, report: &mut Report) -> Result<(), (String, String)> {
    let stage = |s: &str, e: String| (s.to_string(), e);
    // 0. the specification itself, so the report can list declarations
    let lowered = lower_spec(cfg).map_err(|e| stage("specification", e))?;
    report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    for d in &report.declarations {
        for o in &d.obligations {
            report.obligations.insert(o.clone(), "unverified".into());
        }
    }
    // jail: take the LLM-owned files
    if let Some(j) = jail {
        for note in jail::sync_back(cfg, j).map_err(|e| stage("jail sync", e))? {
            log.line(&note);
        }
        report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    }
    // 1–4. Build and extract the exact source captured before Charon.
    let certificate = aeneas_pipeline_bound(cfg, log)?;
    // 5. regenerate the trusted files
    translate_opts(cfg, log, jail.is_none()).map_err(|e| stage("translate", e))?;
    report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    // 6. lake build
    match run(Command::new("lake").arg("build").current_dir(&cfg.proofs), "lake build", log) {
        Ok(text) => {
            if text.contains("declaration uses 'sorry'") || text.contains("declaration uses `sorry`") {
                log.line("note: proofs still contain sorry (the axiom audit will reject them)");
            }
        }
        Err(e) => {
            report.errors = e.lines().filter(|l| l.starts_with("error:") && !noise(l)).map(|s| s.to_string()).collect();
            for o in report.obligations.values_mut() {
                *o = "error".into();
            }
            return Err(stage("lake build", e));
        }
    }
    // 7. axiom audit
    let audit = run(
        Command::new("lake").args(["env", "lean"]).arg(format!("{}/Audit.lean", cfg.ns)).current_dir(&cfg.proofs),
        "axiom audit",
        log,
    )
    .map_err(|e| stage("axiom audit", e))?;
    let allowed = ["propext", "Classical.choice", "Quot.sound"];
    let prefix = format!("{}.Obligations.", cfg.ns);
    let mut bad = Vec::new();
    for line in audit.lines() {
        let name_of = |l: &str| l.trim_start_matches('\'').split('\'').next().unwrap_or("").trim_start_matches(&prefix).to_string();
        if line.contains("does not depend on any axioms") {
            report.obligations.insert(name_of(line), "proved".into());
            continue;
        }
        if let Some((name, rest)) = line.split_once("depends on axioms:") {
            let axioms: Vec<&str> = rest.trim().trim_start_matches('[').trim_end_matches(']').split(',').map(|s| s.trim()).filter(|s| !s.is_empty()).collect();
            let extra: Vec<&str> = axioms.iter().copied().filter(|a| !allowed.contains(a)).collect();
            let n = name_of(name);
            if extra.is_empty() {
                report.obligations.insert(n, "proved".into());
            } else {
                let status = if extra.contains(&"sorryAx") { "sorry".to_string() } else { format!("axiom:{}", extra.join(",")) };
                report.obligations.insert(n.clone(), status);
                bad.push(format!("{n} uses {}", extra.join(", ")));
            }
        } else if line.contains("error") {
            bad.push(line.to_string());
        }
    }
    if !bad.is_empty() {
        return Err(stage("axiom audit", format!("FAIL: axiom audit\n  {}", bad.join("\n  "))));
    }
    // Concurrent edits, build scripts and other pipeline side effects must not
    // turn a proof of the extracted program into a certificate for another one.
    let after = djinn_syntax::certificate::capture(&cfg.crate_dir).map_err(|e| stage("source snapshot", e))?;
    if certificate != after { return Err(stage("source snapshot", "source inputs changed during verification; run verification again on stable inputs".into())); }
    report.certificate = Some(certificate);
    Ok(())
}
