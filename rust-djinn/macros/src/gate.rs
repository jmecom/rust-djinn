//! The compile-time gate: a `fn` of the specification compiles only if the
//! verifier's report (`<work_dir>/report.toml`) says it is implemented and
//! every obligation of it and of what it uses is proved, and if its tokens
//! (and those of what it uses) are the ones that were verified. Otherwise
//! the expansion carries a `compile_error!` at the function's name.
//!
//! Exempt: the verifier's own build (`DJINN_VERIFYING`), builds inside a
//! jail (`in_jail` in the crate metadata), Clippy (`CLIPPY_ARGS`), and
//! anything run with `DJINN_GATE=off` (the shipped rust-analyzer configs).

use djinn_syntax::project::{index, stale, Entry};
use djinn_syntax::{Decl, Kind};
use quote::{quote, quote_spanned};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

pub(crate) struct Project {
    pub(crate) crate_dir: PathBuf,
    /// The specification files (see `djinn_syntax::project::spec_files`).
    pub(crate) specs: Vec<PathBuf>,
    pub(crate) solution: PathBuf,
    report: PathBuf,
    report_rel: String,
    in_jail: bool,
}

pub(crate) fn project() -> Option<Project> {
    let dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").ok()?);
    let text = fs::read_to_string(dir.join("Cargo.toml")).ok()?;
    let toml: toml::Value = toml::from_str(&text).ok()?;
    let meta = toml.get("package").and_then(|p| p.get("metadata")).and_then(|m| m.get("djinn")).cloned().unwrap_or(toml::Value::Table(Default::default()));
    let get = |k: &str| meta.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    let work = get("work_dir").unwrap_or_else(|| "djinn".into());
    let manual: Option<Vec<String>> = match meta.get("spec") {
        Some(toml::Value::String(p)) => Some(vec![p.clone()]),
        Some(toml::Value::Array(a)) => Some(a.iter().filter_map(|x| x.as_str().map(|s| s.to_string())).collect()),
        _ => None,
    };
    Some(Project {
        crate_dir: dir.clone(),
        specs: djinn_syntax::project::spec_files(&dir, manual.as_deref()).into_iter().map(|f| f.path).collect(),
        solution: dir.join(&work).join("solution"),
        report: dir.join(&work).join("report.toml"),
        report_rel: format!("{work}/report.toml"),
        in_jail: meta.get("in_jail").and_then(|v| v.as_bool()).unwrap_or(false),
    })
}

impl Project {
    /// The specification files' texts (`None` if one cannot be read).
    pub(crate) fn texts(&self) -> Option<Vec<String>> {
        self.specs.iter().map(|p| fs::read_to_string(p).ok()).collect()
    }
}

fn gate_off(p: &Project) -> bool {
    let off = |k: &str| std::env::var(k).map(|v| matches!(v.as_str(), "off" | "0" | "false")).unwrap_or(false);
    p.in_jail || off("DJINN_GATE") || std::env::var_os("DJINN_VERIFYING").is_some() || std::env::var_os("CLIPPY_ARGS").is_some()
}

/// The report's entries, and per declaration its `ok` verdict with the
/// reasons it is not ok.
struct GateReport {
    entries: HashMap<String, Entry>,
    verdicts: HashMap<String, (bool, Vec<String>)>,
    certificate: Option<djinn_syntax::certificate::Certificate>,
}

fn read_report(p: &Project) -> Option<GateReport> {
    let text = fs::read_to_string(&p.report).ok()?;
    let v: toml::Value = toml::from_str(&text).ok()?;
    let mut entries = HashMap::new();
    let mut verdicts = HashMap::new();
    for d in v.get("decl").and_then(|d| d.as_array()).into_iter().flatten() {
        let name = d.get("name").and_then(|x| x.as_str()).unwrap_or("").to_string();
        let kind = d.get("kind").and_then(|x| x.as_str()).unwrap_or("func").to_string();
        let tokens = d.get("tokens").and_then(|x| x.as_str()).unwrap_or("").to_string();
        let uses: Vec<String> = d.get("uses").and_then(|x| x.as_array()).into_iter().flatten().filter_map(|x| x.as_str().map(|s| s.to_string())).collect();
        let ok = d.get("ok").and_then(|x| x.as_bool()).unwrap_or(false);
        let implemented = d.get("implemented").and_then(|x| x.as_bool()).unwrap_or(false);
        let mut problems = Vec::new();
        if !implemented {
            problems.push("not implemented".to_string());
        }
        if let Some(obs) = d.get("obligations").and_then(|x| x.as_table()) {
            let mut keys: Vec<&String> = obs.keys().collect();
            keys.sort();
            for k in keys {
                let st = obs[k].as_str().unwrap_or("?");
                if st != "proved" {
                    problems.push(format!("{name}.{k}: {st}"));
                }
            }
        }
        entries.insert(name.clone(), Entry { name: name.clone(), kind, tokens, uses });
        verdicts.insert(name, (ok, problems));
    }
    let certificate = v.get("certificate").cloned().and_then(|c| c.try_into().ok());
    Some(GateReport { entries, verdicts, certificate })
}

/// Tokens to prepend to a block's expansion: dependency trackers, and one
/// `compile_error!` per `fn` that may not be compiled.
pub fn check(decls: &[Decl], project: Option<&Project>) -> proc_macro2::TokenStream {
    let mut out = proc_macro2::TokenStream::new();
    // Charon's rustc pass (`CHARON_*` in its environment) must see only the
    // stubs: the trackers below would become Lean constants holding the whole
    // report as a byte array. Charon's build is fingerprinted separately
    // (it runs through a rustc wrapper), so omitting them there is safe.
    if std::env::vars_os().any(|(k, _)| k.to_string_lossy().starts_with("CHARON_")) {
        return out;
    }
    let Some(p) = project else { return out };
    // cargo re-expands when these change: the report, and the gate's environment
    if p.report.exists() {
        let path = p.report.to_string_lossy().into_owned();
        out.extend(quote! { const _: &[u8] = include_bytes!(#path); });
    }
    out.extend(quote! {
        const _: (Option<&str>, Option<&str>, Option<&str>) = (option_env!("DJINN_GATE"), option_env!("DJINN_VERIFYING"), option_env!("CLIPPY_ARGS"));
    });
    if gate_off(p) {
        return out;
    }
    let report = read_report(p);
    let certificate = report.as_ref().and_then(|r| r.certificate.as_ref()).filter(|recorded| {
        recorded.version == djinn_syntax::certificate::VERSION
            && djinn_syntax::certificate::capture(&p.crate_dir).is_ok_and(|current| &current == *recorded)
    });
    if let Some(certificate) = certificate {
        for guard in &certificate.cfg {
            let Ok(predicate) = guard.predicate.parse::<proc_macro2::TokenStream>() else { continue };
            let condition = if guard.enabled { quote! { not(#predicate) } } else { quote! { #predicate } };
            let msg = format!("djinn: build configuration differs from verification ({})", guard.predicate);
            out.extend(quote! { #[cfg(#condition)] compile_error!(#msg); });
        }
    }
    let implemented = djinn_syntax::project::solution_fns_in(&p.solution);
    // the current declarations: the whole specification when it parses
    // (a used declaration may live in another block), else this block
    let mut current: HashMap<String, Entry> = {
        let all = p.texts().map(|t| djinn_syntax::project::index_texts(&t)).unwrap_or_default();
        let v = if all.is_empty() { index(decls) } else { all };
        v.into_iter().map(|e| (e.name.clone(), e)).collect()
    };
    // The compiler's actual invocation is authoritative, including relations
    // used by an unchanged function. Discovery only supplies other context.
    let names: Vec<String> = current.keys().cloned().chain(decls.iter().map(|d| d.name.clone())).collect();
    for d in decls {
        let uses = d.source.split(' ').filter(|word| *word != d.name && names.iter().any(|n| n == word))
            .map(str::to_string).collect();
        current.insert(d.name.clone(), Entry { name: d.name.clone(), kind: d.kind.word().into(), tokens: d.source.clone(), uses });
    }
    // implementations of functions the specification no longer declares: live,
    // unverifiable code until `translate` archives them — unless other solution
    // code calls them (then they are helpers of verified functions)
    if let Some(GateReport { entries, .. }) = &report {
        let mut orphans: Vec<String> = entries
            .iter()
            .filter(|(n, e)| e.kind == "func" && !current.contains_key(*n))
            .map(|(n, _)| n.clone())
            .filter(|f| implemented.contains(f) && !djinn_syntax::project::rust_fn_referenced(&p.solution, f))
            .collect();
        orphans.sort();
        for n in orphans {
            let msg = format!("djinn: `solution::{n}` implements a function the specification no longer declares, so nothing verifies it; run `cargo djinn translate` to archive it");
            out.extend(quote! { compile_error!(#msg); });
        }
    }
    for d in decls {
        let name = &d.name;
        let word = d.kind.word();
        let msg = match &report {
            None => format!("djinn {word} `{name}`: the crate has not been verified (no {}); run `cargo djinn implement`", p.report_rel),
            Some(GateReport { entries, verdicts, .. }) => match verdicts.get(name) {
                None => format!("djinn {word} `{name}` was never attempted (not in {}); run `cargo djinn implement`", p.report_rel),
                Some((ok, problems)) => {
                    if entries.get(name).is_none_or(|entry| entry.tokens != d.source || entry.kind != word) {
                        format!("djinn {word} `{name}` does not match the declaration actually expanded; run `cargo djinn verify`")
                    } else if d.kind == Kind::Func && !implemented.contains(name) {
                        format!("djinn {word} `{name}` has no current implementation; run `cargo djinn implement`")
                    } else if certificate.is_none() {
                        format!("djinn {word} `{name}`: verification certificate is missing or stale; run `cargo djinn verify`")
                    } else if let Some(which) = stale(name, entries, &current) {
                        if &which == name {
                            format!("djinn {word} `{name}` changed since it was verified; run `cargo djinn implement`")
                        } else {
                            format!("djinn {word} `{name}` uses `{which}`, which changed since `{name}` was verified; run `cargo djinn implement`")
                        }
                    } else if *ok {
                        continue;
                    } else {
                        // own problems, then those of the declarations it uses
                        let uses_map: HashMap<String, Vec<String>> = entries.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
                        let mut all = problems.clone();
                        for u in djinn_syntax::project::closure(name, &[&uses_map]).iter().skip(1) {
                            if let Some((_, ps)) = verdicts.get(u) {
                                all.extend(ps.iter().filter(|x| *x != "not implemented").cloned());
                            }
                        }
                        if all.is_empty() {
                            all.push("not verified".into());
                        }
                        format!("djinn {word} `{name}` is not verified ({}); run `cargo djinn implement`", all.join(", "))
                    }
                }
            },
        };
        out.extend(quote_spanned! { d.name_span => compile_error!(#msg); });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    struct Fixture { project: Project, decls: Vec<Decl> }
    impl Fixture {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!("djinn-gate-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir_all(root.join("src")).unwrap();
            fs::create_dir_all(root.join("djinn/solution")).unwrap();
            fs::write(root.join("Cargo.toml"), "[package]\nname='gate_test'\nversion='0.1.0'\n[workspace]\n").unwrap();
            let source = "djinn! { pub fn f() -> r: bool { r == true; } }";
            fs::write(root.join("src/lib.rs"), source).unwrap();
            fs::write(root.join("djinn/solution/mod.rs"), "pub fn f() -> bool { true }").unwrap();
            let decls = djinn_syntax::parse_program(source).unwrap().decls;
            Self { project: Project { crate_dir: root.clone(), specs: vec![root.join("src/lib.rs")], solution: root.join("djinn/solution"), report: root.join("djinn/report.toml"), report_rel: "djinn/report.toml".into(), in_jail: false }, decls }
        }
        fn report(&self, certificate: bool) {
            let mut value = toml::map::Map::new();
            let declarations = self.decls.iter().map(|entry| {
                let mut declaration = toml::map::Map::new();
                for (key, value) in [("name", entry.name.as_str()), ("kind", entry.kind.word()), ("tokens", &entry.source)] { declaration.insert(key.into(), toml::Value::String(value.into())); }
                declaration.insert("implemented".into(), toml::Value::Boolean(true));
                declaration.insert("ok".into(), toml::Value::Boolean(true));
                toml::Value::Table(declaration)
            }).collect();
            value.insert("decl".into(), toml::Value::Array(declarations));
            if certificate { value.insert("certificate".into(), toml::Value::try_from(djinn_syntax::certificate::capture(&self.project.crate_dir).unwrap()).unwrap()); }
            fs::write(&self.project.report, toml::to_string(&value).unwrap()).unwrap();
        }
    }
    impl Drop for Fixture { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.project.crate_dir); } }

    #[test]
    fn gate_rejects_legacy_modified_and_deleted_implementations() {
        let f = Fixture::new();
        f.report(false);
        assert!(check(&f.decls, Some(&f.project)).to_string().contains("certificate is missing or stale"));
        f.report(true);
        assert!(!check(&f.decls, Some(&f.project)).to_string().contains("djinn func"));
        fs::write(f.project.solution.join("mod.rs"), "pub fn f() -> bool { false }").unwrap();
        assert!(check(&f.decls, Some(&f.project)).to_string().contains("certificate is missing or stale"));
        fs::remove_file(f.project.solution.join("mod.rs")).unwrap();
        assert!(check(&f.decls, Some(&f.project)).to_string().contains("has no current implementation"));
    }

    #[test]
    fn actual_macro_input_must_match_even_with_fresh_files() {
        let f = Fixture::new();
        f.report(true);
        let actual = djinn_syntax::parse_program("djinn! { pub fn f() -> r: bool { r == false; } }").unwrap().decls;
        assert!(check(&actual, Some(&f.project)).to_string().contains("does not match the declaration actually expanded"));
    }
    #[test]
    fn changed_relation_cannot_authorize_an_unchanged_function() {
        let mut f = Fixture::new();
        let source = "djinn! { rel p(x: bool) { x == true; } pub fn f() -> r: bool { p(r); } }";
        fs::write(&f.project.specs[0], source).unwrap();
        f.decls = djinn_syntax::parse_program(source).unwrap().decls;
        f.report(true);
        let actual = djinn_syntax::parse_program(&source.replace("x == true", "x == false")).unwrap().decls;
        let result = check(&actual, Some(&f.project)).to_string();
        assert!(result.contains("djinn rel `p` does not match the declaration actually expanded"));
        assert!(result.contains("uses `p`, which changed"));
    }

}
