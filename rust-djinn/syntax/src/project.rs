//! Facts about a Djinn project shared by `cargo-djinn` (which writes the
//! report) and the `djinn!` macro (which reads it): the canonical text of a
//! declaration's tokens, which declarations it mentions, whether a declaration
//! is stale with respect to a report, and the functions present in a
//! solution directory.

use crate::ast::{Decl, Program};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Tokens as one canonical line: every token separated by a single space,
/// groups with their delimiters. Independent of the token source (the
/// compiler's tokens inside the macro, or `syn`'s when the driver parses the
/// file) and of whitespace and comments in the source.
pub fn canonical(ts: &TokenStream) -> String {
    let trees: Vec<TokenTree> = ts.clone().into_iter().collect();
    canonical_trees(&trees)
}

pub fn canonical_trees(trees: &[TokenTree]) -> String {
    let mut out = Vec::new();
    for t in trees {
        match t {
            TokenTree::Group(g) => {
                let (o, c) = match g.delimiter() {
                    Delimiter::Parenthesis => ("(", ")"),
                    Delimiter::Brace => ("{", "}"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::None => ("", ""),
                };
                let inner = canonical(&g.stream());
                if inner.is_empty() {
                    out.push(format!("{o}{c}"));
                } else {
                    out.push(format!("{o} {inner} {c}"));
                }
            }
            TokenTree::Ident(i) => out.push(i.to_string()),
            TokenTree::Punct(p) => out.push(p.as_char().to_string()),
            TokenTree::Literal(l) => out.push(l.to_string()),
        }
    }
    out.join(" ")
}

/// What the report records per declaration, computed from the parsed spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    /// `func`, `rel`, or `ambient` (an ordinary function of the file that
    /// constraints call).
    pub kind: String,
    pub tokens: String,
    /// Other declarations mentioned in the tokens, in order of first mention.
    pub uses: Vec<String>,
}

/// Entries for the declarations of a block (no ambient functions known).
pub fn index(decls: &[Decl]) -> Vec<Entry> {
    index_with(decls, &[])
}

fn index_with(decls: &[Decl], ambient: &[(String, String)]) -> Vec<Entry> {
    let names: HashSet<&str> = decls.iter().map(|d| d.name.as_str()).chain(ambient.iter().map(|(n, _)| n.as_str())).collect();
    let uses_of = |me: &str, source: &str| {
        let mut uses = Vec::new();
        for w in source.split(' ') {
            if w != me && names.contains(w) && !uses.iter().any(|u| u == w) {
                uses.push(w.to_string());
            }
        }
        uses
    };
    decls
        .iter()
        .map(|d| Entry { name: d.name.clone(), kind: d.kind.word().into(), tokens: d.source.clone(), uses: uses_of(&d.name, &d.source) })
        .chain(ambient.iter().map(|(n, src)| Entry { name: n.clone(), kind: "ambient".into(), tokens: src.clone(), uses: uses_of(n, src) }))
        .collect()
}

/// Entries for a parsed program: its declarations and its ambient functions.
pub fn index_program(prog: &Program) -> Vec<Entry> {
    let mut ambient: Vec<(String, String)> = prog.types.ambient.values().map(|a| (a.name.clone(), a.source.clone())).collect();
    ambient.sort();
    index_with(&prog.decls, &ambient)
}

/// Entries for a specification source text (empty if it does not parse).
pub fn index_text(src: &str) -> Vec<Entry> {
    crate::parse_program(src).map(|p| index_program(&p)).unwrap_or_default()
}

/// `name` and every declaration it depends on, transitively, following
/// `uses` in every given map (the report's and the current one), so that a
/// newly added mention counts as well as a removed one.
pub fn closure(name: &str, uses_maps: &[&HashMap<String, Vec<String>>]) -> Vec<String> {
    let mut out: Vec<String> = vec![name.to_string()];
    let mut i = 0;
    while i < out.len() {
        let n = out[i].clone();
        for m in uses_maps {
            for u in m.get(&n).into_iter().flatten() {
                if !out.contains(u) {
                    out.push(u.clone());
                }
            }
        }
        i += 1;
    }
    out
}

/// Is `name` stale with respect to a report? `Some(decl)` names the first
/// declaration in its closure whose tokens differ from the report (or that
/// the report does not know).
pub fn stale(name: &str, report: &HashMap<String, Entry>, current: &HashMap<String, Entry>) -> Option<String> {
    let ru: HashMap<String, Vec<String>> = report.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
    let cu: HashMap<String, Vec<String>> = current.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
    for d in closure(name, &[&ru, &cu]) {
        match (report.get(&d), current.get(&d)) {
            (Some(r), Some(c)) if r.tokens == c.tokens && r.kind == c.kind => {}
            _ => return Some(d),
        }
    }
    None
}

/// Does solution code other than the definition of `name` itself mention the
/// identifier `name`? Then a function the specification no longer declares is
/// a helper that verified code depends on, and must stay.
pub fn rust_fn_referenced(dir: &Path, name: &str) -> bool {
    use quote::ToTokens;
    fn has_ident(ts: TokenStream, name: &str) -> bool {
        ts.into_iter().any(|t| match t {
            TokenTree::Ident(i) => i == name,
            TokenTree::Group(g) => has_ident(g.stream(), name),
            _ => false,
        })
    }
    fn scan(items: &[syn::Item], name: &str) -> bool {
        items.iter().any(|it| match it {
            syn::Item::Fn(f) if f.sig.ident == name => false,
            syn::Item::Mod(m) => m.content.as_ref().map(|(_, items)| scan(items, name)).unwrap_or(false),
            other => has_ident(other.to_token_stream(), name),
        })
    }
    let mut files = Vec::new();
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
    walk(dir, &mut files);
    files.iter().any(|f| fs::read_to_string(f).ok().and_then(|s| syn::parse_file(&s).ok()).map(|ast| scan(&ast.items, name)).unwrap_or(false))
}

/// Names of functions defined in a solution directory (every `.rs` file,
/// recursively, including inline modules).
pub fn solution_fns_in(dir: &Path) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(dir: &Path, out: &mut Vec<String>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().map(|x| x == "rs").unwrap_or(false) {
                if let Ok(src) = fs::read_to_string(&p) {
                    if let Ok(file) = syn::parse_file(&src) {
                        collect(&file.items, out);
                    }
                }
            }
        }
    }
    fn collect(items: &[syn::Item], out: &mut Vec<String>) {
        for it in items {
            match it {
                syn::Item::Fn(f) => out.push(f.sig.ident.to_string()),
                syn::Item::Mod(m) => {
                    if let Some((_, items)) = &m.content {
                        collect(items, out);
                    }
                }
                _ => {}
            }
        }
    }
    walk(dir, &mut out);
    out
}

/// A file of the specification, and the Rust module it is (`a::b`; `None`
/// for the crate root).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecFile {
    pub path: std::path::PathBuf,
    pub module: Option<String>,
}

/// The specification files of a crate. `manual` is the `spec` setting
/// (`spec = "src/spec.rs"` or `spec = ["src/a.rs", "src/b.rs"]`), taken as
/// given; without it, every `.rs` file under `src/` with a top-level
/// `djinn!` block, except `src/bin/` (other crates than the library), in
/// path order.
pub fn spec_files(crate_dir: &Path, manual: Option<&[String]>) -> Vec<SpecFile> {
    let paths: Vec<std::path::PathBuf> = match manual {
        Some(v) => v.iter().map(|p| crate_dir.join(p)).collect(),
        None => {
            fn walk(d: &Path, v: &mut Vec<std::path::PathBuf>) {
                for e in fs::read_dir(d).into_iter().flatten().flatten() {
                    let p = e.path();
                    if p.is_dir() {
                        walk(&p, v);
                    } else if p.extension().is_some_and(|x| x == "rs") {
                        v.push(p);
                    }
                }
            }
            let src = crate_dir.join("src");
            let mut v = Vec::new();
            for e in fs::read_dir(&src).into_iter().flatten().flatten() {
                let p = e.path();
                if p.is_dir() && p.file_name().is_some_and(|n| n != "bin") {
                    walk(&p, &mut v);
                } else if p.extension().is_some_and(|x| x == "rs") {
                    // a binary's root next to a library belongs to another crate
                    if !(p.file_name().is_some_and(|n| n == "main.rs") && src.join("lib.rs").exists()) {
                        v.push(p);
                    }
                }
            }
            v.sort();
            v.into_iter().filter(|p| fs::read_to_string(p).is_ok_and(|s| has_djinn(&s))).collect()
        }
    };
    paths.into_iter().map(|path| SpecFile { module: module_of(crate_dir, &path), path }).collect()
}

/// The Rust module of a source file, from its place under `src/`:
/// `src/a/b.rs` and `src/a/b/mod.rs` are `a::b`, `src/lib.rs` and
/// `src/main.rs` the crate root. A file outside `src/` is named by its stem.
pub fn module_of(crate_dir: &Path, path: &Path) -> Option<String> {
    let rel = path.strip_prefix(crate_dir.join("src")).ok();
    let Some(rel) = rel else {
        let stem = path.file_stem()?.to_string_lossy().into_owned();
        return (stem != "lib" && stem != "main").then_some(stem);
    };
    let mut parts: Vec<String> = rel.with_extension("").iter().map(|c| c.to_string_lossy().into_owned()).collect();
    if parts.last().is_some_and(|l| l == "mod") || (parts.len() == 1 && (parts[0] == "lib" || parts[0] == "main")) {
        parts.pop();
    }
    (!parts.is_empty()).then(|| parts.join("::"))
}

/// Does a source text have a top-level `djinn!` block (or the older
/// `func!`/`rel!` forms)? A text that does not parse counts if it mentions
/// `djinn!`, so that its error is reported rather than the file ignored.
pub fn has_djinn(src: &str) -> bool {
    if !(src.contains("djinn!") || src.contains("func!") || src.contains("rel!")) {
        return false;
    }
    match syn::parse_file(src) {
        Ok(f) => f.items.iter().any(|it| match it {
            syn::Item::Macro(m) => m.mac.path.segments.last().is_some_and(|s| matches!(s.ident.to_string().as_str(), "djinn" | "func" | "rel")),
            _ => false,
        }),
        Err(_) => src.contains("djinn!"),
    }
}

/// The program of several specification files' texts (see
/// `crate::parse_sources`), indexed.
pub fn index_texts(srcs: &[String]) -> Vec<Entry> {
    crate::parse_sources(srcs).map(|p| index_program(&p)).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn modules() {
        let c = Path::new("/c");
        assert_eq!(module_of(c, Path::new("/c/src/lib.rs")), None);
        assert_eq!(module_of(c, Path::new("/c/src/spec.rs")), Some("spec".into()));
        assert_eq!(module_of(c, Path::new("/c/src/a/b.rs")), Some("a::b".into()));
        assert_eq!(module_of(c, Path::new("/c/src/a/mod.rs")), Some("a".into()));
        assert_eq!(module_of(c, Path::new("/c/spec/x.rs")), Some("x".into()));
    }
    #[test]
    fn merged() {
        let a = "djinn! { pub fn f(x: u32) -> y: u32 { y == g(x); } }".to_string();
        let b = "djinn! { pub fn g(x: u32) -> y: u32 { y == x; } }".to_string();
        let p = crate::parse_sources(&[a.clone(), b.clone()]).unwrap();
        assert_eq!(p.origin["f"], 0);
        assert_eq!(p.origin["g"], 1);
        // `g` is lowered before its caller `f`, though it comes later
        let order: Vec<&str> = crate::dependency_order(&p.decls).iter().map(|d| d.name.as_str()).collect();
        assert_eq!(order, ["g", "f"]);
        assert!(crate::lower_program(&p).is_ok());
        let e = crate::parse_sources(&[a.clone(), a]).unwrap_err();
        assert_eq!(e.file, 1);
    }
}
