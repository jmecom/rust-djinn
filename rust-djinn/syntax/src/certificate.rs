//! Versioned input certificates shared by the verifier and the compile gate.
//!
//! This is a freshness check, not a signature: the report and the Rust/Lean
//! toolchains are trusted. The verifier's own registry dependencies are bound
//! by Cargo.lock and Cargo's checksum checks. Runtime dependencies currently
//! require local, feature-free sources, which are hashed recursively.
//! Unsupported generated or external inputs fail closed instead of being
//! silently left out of the certificate.

use proc_macro2::{TokenStream, TokenTree};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use syn::visit::Visit;
use syn::ext::IdentExt;

pub const VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CfgGuard {
    pub predicate: String,
    pub enabled: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Certificate {
    pub version: u32,
    pub digest: String,
    /// Evaluated in the consuming crate, not in the procedural macro's host.
    pub cfg: Vec<CfgGuard>,
}

/// Capture all supported local inputs. Absolute checkout locations are not
/// hashed, so an unchanged checkout and dependency graph may be relocated.
pub fn capture(crate_dir: &Path) -> Result<Certificate, String> {
    for (key, value) in std::env::vars_os() {
        let key = key.to_string_lossy();
        if !value.is_empty() && (["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"].contains(&key.as_ref())
            || key.starts_with("CARGO_TARGET_") && key.ends_with("_RUSTFLAGS")) {
            return Err(format!("cannot certify Cargo override {key}; verify with the default build configuration"));
        }
    }
    let root = crate_dir.canonicalize().map_err(|e| format!("{}: {e}", crate_dir.display()))?;
    let manifest = read_manifest(&root)?;
    let mut inputs = BTreeMap::new();
    let mut seen = BTreeSet::new();
    package(&root, "crate", true, &mut seen, &mut inputs)?;
    // Cargo reads every ancestor configuration, even above the workspace.
    let mut workspace_seen = manifest.get("workspace").is_some();
    for (depth, ancestor) in root.ancestors().enumerate() {
        for name in [".cargo/config", ".cargo/config.toml"] {
            cargo_config(&ancestor.join(name), format!("cargo-config/{depth}/{name}"), &mut inputs)?;
        }
        if !workspace_seen && ancestor != root && ancestor.join("Cargo.toml").exists() {
            let value = read_manifest(ancestor)?;
            if value.get("workspace").is_some() {
                workspace_seen = true;
                insert_file(&ancestor.join("Cargo.toml"), "workspace/Cargo.toml".into(), &mut inputs)?;
                if ancestor.join("Cargo.lock").exists() {
                    insert_file(&ancestor.join("Cargo.lock"), "workspace/Cargo.lock".into(), &mut inputs)?;
                }
                let mut dependencies = BTreeMap::new();
                dependency_paths(&value, ancestor, false, &mut dependencies)?;
                for (name, dependency) in dependencies {
                    package(&dependency, &format!("workspace/dependency/{name}"), false, &mut seen, &mut inputs)?;
                }
            }
        }
    }
    let cargo_home = std::env::var_os("CARGO_HOME").map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|p| PathBuf::from(p).join(".cargo")));
    if let Some(home) = cargo_home {
        for name in ["config", "config.toml"] {
            cargo_config(&home.join(name), format!("cargo-home/{name}"), &mut inputs)?;
        }
    }
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc).args(["--print", "cfg"]).current_dir(&root).output()
        .map_err(|e| format!("cannot determine compiler configuration: {e}"))?;
    if !output.status.success() {
        return Err(format!("cannot determine compiler configuration: {}", String::from_utf8_lossy(&output.stderr)));
    }
    let active: BTreeSet<String> = String::from_utf8_lossy(&output.stdout).lines()
        .map(|l| l.parse::<TokenStream>().map(|t| crate::project::canonical(&t)).map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;
    if manifest.get("features").and_then(|v| v.as_table()).is_some_and(|v| !v.is_empty()) {
        return Err("Cargo features require per-configuration source certification and are not supported".into());
    }
    // These target properties also affect the integer and library semantics
    // even when the source has no explicit cfg predicate.
    let cfg = active.into_iter()
        .filter(|cfg| ["target_arch ", "target_os ", "target_env ", "target_endian ", "target_pointer_width "].iter().any(|key| cfg.starts_with(key)))
        .map(|predicate| CfgGuard { predicate, enabled: true }).collect();
    let mut digest = Sha256::new();
    digest.update(b"djinn-input-certificate-v1\0");
    for (name, bytes) in inputs {
        digest.update((name.len() as u64).to_le_bytes());
        digest.update(name.as_bytes());
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    Ok(Certificate { version: VERSION, digest: format!("{:x}", digest.finalize()), cfg })
}

fn read_manifest(dir: &Path) -> Result<toml::Value, String> {
    let path = dir.join("Cargo.toml");
    let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    toml::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))
}

fn cargo_config(path: &Path, name: String, inputs: &mut BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    if !path.exists() { return Ok(()); }
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    if ["target", "env", "paths", "source"].iter().any(|k| value.get(k).is_some())
        || value.get("build").and_then(|v| v.as_table()).is_some_and(|t| t.keys().any(|k| k != "jobs" && k != "target-dir")) {
        return Err(format!("unsupported build inputs in {}; remove target, environment, source, or compiler overrides before verification", path.display()));
    }
    insert_file(path, name, inputs)
}

fn insert_file(path: &Path, name: String, inputs: &mut BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err(format!("certificate input is not an ordinary file: {}", path.display()));
    }
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    inputs.insert(name, bytes);
    Ok(())
}

fn package(root: &Path, label: &str, primary: bool, seen: &mut BTreeSet<PathBuf>, inputs: &mut BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let root = root.canonicalize().map_err(|e| format!("{}: {e}", root.display()))?;
    if !seen.insert(root.clone()) { return Ok(()); }
    let manifest = read_manifest(&root)?;
    let meta = manifest.get("package").and_then(|v| v.get("metadata")).and_then(|v| v.get("djinn"));
    let work = meta.and_then(|m| m.get("work_dir")).and_then(|v| v.as_str()).unwrap_or("djinn");
    let proofs = meta.and_then(|m| m.get("proofs")).and_then(|v| v.as_str()).map(PathBuf::from).unwrap_or_else(|| PathBuf::from(work).join("proofs"));
    if [Path::new(work), proofs.as_path()].iter().any(|p| p.is_absolute() || p.components().any(|c| matches!(c, std::path::Component::ParentDir))) {
        return Err("certificate work/proof directories must stay inside the crate".into());
    }
    // Djinn's own dependencies are the trusted verifier implementation. Other
    // local runtime dependencies must not choose unrecorded build variants.
    // The source root of the verifier that was actually compiled is trusted,
    // not a package name an unrelated dependency can impersonate.
    let trusted_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().and_then(|p| p.canonicalize().ok());
    let tool = trusted_root.as_ref().is_some_and(|p| root == *p || root == p.join("macros") || root == p.join("syntax"));
    let inspect = primary || !tool;
    let mut dependencies = BTreeMap::new();
    dependency_paths(&manifest, &root, inspect, &mut dependencies)?;
    if inspect {
        let library_name = manifest.get("lib").and_then(|l| l.get("name")).and_then(|v| v.as_str())
            .or_else(|| manifest.get("package").and_then(|p| p.get("name")).and_then(|v| v.as_str())).unwrap_or("").replace('-', "_");
        if ["core", "alloc", "std", "memchr"].contains(&library_name.as_str()) {
            return Err(format!("crate name `{library_name}` is reserved for a trusted external model"));
        }
        if manifest.get("lib").and_then(|l| l.get("proc-macro")).and_then(|v| v.as_bool()) == Some(true) {
            return Err(format!("procedural macro dependencies require expanded source certification: {}", root.display()));
        }
        if root.join("build.rs").exists() || manifest.get("package").and_then(|p| p.get("build")).is_some_and(|v| v.as_bool() != Some(false)) {
            return Err(format!("build scripts are not supported certificate inputs: {}", root.display()));
        }
        if !primary && manifest.get("features").and_then(|v| v.as_table()).is_some_and(|v| !v.is_empty()) {
            return Err(format!("feature-bearing local dependency requires per-package build certification: {}", root.display()));
        }
    }
    let excluded = [proofs, PathBuf::from(work).join("report.toml")];
    for section in ["lib", "bin", "example", "test", "bench"] {
        if let Some(value) = manifest.get(section) {
            let targets: Vec<&toml::Value> = value.as_array().map(|v| v.iter().collect()).unwrap_or_else(|| vec![value]);
            for target in targets {
                if let Some(path) = target.get("path").and_then(|v| v.as_str()) {
                    if !root.join(path).canonicalize().is_ok_and(|p| input_relative(&root, &p, &excluded)) {
                        return Err(format!("external or missing Cargo target source: {path}"));
                    }
                }
            }
        }
    }
    walk(&root, &root, label, inspect, &excluded, inputs)?;
    for (name, dependency) in dependencies {
        package(&dependency, &format!("{label}/dependency/{name}"), false, seen, inputs)?;
    }
    Ok(())
}

/// Until compiler configurations can be bound per dependency, certifying
/// arbitrary registry/git crates would permit downstream feature unification
/// to change their semantics without changing this crate's own cfg values.
fn dependency_paths(value: &toml::Value, root: &Path, inspect: bool, out: &mut BTreeMap<String, PathBuf>) -> Result<(), String> {
    for section in ["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(dependencies) = value.get(section).and_then(|v| v.as_table()) {
            for (name, definition) in dependencies {
                if inspect && (definition.get("optional").and_then(|v| v.as_bool()) == Some(true)
                    || definition.get("features").and_then(|v| v.as_array()).is_some_and(|v| !v.is_empty())
                    || definition.get("default-features").is_some()) {
                    return Err(format!("dependency `{name}` selects unbound Cargo features"));
                }
                let inherited;
                let (definition, base) = if definition.get("workspace").and_then(|v| v.as_bool()) == Some(true) {
                    let (base, workspace) = root.ancestors().find_map(|p| {
                        read_manifest(p).ok().filter(|m| m.get("workspace").is_some()).map(|m| (p, m))
                    }).ok_or_else(|| format!("cannot resolve workspace dependency {name}"))?;
                    inherited = workspace.get("workspace").and_then(|w| w.get("dependencies")).and_then(|d| d.get(name))
                        .cloned().ok_or_else(|| format!("cannot resolve workspace dependency {name}"))?;
                    (&inherited, base)
                } else { (definition, root) };
                if inspect && ["std", "core", "alloc"].contains(&name.as_str()) {
                    return Err(format!("dependency alias `{name}` shadows a trusted compiler namespace"));
                }
                let path = definition.get("path").and_then(|v| v.as_str());
                if inspect && (path.is_none() || definition.get("optional").and_then(|v| v.as_bool()) == Some(true)) {
                    return Err(format!("dependency `{name}` requires per-dependency compiler certification; only non-optional local runtime dependencies are currently supported"));
                }
                if let Some(path) = path { out.insert(name.clone(), base.join(path)); }
            }
        }
    }
    for section in ["target", "patch", "replace"] {
        if let Some(tables) = value.get(section).and_then(|v| v.as_table()) {
            for (name, table) in tables {
                if section == "target" { dependency_paths(table, root, inspect, out)?; }
                else if let Some(path) = table.get("path").and_then(|v| v.as_str()) { out.insert(name.clone(), root.join(path)); }
                else if let Some(replacements) = table.as_table() {
                    for (name, definition) in replacements {
                        if let Some(path) = definition.get("path").and_then(|v| v.as_str()) { out.insert(name.clone(), root.join(path)); }
                    }
                }
            }
        }
    }
    Ok(())
}

fn walk(root: &Path, dir: &Path, label: &str, inspect: bool, excluded: &[PathBuf], inputs: &mut BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let mut paths = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?
        .map(|e| e.map(|e| e.path())).collect::<Result<Vec<_>, _>>().map_err(|e| e.to_string())?;
    paths.sort();
    for path in paths {
        let rel = path.strip_prefix(root).map_err(|e| e.to_string())?;
        let name = path.file_name().and_then(|v| v.to_str()).ok_or("non-UTF-8 certificate path")?;
        if (rel.components().count() == 1 && [".git", "target", ".djinnscratch", ".lake"].contains(&name)) || excluded.iter().any(|e| rel.starts_with(e)) { continue; }
        let metadata = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
        if metadata.file_type().is_symlink() { return Err(format!("certificate input is a symlink: {}", path.display())); }
        if metadata.is_dir() {
            walk(root, &path, label, inspect, excluded, inputs)?;
        } else {
            if inspect && path.extension().is_some_and(|e| e == "rs") {
                let text = fs::read_to_string(&path).map_err(|e| e.to_string())?;
                let parsed = syn::parse_file(&text).map_err(|e| format!("{}: {e}", path.display()))?;
                let local_macros = parsed.items.iter().filter_map(|item| match item {
                    syn::Item::Macro(m) if m.mac.path.is_ident("macro_rules") => m.ident.as_ref().map(|i| i.unraw().to_string()),
                    _ => None,
                }).collect();
                let mut visitor = Inputs { root, file: &path, excluded, local_macros, error: None };
                visitor.visit_file(&parsed);
                if let Some(error) = visitor.error { return Err(error); }
            }
            insert_file(&path, format!("{label}/{}", rel.to_string_lossy().replace('\\', "/")), inputs)?;
        }
    }
    Ok(())
}

struct Inputs<'a> {
    root: &'a Path,
    file: &'a Path,
    excluded: &'a [PathBuf],
    local_macros: BTreeSet<String>,
    error: Option<String>,
}

fn input_relative(root: &Path, path: &Path, excluded: &[PathBuf]) -> bool {
    path.strip_prefix(root).is_ok_and(|rel| {
        !excluded.iter().any(|excluded| rel.starts_with(excluded))
            && !rel.iter().next().is_some_and(|c| ["target", ".git", ".lake", ".djinnscratch"].iter().any(|n| c == *n))
    })
}

/// Expression fragments are opaque Rust ASTs. Unlike ident/tt/path fragments,
/// substituting one cannot assemble a fresh macro name, import, or attribute.
/// Keep this small subset for ordinary expression helpers such as require!.
fn expression_macro(tokens: TokenStream) -> bool {
    fn flatten(tokens: TokenStream, out: &mut Vec<TokenTree>) {
        for token in tokens {
            if let TokenTree::Group(group) = &token { flatten(group.stream(), out); }
            else { out.push(token); }
        }
    }
    let mut flattened = Vec::new();
    flatten(tokens, &mut flattened);
    let tokens = flattened;
    let mut binders = BTreeSet::new();
    for window in tokens.windows(4) {
        if let [TokenTree::Punct(dollar), TokenTree::Ident(name), TokenTree::Punct(colon), TokenTree::Ident(fragment)] = window {
            if dollar.as_char() == '$' && colon.as_char() == ':' {
                if fragment != "expr" { return false; }
                binders.insert(name.to_string());
            }
        }
    }
    tokens.windows(2).all(|pair| match pair {
        [TokenTree::Punct(dollar), TokenTree::Ident(name)] if dollar.as_char() == '$' => binders.contains(&name.to_string()),
        _ => true,
    }) && !tokens.iter().any(|t| matches!(t, TokenTree::Ident(name) if name == "macro_rules"))
}

const STANDARD_MACROS: &[&str] = &["assert", "assert_eq", "assert_ne", "debug_assert", "debug_assert_eq", "debug_assert_ne", "matches", "vec", "format", "format_args", "print", "println", "eprint", "eprintln", "write", "writeln", "panic", "unreachable", "unimplemented", "todo", "concat", "stringify", "line", "column", "file", "module_path", "compile_error", "thread_local", "cfg", "env", "option_env", "include", "include_str", "include_bytes"];

fn path_name(path: &syn::Path) -> String {
    path.segments.last().map(|s| s.ident.unraw().to_string()).unwrap_or_default()
}

impl<'ast> Visit<'ast> for Inputs<'_> {
    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if item.mac.path.is_ident("macro_rules") && item.ident.as_ref().is_some_and(|name| {
            let name = name.unraw().to_string();
            STANDARD_MACROS.contains(&name.as_str()) || ["djinn", "func", "rel"].contains(&name.as_str())
        }) {
            self.error = Some("shadowed standard or Djinn macros require expanded source certification".into());
            return;
        }
        syn::visit::visit_item_macro(self, item);
    }
    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        fn check(tree: &syn::UseTree, prefix: &str) -> bool {
            match tree {
                syn::UseTree::Glob(_) => prefix == "spec::" || prefix == "crate::spec::",
                syn::UseTree::Rename(_) => false,
                syn::UseTree::Group(group) => group.items.iter().all(|tree| check(tree, prefix)),
                syn::UseTree::Path(path) => check(&path.tree, &format!("{prefix}{}::", path.ident.unraw())),
                syn::UseTree::Name(name) => {
                    let name = name.ident.unraw().to_string();
                    if matches!(name.as_str(), "djinn" | "func" | "rel") { return prefix == "djinn::"; }
                    !STANDARD_MACROS.contains(&name.as_str()) && !["derive", "std", "core", "alloc"].contains(&name.as_str())
                }
            }
        }
        if !check(&item.tree, "") { self.error = Some("macro aliases, wildcard imports, and shadowed built-ins require expanded source certification".into()); }
        syn::visit::visit_item_use(self, item);
    }
    fn visit_item_extern_crate(&mut self, _item: &'ast syn::ItemExternCrate) {
        self.error = Some("extern crate declarations require expanded source certification".into());
    }
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if ["std", "core", "alloc", "djinn"].contains(&item.ident.unraw().to_string().as_str()) {
            self.error = Some("shadowed compiler/tool namespaces are not supported certificate inputs".into());
        }
        // Unit-test modules are not part of the extracted library.
        if item.attrs.iter().any(|a| path_name(a.path()) == "cfg" && a.parse_args::<syn::Path>().is_ok_and(|p| path_name(&p) == "test")) { return; }
        if item.content.is_none() && !item.attrs.iter().any(|a| path_name(a.path()) == "path") {
            let parent = self.file.parent().unwrap_or(self.root);
            let stem = self.file.file_stem().and_then(|v| v.to_str()).unwrap_or("");
            let base = if ["lib", "main", "mod"].contains(&stem) { parent.to_path_buf() } else { parent.join(stem) };
            let name = item.ident.unraw().to_string();
            for path in [base.join(format!("{name}.rs")), base.join(&name).join("mod.rs")] {
                if path.exists() { self.check_input_path(&path); }
            }
        }
        syn::visit::visit_item_mod(self, item);
    }
    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        let name = path_name(attr.path());
        if attr.path().segments.len() != 1 {
            self.error = Some("qualified attributes require expanded source certification".into());
            return;
        }
        if name == "cfg" {
            self.error = Some("conditional source requires expanded source certification".into());
        } else if name == "cfg_attr" {
            self.error = Some("cfg_attr inputs require compiler-expanded certification and are not supported".into());
        } else if name == "path" {
            if let syn::Meta::NameValue(v) = &attr.meta {
                if let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(path), .. }) = &v.value {
                    self.check_path(&path.value());
                }
            }
        } else if name == "derive" {
            let names = attr.parse_args_with(syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated);
            if !names.is_ok_and(|names| names.iter().all(|p| p.segments.len() == 1 && ["Clone", "Copy", "Debug", "Default", "PartialEq", "Eq", "PartialOrd", "Ord", "Hash"].contains(&path_name(p).as_str()))) {
                self.error = Some("custom derive macros require expanded source certification".into());
            }
        } else if !["doc", "repr", "allow", "warn", "deny", "forbid", "expect", "inline", "cold", "must_use", "deprecated", "track_caller", "test", "ignore", "should_panic", "no_mangle", "export_name", "link_name", "link_section", "non_exhaustive"].contains(&name.as_str())
 {
            self.error = Some(format!("attribute `{name}` requires expanded source certification"));
        }
        syn::visit::visit_attribute(self, attr);
    }
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        let name = path_name(&mac.path);
        if mac.path.segments.len() > 1 {
            let first = mac.path.segments.first().unwrap().ident.unraw().to_string();
            let standard = ["std", "core", "alloc"].contains(&first.as_str()) && STANDARD_MACROS.contains(&name.as_str());
            let djinn = first == "djinn" && ["djinn", "func", "rel"].contains(&name.as_str());
            if mac.path.segments.len() != 2 || !(standard || djinn) {
                self.error = Some("qualified user macros require expanded source certification".into());
                return;
            }
        }
        // These trusted macros parse a specification language; their
        // requires/ensures attributes are not generated Rust attributes.
        match name.as_str() {
            "djinn" | "func" | "rel" => return,
            "macro_rules" if !expression_macro(mac.tokens.clone()) => {
                self.error = Some("only expression-fragment macro_rules helpers are supported certificate inputs".into());
            }
            "file" => self.error = Some("location-dependent file! inputs are not portable certificate inputs".into()),
            "cfg" => self.error = Some("conditional source requires expanded source certification".into()),
            "env" | "option_env" => self.error = Some("environment-derived source inputs are not supported by verification certificates".into()),
            "include" => self.error = Some("include! code requires expanded source certification".into()),
            "include_str" | "include_bytes" => match syn::parse2::<syn::LitStr>(mac.tokens.clone()) {
                Ok(path) => self.check_path(&path.value()),
                Err(_) => self.error = Some("computed include paths are not supported by verification certificates".into()),
            },
            _ => {
                if name.starts_with("debug_assert") { self.error = Some("conditional debug assertions require per-configuration source certification".into()); }
                if name != "macro_rules" && !STANDARD_MACROS.contains(&name.as_str()) && !self.local_macros.contains(&name) {
                    self.error = Some(format!("macro `{name}` requires expanded source certification"));
                }
                // Inspect nested macro arguments too: a macro_rules expansion may
                // otherwise hide env!, cfg!, or include! from syn's item visitor.
                self.inspect_tokens(mac.tokens.clone());
            }
        }
    }
}

impl Inputs<'_> {
    fn check_path(&mut self, value: &str) {
        let path = self.file.parent().unwrap_or(self.root).join(value);
        self.check_input_path(&path);
    }
    fn check_input_path(&mut self, path: &Path) {
        if !path.canonicalize().is_ok_and(|p| input_relative(self.root, &p, self.excluded)) {
            self.error = Some(format!("external or missing source input is not supported: {}", path.display()));
        }
    }
    fn inspect_tokens(&mut self, tokens: TokenStream) {
        let ts: Vec<_> = tokens.into_iter().collect();
        for (i, token) in ts.iter().enumerate() {
            if matches!(token, TokenTree::Ident(name) if ["use", "extern", "mod"].contains(&name.unraw().to_string().as_str())) {
                self.error = Some("macro-generated imports and modules require expanded source certification".into());
            }
            if let TokenTree::Group(group) = token {
                if group.delimiter() == proc_macro2::Delimiter::Bracket && matches!(ts.get(i.wrapping_sub(1)), Some(TokenTree::Punct(p)) if p.as_char() == '#') {
                    self.error = Some("macro-generated attributes require expanded source certification".into());
                }
                self.inspect_tokens(group.stream());
            }
            if let (TokenTree::Ident(_name), Some(TokenTree::Punct(bang)), Some(TokenTree::Group(args))) = (token, ts.get(i + 1), ts.get(i + 2)) {
                if bang.as_char() == '!' {
                    if matches!(ts.get(i.wrapping_sub(1)), Some(TokenTree::Punct(p)) if p.as_char() == '$') {
                        self.error = Some("forwarded macro names require expanded source certification".into());
                        continue;
                    }
                    if let Ok(mac) = syn::parse2::<syn::Macro>(ts[i..=i + 2].iter().cloned().collect()) { self.visit_macro(&mac); }
                    else { self.error = Some(format!("cannot inspect macro input: {}", args.stream())); }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!("djinn-certificate-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir_all(root.join("src")).unwrap();
            fs::write(root.join("Cargo.toml"), "[package]\nname='certificate_fixture'\nversion='0.1.0'\n[workspace]\n").unwrap();
            fs::write(root.join("src/lib.rs"), "pub fn f() -> bool { true }\n").unwrap();
            Self(root)
        }
        fn write(&self, path: &str, value: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, value).unwrap();
        }
        fn capture(&self) -> Certificate { capture(&self.0).unwrap() }
        fn dependency(&self) {
            self.write("Cargo.toml", "[package]\nname='certificate_fixture'\nversion='0.1.0'\n[workspace]\n[dependencies]\nhelper={path='helper'}\n");
            self.write("helper/Cargo.toml", "[package]\nname='helper'\nversion='0.1.0'\n");
            self.write("helper/src/lib.rs", "pub fn f() -> bool { true }\n");
        }
    }
    impl Drop for Fixture { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }

    #[test]
    fn source_dependency_and_lock_edits_invalidate_certificate() {
        let f = Fixture::new();
        f.dependency();
        let original = f.capture();
        f.write("helper/src/lib.rs", "pub fn f() -> bool { false }\n");
        assert_ne!(original, f.capture());
        let before = f.capture();
        f.write("Cargo.lock", "# newly resolved dependencies\n");
        assert_ne!(before, f.capture());
        let before = f.capture();
        fs::remove_file(f.0.join("src/lib.rs")).unwrap();
        assert_ne!(before, f.capture());
    }

    #[test]
    fn relocatable_and_generated_artifacts_do_not_change_inputs() {
        let a = Fixture::new();
        let b = Fixture::new();
        assert_eq!(a.capture(), b.capture());
        let original = a.capture();
        for path in ["djinn/report.toml", "djinn/proofs/Proofs.lean", "djinn/proofs/.lake/a.olean", "target/debug/artifact", ".djinnscratch/run.log"] {
            a.write(path, "generated content");
        }
        assert_eq!(original, a.capture());
        a.write("djinn/solution/mod.rs", "pub fn f() -> bool { false }\n");
        assert_ne!(original, a.capture());
    }

    #[test]
    fn dependency_inputs_and_impersonated_tool_package_fail_closed() {
        let f = Fixture::new();
        f.dependency();
        f.write("helper/Cargo.toml", "[package]\nname='djinn-impersonator'\nversion='0.1.0'\n");
        f.write("helper/build.rs", "fn main() {}\n");
        assert!(capture(&f.0).unwrap_err().contains("build scripts"));
        fs::remove_file(f.0.join("helper/build.rs")).unwrap();
        f.write("helper/src/lib.rs", "pub fn f() -> &'static str { env!(\"CUSTOM_INPUT\") }\n");
        assert!(capture(&f.0).unwrap_err().contains("environment-derived"));
        f.write("helper/src/lib.rs", "pub fn f() -> bool { cfg!(debug_assertions) }\n");
        assert!(capture(&f.0).unwrap_err().contains("conditional source"));
    }

    #[test]
    fn ignored_and_external_includes_are_not_certified() {
        let f = Fixture::new();
        f.write("target/value.txt", "true");
        f.write("src/lib.rs", "pub const VALUE: &str = include_str!(\"../target/value.txt\");\n");
        assert!(capture(&f.0).is_err());
        let outside = Fixture::new();
        f.write("src/lib.rs", &format!("pub const VALUE: &str = include_str!({:?});\n", outside.0.join("src/lib.rs").to_str().unwrap()));
        assert!(capture(&f.0).is_err());
    }

    #[test]
    fn macro_and_target_configuration_is_guarded() {
        let f = Fixture::new();
        f.write("src/lib.rs", "macro_rules! make { () => { #[cfg(custom_switch)] pub fn f() {} }; } make!();\n");
        assert!(capture(&f.0).is_err());
        f.write("src/lib.rs", "pub fn f() -> bool { true }\n");
        assert!(f.capture().cfg.iter().any(|g| g.predicate.starts_with("target_pointer_width")));
    }

    #[test]
    fn workspace_patch_sources_are_bound() {
        let f = Fixture::new();
        f.write("Cargo.toml", "[workspace]\nmembers=['member']\n[patch.crates-io]\nhelper={path='helper'}\n");
        f.write("member/Cargo.toml", "[package]\nname='member'\nversion='0.1.0'\n");
        f.write("member/src/lib.rs", "pub fn f() -> bool { true }\n");
        f.write("helper/Cargo.toml", "[package]\nname='helper'\nversion='0.1.0'\n");
        f.write("helper/src/lib.rs", "pub fn f() -> bool { true }\n");
        let original = capture(&f.0.join("member")).unwrap();
        f.write("helper/src/lib.rs", "pub fn f() -> bool { false }\n");
        assert_ne!(original, capture(&f.0.join("member")).unwrap());
    }
    #[test]
    fn environment_aliases_qualified_calls_and_forwarded_macros_are_rejected() {
        let f = Fixture::new();
        for source in [
            "use std::env as setting; pub const X: &str = setting!(\"DJINN_PROBE_VALUE\");",
            "pub const X: &str = std::env!(\"DJINN_PROBE_VALUE\");",
            "macro_rules! call { ($m:ident) => { $m!(\"DJINN_PROBE_VALUE\") }; } pub const X: &str = call!(env);",
            "use std::env as format; pub const X: &str = format!(\"DJINN_PROBE_VALUE\");",
            "pub const X: &str = file!();",
            "macro_rules! app { ($m:ident, $b:tt, $arg:tt) => { $m $b $arg }; } pub fn f() -> bool { app!(env, !, (\"VALUE\")) == \"true\" }",
            "macro_rules! call { ($stringify:ident) => { $stringify!(\"DJINN_PROBE_VALUE\") }; } pub const X: &str = call!(env);",
        ] {
            f.write("src/lib.rs", source);
            assert!(capture(&f.0).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn external_and_procedural_runtime_dependencies_are_rejected() {
        let f = Fixture::new();
        f.write("Cargo.toml", "[package]\nname='fixture'\nversion='0.1.0'\n[dependencies]\nhelper='1'\n[workspace]\n");
        assert!(capture(&f.0).unwrap_err().contains("per-dependency"));
        f.dependency();
        f.write("helper/Cargo.toml", "[package]\nname='helper'\nversion='0.1.0'\n[lib]\nproc-macro=true\n");
        assert!(capture(&f.0).unwrap_err().contains("procedural macro"));
    }

    #[test]
    fn conventional_modules_named_target_are_hashed_and_root_outputs_are_rejected() {
        let f = Fixture::new();
        f.write("src/lib.rs", "mod target; pub fn f() -> bool { target::f() }
");
        f.write("src/target/mod.rs", "pub fn f() -> bool { true }
");
        let original = f.capture();
        f.write("src/target/mod.rs", "pub fn f() -> bool { false }
");
        assert_ne!(original, f.capture());
        f.write("Cargo.toml", "[package]\nname='fixture'\nversion='0.1.0'\n[lib]\npath='lib.rs'\n[workspace]\n");
        f.write("lib.rs", "mod target;
");
        f.write("target/mod.rs", "pub fn f() -> bool { true }
");
        assert!(capture(&f.0).is_err());
    }

    #[test]
    fn trusted_model_crate_names_cannot_be_impersonated() {
        let f = Fixture::new();
        for manifest in [
            "[package]\nname='memchr'\nversion='0.1.0'\n[workspace]\n",
            "[package]\nname='other'\nversion='0.1.0'\n[lib]\nname='memchr'\n[workspace]\n",
        ] {
            f.write("Cargo.toml", manifest);
            assert!(capture(&f.0).unwrap_err().contains("reserved for a trusted external model"));
        }
    }

    #[test]
    fn code_includes_are_rejected_but_literal_data_is_bound() {
        let f = Fixture::new();
        f.write("src/generated.inc", "pub const X: &str = env!(\"DJINN_PROBE_VALUE\");");
        f.write("src/lib.rs", "include!(\"generated.inc\");");
        assert!(capture(&f.0).unwrap_err().contains("include! code"));
        f.write("src/lib.rs", "pub const X: &str = include_str!(\"generated.inc\");");
        let old = f.capture();
        f.write("src/generated.inc", "changed data");
        assert_ne!(old, f.capture());
    }

    #[test]
    fn ordinary_expression_macro_is_supported() {
        let f = Fixture::new();
        f.write("src/lib.rs", "macro_rules! require { ($value:expr) => { match $value { Some(value) => value, None => return None } }; } pub fn f(x: Option<bool>) -> Option<bool> { Some(require!(x)) }");
        assert!(capture(&f.0).is_ok());
    }

    #[test]
    fn excluded_cargo_entrypoints_cannot_escape_the_snapshot() {
        let f = Fixture::new();
        for path in ["target/lib.rs", "djinn/proofs/lib.rs"] {
            f.write("Cargo.toml", &format!("[package]\nname='fixture'\nversion='0.1.0'\n[lib]\npath='{path}'\n[workspace]\n"));
            f.write(path, "pub fn f() -> bool { true }");
            assert!(capture(&f.0).is_err());
        }
    }

}
