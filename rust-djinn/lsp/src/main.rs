//! rust-djinn-lsp — a language server for Djinn specifications inside Rust
//! files. It runs beside rust-analyzer (the editor attaches both to Rust
//! documents) and only acts on a crate's configured spec file.
//!
//! What it provides, and the LSP mechanism used:
//!   proof status per declaration      inlay hint at the end of the `fn` line (small, always on)
//!                                     + a code lens above it (clickable: open obligations)
//!   smoke-test as a linter            textDocument/publishDiagnostics on open/change/save
//!                                     (debounced), with the conflicting statements linked
//!                                     through relatedInformation
//!   implement / verify / smoke-test   workspace/executeCommand with $/progress reports and a
//!                                     final window/showMessage; lenses and hints refresh after
//!   jump to the obligations / proofs  window/showDocument at the theorem's line
//!
//! LSP has no way to render text on its own line below a function; inlay
//! hints (inline) and code lenses (above) are the standard substitutes.

use cargo_djinn::config::{load_config, Config};
use cargo_djinn::smoke::{self, CheckStatus, SmokeReport};
use cargo_djinn::status::{self, ObState};
use cargo_djinn::verify;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::*;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

const COMMANDS: &[&str] = &[
    "djinn.implement",
    "djinn.verify",
    "djinn.smokeTest",
    "djinn.status",
    "djinn.openObligations",
    "djinn.openProofs",
    "djinn.openGuide",
];

#[derive(Clone)]
struct Doc {
    text: String,
    version: i32,
}

type SmokeState = Result<SmokeReport, String>;

struct State {
    docs: HashMap<String, Doc>,
    smoke: HashMap<String, SmokeState>,
    /// Any changed buffer invalidates checks of its dependants as well.
    revision: u64,
    agent: String,
}

impl Default for State {
    fn default() -> Self {
        Self { docs: HashMap::new(), smoke: HashMap::new(), revision: 0, agent: "codex".into() }
    }
}

#[derive(Clone)]
struct Ctx {
    sender: crossbeam_sender::Sender,
    state: Arc<Mutex<State>>,
    ids: Arc<AtomicU64>,
    bin: PathBuf,
}

/// A tiny wrapper so the worker threads can send protocol messages.
mod crossbeam_sender {
    pub type Sender = crossbeam_channel::Sender<lsp_server::Message>;
}

impl Ctx {
    fn notify<N: lsp_types::notification::Notification>(&self, params: N::Params) {
        let _ = self.sender.send(Message::Notification(Notification::new(N::METHOD.to_string(), params)));
    }
    fn request<R: lsp_types::request::Request>(&self, params: R::Params) -> RequestId {
        let id = RequestId::from(self.ids.fetch_add(1, Ordering::SeqCst) as i32 + 1_000_000);
        let _ = self.sender.send(Message::Request(Request::new(id.clone(), R::METHOD.to_string(), params)));
        id
    }
    fn log(&self, msg: impl Into<String>) {
        self.notify::<notification::LogMessage>(LogMessageParams { typ: MessageType::LOG, message: msg.into() });
    }
    fn show(&self, typ: MessageType, msg: impl Into<String>) {
        self.notify::<notification::ShowMessage>(ShowMessageParams { typ, message: msg.into() });
    }
    fn refresh(&self) {
        let _ = self.request::<request::CodeLensRefresh>(());
        let _ = self.request::<request::InlayHintRefreshRequest>(());
    }
}

fn main() -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let (connection, _io_threads) = Connection::stdio();
    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::FULL),
            save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions { include_text: Some(true) })),
            ..Default::default()
        })),
        code_lens_provider: Some(CodeLensOptions { resolve_provider: Some(false) }),
        inlay_hint_provider: Some(OneOf::Left(true)),
        execute_command_provider: Some(ExecuteCommandOptions {
            commands: COMMANDS.iter().map(|s| s.to_string()).collect(),
            work_done_progress_options: Default::default(),
        }),
        ..Default::default()
    };
    // `Connection::initialize` wraps its argument as the capabilities; to also
    // send serverInfo, answer the initialize request ourselves.
    let (init_id, init_params) = connection.initialize_start()?;
    connection.initialize_finish(
        init_id,
        json!({
            "capabilities": caps,
            "serverInfo": { "name": "rust-djinn-lsp", "version": env!("CARGO_PKG_VERSION") }
        }),
    )?;
    let bin = std::env::var("DJINN_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_exe().ok().and_then(|p| p.parent().map(|d| d.join("cargo-djinn"))).unwrap_or_else(|| PathBuf::from("cargo-djinn")));
    let mut state = State::default();
    if let Some(agent) = init_params.pointer("/initializationOptions/agent").and_then(Value::as_str).filter(|s| !s.is_empty()) {
        state.agent = agent.to_string();
    }
    let ctx = Ctx { sender: connection.sender.clone(), state: Arc::new(Mutex::new(state)), ids: Arc::new(AtomicU64::new(0)), bin };
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    break;
                }
                handle_request(&ctx, req);
            }
            Message::Notification(n) => handle_notification(&ctx, n),
            Message::Response(_) => {}
        }
    }
    // The client is gone (shutdown, or its pipe closed). Do not wait for the
    // I/O threads: background lint/driver threads hold clones of the sender,
    // so the writer would never finish and the server would linger forever
    // (as orphaned `rust-djinn-lsp` processes did after the editor closed).
    drop(ctx);
    std::process::exit(0);
}

// ------------------------------------------------------------------ helpers

/// Decode a local file URI as bytes: widening each percent-decoded UTF-8
/// byte to a character corrupts every non-ASCII pathname.
fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    if uri.scheme()?.as_str() != "file" || !uri.path().is_absolute() || uri.query().is_some() || uri.fragment().is_some() {
        return None;
    }
    if let Some(authority) = uri.authority() {
        if !authority.as_str().is_empty() && !authority.as_str().eq_ignore_ascii_case("localhost") {
            return None;
        }
    }
    let bytes = uri.path().as_estr().decode().into_bytes().into_owned();
    if bytes.contains(&0) {
        return None;
    }
    #[cfg(unix)]
    let path = {
        use std::os::unix::ffi::OsStringExt;
        PathBuf::from(std::ffi::OsString::from_vec(bytes))
    };
    #[cfg(not(unix))]
    let path = PathBuf::from(String::from_utf8(bytes).ok()?);
    path.is_absolute().then_some(path)
}

fn path_to_uri(p: &Path) -> Option<Uri> {
    if !p.is_absolute() {
        return None;
    }
    #[cfg(unix)]
    let bytes = {
        use std::os::unix::ffi::OsStrExt;
        p.as_os_str().as_bytes()
    };
    #[cfg(not(unix))]
    let bytes = p.to_str()?.as_bytes();
    let mut uri = String::from("file://");
    for &b in bytes {
        if b.is_ascii_alphanumeric() || b"/-._~".contains(&b) {
            uri.push(b as char);
        } else {
            use std::fmt::Write;
            write!(uri, "%{b:02X}").ok()?;
        }
    }
    Uri::from_str(&uri).ok()
}

/// The crate configuration for a document, if the document is one of its
/// specification files — or, without a manual `spec` setting, a file under
/// `src/` whose buffer has a `djinn!` block (perhaps not saved yet).
fn crate_for(path: &Path, text: Option<&str>) -> Option<Config> {
    let mut dir = path.parent()?.to_path_buf();
    loop {
        let m = dir.join("Cargo.toml");
        if m.exists() {
            if let Ok(cfg) = load_config(&m) {
                if cfg.is_spec(path) {
                    return Some(cfg);
                }
                let here = path.canonicalize().unwrap_or(path.to_path_buf());
                let src = cfg.crate_dir.join("src");
                let scanned = cfg.spec_manual.is_none() && here.starts_with(&src) && !here.starts_with(src.join("bin"));
                if scanned && text.is_some_and(djinn_syntax::project::has_djinn) {
                    return Some(cfg);
                }
            }
            return None;
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// Overlay every open specification buffer on one coherent document
/// snapshot, including newly created specification files not yet on disk.
fn spec_texts_with(cfg: &Config, path: &Path, docs: &HashMap<String, Doc>) -> Result<(Vec<String>, usize), String> {
    let normalize = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let here = normalize(path);
    let mut overlays = HashMap::new();
    for (uri, doc) in docs {
        if let Some(path) = Uri::from_str(uri).ok().and_then(|u| uri_to_path(&u)) {
            overlays.insert(normalize(&path), doc.text.clone());
        }
    }
    let mut paths: Vec<PathBuf> = cfg.specs().iter().map(|f| normalize(&f.path)).collect();
    if cfg.spec_manual.is_none() {
        let src = cfg.crate_dir.join("src");
        for (p, text) in &overlays {
            if p.starts_with(&src) && !p.starts_with(src.join("bin")) && djinn_syntax::project::has_djinn(text) && !paths.contains(p) {
                paths.push(p.clone());
            }
        }
    }
    if !paths.contains(&here) {
        paths.push(here.clone());
    }
    // Deterministic ordering also keeps dependency diagnostics reproducible.
    paths.sort();
    let idx = paths.iter().position(|p| p == &here).unwrap();
    let texts = paths.iter().map(|p| {
        overlays.get(p).cloned().map(Ok).unwrap_or_else(|| std::fs::read_to_string(p).map_err(|e| format!("cannot read {}: {e}", p.display())))
    }).collect::<Result<Vec<_>, _>>()?;
    Ok((texts, idx))
}

/// proc-macro2 source columns count Unicode scalar values; LSP defaults to
/// UTF-16 code units. Convert using the actual line, including astral text.
fn pos(text: &str, line1: usize, col0: usize) -> Position {
    let character = text.lines().nth(line1.saturating_sub(1)).unwrap_or("").chars().take(col0).map(char::len_utf16).sum::<usize>();
    Position { line: line1.saturating_sub(1) as u32, character: character as u32 }
}

fn line_range(text: &str, line1: usize) -> Range {
    let line = line1.saturating_sub(1) as u32;
    let len = text.lines().nth(line as usize).map(|l| l.encode_utf16().count()).unwrap_or(0);
    Range { start: Position { line, character: 0 }, end: Position { line, character: len as u32 } }
}

/// Declarations of a document: (name, kind, 1-based line, 0-based column, name length)
fn decls_of(text: &str) -> Result<Vec<(String, String, usize, usize)>, djinn_syntax::Error> {
    let decls = djinn_syntax::parse_file(text)?;
    Ok(decls
        .into_iter()
        .map(|d| {
            let st = d.name_span.start();
            (d.name.clone(), d.kind.word().into(), st.line, st.column)
        })
        .collect())
}

fn find_theorem_line(file: &Path, decl: &str) -> Option<u32> {
    let text = std::fs::read_to_string(file).ok()?;
    text.lines().position(|l| l.starts_with(&format!("theorem {decl}."))).map(|n| n as u32)
}

// ----------------------------------------------------------------- handlers

fn handle_notification(ctx: &Ctx, n: Notification) {
    let mut st = ctx.state.lock().unwrap();
    let delay = match n.method.as_str() {
        "textDocument/didOpen" => {
            let Ok(p) = serde_json::from_value::<DidOpenTextDocumentParams>(n.params) else { return };
            st.docs.insert(p.text_document.uri.as_str().to_string(), Doc { text: p.text_document.text, version: p.text_document.version });
            0
        }
        "textDocument/didChange" => {
            let Ok(p) = serde_json::from_value::<DidChangeTextDocumentParams>(n.params) else { return };
            let Some(change) = p.content_changes.into_iter().last() else { return };
            st.docs.insert(p.text_document.uri.as_str().to_string(), Doc { text: change.text, version: p.text_document.version });
            600
        }
        "textDocument/didSave" => {
            let Ok(p) = serde_json::from_value::<DidSaveTextDocumentParams>(n.params) else { return };
            if let Some(t) = p.text {
                if let Some(doc) = st.docs.get_mut(p.text_document.uri.as_str()) {
                    doc.text = t;
                }
            }
            0
        }
        "textDocument/didClose" => {
            let Ok(p) = serde_json::from_value::<DidCloseTextDocumentParams>(n.params) else { return };
            st.docs.remove(p.text_document.uri.as_str());
            // Send while holding the same lock used to commit lint results.
            ctx.notify::<notification::PublishDiagnostics>(PublishDiagnosticsParams { uri: p.text_document.uri, diagnostics: vec![], version: None });
            0
        }
        "workspace/didChangeConfiguration" => {
            let Ok(p) = serde_json::from_value::<DidChangeConfigurationParams>(n.params) else { return };
            if let Some(agent) = p.settings.pointer("/djinn/agent").and_then(Value::as_str).filter(|s| !s.is_empty()) {
                st.agent = agent.to_string();
                ctx.refresh();
            }
            return;
        }
        _ => return,
    };
    // A changed relation may affect any open caller. Each job captures all
    // buffers at the same revision, and old revisions cannot publish/cache.
    invalidate(&mut st);
    let uris: Vec<String> = st.docs.keys().cloned().collect();
    drop(st);
    for uri in uris {
        schedule_lint(ctx, &uri, delay, false);
    }
    ctx.refresh();
}

fn invalidate(st: &mut State) {
    st.revision += 1;
    st.smoke.clear();
}

fn handle_request(ctx: &Ctx, req: Request) {
    let id = req.id.clone();
    let result: Result<Value, String> = match req.method.as_str() {
        "textDocument/codeLens" => {
            let p: CodeLensParams = serde_json::from_value(req.params).unwrap();
            Ok(serde_json::to_value(code_lenses(ctx, &p.text_document.uri)).unwrap())
        }
        "textDocument/inlayHint" => {
            let p: InlayHintParams = serde_json::from_value(req.params).unwrap();
            Ok(serde_json::to_value(inlay_hints(ctx, &p.text_document.uri)).unwrap())
        }
        "workspace/executeCommand" => {
            let p: ExecuteCommandParams = serde_json::from_value(req.params).unwrap();
            execute(ctx, &p.command, &p.arguments).map(|_| Value::Null)
        }
        _ => Err(format!("unsupported method {}", req.method)),
    };
    let resp = match result {
        Ok(v) => Response::new_ok(id, v),
        Err(e) => Response::new_err(id, lsp_server::ErrorCode::InvalidRequest as i32, e),
    };
    let _ = ctx.sender.send(Message::Response(resp));
}

// ------------------------------------------------------------------- status

/// Per-declaration status line and detail, from the last verify report.
fn status_views(cfg: &Config, path: &Path, docs: &HashMap<String, Doc>) -> HashMap<String, (String, String)> {
    let report = verify::Report::load(cfg);
    let Ok((texts, _)) = spec_texts_with(cfg, path, docs) else { return HashMap::new() };
    let views = status::views_text(cfg, report.as_ref(), None, &texts);
    let mut m = HashMap::new();
    for v in views {
        let proved = v.obs.iter().filter(|(_, s)| *s == ObState::Verified).count();
        let short = if v.changed {
            "changed since verification".to_string()
        } else if v.kind == "rel" {
            // a rel has no implementation: only proof obligations, if any
            if v.obs.is_empty() {
                "✓ nothing to prove".to_string()
            } else if v.all_verified() {
                "✓ ok".to_string()
            } else {
                format!("{}/{} proved", proved, v.obs.len())
            }
        } else {
            let un = v.get("unambiguous");
            let ic = v.get("impl_correct");
            if v.implemented && v.all_verified() {
                "✓ ok".into()
            } else if un != ObState::Verified {
                "unambiguity unproved".into()
            } else if !v.implemented {
                "unambiguous · no implementation".into()
            } else if ic == ObState::Verified {
                "impl ✓".into()
            } else {
                "impl drafted · correctness unproved".into()
            }
        };
        let detail = v.line().trim().to_string();
        m.insert(v.name.clone(), (short, detail));
    }
    m
}

/// The smoke-test verdict for a declaration, with its first counterexample.
fn smoke_summary(report: Option<&SmokeState>, name: &str) -> Option<String> {
    let r = match report? {
        Ok(r) => r,
        Err(e) => return Some(format!("smoke failed: {e}")),
    };
    let d = r.decls.iter().find(|d| d.name == name)?;
    let mut parts = Vec::new();
    for c in &d.checks {
        if let CheckStatus::Problem { what, examples, conflicts, example_input, .. } = &c.status {
            let mut p = what.to_lowercase();
            let ex = examples.first().map(|e| e.trim_start_matches("counterexample: ").to_string()).or_else(|| {
                if conflicts.is_empty() {
                    None
                } else {
                    let lines: Vec<String> = conflicts.iter().map(|(l, t)| format!("line {l}: {t}")).collect();
                    Some(format!("{}{}", lines.join(" vs "), example_input.as_ref().map(|e| format!(" (at {e})")).unwrap_or_default()))
                }
            });
            if let Some(e) = ex {
                let compact: String = e.split_whitespace().collect::<Vec<_>>().join(" ");
                let short: String = compact.chars().take(90).collect();
                p.push_str(&format!(" — {short}{}", if compact.chars().count() > 90 { "…" } else { "" }));
            }
            parts.push(p);
        }
    }
    if parts.is_empty() && d.checks.iter().any(|c| matches!(c.status, CheckStatus::Unsupported(_))) {
        return Some("smoke inconclusive".into());
    }
    if parts.is_empty() && d.checks.iter().all(|c| matches!(c.status, CheckStatus::Skipped)) {
        return Some("smoke skipped".into());
    }
    Some(if parts.is_empty() { "smoke ok".into() } else { format!("smoke: {}", parts.join("; ")) })
}

/// One label per declaration, shared by the code lens and the inlay hint so
/// the two can never disagree: (short label, full detail for tooltips).
fn status_label(views: &HashMap<String, (String, String)>, smoke: Option<&SmokeState>, name: &str) -> (String, String) {
    let (short, detail) = views.get(name).cloned().unwrap_or(("unverified".into(), String::new()));
    let mut label = short.clone();
    match smoke_summary(smoke, name) {
        Some(s) if s == "smoke ok" => {
            if !short.starts_with('✓') {
                label.push_str(" · smoke ok");
            }
        }
        Some(s) => label.push_str(&format!(" · {s}")),
        None => {}
    }
    (label, detail)
}

fn code_lenses(ctx: &Ctx, uri: &Uri) -> Vec<CodeLens> {
    let Some(path) = uri_to_path(uri) else { return vec![] };
    let st = ctx.state.lock().unwrap();
    let Some(doc) = st.docs.get(uri.as_str()) else { return vec![] };
    let Some(cfg) = crate_for(&path, Some(&doc.text)) else { return vec![] };
    let Ok(decls) = decls_of(&doc.text) else { return vec![] };
    let views = status_views(&cfg, &path, &st.docs);
    let smoke = st.smoke.get(uri.as_str());
    let mut out = Vec::new();
    for (i, (name, _kind, line, col)) in decls.iter().enumerate() {
        let range = Range { start: pos(&doc.text, *line, *col), end: pos(&doc.text, *line, col + name.chars().count()) };
        let (label, detail) = status_label(&views, smoke, name);
        let title = format!("djinn: {label}");
        let cmd = |title: String, command: &str, args: Vec<Value>| Command { title, command: command.into(), arguments: Some(args) };
        let a = vec![json!(uri.as_str()), json!(name)];
        out.push(CodeLens { range, command: Some(cmd(title, "djinn.openObligations", a.clone())), data: Some(json!(detail)) });
        out.push(CodeLens { range, command: Some(cmd("proofs".into(), "djinn.openProofs", a.clone())), data: None });
        if i == 0 {
            out.push(CodeLens { range, command: Some(cmd("▶ implement".into(), "djinn.implement", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("verify".into(), "djinn.verify", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("smoke-test".into(), "djinn.smokeTest", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("guide".into(), "djinn.openGuide", vec![json!(uri.as_str())])), data: None });
        }
    }
    out
}

fn inlay_hints(ctx: &Ctx, uri: &Uri) -> Vec<InlayHint> {
    let Some(path) = uri_to_path(uri) else { return vec![] };
    let st = ctx.state.lock().unwrap();
    let Some(doc) = st.docs.get(uri.as_str()) else { return vec![] };
    let Some(cfg) = crate_for(&path, Some(&doc.text)) else { return vec![] };
    let Ok(decls) = decls_of(&doc.text) else { return vec![] };
    let views = status_views(&cfg, &path, &st.docs);
    let smoke = st.smoke.get(uri.as_str());
    let mut out = Vec::new();
    for (name, _kind, line, _col) in &decls {
        let end = line_range(&doc.text, *line).end;
        let (label, detail) = status_label(&views, smoke, name);
        out.push(InlayHint {
            position: end,
            label: InlayHintLabel::String(format!("⟵ {label}")),
            kind: None,
            text_edits: None,
            tooltip: if detail.is_empty() { None } else { Some(InlayHintTooltip::String(detail)) },
            padding_left: Some(true),
            padding_right: None,
            data: None,
        });
    }
    out
}

// --------------------------------------------------------------------- lint

struct LintResult {
    diagnostics: Vec<Diagnostic>,
    smoke: Option<SmokeState>,
    verdict: &'static str,
}

impl LintResult {
    fn empty() -> Self {
        Self { diagnostics: vec![], smoke: None, verdict: "no specifications to check" }
    }
    fn failed(text: &str, message: String) -> Self {
        Self {
            diagnostics: vec![Diagnostic { range: line_range(text, 1), severity: Some(DiagnosticSeverity::WARNING), source: Some("djinn smoke-test".into()), message: format!("smoke-test failed: {message}"), ..Default::default() }],
            smoke: Some(Err(message)),
            verdict: "failed; see the diagnostics",
        }
    }
}

fn schedule_lint(ctx: &Ctx, uri: &str, delay_ms: u64, announce: bool) {
    let revision = ctx.state.lock().unwrap().revision;
    let ctx = ctx.clone();
    let uri = uri.to_string();
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(delay_ms));
        let docs = {
            let st = ctx.state.lock().unwrap();
            if st.revision != revision || !st.docs.contains_key(&uri) {
                return;
            }
            st.docs.clone()
        };
        let doc = &docs[&uri];
        let Ok(u) = Uri::from_str(&uri) else { return };
        let result = match uri_to_path(&u).and_then(|path| crate_for(&path, Some(&doc.text)).map(|cfg| (path, cfg))) {
            Some((path, cfg)) => lint(&cfg, &u, &path, &docs),
            None => LintResult::empty(),
        };
        commit_lint(&ctx, u, revision, doc.version, result, announce);
    });
}

/// Commit the cache and its diagnostics together. The lock also serializes
/// this publication with edits and close notifications.
fn commit_lint(ctx: &Ctx, uri: Uri, revision: u64, version: i32, result: LintResult, announce: bool) {
    let mut st = ctx.state.lock().unwrap();
    if st.revision != revision || st.docs.get(uri.as_str()).map(|d| d.version) != Some(version) {
        return;
    }
    let verdict = result.verdict;
    let success = verdict == "no contradiction and no counterexample within the bounds";
    match result.smoke {
        Some(report) => { st.smoke.insert(uri.as_str().to_string(), report); }
        None => { st.smoke.remove(uri.as_str()); }
    }
    ctx.notify::<notification::PublishDiagnostics>(PublishDiagnosticsParams { uri, diagnostics: result.diagnostics, version: Some(version) });
    ctx.refresh();
    if announce {
        ctx.show(if success { MessageType::INFO } else { MessageType::WARNING }, format!("smoke-test: {verdict}"));
    }
}

fn lint(cfg: &Config, uri: &Uri, path: &Path, docs: &HashMap<String, Doc>) -> LintResult {
    let text = &docs[uri.as_str()].text;
    let mut diags = Vec::new();
    // syntax and scoping first
    if let Err(e) = djinn_syntax::parse_file(text) {
        let s = e.span.start();
        diags.push(Diagnostic {
            range: Range { start: pos(text, s.line, s.column), end: pos(text, s.line, s.column + 1) },
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("djinn".into()),
            message: e.msg,
            ..Default::default()
        });
        return LintResult { diagnostics: diags, smoke: None, verdict: "syntax errors; see the diagnostics" };
    }
    let bounds = smoke::Bounds { timeout_ms: 5_000, ..Default::default() };
    // the whole specification, for what this file uses from the others;
    // findings of this file only
    let (texts, me) = match spec_texts_with(cfg, path, docs) {
        Ok(sources) => sources,
        Err(e) => return LintResult::failed(text, e),
    };
    let mut report = match smoke::smoke_run_sources(&texts, &bounds) {
        Ok(r) => r,
        Err((_, e)) => return LintResult::failed(text, e),
    };
    report.decls.retain(|d| d.file == me);
    let u = uri;
    for d in &report.decls {
        let name_range = Range { start: pos(text, d.line, d.col.saturating_sub(1)), end: pos(text, d.line, d.col.saturating_sub(1) + d.name.chars().count()) };
        for c in &d.checks {
            if let CheckStatus::Problem { what, how_many, examples, conflict_title, conflicts, example_input } = &c.status {
                let severity = if what.starts_with("ENSURES") { DiagnosticSeverity::WARNING } else { DiagnosticSeverity::ERROR };
                let mut message = format!("{} {}: {what} — {how_many}", d.name, c.label);
                for e in examples.iter().take(2) {
                    message.push_str(&format!("\n{e}"));
                }
                if let Some(e) = example_input {
                    message.push_str(&format!("\ne.g. at {e}"));
                }
                if !conflicts.is_empty() {
                    message.push_str(&format!("\n{conflict_title}"));
                    for (line, t) in conflicts {
                        message.push_str(&format!("\n  line {line}: {t}"));
                    }
                }
                let related: Vec<DiagnosticRelatedInformation> = conflicts
                    .iter()
                    .map(|(line, t)| DiagnosticRelatedInformation {
                        location: Location { uri: u.clone(), range: line_range(text, *line) },
                        message: format!("part of the conflict: {t}"),
                    })
                    .collect();
                diags.push(Diagnostic {
                    range: name_range,
                    severity: Some(severity),
                    source: Some("djinn smoke-test".into()),
                    code: Some(NumberOrString::String(c.label.replace(' ', "-"))),
                    message,
                    related_information: if related.is_empty() { None } else { Some(related) },
                    ..Default::default()
                });
                // also mark each conflicting statement, with a short self-contained message
                let at = example_input.as_ref().map(|e| format!(" at {e}")).unwrap_or_default();
                for (line, t) in conflicts {
                    let message = if conflicts.len() == 1 {
                        if what.starts_with("NO OUTPUT") {
                            format!("{}: no output satisfies this statement{at}", d.name)
                        } else {
                            format!("{}: this statement is unsatisfiable{at}", d.name)
                        }
                    } else {
                        let others: Vec<String> = conflicts.iter().filter(|(l, _)| l != line).map(|(l, ot)| format!("line {l} ({})", ot.trim_end_matches(';'))).collect();
                        format!("{}: contradicts {}{at}", d.name, others.join(" and "))
                    };
                    let _ = t;
                    diags.push(Diagnostic {
                        range: line_range(text, *line),
                        severity: Some(DiagnosticSeverity::ERROR),
                        source: Some("djinn smoke-test".into()),
                        message,
                        ..Default::default()
                    });
                }
            }
        }
    }
    let checked = report.decls.iter().flat_map(|d| &d.checks).collect::<Vec<_>>();
    let verdict = if checked.iter().any(|c| matches!(c.status, CheckStatus::Problem { .. })) {
        "findings; see the diagnostics"
    } else if checked.iter().any(|c| matches!(c.status, CheckStatus::Unsupported(_))) {
        "inconclusive: some checks could not run within the supported bounds"
    } else if checked.is_empty() || checked.iter().all(|c| matches!(c.status, CheckStatus::Skipped)) {
        "skipped: no checks were run"
    } else {
        "no contradiction and no counterexample within the bounds"
    };
    LintResult { diagnostics: diags, smoke: Some(Ok(report)), verdict }
}

// ----------------------------------------------------------------- commands

fn arg_uri(args: &[Value], i: usize) -> Result<Uri, String> {
    let s = args.get(i).and_then(|v| v.as_str()).ok_or("missing document argument")?;
    Uri::from_str(s).map_err(|e| format!("bad uri: {e}"))
}

fn execute(ctx: &Ctx, command: &str, args: &[Value]) -> Result<(), String> {
    let uri = arg_uri(args, 0)?;
    let path = uri_to_path(&uri).ok_or("expected a local file URI")?;
    let text = ctx.state.lock().unwrap().docs.get(uri.as_str()).map(|d| d.text.clone());
    let cfg = crate_for(&path, text.as_deref()).ok_or("this file is not a specification file of a Djinn crate")?;
    match command {
        "djinn.openObligations" | "djinn.openProofs" | "djinn.openGuide" => {
            let file = match command {
                "djinn.openObligations" => cfg.lean_dir().join("Obligations.lean"),
                "djinn.openProofs" => cfg.lean_dir().join("Proofs.lean"),
                _ => cfg.guide_path(),
            };
            if !file.exists() {
                // produce the trusted files first
                if let Err(e) = verify::translate(&cfg, &mut verify::Log::new(false)) {
                    return Err(format!("translate failed: {e}"));
                }
            }
            let name = args.get(1).and_then(|v| v.as_str()).unwrap_or("");
            let line = if name.is_empty() { None } else { find_theorem_line(&file, name) };
            let target = path_to_uri(&file).ok_or("bad path")?;
            let selection = line.map(|l| Range { start: Position { line: l, character: 0 }, end: Position { line: l, character: 0 } });
            let _ = ctx.request::<request::ShowDocument>(ShowDocumentParams { uri: target, external: Some(false), take_focus: Some(true), selection });
            Ok(())
        }
        "djinn.smokeTest" => {
            if text.is_none() {
                return Err("open the specification document before running smoke-test".into());
            }
            schedule_lint(ctx, uri.as_str(), 0, true);
            Ok(())
        }
        "djinn.status" => {
            let text = status::status_text(&cfg);
            ctx.log(text.clone());
            ctx.show(MessageType::INFO, text.lines().take(8).collect::<Vec<_>>().join("\n"));
            Ok(())
        }
        "djinn.implement" | "djinn.verify" => {
            let agent = args.get(1).and_then(Value::as_str).map(str::to_string).unwrap_or_else(|| ctx.state.lock().unwrap().agent.clone());
            let manifest = cfg.crate_dir.join("Cargo.toml");
            let bin = ctx.bin.clone();
            let ctx2 = ctx.clone();
            let is_impl = command == "djinn.implement";
            std::thread::spawn(move || run_driver(&ctx2, &bin, &manifest, is_impl, &agent));
            Ok(())
        }
        _ => Err(format!("unknown command {command}")),
    }
}

/// Run `cargo-djinn implement|verify` as a child, streaming its progress.
fn run_driver(ctx: &Ctx, bin: &Path, manifest: &Path, is_impl: bool, agent: &str) {
    use std::io::BufRead;
    let token = NumberOrString::String(format!("djinn-{}", ctx.ids.fetch_add(1, Ordering::SeqCst)));
    let _ = ctx.request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams { token: token.clone() });
    let title = if is_impl { format!("djinn implement ({agent})") } else { "djinn verify".to_string() };
    ctx.notify::<notification::Progress>(ProgressParams {
        token: token.clone(),
        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(WorkDoneProgressBegin { title: title.clone(), cancellable: Some(false), message: Some("starting".into()), percentage: None })),
    });
    let mut cmd = std::process::Command::new(bin);
    if is_impl {
        cmd.args(["implement", "--agent", agent]);
    } else {
        cmd.arg("verify");
    }
    cmd.arg("--manifest-path").arg(manifest);
    cmd.stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped()).stdin(std::process::Stdio::null());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            ctx.show(MessageType::ERROR, format!("cannot run {}: {e}", bin.display()));
            return;
        }
    };
    let stderr = child.stderr.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let ctx_out = ctx.clone();
    let out_thread = std::thread::spawn(move || {
        let mut last = String::new();
        for line in std::io::BufReader::new(stdout).lines().flatten() {
            ctx_out.log(line.clone());
            last = line;
        }
        last
    });
    let mut last_lines: Vec<String> = Vec::new();
    let mut last_refresh = std::time::Instant::now();
    for line in std::io::BufReader::new(stderr).lines().flatten() {
        ctx.log(line.clone());
        let msg: String = line.trim().chars().take(100).collect();
        ctx.notify::<notification::Progress>(ProgressParams {
            token: token.clone(),
            value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(WorkDoneProgressReport { cancellable: Some(false), message: Some(msg), percentage: None })),
        });
        // keep the editor's status current while the agent works: every
        // verify writes the report, and the monitor announces it
        if line.contains("verify #") || line.contains(": → ") || last_refresh.elapsed().as_secs() >= 10 {
            ctx.refresh();
            last_refresh = std::time::Instant::now();
        }
        last_lines.push(line);
        if last_lines.len() > 12 {
            last_lines.remove(0);
        }
    }
    let status = child.wait().ok();
    let last_out = out_thread.join().unwrap_or_default();
    let ok = status.map(|s| s.success()).unwrap_or(false);
    ctx.notify::<notification::Progress>(ProgressParams {
        token: token.clone(),
        value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(WorkDoneProgressEnd { message: Some(if ok { "PASS".into() } else { "FAIL".into() }) })),
    });
    let _ = last_out;
    // one line for the message area; the details are in the log
    let fail_line = last_lines.iter().rev().find(|l| l.starts_with("FAIL")).cloned().unwrap_or_else(|| last_lines.last().cloned().unwrap_or_default());
    ctx.show(if ok { MessageType::INFO } else { MessageType::WARNING }, format!("{title}: {}", if ok { "PASS — every obligation verified".to_string() } else { fail_line }));
    ctx.refresh();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_uris_preserve_unicode_and_reserved_bytes() {
        let path = Path::new("/tmp/café 😀/#100%?file.rs");
        let uri = path_to_uri(path).unwrap();
        assert_eq!(uri.as_str(), "file:///tmp/caf%C3%A9%20%F0%9F%98%80/%23100%25%3Ffile.rs");
        assert_eq!(uri_to_path(&uri).as_deref(), Some(path));
        assert_eq!(uri_to_path(&Uri::from_str("file://localhost/tmp/spec.rs").unwrap()).as_deref(), Some(Path::new("/tmp/spec.rs")));
        assert!(uri_to_path(&Uri::from_str("file://remote/tmp/spec.rs").unwrap()).is_none());
        assert!(uri_to_path(&Uri::from_str("https://example.com/spec.rs").unwrap()).is_none());
        assert!(uri_to_path(&Uri::from_str("file:///tmp/spec.rs#fragment").unwrap()).is_none());
    }

    #[test]
    fn declaration_and_line_positions_use_utf16() {
        let text = "djinn! {\n /*😀*/ pub fn café(x: i32) -> r: i32 { r == x; }\n}";
        let (name, _, line, column) = decls_of(text).unwrap().remove(0);
        assert_eq!(name, "café");
        assert_eq!(pos(text, line, column), Position::new(1, 15));
        assert_eq!(pos(text, line, column + name.chars().count()), Position::new(1, 19));
        assert_eq!(line_range(text, line).end.character, 49);
    }

    #[test]
    fn inconclusive_checks_never_have_an_ok_label() {
        let report = Ok(SmokeReport {
            decls: vec![smoke::DeclReport {
                name: "f".into(), kind: "fn".into(), line: 1, col: 1, file: 0,
                checks: vec![smoke::CheckReport { label: "consistency".into(), status: CheckStatus::Unsupported("timeout".into()) }],
            }],
            all_ok: false,
        });
        assert_eq!(smoke_summary(Some(&report), "f").as_deref(), Some("smoke inconclusive"));
        let failed = Err("cannot run z3".into());
        assert!(smoke_summary(Some(&failed), "f").unwrap().starts_with("smoke failed:"));
    }

    #[test]
    fn obsolete_results_cannot_publish_or_mutate_the_cache() {
        let (sender, receiver) = crossbeam_channel::unbounded();
        let ctx = Ctx { sender, state: Arc::new(Mutex::new(State::default())), ids: Arc::new(AtomicU64::new(0)), bin: PathBuf::new() };
        let uri = Uri::from_str("file:///tmp/spec.rs").unwrap();
        {
            let mut st = ctx.state.lock().unwrap();
            st.docs.insert(uri.to_string(), Doc { text: String::new(), version: 2 });
            st.revision = 2;
        }
        commit_lint(&ctx, uri.clone(), 1, 1, LintResult::failed("", "old failure".into()), true);
        assert!(ctx.state.lock().unwrap().smoke.is_empty());
        assert!(receiver.try_recv().is_err());
        commit_lint(&ctx, uri.clone(), 2, 2, LintResult::failed("", "current failure".into()), false);
        assert!(matches!(ctx.state.lock().unwrap().smoke.get(uri.as_str()), Some(Err(e)) if e == "current failure"));
        let published: Vec<_> = receiver.try_iter().collect();
        assert!(published.iter().any(|m| matches!(m, Message::Notification(n) if n.method == "textDocument/publishDiagnostics" && n.params["version"] == 2)));
        {
            let mut st = ctx.state.lock().unwrap();
            st.docs.remove(uri.as_str());
            invalidate(&mut st);
        }
        commit_lint(&ctx, uri, 2, 2, LintResult::failed("", "closed failure".into()), true);
        assert!(ctx.state.lock().unwrap().smoke.is_empty());
        assert!(receiver.try_recv().is_err());
    }
}
