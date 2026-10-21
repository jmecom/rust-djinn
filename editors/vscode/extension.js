// Djinn for Rust — launches rust-djinn-lsp beside rust-analyzer on Rust files.
//
// rust-analyzer handles the Rust; rust-djinn-lsp adds, for the crate's spec
// file: a status after every func/rel (drawn from the server's code lenses,
// coloured: green when verified, red on a smoke-test finding), smoke-test
// diagnostics as you type, progress reports for implement/verify in the
// status bar, and jumps to the obligations, the proofs and the guide.
//
// The server declares `djinn.*` commands through executeCommandProvider; the
// language client registers them, so the code lenses work out of the box.
// The *Active commands below are palette entries (and chords on ctrl+alt+d)
// that forward to the server for the active editor, passing the name of the
// function under the cursor where the command takes one.
const vscode = require("vscode");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

// ------------------------------------------------------------ the server
// Where the server is: the setting, else `rust-djinn-lsp` on PATH, else
// ~/.cargo/bin, else the debug build of the checkout this extension lives in.
function serverPath(context) {
  const configured = vscode.workspace.getConfiguration("djinn").get("serverPath");
  if (configured && configured !== "rust-djinn-lsp") return configured;
  const onPath = (process.env.PATH || "")
    .split(path.delimiter)
    .map((d) => path.join(d, "rust-djinn-lsp"))
    .find((p) => fs.existsSync(p));
  if (onPath) return onPath;
  for (const p of [
    path.join(os.homedir(), ".cargo", "bin", "rust-djinn-lsp"),
    path.join(context.extensionPath, "..", "..", "rust-djinn", "target", "debug", "rust-djinn-lsp"),
  ]) {
    if (fs.existsSync(p)) return p;
  }
  return "rust-djinn-lsp";
}

// -------------------------------------------------------- status after fns
// The server's code lenses carry the status (`djinn: …`) plus buttons, and
// an inlay hint says the same thing inline. VS Code cannot draw a line
// below a function, so `djinn.status = "line"` (the default) draws the
// status as a coloured decoration after the `fn` line and suppresses the
// inlay hint; `"inlayHint"` keeps the server's hint instead; `"off"` neither.
const decorations = {
  ok: vscode.window.createTextEditorDecorationType({
    after: { color: "#6fbf73", fontStyle: "italic", margin: "0 0 0 2em" },
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
  }),
  bad: vscode.window.createTextEditorDecorationType({
    after: { color: "#e06c75", fontStyle: "italic", margin: "0 0 0 2em" },
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
  }),
  plain: vscode.window.createTextEditorDecorationType({
    after: { color: "#8a8f98", fontStyle: "italic", margin: "0 0 0 2em" },
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
  }),
};

function statusMode() {
  return vscode.workspace.getConfiguration("djinn").get("status") || "line";
}

function clearStatus(editor) {
  for (const d of Object.values(decorations)) editor.setDecorations(d, []);
}

// Ask the server for the lenses of `document` and draw the `djinn: …` ones
// after their `fn` lines (the lens data holds the detail, shown on hover).
async function drawStatus(document) {
  if (!client || !client.isRunning() || document.languageId !== "rust") return;
  const editors = vscode.window.visibleTextEditors.filter((e) => e.document === document);
  if (editors.length === 0) return;
  if (statusMode() !== "line") {
    editors.forEach(clearStatus);
    return;
  }
  let lenses;
  try {
    lenses = await client.sendRequest("textDocument/codeLens", {
      textDocument: { uri: document.uri.toString() },
    });
  } catch (_) {
    return;
  }
  // A setting change may arrive while the lens request is in flight.
  if (statusMode() !== "line") {
    editors.forEach(clearStatus);
    return;
  }
  const byLine = new Map();
  for (const lens of lenses || []) {
    const title = (lens.command && lens.command.title) || "";
    if (!title.startsWith("djinn: ")) continue;
    const line = lens.range.start.line;
    const entry = byLine.get(line) || { parts: [], detail: [] };
    entry.parts.push(title.slice("djinn: ".length));
    if (typeof lens.data === "string" && lens.data) entry.detail.push(lens.data);
    byLine.set(line, entry);
  }
  const groups = { ok: [], bad: [], plain: [] };
  for (const [line, entry] of byLine) {
    if (line >= document.lineCount) continue;
    const text = entry.parts.join(" · ");
    const kind = text.includes("✓ ok") ? "ok" : text.includes("smoke:") ? "bad" : "plain";
    const end = document.lineAt(line).range.end;
    groups[kind].push({
      range: new vscode.Range(end, end),
      renderOptions: { after: { contentText: "⤷ " + text } },
      hoverMessage: entry.detail.length ? new vscode.MarkdownString(entry.detail.join("\n\n")) : undefined,
    });
  }
  for (const editor of editors) {
    for (const kind of Object.keys(groups)) editor.setDecorations(decorations[kind], groups[kind]);
  }
}

// Coalesce the redraw requests for a document (open, edit, lens refresh,
// the safety-net timer) into one request a short moment later.
const pending = new Map();
function scheduleDraw(document, delay = 150) {
  const key = document.uri.toString();
  if (pending.has(key)) clearTimeout(pending.get(key));
  pending.set(
    key,
    setTimeout(() => {
      pending.delete(key);
      drawStatus(document);
    }, delay),
  );
}

// --------------------------------------------------------------- commands
// The name of the `fn`/`rel` the cursor is in (the nearest declaration above).
function enclosingFn(editor) {
  const line = editor.selection.active.line;
  for (let l = line; l >= 0; l--) {
    const m = /\b(?:fn|rel)\s+([A-Za-z_]\w*)\s*\(/.exec(editor.document.lineAt(l).text);
    if (m) return m[1];
  }
  return "";
}

function activate(context) {
  const cfg = vscode.workspace.getConfiguration("djinn");
  const env = Object.assign({}, process.env);
  if (cfg.get("driverPath")) env.DJINN_BIN = cfg.get("driverPath");
  const serverOptions = {
    command: serverPath(context),
    transport: TransportKind.stdio,
    options: { env },
  };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "rust" }],
    outputChannelName: "Djinn",
    initializationOptions: { agent: cfg.get("agent") },
    middleware: {
      // VS Code asks for lenses on open, on edits and whenever the server
      // sends workspace/codeLens/refresh (after verify/implement/lint):
      // the moment to redraw the status after the functions. With the status
      // drawn there, the status lens above keeps only its button.
      provideCodeLenses: async (document, token, next) => {
        const lenses = await next(document, token);
        scheduleDraw(document);
        if (statusMode() === "line" && lenses) {
          for (const lens of lenses) {
            if (lens.command && lens.command.title.startsWith("djinn: ")) lens.command.title = "obligations";
          }
        }
        return lenses;
      },
      // the server's inline hint says the same as the decoration
      provideInlayHints: (document, range, token, next) =>
        statusMode() === "inlayHint" ? next(document, range, token) : [],
    },
  };
  client = new LanguageClient("rust-djinn-lsp", "Djinn for Rust", serverOptions, clientOptions);
  client.start();

  const forward = (command, withName, extra) => () => {
    const ed = vscode.window.activeTextEditor;
    if (!ed) return;
    const args = [ed.document.uri.toString()];
    if (withName) args.push(enclosingFn(ed));
    if (extra) args.push(...extra());
    return client
      .sendRequest("workspace/executeCommand", { command, arguments: args })
      .then(undefined, (err) => vscode.window.showErrorMessage("Djinn: " + ((err && err.message) || String(err))));
  };
  const agent = () => [vscode.workspace.getConfiguration("djinn").get("agent")];
  context.subscriptions.push(
    vscode.commands.registerCommand("djinn.implementActive", forward("djinn.implement", false, agent)),
    vscode.commands.registerCommand("djinn.verifyActive", forward("djinn.verify")),
    vscode.commands.registerCommand("djinn.smokeTestActive", forward("djinn.smokeTest")),
    vscode.commands.registerCommand("djinn.openObligationsActive", forward("djinn.openObligations", true)),
    vscode.commands.registerCommand("djinn.openProofsActive", forward("djinn.openProofs", true)),
    vscode.commands.registerCommand("djinn.openGuideActive", forward("djinn.openGuide")),
    vscode.commands.registerCommand("djinn.statusActive", forward("djinn.status")),
  );

  // redraw on view changes and saves, and on a slow timer as a safety net so
  // the status after a function can never stay stale
  const redrawVisible = () => vscode.window.visibleTextEditors.forEach((e) => scheduleDraw(e.document));
  context.subscriptions.push(
    vscode.window.onDidChangeVisibleTextEditors(redrawVisible),
    vscode.workspace.onDidSaveTextDocument((doc) => scheduleDraw(doc)),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("djinn.status")) redrawVisible();
      if ((e.affectsConfiguration("djinn.agent") || e.affectsConfiguration("djinn.status")) && client.isRunning()) {
        // The server refreshes lenses and hints, clearing any hints that
        // were already displayed before the status mode changed.
        client.sendNotification("workspace/didChangeConfiguration", {
          settings: { djinn: { agent: vscode.workspace.getConfiguration("djinn").get("agent") } },
        });
      }
    }),
    ...Object.values(decorations),
  );
  const timer = setInterval(redrawVisible, 3000);
  context.subscriptions.push({ dispose: () => clearInterval(timer) });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
