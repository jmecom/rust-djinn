# rust-djinn-lsp — Djinn in the editor

A language server for the Djinn specification language inside Rust files.
It runs **beside rust-analyzer**: the editor attaches both servers to Rust
documents, rust-analyzer handles the Rust, and `rust-djinn-lsp` only acts on
a crate's specification files: by default every file under `src/` with a
`djinn! { … }` block, or the files `[package.metadata.djinn] spec` names.
Other Rust files get nothing from it.

| Feature | LSP mechanism | What you see |
|---|---|---|
| Proof status per `func`/`rel` | inlay hint at the end of the `fn` line, and a code lens above it (both editor configs below draw it from the lenses instead: Neovim as a dimmed line below, VS Code as a coloured decoration after the line) | `⟵ ✓ ok`, `⟵ changed since verification` (the buffer's semantics differ from what was verified), `⟵ unambiguity unproved · smoke: ambiguous — list = [1, 0] admits both r = 0 and also r = 1`; the lens opens the obligations when clicked |
| Smoke-test as a linter | `publishDiagnostics` on open, save and (debounced) change | an error on the declaration name with the counterexample, and one on each statement of a contradiction; the pair is linked through related information |
| `implement` / `verify` / `smoke-test` | `workspace/executeCommand` with `$/progress` and a final `showMessage` | the driver's stage lines in the progress area; lenses and hints refresh afterwards |
| Jump to the obligations / proofs / guide | `window/showDocument` | `Obligations.lean` opens at the declaration's first theorem |

LSP has no way to render text on its own line below a function, so the
status lives in the inlay hint (inline, small) and the code lens (above).

## Build

```sh
cd rust-djinn && cargo build --workspace     # produces target/debug/rust-djinn-lsp and cargo-djinn
```

The server finds `cargo-djinn` next to its own binary; set `DJINN_BIN` to
point elsewhere. The crate's `Cargo.toml` metadata provides the tool paths
(Charon, Aeneas, the Aeneas Lean backend) as for the CLI.

## VS Code

`editors/vscode/` is a minimal extension (`vscode-languageclient`):

```sh
cd editors/vscode && npm install
code --extensionDevelopmentPath=$PWD /path/to/your/crate      # or package with `vsce`
```

The server is looked up on `PATH`, then in `~/.cargo/bin`, then as the
debug build of the checkout the extension lives in; `djinn.serverPath`
overrides that. Other settings: `djinn.driverPath`, `djinn.agent` (`codex`,
the default, or `claude`), and `djinn.status`: `line` (default) draws the proof status
after each `fn`/`rel` line as a coloured decoration built from the server's
code lenses (green when verified, red on a smoke-test finding, grey
otherwise; the detail on hover) and hides the server's inlay hint so the
status is not shown twice; `inlayHint` shows the hint instead; `off` leaves
only the lens above. The decoration redraws when VS Code refetches the
lenses (edits, and the server's refresh after implement/verify/lint), on
save, and every three seconds as a safety net. Progress of implement/verify
appears in the status bar; the final line as a notification.

Commands in the palette: *Djinn: Implement*, *Verify*, *Smoke-test*, *Open
the proof obligations*, *Open the proofs* (both of the function under the
cursor), *Open the guide*, *Status*. They are chords on `ctrl+alt+d`
followed by `i`, `v`, `s`, `o`, `p`, `g` and `shift+s`, the same letters as
the Neovim keys. The code lenses call the same commands.

## Neovim (0.10+; tested with 0.12)

`editors/nvim/djinn.lua` is a complete, plugin-free demo config: `nvim -u
editors/nvim/djinn.lua example/clamp/src/spec.rs`. It also draws the status
as a dimmed virtual line *below* each function (Neovim's `virt_lines`),
which LSP itself cannot express. Minimal version:

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "rust",
  callback = function(ev)
    vim.lsp.start({
      name = "rust-djinn-lsp",
      cmd = { "/path/to/rust-djinn/target/debug/rust-djinn-lsp" },
      root_dir = vim.fs.root(ev.buf, { "Cargo.toml" }),
    })
  end,
})
vim.lsp.inlay_hint.enable(true)
-- run a command: :lua vim.lsp.buf.execute_command({ command = "djinn.implement",
--   arguments = { vim.uri_from_bufnr(0), "claude" } })
-- code lenses: :lua vim.lsp.codelens.refresh() then vim.lsp.codelens.run()
```

## Checking the server without an editor

The scripted client also asserts that the `initialize` result carries the
server capabilities at the top level (a mistake there makes editors ignore
the server silently while a naive client still works).


`editors/lsp-check.py` speaks the protocol over stdio and prints what the
server sends:

```sh
python3 editors/lsp-check.py rust-djinn/target/debug/rust-djinn-lsp example/broken/src/spec.rs
python3 editors/lsp-check.py rust-djinn/target/debug/rust-djinn-lsp example/clamp/src/spec.rs \
    djinn.openObligations:count_negative djinn.verify
```

## The compile-time gate and the editor

`cargo build` refuses to compile a `fn` whose implementation is not verified
against the current specification (see `DESIGN.md`, "The report and the
compile-time gate"). Analysis is exempt so that the editor stays usable while
you edit or while an agent works: both configurations here set
`DJINN_GATE=off` in rust-analyzer's environment (`rust-analyzer.cargo.extraEnv`),
and the Djinn status line reports the verification state instead. Clippy is
exempt automatically.
