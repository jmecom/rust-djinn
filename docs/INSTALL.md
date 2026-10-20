# Installing Djinn

Start with the Rust tools and a checked-in example. Install the verification
toolchain when you are ready to implement a specification or check proofs yourself.
An agent and an editor extension are optional.

| What you want to do | What you need |
|---|---|
| Build and run an unchanged, verified example; inspect `status` and `guide` | Git, Rust, and the Djinn tools |
| Check specifications for bounded counterexamples with `smoke-test` | The above, plus Z3 |
| Translate a crate or verify its implementation and proofs | The Rust tools, Charon, Aeneas, and Lean/Lake |
| Generate implementations with `implement`, or improve them with `optimize` | The verification toolchain and an authenticated Codex or Claude Code CLI |
| See proof status and diagnostics while editing | The Djinn language server, an editor integration, and Z3 for smoke-test diagnostics |

The commands below target Linux and macOS with a POSIX shell. The current driver
uses Unix filesystem and process APIs; it does not support native Windows.
On Windows, use a Linux environment such as WSL and install the whole toolchain
inside it. The agent workflow also requires Bash.

## 1. Build the Rust tools

Install Rust through [rustup](https://rustup.rs/) if you do not already have
`cargo` and `rustc`. A native linker must also be available. The Djinn tools do
not require Charon's nightly toolchain to build.

```sh
git clone https://github.com/shenniger/rust-djinn.git
cd rust-djinn
```

If you already cloned the repository, skip those commands and enter its root.
Then build the tools:

```sh
export DJINN_REPO="$PWD"

cd "$DJINN_REPO/rust-djinn"
cargo build --workspace --locked
export PATH="$DJINN_REPO/rust-djinn/target/debug:$PATH"
```

`DJINN_REPO` names the **repository root**, which contains `docs/`, `example/`,
and `editors/`. The second `rust-djinn/` directory contains the Cargo workspace.
Keep this terminal open for the remaining commands. In a new terminal, set
`DJINN_REPO` to the absolute checkout path and repeat the `PATH` export.

The workspace builds `cargo-djinn`, the `rust-djinn-lsp` language server, and the
`djinn` library used by example crates. Adding the debug directory to `PATH`
makes subsequent rebuilds available immediately. To install copies of the two
executables instead, run:

```sh
cargo install --locked --path "$DJINN_REPO/rust-djinn/cargo-djinn"
cargo install --locked --path "$DJINN_REPO/rust-djinn/lsp"
```

For that alternative, put Cargo's installation directory, normally
`$HOME/.cargo/bin`, on `PATH`; reinstall after changing the tool sources.

### Check the Rust-only installation

```sh
cd "$DJINN_REPO/example/clamp"
cargo build --locked
printf '3\n-4\n12\n' | cargo run --locked -- 0 10
cargo djinn status
cargo djinn guide
```

The clamp example includes its implementation, proofs, and verification report,
so it builds without running Lean or an agent. `status` reads that report;
building the example does **not** perform a fresh proof check. Use
`cargo djinn verify` after installing the full toolchain below to check it yourself.

You can now follow the first part of [First steps](FIRST_STEPS.md) and read the
[Language tour](LANGUAGE_TOUR.md). To see the driver's command list, run
`cargo djinn --help`; the current CLI prints usage with exit status 2, including
for `--help`.

## 2. Add Z3 for specification checks

`cargo djinn smoke-test` uses [Z3](https://github.com/Z3Prover/z3) to search for
contradictions and ambiguous outputs within finite bounds. The editor also uses
these checks for diagnostics. They do not require Charon, Aeneas, Lean, or an
agent, and they are not proofs. Other CLI commands do not run them automatically.

Install the `z3` executable using your package manager or the project's
[release binaries](https://github.com/Z3Prover/z3/releases), then check:

```sh
z3 --version
cd "$DJINN_REPO/example/clamp"
cargo djinn smoke-test
```

For example, use `brew install z3` with the [Homebrew package](https://formulae.brew.sh/formula/z3),
or `sudo apt install z3` with the [Debian package](https://packages.debian.org/stable/z3).

## 3. Install the verification toolchain

Charon extracts a Rust crate into an intermediate representation. Aeneas turns
that representation into Lean definitions, and Lean checks the proofs against
the Aeneas library and Mathlib. These components must agree on their versions;
installing the latest version of each independently is not sufficient.

This repository's examples use the following versions:

| Component | Version and source |
|---|---|
| Aeneas | [`557eff83ecef5083b98a52a94ca7fae63d6c1dab`](https://github.com/AeneasVerif/aeneas/tree/557eff83ecef5083b98a52a94ca7fae63d6c1dab) |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04`, selected by Aeneas's [`charon-pin`](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/charon-pin) |
| Rust for Charon | `nightly-2026-09-17`, selected by Charon's [`rust-toolchain`](https://github.com/AeneasVerif/charon/blob/c8f15d7d658c86a95658f71ad99cddd4be002e04/rust-toolchain) |
| Lean | `leanprover/lean4:v4.31.0`, selected by Aeneas's [`lean-toolchain`](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/backends/lean/lean-toolchain) |
| Mathlib | Selected by the pinned Aeneas Lean project's Lake manifest |

The examples expect the tools under `$DJINN_REPO/tools/aeneas`. Use that layout
for your first installation; [custom paths](#4-configure-tool-paths) are described
below. Building these dependencies requires network access and can take much
longer than building Djinn itself.

### OCaml, opam, and Make

Install [opam](https://opam.ocaml.org/doc/Install.html) and initialize it with
`opam init` if this is your first opam installation. Install any native build
dependencies requested by opam. The following uses the OCaml version and
formatter from the [pinned Aeneas build instructions](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/README.md#installation--build),
with the additional packages used by Charon and its tests:

```sh
opam switch create djinn-5.3 5.3.0
eval "$(opam env --switch=djinn-5.3 --set-switch)"
opam install 'dune>=3.7' calendar core_unix domainslib easy_logging logs menhir \
  menhirLib ocamlformat.0.27.0 ocamlgraph odoc ppx_deriving \
  ppx_deriving_yojson progress re unionFind 'visitors>=20260520' yojson zarith
```

If the switch already exists, skip `opam switch create`. Repeat the `opam env`
command in new terminals before building Aeneas. The OCaml packages above are
resolved by opam; this is not a fully pinned opam environment.

The pinned Aeneas Makefile rejects macOS's system Make 3.81. On macOS, install
the [Homebrew GNU Make package](https://formulae.brew.sh/formula/make) and put its
`make` command first on `PATH`, including for the helper
scripts that invoke `make` themselves:

```sh
brew install make
export PATH="$(brew --prefix make)/libexec/gnubin:$PATH"
make --version
```

On Linux, use your distribution's GNU Make.

### Build Charon and Aeneas

```sh
mkdir -p "$DJINN_REPO/tools"
git clone https://github.com/AeneasVerif/aeneas.git "$DJINN_REPO/tools/aeneas"
cd "$DJINN_REPO/tools/aeneas"
git checkout 557eff83ecef5083b98a52a94ca7fae63d6c1dab
make setup-charon
make build-bin-dir
```

`setup-charon` clones Charon at the pinned commit, builds its Rust and OCaml
parts, and runs its tests. With rustup, Charon's toolchain file selects its
nightly and components automatically. The setup helper prefers Nix if Nix is
installed; consult the pinned Aeneas instructions if you use that route.

`build-bin-dir` builds Aeneas and copies it into `bin/aeneas`.
`make build-bin` alone only builds inside `src/_build/`; it does not create the
executable at the path Djinn's examples use.

Check that both executables exist:

```sh
test -x "$DJINN_REPO/tools/aeneas/charon/bin/charon"
test -x "$DJINN_REPO/tools/aeneas/bin/aeneas"
```

Charon's nightly is used during translation. Your crate must be compatible
with it even if you normally build the crate using another Rust toolchain.

### Build the Lean backend

Install [elan](https://github.com/leanprover/elan#installation), which puts
`lean` and `lake` on `PATH` and selects the version from `lean-toolchain`.
Then build the pinned backend:

```sh
cd "$DJINN_REPO/tools/aeneas/backends/lean"
lake exe cache get
lake build
```

The cache command downloads prebuilt Mathlib artifacts. The Aeneas library
still builds from source. Keep the generated files and pinned manifests;
subsequent verification runs reuse them.

Each Djinn crate has a Lean project, normally `djinn/proofs/`. To let these
projects share the backend's downloaded packages, set:

```sh
export DJINN_LAKE_PACKAGES="$DJINN_REPO/tools/aeneas/backends/lean/.lake/packages"
```

Djinn creates a symlink to this directory when a crate has no
`djinn/proofs/.lake/packages` yet. It leaves an existing package directory or
symlink alone. Without this setting it looks for
`$HOME/.cache/djinn/lake-packages`; if no shared directory exists, Lake manages
the crate's own packages.

## 4. Configure tool paths

For new crates, export absolute paths in the terminal where you run Djinn:

```sh
export DJINN_CHARON="$DJINN_REPO/tools/aeneas/charon/bin/charon"
export DJINN_AENEAS="$DJINN_REPO/tools/aeneas/bin/aeneas"
export DJINN_AENEAS_LEAN="$DJINN_REPO/tools/aeneas/backends/lean"
```

Persist these exports in your shell configuration if needed, using your actual
absolute checkout path. The [new-crate walkthrough](FIRST_STEPS.md) uses them.

`[package.metadata.djinn]` in a crate's `Cargo.toml` takes precedence over the
corresponding environment variables. The checked-in examples already specify
their tool paths, so setting environment variables does **not** override those
paths. If your tools are elsewhere, update the example's metadata as well.

| Metadata key | Environment variable | How the value is interpreted |
|---|---|---|
| `charon` | `DJINN_CHARON` | A bare executable name is searched on `PATH`; a relative path containing `/` is relative to the crate directory |
| `aeneas` | `DJINN_AENEAS` | Same as `charon` |
| `aeneas_lean` | `DJINN_AENEAS_LEAN` | Path written into the Lean project's `lakefile.lean`; a relative path is relative to that project, normally `<crate>/djinn/proofs/` |
| `lake_packages` | `DJINN_LAKE_PACKAGES` | Metadata paths are relative to the crate; use an absolute path for the environment variable |

For example, the paths in `example/clamp/Cargo.toml` are:

```toml
[package.metadata.djinn]
namespace = "ClampDemo"
spec = "src/spec.rs"
charon = "../../tools/aeneas/charon/bin/charon"
aeneas = "../../tools/aeneas/bin/aeneas"
aeneas_lean = "../../../../tools/aeneas/backends/lean"
```

The extra `../` components in `aeneas_lean` account for `djinn/proofs/`.
Neither TOML paths nor these configuration values expand `~` or shell variables;
use literal absolute paths in TOML, or shell-expanded exports as above.

Djinn creates `lakefile.lean` only when it is missing. Changing `aeneas_lean`
later does not rewrite an existing lakefile. Update its `require aeneas from`
path if you move the backend, then run `lake update` from that Lean project to
refresh its dependency manifest.

### Check full verification

```sh
cd "$DJINN_REPO/example/clamp"
cargo djinn verify
```

A successful run ends with `PASS` after the `cargo build`, `charon`, `aeneas`,
`lake build`, and `axiom audit` stages. This is the installation check that
actually reruns the proof pipeline. The first run may need to compile the
crate's Lean files even after the backend has been built.

| Failure | What to check |
|---|---|
| `no such command: djinn` | The directory containing `cargo-djinn` must be on `PATH` in this terminal |
| Cannot read `Cargo.toml` | Run inside the example crate, or pass `--manifest-path` with its manifest path |
| `charon: cannot run` or `aeneas: cannot run` | Check executable paths in crate metadata first; metadata overrides environment variables |
| Missing OCaml library during setup | Activate the intended opam switch and install the requested package |
| Missing Lean imports or Mathlib artifacts | Check `lakefile.lean`, `lean-toolchain`, the backend build, and the target of `.lake/packages`; a missing shared cache is not the only possible cause |
| Rust refuses an unverified declaration | The example was changed or its report is missing; see the compile-time gate explanation in [First steps](FIRST_STEPS.md) |

## 5. Optional coding agent

Only `cargo djinn implement` and `cargo djinn optimize` launch a coding agent.
Install and authenticate either the [Codex CLI](https://developers.openai.com/codex/cli)
or [Claude Code](https://code.claude.com/docs/en/setup) using their official
instructions. These commands consume the selected account's usage or API
budget. `translate`, `verify`, `status`, `guide`, `smoke-test`, and `bench` do not
make model requests.

Codex is the default; select Claude with `--agent claude`. Check the executable
with `codex --version` or `claude --version`. For Codex, `codex login status`
checks authentication without sending a model request; see its
[authentication guide](https://developers.openai.com/codex/auth) for setup.

Set a spending limit on your first run, for example
`cargo djinn implement --agent codex --limit 2`. Djinn polls logged usage about
every five seconds and stops the process group at the reported or estimated
cost in US dollars. The estimate depends on CLI logs and Djinn's price table,
can lag usage, and can exceed the requested amount. It is not a provider billing
cap or a measure of remaining subscription allowance. If cost and token data
are unavailable, the supervisor cannot enforce an accurate limit. Claude also
receives `--max-budget-usd`; that separate CLI option does not apply to Codex.
`cargo djinn status` reports recorded jobs and usage.

The agent's *jail* is a working copy of the crate, not a virtual machine or
container. Djinn copies implementation and proof files back for verification
and regenerates trusted files. By default it also selects Codex's
`workspace-write` sandbox or Claude's allowed-tool restrictions. The working
copy alone does not isolate the agent from your machine. `--yolo` bypasses the
agent CLI's normal restrictions.

## 6. Optional editor integration

The Djinn language server runs beside rust-analyzer. It adds proof status,
smoke-test diagnostics, navigation to proofs, and commands to verify or invoke
an agent. Install Z3 for the diagnostics and the verification toolchain for
Verify. An editor is not needed to use the CLI.

### VS Code

With Node.js/npm and the VS Code `code` command available:

```sh
cd "$DJINN_REPO/editors/vscode"
npm ci
code --extensionDevelopmentPath="$PWD" "$DJINN_REPO/example/clamp"
```

This starts an extension development window. To package and install it, run
`npx @vscode/vsce package --allow-missing-repository` in the same directory, then
`code --install-extension rust-djinn-0.2.0.vsix`.

The extension looks for `rust-djinn-lsp` on `PATH`, then in `~/.cargo/bin`, then
in this checkout's debug build. Set `djinn.serverPath` to an absolute path if
your editor has a different environment from the terminal.

| Setting | Default | Purpose |
|---|---|---|
| `djinn.serverPath` | `rust-djinn-lsp` | Language server executable |
| `djinn.driverPath` | empty | Driver override; otherwise the server looks beside itself |
| `djinn.agent` | `codex` | Agent for the Implement command |
| `djinn.status` | `line` | Display status after declarations, as `inlayHint`, or `off` |

The extension defaults rust-analyzer's `cargo.extraEnv` to `DJINN_GATE=off`
so analysis remains usable while a specification is unverified. This affects
editor analysis; normal terminal builds still use the gate unless you also
disable it there. See [First steps](FIRST_STEPS.md) for the gate's scope.

### Neovim and language-server diagnostics

The repository provides a complete configuration for Neovim 0.10 or later:

```sh
cd "$DJINN_REPO"
nvim -u editors/nvim/djinn.lua example/clamp/src/spec.rs
```

Ensure `rust-djinn-lsp` is on `PATH` before starting Neovim. The demo's final
fallback path is specific to the author's machine. To integrate it with your
own setup, use [the editor guide](../editors/README.md).

To inspect the language server without an editor:

```sh
cd "$DJINN_REPO"
python3 editors/lsp-check.py rust-djinn-lsp example/clamp/src/spec.rs
```

The scripted client prints lenses, hints, and diagnostics, helping distinguish
a server problem from an editor configuration problem.

Continue with [First steps](FIRST_STEPS.md) to write a specification, interpret
verification results, and create your own crate.
