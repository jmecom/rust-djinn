# Installation reference

This reference describes the prerequisites for the [Djinn tutorial](README.md).
The required tools depend on the operation. Rust is sufficient to run an
unchanged example with its supplied verification report. Z3 adds bounded
specification checks, while Charon, Aeneas, and Lean provide the full
verification pipeline. Coding agents and editor integrations are optional.

| Operation | Prerequisites |
|---|---|
| Build and run an unchanged, verified example; inspect `status` and `guide` | Git, Rust, and the Djinn tools |
| Check specifications for bounded counterexamples with `smoke-test` | The above, plus Z3 |
| Translate a crate or verify its implementation and proofs | The Rust tools, Charon, Aeneas, and Lean/Lake |
| Generate implementations with `implement`, or improve them with `optimize` | The verification toolchain and an authenticated Codex or Claude Code CLI |
| See proof status and diagnostics while editing | The Djinn language server, an editor integration, and Z3 for smoke-test diagnostics |

The commands target Linux and macOS with a POSIX shell. The driver uses Unix
filesystem and process APIs, so native Windows is not supported. A Windows
installation requires a Linux environment, such as WSL, with the toolchain
installed inside that environment. The agent workflow also requires Bash.

The Rust build, example program, and tutorial smoke checks were exercised
during preparation of this tutorial. The external verifier installation was
checked against the pinned projects' source files but was not executed from
start to finish. The verification commands below therefore describe expected
behavior, rather than a recorded successful installation.

## Rust tools

The Rust build requires `cargo`, `rustc`, and a native linker.
[rustup](https://rustup.rs/) supplies the Rust toolchain. Charon's separate
nightly toolchain is not required to build Djinn itself. The following commands
create a checkout:

```sh
git clone https://github.com/shenniger/rust-djinn.git
cd rust-djinn
```

For an existing checkout, the starting directory is its repository root. The
following commands record that path and build the tools:

```sh
export DJINN_REPO="$PWD"

cd "$DJINN_REPO/rust-djinn"
cargo build --workspace --locked
export PATH="$DJINN_REPO/rust-djinn/target/debug:$PATH"
```

`DJINN_REPO` names the repository root, which contains `docs/`, `example/`,
and `editors/`. The second `rust-djinn/` directory contains the Cargo workspace.
The exports apply to the current shell. Commands in later sections assume
that `DJINN_REPO` is still set to the absolute checkout path and that the build
directory remains on `PATH`.

The workspace builds `cargo-djinn`, the `rust-djinn-lsp` language server, and the
`djinn` library used by example crates. Adding the debug directory to `PATH`
makes subsequent rebuilds available immediately. Cargo can alternatively
install copies of the two executables:

```sh
cargo install --locked --path "$DJINN_REPO/rust-djinn/cargo-djinn"
cargo install --locked --path "$DJINN_REPO/rust-djinn/lsp"
```

That alternative requires Cargo's installation directory, normally
`$HOME/.cargo/bin`, on `PATH`. Changes to the tool sources require reinstallation.

### Rust-only installation check

```sh
cd "$DJINN_REPO/example/clamp"
cargo build --locked
printf '3\n-4\n12\n' | cargo run --locked -- 0 10
cargo djinn status
cargo djinn guide
```

The clamp example includes its implementation, proofs, and verification report,
so it builds without running Lean or an agent. `status` reads that report;
building the example does not perform a fresh proof check. A fresh check
requires `cargo djinn verify` and the verification toolchain described below.

This installation is sufficient for the initial example in
[First steps](FIRST_STEPS.md). The [Language tour](LANGUAGE_TOUR.md) explains
the specification syntax independently of tool installation. The command
`cargo djinn --help` lists the driver's commands; the current CLI exits with
status 2 when printing usage, including for `--help`.

## Z3 for specification checks

`cargo djinn smoke-test` uses [Z3](https://github.com/Z3Prover/z3) to search for
contradictions and ambiguous outputs within finite bounds. The editor also uses
these checks for diagnostics. They do not require Charon, Aeneas, Lean, or an
agent, and they are not proofs. Other CLI commands do not run them automatically.

The checks require the `z3` executable on `PATH`, available through a package
manager or the project's [release binaries](https://github.com/Z3Prover/z3/releases).
The following commands inspect the installed version and check the clamp
specification:

```sh
z3 --version
cd "$DJINN_REPO/example/clamp"
cargo djinn smoke-test
```

Package-manager installation commands include `brew install z3` for the
[Homebrew package](https://formulae.brew.sh/formula/z3) and `sudo apt install z3`
for the [Debian package](https://packages.debian.org/stable/z3).

## Verification toolchain

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

The examples expect the tools under `$DJINN_REPO/tools/aeneas`, which is the
layout used below. Alternative locations require explicit
[tool-path configuration](#tool-path-configuration). Building these dependencies
requires network access and can take substantially longer than building Djinn.

### OCaml, opam, and Make

Aeneas and Charon's OCaml libraries require [opam](https://opam.ocaml.org/doc/Install.html)
and the native build dependencies it requests. A new opam installation must be
initialized with `opam init` before creating a switch, which is an environment
containing a selected OCaml compiler and packages. The following uses the OCaml
version and formatter from the
[pinned Aeneas build instructions](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/README.md#installation--build),
with additional packages used by Charon and its tests:

```sh
opam switch create djinn-5.3 5.3.0
eval "$(opam env --switch=djinn-5.3 --set-switch)"
opam install 'dune>=3.7' calendar core_unix domainslib easy_logging logs menhir \
  menhirLib ocamlformat.0.27.0 ocamlgraph odoc ppx_deriving \
  ppx_deriving_yojson progress re unionFind 'visitors>=20260520' yojson zarith
```

The switch creation command is needed only once. The `opam env` command selects
that switch for the current shell and must be repeated in new terminals used
to build Aeneas. Most package versions are resolved by opam, so the command
does not define a fully pinned opam environment.

The pinned Aeneas Makefile rejects macOS's system Make 3.81. The
[Homebrew GNU Make package](https://formulae.brew.sh/formula/make) supplies a
compatible alternative. Its `make` command must precede the system version on
`PATH` because the setup helper scripts also invoke `make`:

```sh
brew install make
export PATH="$(brew --prefix make)/libexec/gnubin:$PATH"
make --version
```

On Linux, the distribution's GNU Make provides this dependency.

### Charon and Aeneas build

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
installed; that route is described in the pinned Aeneas instructions.

`build-bin-dir` builds Aeneas and copies it into `bin/aeneas`.
`make build-bin` alone only builds inside `src/_build/`; it does not create the
executable at the path Djinn's examples use.

Both executables must exist at the configured paths after these builds:

```sh
test -x "$DJINN_REPO/tools/aeneas/charon/bin/charon"
test -x "$DJINN_REPO/tools/aeneas/bin/aeneas"
```

Charon's nightly is used during translation. A crate must therefore be
compatible with that nightly even if its ordinary builds use another Rust
toolchain.

### Lean backend and package cache

[elan](https://github.com/leanprover/elan#installation) supplies `lean` and
`lake` on `PATH` and selects the version specified in `lean-toolchain`.
With elan installed, the pinned backend is built as follows:

```sh
cd "$DJINN_REPO/tools/aeneas/backends/lean"
lake exe cache get
lake build
```

The cache command downloads prebuilt Mathlib artifacts. The Aeneas library
still builds from source. Subsequent verification runs reuse these build
artifacts and the dependency versions recorded in the manifests.

Each Djinn crate has a Lean project, normally `djinn/proofs/`. The following
setting allows those projects to share the backend's downloaded packages:

```sh
export DJINN_LAKE_PACKAGES="$DJINN_REPO/tools/aeneas/backends/lean/.lake/packages"
```

Djinn creates a symlink to this directory when a crate has no
`djinn/proofs/.lake/packages` yet. It leaves an existing package directory or
valid symlink alone. Without this setting it looks for
`$HOME/.cache/djinn/lake-packages`; if no shared directory exists, Lake manages
the crate's own packages.

## Tool-path configuration

For new crates, the following exports provide absolute tool paths:

```sh
export DJINN_CHARON="$DJINN_REPO/tools/aeneas/charon/bin/charon"
export DJINN_AENEAS="$DJINN_REPO/tools/aeneas/bin/aeneas"
export DJINN_AENEAS_LEAN="$DJINN_REPO/tools/aeneas/backends/lean"
```

The [new-crate walkthrough](FIRST_STEPS.md) assumes these variables are set.
They can be retained in shell configuration, provided `DJINN_REPO` is assigned
the absolute checkout path before the exports are evaluated.

`[package.metadata.djinn]` in a crate's `Cargo.toml` takes precedence over the
corresponding environment variables. The checked-in examples already specify
their tool paths, so environment variables do not override them. A tool
installation in another location requires corresponding changes to the
example's metadata.

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
Neither TOML paths nor these configuration values expand `~` or shell variables.
Literal absolute paths in TOML and shell-expanded exports, as above, avoid
that ambiguity.

Djinn creates `lakefile.lean` only when it is missing. Changing `aeneas_lean`
later does not rewrite an existing lakefile. Moving the backend therefore
requires updating the lakefile's `require aeneas from` path and running
`lake update` from that Lean project to refresh its dependency manifest.

### Full verification check

```sh
cd "$DJINN_REPO/example/clamp"
cargo djinn verify
```

A successful run ends with `PASS` after the `cargo build`, `charon`, `aeneas`,
`lake build`, and `axiom audit` stages. This check reruns the proof pipeline.
The first run may need to compile the crate's Lean files even after the backend
has been built.

| Failure | What to check |
|---|---|
| `no such command: djinn` | The directory containing `cargo-djinn` must be on `PATH` in this terminal |
| Cannot read `Cargo.toml` | Run inside the example crate, or pass `--manifest-path` with its manifest path |
| `charon: cannot run` or `aeneas: cannot run` | Check executable paths in crate metadata first; metadata overrides environment variables |
| Missing OCaml library during setup | Activate the intended opam switch and install the requested package |
| Missing Lean imports or Mathlib artifacts | Check `lakefile.lean`, `lean-toolchain`, the backend build, and the target of `.lake/packages`; a missing shared cache is not the only possible cause |
| Rust refuses an unverified declaration | The example was changed or its report is missing; see the compile-time gate explanation in [First steps](FIRST_STEPS.md) |

## Optional coding agent

Only `cargo djinn implement` and `cargo djinn optimize` launch a coding agent.
They require an installed and authenticated
[Codex CLI](https://developers.openai.com/codex/cli) or
[Claude Code](https://code.claude.com/docs/en/setup). The linked documentation
describes installation and authentication. These commands consume the selected
account's usage or API budget. `translate`, `verify`, `status`, `guide`,
`smoke-test`, and `bench` do not make model requests.

Codex is the default; `--agent claude` selects Claude. The commands
`codex --version` and `claude --version` check executable availability.
For Codex, `codex login status` checks authentication without sending a model
request; see its
[authentication guide](https://developers.openai.com/codex/auth) for setup.

The `--limit` option sets a stopping threshold, for example
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
copy alone does not isolate the agent from the host machine. `--yolo` bypasses
the agent CLI's normal restrictions.

## Optional editor integration

The Djinn language server runs beside rust-analyzer. It adds proof status,
smoke-test diagnostics, navigation to proofs, and commands to verify or invoke
an agent. Diagnostics require Z3, and the Verify command requires the
verification toolchain. The CLI operates independently of an editor.

### VS Code

The extension requires Node.js/npm and the VS Code `code` command. The following
commands install its dependencies and open an extension development window:

```sh
cd "$DJINN_REPO/editors/vscode"
npm ci
code --extensionDevelopmentPath="$PWD" "$DJINN_REPO/example/clamp"
```

For a packaged installation, `npx @vscode/vsce package --allow-missing-repository`
creates the extension package in the same directory, and
`code --install-extension rust-djinn-0.2.0.vsix` installs it.

The extension looks for `rust-djinn-lsp` on `PATH`, then in `~/.cargo/bin`, then
in this checkout's debug build. An absolute `djinn.serverPath` setting handles
cases where the editor's environment differs from the terminal's.

| Setting | Default | Purpose |
|---|---|---|
| `djinn.serverPath` | `rust-djinn-lsp` | Language server executable |
| `djinn.driverPath` | empty | Driver override; otherwise the server looks beside itself |
| `djinn.agent` | `codex` | Agent for the Implement command |
| `djinn.status` | `line` | Display status after declarations, as `inlayHint`, or `off` |

The extension defaults rust-analyzer's `cargo.extraEnv` to `DJINN_GATE=off`
so analysis remains usable while a specification is unverified. This affects
editor analysis; normal terminal builds still use the gate unless it is also
disabled in their environment. [First steps](FIRST_STEPS.md) explains the
gate's scope.

### Neovim and language-server diagnostics

The repository provides a complete configuration for Neovim 0.10 or later:

```sh
cd "$DJINN_REPO"
nvim -u editors/nvim/djinn.lua example/clamp/src/spec.rs
```

The `rust-djinn-lsp` executable must be on `PATH` before Neovim starts. The
demo's final fallback path is specific to the author's machine.
[The editor guide](../editors/README.md) describes integration with an existing
Neovim configuration.

The scripted client can inspect the language server without an editor:

```sh
cd "$DJINN_REPO"
python3 editors/lsp-check.py rust-djinn-lsp example/clamp/src/spec.rs
```

The scripted client prints lenses, hints, and diagnostics, helping distinguish
a server problem from an editor configuration problem.

[First steps](FIRST_STEPS.md) uses this setup to introduce specification
writing, verification results, and crate creation. The
[tutorial overview](README.md) describes the remaining material.
