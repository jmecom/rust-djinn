//! External Cargo → Charon → Aeneas → Lean security regressions.
//! Set DJINN_CHARON, DJINN_AENEAS and DJINN_AENEAS_LEAN, put Cargo and Lake on
//! PATH, then run:
//!
//! cargo test -p cargo-djinn --test verification_regressions -- --ignored --test-threads=1
//!
//! Tests are ignored by default and require passing controls before attacks.
//! Crates have separate Cargo targets; failed fixtures and subprocess logs stay
//! in the system temporary directory. DJINN_TEST_KEEP=1 retains successes too.

use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
const NS: &str = "AuditRegression";
const TRUE_SPEC: &str = "pub fn answer() -> out: bool { out == true; }";
const TRUE_IMPL: &str = "pub fn answer() -> bool { true }\n";
const TRUE_TACTICS: [&str; 2] = [
    "simp [answer_spec, answer_pre]",
    "simp [AuditRegression.answer, AuditRegression.solution.answer,\n        WP.spec_equiv_exists, answer_pre, answer_spec]",
];

struct Fixture {
    root: PathBuf,
    invocation: usize,
}

struct Run {
    status: ExitStatus,
    text: String,
}

impl Fixture {
    fn baseline(label: &str) -> Self {
        for key in ["DJINN_CHARON", "DJINN_AENEAS", "DJINN_AENEAS_LEAN"] {
            let path = std::env::var_os(key)
                .unwrap_or_else(|| panic!("set {key} to run the external-toolchain regressions"));
            assert!(Path::new(&path).exists(), "{key} does not exist: {path:?}");
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let id = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "djinn-regression-{label}-{}-{nonce}-{id}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        let mut f = Self {
            root,
            invocation: 0,
        };
        let djinn = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let backend = std::env::var("DJINN_AENEAS_LEAN").unwrap();
        // TOML's string serializer handles spaces, quotes and Windows paths.
        let quoted = |s: &str| toml::Value::String(s.to_owned()).to_string();
        f.write("Cargo.toml", &format!(
            "[package]\nname = \"djinn-verification-regression\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\
             [workspace]\n[dependencies]\ndjinn = {{ path = {} }}\n\
             [package.metadata.charon]\npreset = \"aeneas\"\n\
             [package.metadata.djinn]\nnamespace = \"{NS}\"\nlake_packages = {}\n",
            quoted(djinn.to_str().unwrap()), quoted(&format!("{backend}/.lake/packages"))
        ));
        f.write("src/lib.rs", &format!("use djinn::djinn;\n#[forbid(unsafe_code)]\n#[path = \"../djinn/solution/mod.rs\"]\npub mod solution;\ndjinn! {{ {TRUE_SPEC} }}\n"));
        f.write("djinn/solution/mod.rs", TRUE_IMPL);
        f.proof(&answer_proofs("", TRUE_TACTICS));
        let run = f.verify();
        assert!(
            run.status.success(),
            "valid reference fixture failed: {}\n{}",
            f.root.display(),
            tail(&run.text)
        );
        let report = f.report();
        assert_eq!(
            report["run"]["pass"].as_bool(),
            Some(true),
            "valid reference report did not pass"
        );
        assert!(
            report["decl"]
                .as_array()
                .unwrap()
                .iter()
                .all(|d| d["ok"].as_bool() == Some(true)),
            "valid reference has incomplete declarations"
        );
        f
    }

    fn write(&self, path: &str, content: &str) {
        let path = self.root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, content).unwrap();
    }

    fn proof(&self, content: &str) {
        self.write(&format!("djinn/proofs/{NS}/Proofs.lean"), content);
    }

    fn report(&self) -> toml::Value {
        let path = self.root.join("djinn/report.toml");
        toml::from_str(
            &fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display())),
        )
        .unwrap()
    }

    fn verify(&mut self) -> Run {
        let mut command = Command::new(env!("CARGO_BIN_EXE_cargo-djinn"));
        self.invocation += 1;
        // Keep logs outside the certified crate: checking must not itself
        // change an input certificate between verification and compilation.
        let log_path = self
            .root
            .with_extension(format!("run-{}.log", self.invocation));
        let log = File::create(&log_path).unwrap();
        command
            .arg("verify")
            .current_dir(&self.root)
            .env("CARGO_TARGET_DIR", self.root.join("target"))
            .env("CARGO_INCREMENTAL", "0")
            .env_remove("DJINN_GATE")
            .env_remove("DJINN_VERIFYING")
            .env_remove("CLIPPY_ARGS")
            .stdout(Stdio::from(log.try_clone().unwrap()))
            .stderr(Stdio::from(log));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("CHARON_") {
                command.env_remove(key);
            }
        }
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        let mut child = command
            .spawn()
            .unwrap_or_else(|e| panic!("cannot run {command:?}: {e}"));
        let timeout = Duration::from_secs(
            std::env::var("DJINN_TEST_TIMEOUT_SECS")
                .ok()
                .map(|s| {
                    s.parse()
                        .expect("DJINN_TEST_TIMEOUT_SECS must be an integer")
                })
                .unwrap_or(600),
        );
        let started = Instant::now();
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if started.elapsed() > timeout {
                #[cfg(unix)]
                unsafe {
                    libc::kill(-(child.id() as i32), libc::SIGKILL);
                }
                let _ = child.kill();
                let _ = child.wait();
                panic!(
                    "external-toolchain command timed out after {timeout:?}; fixture {}, log {}",
                    self.root.display(),
                    log_path.display()
                );
            }
            std::thread::sleep(Duration::from_millis(50));
        };
        Run {
            status,
            text: fs::read_to_string(log_path).unwrap(),
        }
    }

    fn rejected(&mut self, expected_stage: &str) -> Run {
        let run = self.verify();
        self.assert_rejected(&run, expected_stage);
        run
    }

    fn assert_rejected(&self, run: &Run, expected_stage: &str) {
        assert!(
            !run.status.success(),
            "exploit unexpectedly passed: {}\n{}",
            self.root.display(),
            tail(&run.text)
        );
        let report = self.report();
        assert_eq!(report["run"]["pass"].as_bool(), Some(false));
        let stage = report["run"]["stage"].as_str().unwrap();
        assert_eq!(stage, expected_stage, "fixture failed for an unrelated reason: {}\n{}", self.root.display(), tail(&run.text));
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if std::thread::panicking() || std::env::var_os("DJINN_TEST_KEEP").is_some() {
            eprintln!("retained fixture: {}", self.root.display());
        } else {
            let _ = fs::remove_dir_all(&self.root);
            for n in 1..=self.invocation {
                let _ = fs::remove_file(self.root.with_extension(format!("run-{n}.log")));
            }
        }
    }
}

fn tail(text: &str) -> String {
    let mut lines: Vec<_> = text.lines().rev().take(100).collect();
    lines.reverse();
    lines.join("\n")
}

fn answer_proofs(preamble: &str, tactics: [&str; 2]) -> String {
    let [unambiguous, implementation] = tactics;
    format!(r#"
import Aeneas
import AuditRegression.Spec
import AuditRegression.Code.Funs
{preamble}
namespace AuditRegression.Proofs
open Aeneas Std Result AuditRegression.Spec

theorem answer.unambiguous :
    ∀ (a b : Bool), answer_spec a → answer_spec b → a = b := by
  {unambiguous}

theorem answer.impl_correct :
    answer_pre → AuditRegression.answer ⦃ out => answer_spec out ⦄ := by
  {implementation}
end AuditRegression.Proofs
"#)
}

#[test]
#[ignore = "requires real Cargo/Charon/Aeneas/Lean toolchain and process isolation"]
fn proof_audits_reject_spoofed_output_and_wrong_types() {
    let mut f = Fixture::baseline("proof-audit");
    f.write(
        "djinn/solution/mod.rs",
        "pub fn answer() -> bool { false }\n",
    );
    f.proof(&answer_proofs(
        "axiom «does not depend on any axioms» : False",
        ["exact False.elim «does not depend on any axioms»"; 2],
    ));
    f.rejected("axiom audit");

    f.proof(&(answer_proofs("", ["sorry"; 2]) + r#"
open Lean Elab Command
@[command_elab Lean.Parser.Command.printAxioms]
def falsifyAxiomAudit : CommandElab := fun stx => do
  logInfo m!"'{stx[2].getId}' does not depend on any axioms"
"#));
    f.rejected("axiom audit");

    // Bypass Lean's ordinary elaboration-time kernel check deliberately. The
    // artifact loader must replay these declarations, not merely trust an
    // .olean file whose axiom closure happens to be empty.
    f.proof(&answer_proofs(
        r#"
import Lean
set_option debug.skipKernelTC true
open Lean Elab Command
run_cmd liftCoreM do
  addDecl (.thmDecl (mkTheoremValEx `forgedFalse [] (mkConst ``False)
    (mkConst ``True.intro) [`forgedFalse]))
"#,
        ["exact False.elim forgedFalse"; 2],
    ));
    let forged = f.rejected("isolated proof check");
    assert!(
        forged.text.contains("trusted kernel audit"),
        "forged declaration was not exercised by the trusted kernel checker\n{}",
        tail(&forged.text)
    );

    f.write("djinn/solution/mod.rs", TRUE_IMPL);
    f.proof(&answer_proofs("", TRUE_TACTICS).replace(
        "answer_pre → AuditRegression.answer ⦃ out => answer_spec out ⦄ := by\n  simp [AuditRegression.answer, AuditRegression.solution.answer,\n        WP.spec_equiv_exists, answer_pre, answer_spec]",
        "True := by trivial",
    ));
    f.rejected("isolated proof check");
}

#[test]
#[ignore = "requires real Cargo/Charon/Aeneas/Lean toolchain and process isolation"]
fn proof_evaluation_cannot_mutate_source_or_host_files() {
    let mut f = Fixture::baseline("proof-io");
    let marker = f.root.with_extension("host-write-marker");
    assert!(!marker.exists());
    // Lean and JSON use the same escapes for these temporary absolute paths.
    let quoted_marker = serde_json::to_string(marker.to_str().unwrap()).unwrap();
    let quoted_solution =
        serde_json::to_string(f.root.join("djinn/solution/mod.rs").to_str().unwrap()).unwrap();
    let true_proofs = answer_proofs("", TRUE_TACTICS);
    let attempts = [
        (format!("#eval IO.FS.writeFile {quoted_marker} \"untrusted proof executed\""), true),
        (format!("#eval IO.FS.writeFile {quoted_solution} \"pub fn answer() -> bool {{ false }}\\n\""), true),
        ("#eval IO.FS.writeFile \"../solution/mod.rs\" \"pub fn answer() -> bool { false }\\n\"".to_owned(), false),
    ];
    for (attempt, absolute) in attempts {
        f.proof(&format!("{true_proofs}\n{attempt}\n"));
        let run = f.verify();
        // Check containment even when an unrelated failure is reported. The
        // writes are separate runs so a denied first write cannot hide a
        // vulnerability in the second path.
        assert!(
            !marker.exists(),
            "untrusted proof wrote outside its build directory: {}",
            marker.display()
        );
        assert_eq!(
            fs::read_to_string(f.root.join("djinn/solution/mod.rs")).unwrap(),
            TRUE_IMPL,
            "untrusted proof changed the implementation after extraction"
        );
        f.assert_rejected(&run, "isolated proof check");
        if absolute {
            let message = run.text.to_ascii_lowercase();
            assert!(
                [
                    "permission denied",
                    "operation not permitted",
                    "read-only file system"
                ]
                .iter()
                .any(|error| message.contains(error)),
                "absolute write was not rejected by filesystem confinement\n{}",
                tail(&run.text)
            );
        }
    }
}

#[test]
#[ignore = "requires real Cargo/Charon/Aeneas/Lean toolchain and process isolation"]
fn missing_implementation_cannot_receive_a_passing_report() {
    let mut f = Fixture::baseline("missing-implementation");
    f.write(
        "djinn/solution/mod.rs",
        "// Deliberately no implementation.\n",
    );
    f.proof(
        r#"
import Aeneas
import AuditRegression.Spec
namespace AuditRegression.Proofs
open Aeneas Std Result AuditRegression.Spec

theorem answer.unambiguous :
    ∀ (a b : Bool), answer_spec a → answer_spec b → a = b := by
  simp [answer_spec, answer_pre]
end AuditRegression.Proofs
"#,
    );
    f.rejected("incomplete");
}
