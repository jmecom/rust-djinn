use cargo_djinn::{config, status, verify};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!("djinn-report-freshness-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::create_dir_all(path.join("djinn/solution")).unwrap();
        fs::write(path.join("Cargo.toml"), "[package]\nname='freshness'\nversion='0.1.0'\n[workspace]\n").unwrap();
        fs::write(path.join("src/lib.rs"), "fn helper(x: u8) -> u8 { x }\nfn outer(x: u8) -> u8 { helper(x) }\nconst LIMIT: u8 = 1;\ndjinn! { pub fn f(x: u8) -> y: u8 { y == outer(x) + LIMIT; } }\n").unwrap();
        fs::write(path.join("djinn/solution/mod.rs"), "pub fn f(x: u8) -> u8 { x + 1 }").unwrap();
        Self(path)
    }
}
impl Drop for Fixture { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }

fn proved_report(cfg: &config::Config) -> verify::Report {
    let lowered = verify::lower_spec(cfg).unwrap();
    let declarations = verify::decl_statuses(cfg, &lowered, &HashMap::new());
    let obligations = declarations.iter().flat_map(|d| d.obligations.iter().map(|o| (o.clone(), "proved".into()))).collect();
    verify::Report {
        certificate: None, time: 0, duration_secs: 0, pass: true, stage: "done".into(),
        obligations, declarations, errors: vec![], log_tail: vec![],
    }
}

#[test]
fn report_contains_transitive_ambient_and_constant_dependencies() {
    let f = Fixture::new();
    let cfg = config::load_config(&f.0.join("Cargo.toml")).unwrap();
    let mut report = proved_report(&cfg);
    for name in ["f", "outer", "helper", "LIMIT"] {
        assert!(report.declarations.iter().any(|d| d.name == name), "missing {name}");
    }
    report.finalize();
    assert!(report.declarations.iter().all(|d| d.ok));
}

#[test]
fn old_or_changed_source_never_displays_verified_state() {
    let f = Fixture::new();
    let cfg = config::load_config(&f.0.join("Cargo.toml")).unwrap();
    let mut report = proved_report(&cfg);
    assert!(status::views(&cfg, Some(&report), None).iter().all(|d| d.changed));
    report.certificate = Some(djinn_syntax::certificate::capture(&cfg.crate_dir).unwrap());
    assert!(status::views(&cfg, Some(&report), None).iter().all(|d| !d.changed));
    fs::write(cfg.solution_dir().join("mod.rs"), "pub fn f(_: u8) -> u8 { 0 }").unwrap();
    let views = status::views(&cfg, Some(&report), None);
    assert!(views.iter().all(|d| d.changed));
    assert!(views.iter().all(|d| d.obs.iter().all(|(_, s)| *s != status::ObState::Verified)));
}

#[test]
fn local_status_does_not_run_lean_or_claim_checked_proofs() {
    let f = Fixture::new();
    let proofs = f.0.join("proofs");
    fs::create_dir_all(proofs.join("Demo")).unwrap();
    let marker = f.0.join("should-not-exist");
    fs::write(proofs.join("Demo/Proofs.lean"), format!("#eval IO.FS.writeFile {:?} \"ran\"\ntheorem impossible : False := by trivial\n", marker.to_str().unwrap())).unwrap();
    fs::write(proofs.join("lean-toolchain"), "nonexistent-toolchain").unwrap();
    let states = status::local_states("Demo", &proofs, 1).unwrap();
    assert_eq!(states.get("impossible"), Some(&status::ObState::Drafted));
    assert!(!marker.exists());
}

#[test]
fn repeated_translate_preserves_proofs_using_constant_and_type_dependencies() {
    let f = Fixture::new();
    fs::write(f.0.join("src/lib.rs"), "const LIMIT: u8 = 1;\npub struct Token { value: u8 }\ndjinn! { pub fn f(x: Token) -> r: u8 { r == LIMIT; } }\n").unwrap();
    let mut cfg = config::load_config(&f.0.join("Cargo.toml")).unwrap();
    cfg.aeneas_lean = Some(f.0.join("backend").display().to_string());
    cfg.lake_packages = f.0.join("unused-package-cache");
    fs::create_dir_all(cfg.lean_dir().join("Code")).unwrap();
    // This is an archive/scaffolding test: supply an available type model so
    // translate does not invoke Charon, Aeneas, or Lean.
    fs::write(cfg.lean_dir().join("Code/Types.lean"), "structure Freshness.Token where\n  value : U8\n").unwrap();
    let mut log = verify::Log::new(false);
    verify::translate(&cfg, &mut log).unwrap();
    let report = verify::Report::load(&cfg).unwrap();
    for (name, kind) in [("LIMIT", "constant"), ("Token", "type")] {
        assert!(report.declarations.iter().any(|d| d.name == name && d.kind == kind));
    }
    let path = cfg.lean_dir().join("Proofs.lean");
    let helpers = "theorem keep_limit : Freshness.LIMIT = Freshness.LIMIT := rfl\ntheorem keep_token (x : Freshness.Token) : x = x := rfl\n\n";
    let end = "end Freshness.Proofs";
    let original = fs::read_to_string(&path).unwrap().replace(end, &format!("{helpers}{end}"));
    fs::write(&path, &original).unwrap();
    verify::translate(&cfg, &mut log).unwrap();
    assert_eq!(fs::read_to_string(&path).unwrap(), original);
    assert!(!log.text.contains("archived"), "{}", log.text);
}


#[test]
fn native_gate_accepts_a_fresh_documented_enum_and_rejects_shape_changes() {
    let f = Fixture::new();
    let djinn = PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf();
    fs::write(f.0.join("Cargo.toml"), format!("[package]\nname='freshness'\nversion='0.1.0'\nedition='2021'\n[workspace]\n[dependencies]\ndjinn={{path={}}}\n", toml::Value::String(djinn.display().to_string()))).unwrap();
    let source = "/// The format's \"alphabet\".\n#[derive(Clone, Copy)]\npub enum Token { A }\n#[path=\"../djinn/solution/mod.rs\"] mod solution;\ndjinn::djinn! { pub fn f(t: Token) -> r: u8 { r == 0; } }\n";
    fs::write(f.0.join("src/lib.rs"), source).unwrap();
    fs::write(f.0.join("djinn/solution/mod.rs"), "pub fn f(_: crate::Token) -> u8 { 0 }\n").unwrap();
    let cargo = |args: &[&str]| {
        let mut cmd = std::process::Command::new(env!("CARGO"));
        cmd.args(args).current_dir(&f.0).env("CARGO_TARGET_DIR", f.0.join("target"))
            .env_remove("DJINN_GATE").env_remove("DJINN_VERIFYING").env_remove("CLIPPY_ARGS");
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("CHARON_") { cmd.env_remove(key); }
        }
        cmd.output().unwrap()
    };
    let lock = cargo(&["generate-lockfile", "--offline"]);
    assert!(lock.status.success(), "{}", String::from_utf8_lossy(&lock.stderr));
    let cfg = config::load_config(&f.0.join("Cargo.toml")).unwrap();
    // Compare standalone report serialization with rustc's actual macro.
    let mut report = proved_report(&cfg);
    report.certificate = Some(djinn_syntax::certificate::capture(&f.0).unwrap());
    report.finalize();
    report.save(&cfg);
    let fresh = cargo(&["check", "--locked", "--offline"]);
    assert!(fresh.status.success(), "{}", String::from_utf8_lossy(&fresh.stderr));
    fs::write(f.0.join("src/lib.rs"), source.replace("enum Token { A }", "enum Token { A, B }")).unwrap();
    // Keep the source certificate current to isolate the type-token check.
    report.certificate = Some(djinn_syntax::certificate::capture(&f.0).unwrap());
    report.save(&cfg);
    let changed = cargo(&["check", "--locked", "--offline"]);
    assert!(!changed.status.success());
    assert!(String::from_utf8_lossy(&changed.stderr).contains("uses `Token`, which changed"), "{}", String::from_utf8_lossy(&changed.stderr));
}
