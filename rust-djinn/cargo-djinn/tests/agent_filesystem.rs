#![cfg(unix)]

use cargo_djinn::{agent, config, jail};
use std::fs;
use std::os::unix::fs::{symlink, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

fn assert_text(path: impl AsRef<Path>, expected: &str) {
    let path = path.as_ref();
    assert_eq!(fs::read_to_string(path).unwrap(), expected, "{}", path.display());
}

struct Fixture {
    base: PathBuf,
    cfg: config::Config,
}
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let base = std::env::temp_dir().join(format!(
            "djinn-fs-test-{}-{}-O'Brien",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&base).unwrap();
        let base = base.canonicalize().unwrap();
        let root = base.join("crate");
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(root.join("src/lib.rs"), "// no specification\n").unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname='probe'\nversion='0.0.0'\n",
        )
        .unwrap();
        let cfg = config::load_config(&root.join("Cargo.toml")).unwrap();
        fs::create_dir_all(cfg.solution_dir()).unwrap();
        fs::create_dir_all(cfg.lean_dir()).unwrap();
        fs::write(cfg.solution_dir().join("mod.rs"), "valuable implementation").unwrap();
        Self { base, cfg }
    }
    fn jail(&self) -> PathBuf {
        let jail = self.base.join("jail");
        fs::create_dir_all(jail::proofs_in(&self.cfg, &jail).join(&self.cfg.ns)).unwrap();
        jail
    }
    fn original(&self) -> String {
        fs::read_to_string(self.cfg.solution_dir().join("mod.rs")).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.base);
    }
}

#[test]
fn virtual_workspace_is_an_error_instead_of_a_panic() {
    let f = Fixture::new();
    fs::write(
        f.cfg.crate_dir.join("Cargo.toml"),
        "[workspace]\nmembers=[]\n",
    )
    .unwrap();
    assert!(config::load_config(&f.cfg.crate_dir.join("Cargo.toml"))
        .err()
        .unwrap()
        .contains("package.name"));
}

#[test]
fn config_rejects_absolute_and_escaping_mirrored_paths() {
    let f = Fixture::new();
    for field in ["work_dir", "proofs"] {
        for value in [
            "/tmp/outside",
            "../outside",
            "djinn/../../outside",
            ".djinnscratch/shared",
        ] {
            fs::write(f.cfg.crate_dir.join("Cargo.toml"), format!("[package]\nname='probe'\nversion='0.0.0'\n[package.metadata.djinn]\n{field}='{value}'\n")).unwrap();
            assert!(
                config::load_config(&f.cfg.crate_dir.join("Cargo.toml")).is_err(),
                "accepted {field}={value}"
            );
        }
    }
    assert_eq!(f.original(), "valuable implementation");
}

#[test]
fn source_aliases_and_forged_absolute_config_cannot_destroy_work() {
    let mut f = Fixture::new();
    assert!(jail::sync_back(&f.cfg, &f.cfg.crate_dir).is_err());
    let alias = f.base.join("alias");
    symlink(&f.cfg.crate_dir, &alias).unwrap();
    assert!(jail::sync_back(&f.cfg, &alias).is_err());
    assert_eq!(f.original(), "valuable implementation");
    f.cfg.work_dir = f.base.join("external");
    fs::create_dir_all(f.cfg.solution_dir()).unwrap();
    fs::write(f.cfg.solution_dir().join("mod.rs"), "outside original").unwrap();
    assert!(jail::create(&f.cfg, "absolute", Path::new("/usr/bin/true")).is_err());
    assert_eq!(f.original(), "outside original");
}

#[test]
fn immediate_backups_are_distinct_and_preserve_both_generations() {
    let f = Fixture::new();
    fs::write(f.cfg.lean_dir().join("Proofs.lean"), "proof one").unwrap();
    let first = agent::reset_work(&f.cfg).unwrap();
    fs::write(f.cfg.solution_dir().join("mod.rs"), "implementation two").unwrap();
    fs::write(f.cfg.lean_dir().join("Proofs.lean"), "proof two").unwrap();
    let second = agent::reset_work(&f.cfg).unwrap();
    assert_ne!(first, second);
    assert_text(first.join("solution/mod.rs"), "valuable implementation");
    assert_text(first.join("Proofs.lean"), "proof one");
    assert_text(second.join("solution/mod.rs"), "implementation two");
    assert_text(second.join("Proofs.lean"), "proof two");
}

#[test]
fn archive_failure_rolls_back_already_moved_solution() {
    let f = Fixture::new();
    let external = f.base.join("external");
    fs::create_dir(&external).unwrap();
    fs::write(external.join("Proofs.lean"), "external proof").unwrap();
    fs::remove_dir(f.cfg.lean_dir()).unwrap();
    symlink(&external, f.cfg.lean_dir()).unwrap();
    assert!(agent::reset_work(&f.cfg).is_err());
    assert_eq!(f.original(), "valuable implementation");
    assert_text(external.join("Proofs.lean"), "external proof");
}

#[test]
fn refresh_replaces_leaf_links_without_writing_or_chmodding_their_targets() {
    let f = Fixture::new();
    let jail = f.jail();
    let external = f.base.join("external");
    fs::write(&external, "host original").unwrap();
    fs::set_permissions(&external, fs::Permissions::from_mode(0o600)).unwrap();
    fs::write(f.cfg.lean_dir().join("Spec.lean"), "trusted spec").unwrap();
    let target = jail::proofs_in(&f.cfg, &jail)
        .join(&f.cfg.ns)
        .join("Spec.lean");
    for hardlink in [false, true] {
        if hardlink {
            fs::hard_link(&external, &target).unwrap();
        } else {
            symlink(&external, &target).unwrap();
        }
        jail::sync_forward(&f.cfg, &jail).unwrap();
        assert_text(&external, "host original");
        assert_eq!(
            fs::metadata(&external).unwrap().permissions().mode() & 0o777,
            0o600
        );
        assert_text(&target, "trusted spec");
        assert!(!fs::symlink_metadata(&target)
            .unwrap()
            .file_type()
            .is_symlink());
        fs::remove_file(&target).unwrap();
    }
}

#[test]
fn parent_links_are_rejected_and_untrusted_source_links_preserve_originals() {
    let f = Fixture::new();
    let jail = f.jail();
    let external = f.base.join("external");
    fs::create_dir(&external).unwrap();
    fs::write(external.join("Spec.lean"), "host original").unwrap();
    fs::write(f.cfg.lean_dir().join("Spec.lean"), "trusted spec").unwrap();
    let target = jail::proofs_in(&f.cfg, &jail).join(&f.cfg.ns);
    fs::remove_dir(&target).unwrap();
    symlink(&external, &target).unwrap();
    assert!(jail::sync_forward(&f.cfg, &jail).is_err());
    assert_text(external.join("Spec.lean"), "host original");
    let source = jail::sol_in(&f.cfg, &jail);
    fs::create_dir_all(&source).unwrap();
    symlink(external.join("Spec.lean"), source.join("mod.rs")).unwrap();
    assert!(jail::sync_back(&f.cfg, &jail).is_err());
    assert_eq!(f.original(), "valuable implementation");
}

#[test]
fn helper_scripts_preserve_apostrophes_in_every_path_argument() {
    let f = Fixture::new();
    let bin = f.base.join("fake'driver");
    fs::write(&bin, "#!/bin/sh\nprintf '%s\\n' \"$@\"\n").unwrap();
    fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
    let jail = jail::create(&f.cfg, "quoting", &bin).unwrap();
    for command in ["verify", "status", "bench"] {
        let output = std::process::Command::new("/bin/sh")
            .arg(jail.join(command))
            .arg("extra'arg")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let mut expected = vec![command.to_owned()];
        if command != "bench" {
            expected.extend(["--jail".into(), jail.display().to_string()]);
        }
        expected.push("--manifest-path".into());
        expected.push(
            if command == "bench" {
                jail.join("Cargo.toml")
            } else {
                f.cfg.crate_dir.join("Cargo.toml")
            }
            .display()
            .to_string(),
        );
        expected.push("extra'arg".into());
        assert_eq!(
            String::from_utf8(output.stdout)
                .unwrap()
                .lines()
                .collect::<Vec<_>>(),
            expected
        );
    }
}
