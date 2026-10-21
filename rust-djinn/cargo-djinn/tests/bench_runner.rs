//! Cargo builds and executes the small generated runner. No Lean or agent is used.
use std::fs;
use std::path::Path;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

fn fixture() -> std::path::PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!("djinn-bench-test-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    fs::create_dir(&root).unwrap();
    root
}
fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
fn measure(root: &Path, target: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cargo-djinn"))
        .args(["bench", "--manifest-path"])
        .arg(root.join("Cargo.toml"))
        .args(["--min-time", "0.001", "--batches", "1", "--jobs", "1"])
        .env("CARGO_TARGET_DIR", target)
        .env_remove("CARGO_BUILD_TARGET")
        .output()
        .unwrap()
}

#[test]
fn custom_target_directory_cannot_select_stale_runner() {
    let root = fixture();
    fs::create_dir(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname=\"bench-regression\"\nversion=\"0.0.0\"\nedition=\"2021\"\n[package.metadata.djinn]\nbench=\"workload\"\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn workload() { std::hint::black_box(1u64); }\n").unwrap();
    let first = measure(&root, &root.join(".djinnscratch/bench/target"));
    assert_success(&first);
    fs::write(root.join("src/lib.rs"), "pub fn workload() { std::thread::sleep(std::time::Duration::from_millis(20)); }\n").unwrap();
    let second = measure(&root, &root.join("custom-target"));
    assert_success(&second);
    let timing = String::from_utf8(second.stdout).unwrap();
    assert!(timing.contains(" ms per iteration"), "must measure the new sleeping workload: {timing}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn invalid_options_fail_before_loading_crate_or_starting_workload() {
    let root = fixture();
    for command in ["bench", "optimize"] {
        for (flag, value) in [
            ("--batches", "0"),
            ("--batches", "invalid"),
            ("--min-time", "inf"),
            ("--min-time", "NaN"),
            ("--min-time", "0"),
            ("--min-time", "-1"),
            ("--min-time", "invalid"),
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_cargo-djinn"))
                .arg(command)
                .arg("--manifest-path")
                .arg(root.join("missing.toml"))
                .args([flag, value])
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(2));
            let message = String::from_utf8(output.stderr).unwrap();
            assert!(message.contains(flag), "{command} {flag} {value}: {message}");
            assert!(!root.join(".djinnscratch").exists());
        }
    }
    fs::remove_dir_all(root).unwrap();
}
