use super::*;

fn fake_solver(script: &str, timeout_ms: u64) -> Z3 {
    let mut command = Command::new("sh");
    command.args(["-c", script]);
    Z3::start_command(command, timeout_ms).expect("start fake solver")
}

#[test]
fn response_parser_respects_smt_quoting_and_comments() {
    for response in [
        "(error \"unknown symbol (\")",
        "(error \"unexpected \"\"(\"\" symbol\")",
        "((|name(with)parentheses| 1))",
        "((x ; ignored unmatched (\n 1))",
    ] {
        let input = format!(" ; leading comment (\n{response}\nsat\n");
        let (start, end) = solver_response_end(input.as_bytes()).unwrap().unwrap();
        assert_eq!(&input[start..end], response);
    }
    assert_eq!(solver_response_end(b"(error \"open"), Ok(None));
    assert!(solver_response_end(b")").is_err());
    assert!(solver_response_end(b"sat)").is_err());
}

#[test]
fn rejected_assertion_cannot_be_followed_by_a_successful_verdict() {
    let mut solver = fake_solver(
        "printf '(error \"unknown constant OptInt (\")\nsat\n'; while IFS= read -r line; do :; done",
        2_000,
    );
    assert_eq!(solver.check_sat(), "unknown");
    let error = solver.failure().unwrap_err();
    assert!(error.contains("unknown constant OptInt"), "{error}");
    // Poisoning persists after reset or a subsequent check.
    solver.send("(reset)");
    assert_eq!(solver.check_sat(), "unknown");
    assert_eq!(solver.failure().unwrap_err(), error);
}

#[test]
fn incomplete_response_has_a_wall_clock_deadline() {
    let mut solver = fake_solver(
        "printf '(error \"unfinished'; while IFS= read -r line; do :; done",
        50,
    );
    let started = Instant::now();
    assert_eq!(solver.check_sat(), "unknown");
    assert!(solver.failure().unwrap_err().contains("timed out reading"));
    assert!(started.elapsed() < Duration::from_secs(5));
}

#[test]
fn blocked_write_has_a_wall_clock_deadline() {
    let mut solver = fake_solver("while :; do :; done", 50);
    let started = Instant::now();
    solver.send(&"x".repeat(1024 * 1024));
    assert!(solver.failure().unwrap_err().contains("timed out writing"));
    assert!(started.elapsed() < Duration::from_secs(5));
}

#[test]
fn incomplete_model_is_not_used_as_a_counterexample() {
    let mut solver = fake_solver(
        "printf '((x 1))\n'; while IFS= read -r line; do :; done",
        2_000,
    );
    assert!(solver.get_value(&["x".into(), "y".into()]).is_empty());
    assert!(solver.failure().unwrap_err().contains("omitted a requested value"));
}

#[test]
fn expected_model_values_still_parse() {
    let mut solver = fake_solver(
        "printf '((x 1) (y (- 2)) (z (some 3)))\n'; while IFS= read -r line; do :; done",
        2_000,
    );
    let values = solver.get_value(&["x".into(), "y".into(), "z".into()]);
    assert_eq!(values.get("x").unwrap(), "1");
    assert_eq!(values.get("y").unwrap(), "-2");
    assert_eq!(values.get("z").unwrap(), "Some(3)");
    solver.failure().unwrap();
}

#[test]
fn drop_reaps_a_solver_that_ignores_exit_commands() {
    let solver = fake_solver("while IFS= read -r line; do :; done", 50);
    let pid = solver.child.id();
    drop(solver);
    #[cfg(unix)]
    unsafe {
        assert_eq!(libc::kill(pid as i32, 0), -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    }
}
