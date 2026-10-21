use cargo_djinn::smoke::{smoke_run, Bounds, CheckStatus, SmokeReport};

// These tests exercise the public API and real SMT solver. Keep the suite
// usable on Rust-only installations, but make the missing prerequisite clear.
fn report(src: &str, only: Option<&str>) -> Option<SmokeReport> {
    if std::process::Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping real-solver smoke regression: install z3 and add it to PATH");
        return None;
    }
    let bounds = Bounds { max_len: 2, max_examples: 2, timeout_ms: 2_000, only: only.map(str::to_owned), ..Bounds::default() };
    Some(smoke_run(src, &bounds).unwrap_or_else(|e| panic!("smoke failed: {e}")))
}

fn good(src: &str, only: Option<&str>) {
    let Some(r) = report(src, only) else { return };
    assert!(r.all_ok, "{r:#?}");
    assert!(r.decls.iter().flat_map(|d| &d.checks).all(|c| matches!(c.status, CheckStatus::Ok { .. } | CheckStatus::NotApplicable)), "{r:#?}");
}

#[test]
fn sequence_outputs_of_different_lengths_are_ambiguous() {
    let Some(r) = report("djinn! { pub fn variable_len() -> r: Vec<u8> { r.len() <= 1; for x in r { x == 0; } } }", None) else { return };
    assert!(!r.all_ok);
    let check = r.decls[0].checks.iter().find(|c| c.label == "unambiguity").unwrap();
    match &check.status {
        CheckStatus::Problem { what, examples, .. } => {
            assert_eq!(what, "AMBIGUOUS");
            assert!(examples.iter().any(|e| e.contains("[]") && e.contains("[0]")), "{examples:?}");
        }
        other => panic!("expected different-length witnesses, got {other:?}"),
    }
}

#[test]
fn nested_calls_remain_inside_existential_and_output_quantifiers() {
    good("djinn! { pub fn identity(x: i32) -> r: i32 { r == x; } pub fn nested() -> r: i32 { some x: i32 { x == 1; r == identity(x) + 1; } } }", None);
}

#[test]
fn unreachable_calls_do_not_restrict_preconditions_or_live_branches() {
    good("djinn! { pub rel contradiction(x: i32) -> r: i32 { r == x; r != x; } pub fn good() -> r: i32 { r == 2; if false { r == contradiction(1) + 1; } } }", Some("good"));
}

#[test]
fn range_membership_uses_the_input_machine_type() {
    good("djinn! { pub fn byte_id(x: u8) -> r: i32 { r == x; } #[ensures(r >= 0)] pub rel ranged() -> r: i32 { r in range(byte_id); } }", None);
}

#[test]
fn nested_enum_fields_keep_machine_ranges() {
    good("enum Inner { Byte(u8) } enum Outer { Nested(Inner) } djinn! { #[ensures(r >= 0)] pub fn get(o: Outer) -> r: i32 { match o { Outer::Nested(i) => { match i { Inner::Byte(b) => { r == b; } } } } } }", None);
}

#[test]
fn enum_option_fields_declare_the_option_sort_and_bound_payloads() {
    good("enum E { Byte(Option<u8>) } djinn! { pub fn same(e: E) -> r: E { r == e; } }", None);
    good("enum E { Byte(Option<u8>) } djinn! { #[requires(true)] #[ensures(r >= 0)] pub rel get(e: E) -> r: i32 { match e { E::Byte(b) => { if b.is_some() { r == b.unwrap(); } else { r == 0; } } } } }", None);
}

#[test]
fn existential_well_formedness_uses_admissible_witnesses() {
    good("djinn! { #[requires(v.len() > 0)] pub fn safe_some(v: &[i32]) -> r: i32 { r == 0; some i: usize { i < v.len(); v[i] == v[i]; } } }", None);
}

#[test]
fn full_width_machine_integers_do_not_overflow_host_arithmetic() {
    good("djinn! { pub fn unsigned(x: u128) -> r: u128 { r == x; } pub fn signed(x: i128) -> r: i128 { r == x; } }", None);
}

#[test]
fn callee_preconditions_restrict_partial_relations_and_function_existence() {
    // f_spec includes f_pre. A partial relation may deliberately have no
    // output outside that domain; a function must instead satisfy existence.
    good("djinn! { #[requires(x > 0)] pub fn positive(x: i32) -> r: i32 { r == x; } pub rel partial(x: i32) -> r: i32 { positive(x) == r; } }", Some("partial"));
    let Some(r) = report("djinn! { #[requires(x > 0)] pub fn positive(x: i32) -> r: i32 { r == x; } pub fn bad(x: i32) -> r: i32 { positive(x) == r; } }", Some("bad")) else { return };
    assert!(!r.all_ok);
    assert!(r.decls[0].checks.iter().any(|c| matches!(&c.status, CheckStatus::Problem { what, .. } if what == "NO OUTPUT FOR SOME INPUT")), "{r:#?}");
}

#[test]
fn mathematical_division_remainder_and_abs_do_not_overflow_i64() {
    good("djinn! { pub fn max() -> r: i64 { r == ((-9223372036854775807 - 1) / -1) - 1; } pub fn rem() -> r: i64 { r == (-9223372036854775807 - 1) % -1; } pub fn abs() -> r: i64 { r == (-9223372036854775807 - 1).abs() - 1; } }", None);
}

#[test]
fn large_ranges_are_symbolic_and_large_powers_are_explicitly_unsupported() {
    good("djinn! { pub fn constant() -> r: i32 { r == 0; for i in 0..1000000000 { true; } } }", None);
    let Some(r) = report("djinn! { pub fn large_power(x: i32) -> r: i32 { r == x.pow(1000000000); } }", None) else { return };
    assert!(!r.all_ok);
    assert!(r.decls[0].checks.iter().any(|c| matches!(&c.status, CheckStatus::Unsupported(e) if e.contains("exponent"))), "{r:#?}");
}

#[test]
fn if_value_guards_only_apply_to_the_selected_branch() {
    good("djinn! { pub fn head(xs: &[i32], fallback: i32) -> r: i32 { r == if xs.is_empty() { fallback } else { xs[0] }; } }", None);
}

#[test]
fn internal_names_do_not_capture_source_identifiers() {
    good("djinn! { pub fn identity(x: i32) -> r: i32 { r == x; } pub fn nested(x_e0: i32, djinn_call_0: i32, o1_r: i32) -> r: i32 { some x: i32 { x == x_e0; r == identity(x) + 0; } } }", None);
}

#[test]
fn full_width_literal_endpoints_remain_representable() {
    good("djinn! { pub fn maximum() -> r: u128 { r == 340282366920938463463374607431768211455; } pub fn minimum() -> r: i128 { r == -170141183460469231731687303715884105728; } }", None);
}

#[test]
fn mutable_input_old_aliases_remain_hygienic() {
    good("djinn! { pub fn preserve(x: &mut i32, x_old: i32) { x == old(x); } }", None);
}

#[test]
fn bounded_choices_still_share_across_unambiguity_copies() {
    good("djinn! { #[weakly_specified] #[requires(lo <= hi)] pub fn pick(lo: i32, hi: i32) -> out: i32 { any k: i32 where lo <= k && k <= hi; out == k; } #[weakly_specified] pub fn shrink(v: &[u8]) -> out: Vec<u8> { out.len() == v.len(); for i in 0..v.len() { any w: u8 where w <= v[i]; out[i] == w; } } }", None);
}

#[test]
fn range_membership_retains_the_callee_precondition() {
    good("djinn! { #[requires(x > 0)] pub fn positive(x: i32) -> r: i32 { r == x; } #[ensures(r > 0)] pub rel ranged() -> r: i32 { r in range(positive); } #[ensures(r == false)] pub fn outside_range() -> r: bool { r == (0 in range(positive)); } }", None);
}

#[test]
fn unsupported_checks_fail_but_explicit_override_remains_an_opt_out() {
    let Some(r) = report("djinn! { pub rel unsupported(x: std::collections::HashMap<u8,u8>) -> r: bool { r == true; } }", None) else { return };
    assert!(!r.all_ok);
    assert!(r.decls[0].checks.iter().any(|c| matches!(c.status, CheckStatus::Unsupported(_))));
    let Some(r) = report("djinn! { #[override_smoke_test] pub fn skipped() -> r: i32 { r == 0; } }", None) else { return };
    assert!(r.all_ok);
    assert!(r.decls[0].checks.iter().all(|c| matches!(c.status, CheckStatus::Skipped)));
}
