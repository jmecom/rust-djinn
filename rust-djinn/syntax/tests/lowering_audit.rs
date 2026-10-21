use djinn_syntax::{emit::{self, EmitCx}, lower::Lowered, lower_program, parse_program};
use std::collections::HashMap;

const FIXTURES: &str = r#"
djinn! {
    rel zero(x: int) -> z: int { z == 0; }
    fn positive(v_call0: i32) -> r: bool { r == (zero(0) < v_call0); }
    #[requires(x > 0)]
    fn positive_id(x: i32) -> r: i32 { r == x; }
    fn in_positive(a0: i32) -> r: bool { r == (a0 in range(positive_id)); }
    fn preserve(x: &mut i32, x_old: i32) { x == old(x); }
    fn count(xs: &[i32]) -> r: usize { r == xs.iter().filter(|x| x != 0 && 100 / x > 1).count(); }
    fn all(xs: &[i32]) -> r: bool { r == xs.iter().all(|x| x != 0 && 100 / x > 1); }
    fn any(xs: &[i32]) -> r: bool { r == xs.iter().any(|x| x != 0 && 100 / x > 1); }
    fn windows(xs: &[i32], w0: i32) -> r: bool { r == xs.windows(2).all(|w| w[1] != 0 && 100 / w[1] > 1); }
    #[requires(xs.iter().all(|x| x > 0))]
    fn for_each(xs: &[i32]) -> r: i32 { for x in xs { 0 <= 100 / x; } r == 0; }
    fn empty_or_first(xs: &[i32], fallback: i32) -> r: i32 { r == if xs.is_empty() { fallback } else { xs[0] }; }
    #[requires(x > 0)]
    rel guarded(x: int) -> r: int { r == x; }
    fn branch_calls(x: i32) -> r: i32 { r == if x > 0 { guarded(x) } else { x }; }
    fn bump(x: &mut i32) -> r: i32 { x == old(x); r == old(x); }
    fn both(x: &mut i32, y: &mut i32) { x == old(x); y == old(y); }
}
"#;

fn lower(source: &str) -> Vec<Lowered> {
    lower_program(&parse_program(source).unwrap()).unwrap()
}
fn named<'a>(ds: &'a [Lowered], name: &str) -> &'a Lowered {
    ds.iter().find(|d| d.name == name).unwrap()
}

#[test]
fn range_and_domain_are_ordered_after_their_targets() {
    let p = parse_program("djinn! { rel f(x: bool) { x in range(g); x in domain(g); } fn g(x: bool) -> r: bool { r == x; } }").unwrap();
    assert!(p.decls[0].callees().iter().any(|n| n == "g"));
    assert_eq!(djinn_syntax::dependency_order(&p.decls).iter().map(|d| d.name.as_str()).collect::<Vec<_>>(), ["g", "f"]);
}

#[test]
fn large_slice_lengths_are_not_truncated_to_machine_integers() {
    let ds = lower("djinn! { rel slice(s: &[u8]) { s[0..18446744073709551616].len() >= 0; } }");
    assert!(ds[0].spec[0].contains("take (18446744073709551616 - 0)"));
}

/// Run with DJINN_AENEAS_BACKEND pointing to the Aeneas backends/lean directory
/// and `lake` available on PATH. The examples and obligations here are emitted
/// by the current code, rather than copied Lean statements that could drift.
#[test]
#[ignore = "requires the Aeneas Lean toolchain; set DJINN_AENEAS_BACKEND"]
fn lean_checks_capture_counterexamples_and_well_formedness() {
    let backend = std::env::var_os("DJINN_AENEAS_BACKEND").expect("set DJINN_AENEAS_BACKEND");
    let ds = lower(FIXTURES);
    let models = HashMap::from([("bump".into(), "Model.bump".into()), ("both".into(), "Model.both".into())]);
    let types = HashMap::new();
    let cx = EmitCx { ns: "Audit", impl_names: &models, type_names: &types, has_types: false, has_funs: false, unfoldable: vec![] };
    let mut text = emit::spec_lean(&cx, &ds).replace("import Audit.Vocab\n", "");
    text.push_str("\nopen Audit.Spec\n");
    text.push_str(r#"
example : positive_spec 1#i32 true := by simp [positive_spec, positive_pre, zero_spec, zero_pre]
example : ¬ positive_spec 1#i32 false := by simp [positive_spec, positive_pre, zero_spec, zero_pre]
example : in_positive_spec 0#i32 false := by simp [in_positive_spec, in_positive_pre, positive_id_spec, positive_id_pre]
example : preserve_spec 1#i32 2#i32 1#i32 := by simp [preserve_spec, preserve_pre]
example : ¬ preserve_spec 1#i32 2#i32 2#i32 := by simp [preserve_spec, preserve_pre]
example : empty_or_first_spec [] 1#i32 1#i32 := by simp [empty_or_first_spec, empty_or_first_pre]
example : branch_calls_spec 0#i32 0#i32 := by simp [branch_calls_spec, branch_calls_pre]
def Model.bump (x : I32) : Result (I32 × I32) := ok (x, x)
def Model.both (x y : I32) : Result (I32 × I32) := ok (x, y)
"#);
    for name in ["count", "all", "any", "windows", "for_each", "empty_or_first", "branch_calls"] {
        let ob = emit::obligations(&cx, named(&ds, name)).into_iter().find(|o| o.name.ends_with(".wf")).unwrap();
        let proof = match name {
            "for_each" => "by\n  intro xs r h x hx\n  have hp := h.1 x hx\n  omega",
            "empty_or_first" => "by\n  intro xs fallback r h hn\n  omega",
            "branch_calls" => "by\n  intro x r h hx\n  exact hx",
            "windows" => "by\n  intro xs w0 r h\n  clear h w0 r\n  simp only [List.Chain']\n  induction xs with\n  | nil => exact .nil\n  | cons a xs ih =>\n    cases xs with\n    | nil => exact .singleton a\n    | cons b xs => exact .cons_cons (fun h => h) ih",
            _ => "by\n  intro xs r h x hx hn\n  exact hn",
        };
        text.push_str(&format!("\ntheorem {} :\n  {} := {proof}\n", ob.name, ob.statement));
    }
    for name in ["bump", "both"] {
        for ob in emit::obligations(&cx, named(&ds, name)) {
            if ob.name.ends_with(".impl_correct") {
                text.push_str(&format!("\ntheorem {} :\n  {} := by\n  intros\n  simp [Model.{name}, {name}_spec, {name}_pre]\n", ob.name, ob.statement));
            } else if let Some(proof) = ob.generated_proof {
                text.push_str(&format!("\ntheorem {} :\n  {} := {proof}\n", ob.name, ob.statement));
            }
        }
    }
    let file = std::env::temp_dir().join(format!("djinn-lowering-audit-{}.lean", std::process::id()));
    std::fs::write(&file, text).unwrap();
    let result = std::process::Command::new("lake").args(["env", "lean"]).arg(&file).current_dir(backend).output().unwrap();
    assert!(result.status.success(), "Lean failed; fixture {}\n{}\n{}", file.display(), String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    std::fs::remove_file(file).unwrap();
}
