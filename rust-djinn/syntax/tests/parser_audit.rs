use djinn_syntax::{lower_program, parse_program, StmtKind};

fn contract(body: &str) -> String {
    let source = format!("djinn! {{ fn f(s: &[u8], t: &[u8]) -> r: bool {{ r == ({body}); }} }}");
    let program = parse_program(&source).unwrap_or_else(|e| panic!("{source}: {}", e.msg));
    lower_program(&program).unwrap_or_else(|e| panic!("{source}: {}", e.msg))[0].spec.join(" ∧ ")
}

#[test]
fn closure_membership_and_chains_preserve_the_parameter_list() {
    for (natural, parenthesized) in [
        ("s.iter().all(|x| x in t)", "s.iter().all(|x| (x in t))"),
        ("s.iter().any(|x| x not in t)", "s.iter().any(|x| (x not in t))"),
        ("s.iter().all(|x| 0 <= x <= 255)", "s.iter().all(|x| (0 <= x <= 255))"),
        ("s.iter().any(|x| x in t && 0 <= x <= 255)", "s.iter().any(|x| (x in t) && (0 <= x) && (x <= 255))"),
        ("s.iter().filter(|x| x in t).count() == 0", "s.iter().filter(|x| (x in t)).count() == 0"),
        ("s.windows(2).all(|w| w[0] in t)", "s.windows(2).all(|w| (w[0] in t))"),
        ("s.iter().all(move |x| x in t)", "s.iter().all(move |x| (x in t))"),
        ("s.iter().all(|x: &u8| 0 <= x <= 255)", "s.iter().all(|x: &u8| (0 <= x <= 255))"),
    ] {
        assert_eq!(contract(natural), contract(parenthesized), "{natural}");
    }
}

#[test]
fn every_supported_method_enforces_arity() {
    for expression in [
        "s.len(bad())", "s.is_empty(bad())", "s.contains(&x, bad())",
        "s.first(bad())", "s.last(bad())", "x.abs(bad())", "x.min(x, bad())",
        "x.max(x, bad())", "x.pow(x, bad())", "o.is_some(bad())",
        "o.is_none(bad())", "o.unwrap(bad())", "s.as_bytes(bad())",
        "m.get(&x, bad())", "m.contains_key(&x, bad())",
        "s.iter(bad()).sum()", "s.iter().sum(bad())",
        "s.iter().all(|x| true, bad())", "s.iter().all(|x| x in s, bad())", "s.iter().any(|x| true, bad())",
        "s.iter().filter(|x| true, bad()).count()",
        "s.iter(bad()).filter(|x| true).count()",
        "s.iter().filter(|x| true).count(bad())",
        "s.windows(2, bad()).all(|x| true)",
        "s.windows(2).all(|x| true, bad())",
        "s.contains()", "x.min()", "x.max()", "x.pow()", "m.get()",
        "m.contains_key()", "s.iter().all()", "s.iter().any()",
        "s.iter().filter().count()", "s.windows().all(|x| true)",
    ] {
        let source = format!("djinn! {{ rel p(s: &[u8], x: u8, o: Option<u8>, m: HashMap<u8, u8>) {{ {expression}; }} }}");
        let error = parse_program(&source).unwrap_err();
        assert!(error.msg.contains("argument(s)"), "{expression}: {}", error.msg);
    }
}

#[test]
fn existential_binders_parse_nested_generic_commas() {
    let program = parse_program("djinn! { rel p() { some x: Result<Option<u8>, Result<u8, u8>>, y: HashMap<u8, bool>, z: u8 { x == x; y == y; z == z; } } }").unwrap();
    let StmtKind::Some { binders, .. } = &program.decls[0].body[0].kind else { panic!("expected existential") };
    assert_eq!(binders.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(), ["x", "y", "z"]);
    lower_program(&program).unwrap();
}

#[test]
fn conditional_definitions_fail_closed_before_constant_selection() {
    for source in [
        "#[cfg(not(any()))] const LIMIT: u8 = 2; #[cfg(any())] const LIMIT: u8 = 1; djinn! { fn f() -> r: u8 { r == LIMIT; } }",
        "#[cfg(any())] const LIMIT: u8 = 1; #[cfg(not(any()))] const LIMIT: u8 = 2; djinn! { fn f() -> r: u8 { r == LIMIT; } }",
        "#[cfg_attr(any(), cfg(any()))] const LIMIT: u8 = 1;",
        "#[r#cfg(any())] const LIMIT: u8 = 1;",
        "#[r#cfg_attr(any(), cfg(any()))] const LIMIT: u8 = 1;",
        "#[cfg(any())] struct S { x: u8 }",
        "struct S { #[cfg(any())] x: u8 }",
        "#[cfg(any())] enum E { A }",
        "enum E { #[cfg(any())] A }",
        "enum E { A(#[cfg(any())] u8) }",
        "enum E { A { #[cfg(any())] x: u8 } }",
        "#[cfg(any())] fn f(x: u8) -> u8 { x }",
        "fn f(#[cfg(any())] x: u8) -> u8 { x }",
        "#[cfg(any())] djinn! { fn f() -> r: u8 { r == 1; } }",
        "#![cfg(any())] djinn! { fn f() -> r: u8 { r == 1; } }",
    ] {
        let error = parse_program(source).unwrap_err();
        assert!(error.msg.contains("conditional definitions"), "{source}: {}", error.msg);
    }
}

#[test]
fn specification_maps_do_not_silently_discard_a_custom_hasher() {
    let error = parse_program("djinn! { rel p(m: HashMap<u8, u8, CustomHasher>) { m.len() == 0; } }").unwrap_err();
    assert!(error.msg.contains("standard default hasher"), "{}", error.msg);
    parse_program("djinn! { rel p(m: HashMap<u8, u8>) { m.len() == 0; } }").unwrap();
}

#[test]
fn attribute_macros_cannot_rewrite_source_constants_or_types() {
    for source in [
        "#[transform::replace] const LIMIT: u8 = 1; djinn! { fn f() -> r: u8 { r == LIMIT; } }",
        "#[replace] struct S { x: u8 }",
        "#[replace] enum E { A(u8) }",
        "extern crate transform as rustfmt; #[rustfmt::skip] const LIMIT: u8 = 1;",
        "use transform::replace as derive; #[derive(Clone)] const LIMIT: u8 = 1;",
    ] {
        let error = parse_program(source).unwrap_err();
        assert!(error.msg.contains("may transform this definition"), "{source}: {}", error.msg);
    }
    parse_program(r#"
        #[doc = "a constant"] #[allow(dead_code)] const LIMIT: u8 = 1;
        #[derive(Clone, Copy)] #[repr(C)] struct S { x: u8 }
        #[deprecated] #[non_exhaustive] enum E { A(u8) }
    "#).unwrap();
}

#[test]
fn derive_must_not_resolve_to_an_imported_attribute_macro() {
    for import in [
        "use transform::replace as derive;", "use transform::r#derive;",
        "use transform::*;", "use transform::{safe, replace as r#derive};",
        "#[macro_use] extern crate transform;", "#[r#macro_use] mod transform;",
    ] {
        let source = format!("{import} #[derive(Clone)] struct S {{ x: u8 }}");
        let error = parse_program(&source).unwrap_err();
        assert!(error.msg.contains("may shadow that attribute"), "{source}: {}", error.msg);
    }
    parse_program("use std::collections::HashMap; #[r#derive(Clone)] struct S { x: u8 }").unwrap();
}
