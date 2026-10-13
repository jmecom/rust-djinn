//! Rust types → Aeneas types and their mathematical views (DESIGN.md §4).

use crate::ast::*;
use std::collections::HashMap;

/// Rust name of a user type → its fully qualified Lean name (from Aeneas's
/// `translation.json`, or predicted from the namespace and module).
pub type TypeNames = HashMap<String, String>;

fn paren(s: String) -> String {
    if s.contains(' ') {
        format!("({s})")
    } else {
        s
    }
}

fn named(n: &str, names: &TypeNames) -> String {
    names.get(n).cloned().unwrap_or_else(|| n.to_string())
}

/// The Lean type Aeneas gives a Rust value of this type.
pub fn aeneas_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Int { signed, bits } => {
            let base = if *signed { "I" } else { "U" };
            if *bits == 0 {
                format!("{}size", base)
            } else {
                format!("{base}{bits}")
            }
        }
        RType::Bool => "Bool".into(),
        RType::Char => "Char".into(),
        RType::MathInt => "ℤ".into(),
        RType::Seq(e, k) => match k {
            SeqKind::Slice => format!("Aeneas.Std.Slice {}", paren(aeneas_type(e, names))),
            SeqKind::Str => "Aeneas.Std.Str".into(),
            SeqKind::String => "String".into(),
            SeqKind::Vec => format!("alloc.vec.Vec {}", paren(aeneas_type(e, names))),
            SeqKind::Array(n) => format!("Aeneas.Std.Array {} {}#usize", paren(aeneas_type(e, names)), n),
        },
        RType::Map(k, v) => format!("std.collections.hash.map.HashMap {} {} std.hash.random.RandomState Global", paren(aeneas_type(k, names)), paren(aeneas_type(v, names))),
        RType::Option(e) => format!("Option {}", paren(aeneas_type(e, names))),
        RType::Result(a, b) => format!("core.result.Result {} {}", paren(aeneas_type(a, names)), paren(aeneas_type(b, names))),
        RType::Unit => "Unit".into(),
        RType::Named(n) => named(n, names),
    }
}

/// The type used in specification predicates: sequences become lists.
pub fn view_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Seq(e, _) => format!("List {}", paren(view_type(e, names))),
        RType::Map(k, v) => format!("List ({} × {})", view_type(k, names), view_type(v, names)),
        RType::Option(e) => format!("Option {}", paren(view_type(e, names))),
        RType::Result(a, b) => format!("core.result.Result {} {}", paren(view_type(a, names)), paren(view_type(b, names))),
        _ => aeneas_type(t, names),
    }
}

/// The view of a variable of Aeneas type `t`, as the `impl_correct`
/// statements have always written it: `.val` on sequences, identity
/// elsewhere (Aeneas's coercions bridge `Option (Vec α)` to `Option (List α)`).
pub fn view_of(var: &str, t: &RType) -> String {
    match t {
        RType::Seq(_, SeqKind::String) => format!("(Djinn.Vocab.bytes {var})"),
        RType::Seq(e, _) if needs_view(e) => format!("({var}.val.map (fun y => {}))", view_term("y", e)),
        RType::Seq(..) => format!("{var}.val"),
        RType::Map(..) => format!("{var}.entries"),
        RType::Result(..) if needs_view(t) => view_term(var, t),
        _ => var.to_string(),
    }
}

/// The view of an Aeneas-typed term, written out in full (no coercions):
/// used for pattern-bound fields.
pub fn view_term(term: &str, t: &RType) -> String {
    match t {
        RType::Seq(_, SeqKind::String) => format!("(Djinn.Vocab.bytes {term})"),
        RType::Seq(e, _) if needs_view(e) => format!("({term}.val.map (fun y => {}))", view_term("y", e)),
        RType::Seq(..) => format!("{term}.val"),
        RType::Map(..) => format!("{term}.entries"),
        RType::Option(e) if needs_view(e) => format!("({term}.map (fun y => {}))", view_term("y", e)),
        RType::Result(a, b) if needs_view(a) || needs_view(b) => format!(
            "(match {term} with | .Ok y => .Ok {} | .Err y => .Err {})",
            paren(view_term("y", a)),
            paren(view_term("y", b))
        ),
        _ => term.to_string(),
    }
}

/// Does the view of a value of this type differ from the value?
pub fn needs_view(t: &RType) -> bool {
    match t {
        RType::Seq(..) | RType::Map(..) => true,
        RType::Option(e) => needs_view(e),
        RType::Result(a, b) => needs_view(a) || needs_view(b),
        _ => false,
    }
}

/// A Rust type's tokens, for messages.
pub fn rust_type(t: &RType) -> String {
    match t {
        RType::Int { signed, bits } => format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }),
        RType::Bool => "bool".into(),
        RType::Char => "char".into(),
        RType::MathInt => "int".into(),
        RType::Seq(e, SeqKind::Vec) => format!("Vec<{}>", rust_type(e)),
        RType::Seq(e, SeqKind::Slice) => format!("&[{}]", rust_type(e)),
        RType::Seq(e, SeqKind::Array(n)) => format!("[{}; {n}]", rust_type(e)),
        RType::Seq(_, SeqKind::Str) => "&str".into(),
        RType::Seq(_, SeqKind::String) => "String".into(),
        RType::Map(k, v) => format!("HashMap<{}, {}>", rust_type(k), rust_type(v)),
        RType::Option(e) => format!("Option<{}>", rust_type(e)),
        RType::Result(a, b) => format!("Result<{}, {}>", rust_type(a), rust_type(b)),
        RType::Unit => "()".into(),
        RType::Named(n) => n.clone(),
    }
}
