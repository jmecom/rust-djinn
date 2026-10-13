//! Trusted Lean models for the standard-library items Aeneas has no model
//! of but Djinn supports: `String` (as its UTF-8 bytes) and `HashMap` (as an
//! association list), plus the hashing and conversion items their use drags
//! in. Aeneas lists what it could not model in `*External_Template.lean`
//! (one `Name pattern` per item, with the exact Lean signature it expects);
//! when every listed item is covered here, `verify` writes
//! `FunsExternal.lean` / `TypesExternal.lean` from this library and goes on;
//! anything uncovered is a failure with an explanation (DESIGN.md §6, §7).
//!
//! These definitions are part of the trusted computing base: they assert
//! that the Rust functions behave like the Lean bodies below.

/// A modeled item: Aeneas's name pattern and its Lean definition.
pub struct Model {
    pub pattern: &'static str,
    pub lean: &'static str,
}

/// The scalar types `HashMap` keys may have; their `Hash` instances are trivial models.
const HASH_SCALARS: &[(&str, &str)] = &[
    ("u8", "U8"), ("u16", "U16"), ("u32", "U32"), ("u64", "U64"), ("u128", "U128"), ("usize", "Usize"),
    ("i8", "I8"), ("i16", "I16"), ("i32", "I32"), ("i64", "I64"), ("i128", "I128"), ("isize", "Isize"),
];

/// Definitions shared by the models live in `Vocab.lean` (`Djinn.Vocab`),
/// which the specification's views use as well. Kept here only for reference.
#[allow(dead_code)]
const PRELUDE: &str = r#"
namespace Djinn.Models

/-- The bytes of a Rust string: its UTF-8 encoding. This is the view the
    specification language gives a `String`, the same as a `&str`'s. -/
def bytes (s : String) : List U8 :=
  s.toUTF8.toList.map (fun b => U8.ofNatCore b.toNat (by have := b.toNat_lt; simp [UScalarTy.numBits]; omega))

/-- A string from bytes, when they are valid UTF-8. -/
def ofBytes (l : List U8) : Option String :=
  String.fromUTF8? ⟨(l.map (fun b => UInt8.ofNat b.val)).toArray⟩

/-- Lookup through Rust's `Borrow` and `Eq` instances: the first entry whose
    borrowed key equals the query. -/
def find {K V Q : Type} (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (Option (K × V))
  | [], _ => ok none
  | (k, v) :: rest, q => do
    let kq ← borrow k
    let b ← eq kq q
    if b then ok (some (k, v)) else find borrow eq rest q

/-- Replace the value of the first entry whose key equals `k`. -/
def replace {K V : Type} (eq : K → K → Result Bool) : List (K × V) → K → V → Result (List (K × V))
  | [], _, _ => ok []
  | (k', v') :: rest, k, v => do
    let b ← eq k' k
    if b then ok ((k', v) :: rest) else do
      let r ← replace eq rest k v
      ok ((k', v') :: r)

/-- Drop the first entry whose borrowed key equals the query. -/
def erase {K V Q : Type} (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (List (K × V))
  | [], _ => ok []
  | (k', v') :: rest, q => do
    let kq ← borrow k'
    let b ← eq kq q
    if b then ok rest else do
      let r ← erase borrow eq rest q
      ok ((k', v') :: r)

end Djinn.Models
"#;

/// Type models (`TypesExternal.lean`).
pub const TYPES: &[Model] = &[
    Model {
        pattern: "std::collections::hash::map::HashMap",
        lean: r#"/-- `std::collections::HashMap<K, V>`, modeled as an association list: the
    entries in insertion order, no key twice. Hashing is irrelevant to the
    model; equality of keys is Rust's `Eq` instance, passed to every operation. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) where
  entries : List (K × V)
"#,
    },
    Model {
        pattern: "memchr::memchr::Memchr",
        lean: r#"/-- `memchr::Memchr<'h>`, the iterator over the positions of a byte in a
    haystack, modeled as the pair; its `count` is `List.count`. -/
@[rust_type "memchr::memchr::Memchr"]
structure memchr.memchr.Memchr where
  needle : Std.U8
  haystack : Aeneas.Std.Slice Std.U8
"#,
    },
    Model { pattern: "std::hash::random::RandomState", lean: "@[rust_type \"std::hash::random::RandomState\"]\ninductive std.hash.random.RandomState where | mk\n" },
    Model { pattern: "std::hash::random::DefaultHasher", lean: "@[rust_type \"std::hash::random::DefaultHasher\"]\ninductive std.hash.random.DefaultHasher where | mk\n" },
    Model { pattern: "alloc::string::FromUtf8Error", lean: "@[rust_type \"alloc::string::FromUtf8Error\"]\ninductive alloc.string.FromUtf8Error where | mk\n" },
];

/// Function models (`FunsExternal.lean`); the hashing models for the scalar
/// key types are generated (`hash_models`).
pub const FUNS: &[Model] = &[
    // ---- hashing: irrelevant to the association-list model
    Model {
        pattern: "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish",
        lean: "def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish\n  : std.hash.random.DefaultHasher → Result Std.U64 := fun _ => ok 0#u64\n",
    },
    Model {
        pattern: "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write",
        lean: "def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write\n  : std.hash.random.DefaultHasher → Slice Std.U8 → Result std.hash.random.DefaultHasher := fun h _ => ok h\n",
    },
    Model {
        pattern: "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher",
        lean: "def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher\n  : std.hash.random.RandomState → Result std.hash.random.DefaultHasher := fun _ => ok .mk\n",
    },
    // ---- small conversions the map API drags in
    Model {
        pattern: "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow",
        lean: "def core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T := fun x => ok x\n",
    },
    Model {
        pattern: "core::option::{core::option::Option<&'0 @T>}::copied",
        lean: "def core.option.OptionShared0T.copied\n  {T : Type} (markerCopyInst : core.marker.Copy T) : Option T → Result (Option T) := fun o => ok o\n",
    },
    Model {
        pattern: "core::result::{core::result::Result<@T, @E>}::ok",
        lean: "def core.result.Result.ok\n  {T : Type} {E : Type} : core.result.Result T E → Result (Option T) :=\n  fun r => Std.Result.ok (match r with | .Ok x => some x | .Err _ => none)\n",
    },
    // ---- HashMap
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new",
        lean: "def std.collections.hash.map.HashMapKVRandomStateGlobal.new\n  (K : Type) (V : Type) :\n  Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState Global) := ok ⟨[]⟩\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::len",
        lean: "def std.collections.hash.map.HashMap.len\n  {K : Type} {V : Type} {S : Type} {A : Type} (m : std.collections.hash.map.HashMap K V S A) : Result Std.Usize :=\n  if h : m.entries.length ≤ Usize.max then ok (Usize.ofNatCore m.entries.length (by scalar_tac)) else fail .panic\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::is_empty",
        lean: "def std.collections.hash.map.HashMap.is_empty\n  {K : Type} {V : Type} {S : Type} {A : Type} (m : std.collections.hash.map.HashMap K V S A) : Result Bool :=\n  ok m.entries.isEmpty\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get",
        lean: "def std.collections.hash.map.HashMap.get\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result (Option V) := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok (r.map (·.2))\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key",
        lean: "def std.collections.hash.map.HashMap.contains_key\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result Bool := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok r.isSome\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert",
        lean: "def std.collections.hash.map.HashMap.insert\n  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :\n  Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do\n  let r ← Djinn.Vocab.find (fun k' => ok k') corecmpEqInst.partialEqInst.eq m.entries k\n  match r with\n  | some (_, old) => do\n    let es ← Djinn.Vocab.replace corecmpEqInst.partialEqInst.eq m.entries k v\n    ok (some old, ⟨es⟩)\n  | none => if m.entries.length + 1 ≤ Usize.max then ok (none, ⟨m.entries ++ [(k, v)]⟩) else fail .panic\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::remove",
        lean: "def std.collections.hash.map.HashMap.remove\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) :\n  Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  let es ← Djinn.Vocab.erase coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok (r.map (·.2), ⟨es⟩)\n",
    },
    // ---- String, as its UTF-8 bytes
    // the `memchr` crate: SIMD byte search, modeled as the first / last index
    // (`Djinn.Vocab.memchr_eq_some`, `memchr_eq_none` and the `memrchr`
    // twins characterize them)
    Model {
        pattern: "memchr::memchr::memchr",
        lean: "def memchr.memchr.memchr (n : Std.U8) (h : Slice Std.U8) : Result (Option Std.Usize) :=\n  ok (match hm : Djinn.Vocab.memchr n h.val with\n      | none => none\n      | some i => some (Usize.ofNatCore i (by\n          have h1 := (Djinn.Vocab.memchr_eq_some.mp hm).1\n          have h2 := h.property\n          scalar_tac)))\n",
    },
    Model {
        pattern: "memchr::memchr::memrchr",
        lean: "def memchr.memchr.memrchr (n : Std.U8) (h : Slice Std.U8) : Result (Option Std.Usize) :=\n  ok (match hm : Djinn.Vocab.memrchr n h.val with\n      | none => none\n      | some i => some (Usize.ofNatCore i (by\n          have h1 := (Djinn.Vocab.memrchr_eq_some.mp hm).1\n          have h2 := h.property\n          scalar_tac)))\n",
    },
    Model {
        pattern: "memchr::memchr::memchr_iter",
        lean: "def memchr.memchr.memchr_iter (n : Std.U8) (h : Slice Std.U8) : Result memchr.memchr.Memchr := ok ⟨n, h⟩\n",
    },
    Model {
        pattern: "memchr::memchr::{core::iter::traits::iterator::Iterator<memchr::memchr::Memchr<'h>, usize>}::count",
        lean: "def memchr.memchr.Memchr.Insts.CoreIterTraitsIteratorIteratorUsize.count (it : memchr.memchr.Memchr) : Result Std.Usize :=\n  ok (Usize.ofNatCore (it.haystack.val.count it.needle) (by\n      have h1 := Djinn.Vocab.count_le_length' it.needle it.haystack.val\n      have h2 := it.haystack.property\n      scalar_tac))\n",
    },
    // `str` is `Slice U8` in Aeneas: its bytes are itself
    Model { pattern: "core::str::{str}::as_bytes", lean: "def core.str.Str.as_bytes (s : Str) : Result (Slice Std.U8) := ok s\n" },
    Model { pattern: "alloc::string::{alloc::string::String}::new", lean: "def alloc.string.String.new : Result String := ok \"\"\n" },
    Model {
        pattern: "alloc::string::{alloc::string::String}::len",
        lean: "def alloc.string.String.len (s : String) : Result Std.Usize :=\n  if h : s.utf8ByteSize ≤ Usize.max then ok (Usize.ofNatCore s.utf8ByteSize (by scalar_tac)) else fail .panic\n",
    },
    Model { pattern: "alloc::string::{alloc::string::String}::is_empty", lean: "def alloc.string.String.is_empty (s : String) : Result Bool := ok s.isEmpty\n" },
    Model { pattern: "alloc::string::{alloc::string::String}::push", lean: "def alloc.string.String.push (s : String) (c : Char) : Result String := ok (s.push c)\n" },
    Model {
        pattern: "alloc::string::{alloc::string::String}::push_str",
        lean: "def alloc.string.String.push_str (s : String) (t : Str) : Result String :=\n  match Djinn.Vocab.ofBytes t.val with\n  | some u => ok (s ++ u)\n  | none => fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::as_bytes",
        lean: "def alloc.string.String.as_bytes (s : String) : Result (Slice Std.U8) :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (Slice.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::as_str",
        lean: "def alloc.string.String.as_str (s : String) : Result Str :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (Slice.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::into_bytes",
        lean: "def alloc.string.String.into_bytes (s : String) : Result (alloc.vec.Vec Std.U8) :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (alloc.vec.Vec.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::from_utf8",
        lean: "def alloc.string.String.from_utf8\n  (v : alloc.vec.Vec Std.U8) : Result (core.result.Result String alloc.string.FromUtf8Error) :=\n  ok (match Djinn.Vocab.ofBytes v.val with | some s => .Ok s | none => .Err .mk)\n",
    },
    Model { pattern: "alloc::string::{core::clone::Clone<alloc::string::String>}::clone", lean: "def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String := ok s\n" },
    Model {
        pattern: "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq",
        lean: "def alloc.string.String.Insts.CoreCmpPartialEqString.eq (s t : String) : Result Bool := ok (s == t)\n",
    },
    Model {
        pattern: "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from",
        lean: "def alloc.string.String.Insts.CoreConvertFromShared0Str.from (t : Str) : Result String :=\n  match Djinn.Vocab.ofBytes t.val with\n  | some u => ok u\n  | none => fail .panic\n",
    },
];

/// The hashing models for the scalar key types.
fn hash_models() -> Vec<(String, String)> {
    HASH_SCALARS
        .iter()
        .map(|(rust, lean)| {
            (
                format!("core::hash::impls::{{core::hash::Hash<{rust}>}}::hash"),
                format!("def {lean}.Insts.CoreHashHash.hash\n  {{H : Type}} (HasherInst : core.hash.Hasher H) : Std.{lean} → H → Result H := fun _ h => ok h\n"),
            )
        })
        .collect()
}

/// The Lean definition for a pattern, if the library has one.
pub fn lookup(pattern: &str) -> Option<String> {
    if let Some(m) = TYPES.iter().chain(FUNS.iter()).find(|m| m.pattern == pattern) {
        return Some(m.lean.to_string());
    }
    hash_models().into_iter().find(|(p, _)| p == pattern).map(|(_, l)| l)
}

fn is_type(pattern: &str) -> bool {
    TYPES.iter().any(|m| m.pattern == pattern)
}

/// Cover the externals Aeneas listed: `Ok((FunsExternal.lean, TypesExternal.lean))`
/// when every pattern has a model, else the uncovered patterns.
pub fn cover(ns: &str, patterns: &[String]) -> Result<(String, String), Vec<String>> {
    let uncovered: Vec<String> = patterns.iter().filter(|p| lookup(p).is_none()).cloned().collect();
    if !uncovered.is_empty() {
        return Err(uncovered);
    }
    let header = |imports: &str| {
        format!(
            "-- Written by `cargo djinn` from its model library (DESIGN.md §6): trusted Lean models\n-- of standard-library items Aeneas has no model for. Regenerated on every verify.\nmodule\npublic import Aeneas\n{imports}@[expose] public section\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\nset_option linter.unusedVariables false\nset_option linter.style.whitespace false\nset_option linter.style.setOption false\nset_option linter.style.longLine false\nset_option maxHeartbeats 1000000\n\n"
        )
    };
    let mut types = header("");
    for p in patterns.iter().filter(|p| is_type(p)) {
        types.push_str(&lookup(p).unwrap());
        types.push('\n');
    }
    let mut funs = header(&format!("public import {ns}.Code.Types\npublic import {ns}.Vocab\n"));
    funs.push_str(&format!("open {ns}\n\n"));
    for p in patterns.iter().filter(|p| !is_type(p)) {
        funs.push_str(&lookup(p).unwrap());
        funs.push('\n');
    }
    Ok((funs, types))
}
