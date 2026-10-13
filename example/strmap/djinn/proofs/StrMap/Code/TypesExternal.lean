-- Written by `cargo djinn` from its model library (DESIGN.md §6): trusted Lean models
-- of standard-library items Aeneas has no model for. Regenerated on every verify.
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

/-- `std::collections::HashMap<K, V>`, modeled as an association list: the
    entries in insertion order, no key twice. Hashing is irrelevant to the
    model; equality of keys is Rust's `Eq` instance, passed to every operation. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) where
  entries : List (K × V)

@[rust_type "std::hash::random::RandomState"]
inductive std.hash.random.RandomState where | mk

@[rust_type "std::hash::random::DefaultHasher"]
inductive std.hash.random.DefaultHasher where | mk

