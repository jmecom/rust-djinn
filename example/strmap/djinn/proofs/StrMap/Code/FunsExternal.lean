-- Written by `cargo djinn` from its model library (DESIGN.md §6): trusted Lean models
-- of standard-library items Aeneas has no model for. Regenerated on every verify.
module
public import Aeneas
public import StrMap.Code.Types
public import StrMap.Vocab
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open StrMap

def core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T := fun x => ok x

def U32.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U32 → H → Result H := fun _ h => ok h

def core.option.OptionShared0T.copied
  {T : Type} (markerCopyInst : core.marker.Copy T) : Option T → Result (Option T) := fun o => ok o

def std.collections.hash.map.HashMap.get
  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)
  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result (Option V) := do
  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q
  ok (r.map (·.2))

def std.collections.hash.map.HashMap.contains_key
  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)
  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result Bool := do
  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q
  ok r.isSome

def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
  : std.hash.random.DefaultHasher → Result Std.U64 := fun _ => ok 0#u64

def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
  : std.hash.random.DefaultHasher → Slice Std.U8 → Result std.hash.random.DefaultHasher := fun h _ => ok h

def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
  : std.hash.random.RandomState → Result std.hash.random.DefaultHasher := fun _ => ok .mk

def alloc.string.String.len (s : String) : Result Std.Usize :=
  if h : s.utf8ByteSize ≤ Usize.max then ok (Usize.ofNatCore s.utf8ByteSize (by scalar_tac)) else fail .panic

