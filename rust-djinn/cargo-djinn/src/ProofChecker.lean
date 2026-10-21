/- This program is driver-owned. It is elaborated using only Lean's installed
   libraries, before the search path is changed to include candidate artifacts.
   In particular, never import the candidate as part of this source file. -/
import Lean
import Lean.Replay

open Lean

-- Compare every declaration field, including inductive and quotient metadata.
deriving instance BEq for InductiveVal, QuotKind, QuotVal, ConstantInfo

/- Walk kernel declarations directly. Do not consult the serialized axiom
   cache or any environment extension supplied by the candidate. -/
private partial def axioms (env : Kernel.Environment) (names : List Name)
    (seen : NameSet := {}) (found : NameSet := {}) : IO NameSet := do
  match names with
  | [] => return found
  | name :: rest =>
    if seen.contains name then return ← axioms env rest seen found
    let some ci := env.find? name |
      throw <| IO.userError s!"missing kernel declaration {name}"
    let found := if ci matches .axiomInfo _ then found.insert name else found
    let used := ci.getUsedConstantsAsSet.toList
    return ← axioms env (used ++ rest) (seen.insert name) found

def main (args : List String) : IO Unit := do
  let ns :: searchPath :: obligations := args |
    throw <| IO.userError "expected namespace, artifact search path and obligations"
  -- The source above was elaborated without LEAN_PATH. Only runtime data
  -- loading sees the candidate. loadExts=false is a security requirement.
  initSearchPath (← getBuildDir) (System.SearchPath.parse searchPath)
  let expected ← importModules #[{ module := (ns ++ ".Expected").toName }] {}
    (loadExts := false)
  let candidate ← importModules #[{ module := (ns ++ ".Obligations").toName }] {}
    (loadExts := false)
  let mut additions : Std.HashMap Name ConstantInfo := {}
  for (name, ci) in candidate.constants.toList do
    if let some old := expected.toKernelEnv.find? name then
      unless ci == old do
        throw <| IO.userError s!"candidate changed trusted declaration {name}"
    else
      additions := additions.insert name ci
  -- Importing .olean data does not kernel-check it. Replaying is essential:
  -- an elaborator can use skipKernelTC or manufacture serialized declarations.
  -- Use Lean's worker stack, as elaboration does: `--run` uses the much
  -- smaller OS main-thread stack, which rejects valid large proof terms.
  let replay ← (expected.replay additions).asTask (prio := .dedicated)
  let checked ← IO.ofExcept replay.get
  let kernel := checked.toKernelEnv
  let mut rows : Array Json := #[]
  for obligation in obligations do
    let name := (ns ++ ".Obligations." ++ obligation).toName
    let expectedName := (ns ++ ".Expected." ++ obligation).toName
    let some actual := kernel.find? name |
      throw <| IO.userError s!"missing required theorem {name}"
    let some required := expected.toKernelEnv.find? expectedName |
      throw <| IO.userError s!"missing expected type {expectedName}"
    unless actual matches .thmInfo _ do
      throw <| IO.userError s!"required declaration is not a theorem: {name}"
    unless actual.levelParams == required.levelParams do
      throw <| IO.userError s!"universe parameters differ: {name}"
    let pin : Declaration := .thmDecl {
      name := `DjinnChecked ++ name
      levelParams := required.levelParams
      type := required.type
      value := mkConst name (required.levelParams.map Level.param)
    }
    match kernel.addDeclCore 0 pin (cancelTk? := none) with
    | .error _ => throw <| IO.userError s!"theorem has the wrong type: {name}"
    | .ok _ => pure ()
    let dependencies ← axioms kernel [name]
    rows := rows.push <| Json.mkObj [
      ("name", toJson obligation),
      ("axioms", toJson <| dependencies.toArray.qsort Name.lt |>.map (·.toString))]
  IO.println <| (Json.arr rows).compress
