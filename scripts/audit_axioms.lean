/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom
import GroupConfig
import Lean.Util.CollectAxioms

/-!
# Mathematical library dependency inventory

Used by `scripts/audit_axioms.py`. Select declarations by their declaring module, so that
project declarations outside the `AclGeom` and `GroupConfig` namespaces are included.
Generated declarations are included. Record private declarations present in the imported
environment too. `collectAxioms` is the implementation used by Lean's `#print axioms`.

The Python driver builds both roots, checks that their imported module inventory equals
the mathematical source inventory, and checks every reported dependency against the
standard three axioms. This does not audit coverage of the blueprint's statements.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let projectModule := fun n : Name ↦
    n == `AclGeom || n == `GroupConfig ||
      n.toString.startsWith "AclGeom." || n.toString.startsWith "GroupConfig."
  for m in env.header.moduleNames do
    if projectModule m then
      liftIO <| IO.println s!"MODULE|{m}"
  let entries := env.constants.fold (init := #[]) fun out n ci ↦
    match env.getModuleIdxFor? n with
    | some idx =>
      if projectModule env.header.moduleNames[idx]! then out.push (n, ci) else out
    | none => out
  let entries := entries.qsort fun a b ↦ Name.lt a.1 b.1
  for (n, ci) in entries do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module for {n}"
    let axioms ← collectAxioms n
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .ctorInfo _ => "constructor"
      | .inductInfo _ => "inductive"
      | .recInfo _ => "recursor"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient"
    let row := Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson env.header.moduleNames[idx]!.toString),
      ("kind", toJson kind),
      ("private", toJson (isPrivateName n)),
      ("unsafe", toJson ci.isUnsafe),
      ("axioms", toJson (axioms.toList.map Name.toString))]
    liftIO <| IO.println s!"DECL|{row.compress}"
