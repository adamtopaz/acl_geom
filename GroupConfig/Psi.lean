/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.ConfigurationInput
import GroupConfig.Main

/-!
# The group configuration theorem for the Ψ witness

Blueprint `sources/group_configuration/11-application.tex`, the interalgebraicity part of
`cor:psi`.

Clauses (i)–(iv) of an actual Ψ witness make its displayed representatives a group
configuration of group rank two and space rank one
(`QWitness.PsiCore.groupConfiguration_with_ranks`, `prop:psi-gc`). The group configuration
theorem (`GroupConfig.GroupConfiguration.exists_main`) applies after adjoining a finite set `E`
independent from the witness. Over `acl(k, E)` it gives a Hrushovski–Weil datum of bijections
between curves, whose group of germs has rank two. Two independent generic members `g_a`, `g_b`
of its difference set and a generic point `y'` of the curve realize the witness: `A`, `B`, `C`,
`X`, `Y`, `Z` are interalgebraic over `acl(k, E)` with `code g_a`, `code g_b`,
`code (g_b g_a⁻¹)`, `g_a(y')`, `y'` and `g_b(y')` (`QWitness.PsiCore.exists_isMainConclusion`).

This is a statement about the group of germs and the curve locus up to interalgebraicity. It does
not provide an algebraic group, a classification of the action, or descent to the original
fields.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the interalgebraicity part of `cor:psi` is complete. The extracted datum has a
constructible group and homogeneous-space presentation in
`GroupConfig.Constructible.CanonicalPresentation`; the full Ψ application is proved in
`GroupConfig.PsiConstructible`.
-/

namespace AclGeom

open GroupConfig Set

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable {w : QWitness k K}

/-- `cor:psi`, interalgebraicity part: for a Ψ witness in an algebraically closed universal
domain over an algebraically closed base, the conclusion of the group configuration theorem holds
over `acl(k, E)` for a finite set `E` independent from the witness, with a group of germs of rank
two acting on a curve. -/
theorem PsiCore.exists_isMainConclusion [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (hw : w.PsiCore) :
    ∃ E : Set K, E.Finite ∧
      IndepOver k ∅ E (range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪
        range w.yTuple ∪ range w.zTuple) ∧
      IsMainConclusion k (racl k E) w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple ∧
      erk (↥(racl k E)) ∅ (range w.aTuple) = 2 ∧ erk (↥(racl k E)) ∅ (range w.xTuple) = 1 := by
  obtain ⟨hc, ha, hx⟩ := hw.groupConfiguration_with_ranks
  obtain ⟨E, hEfin, hEind, hmain⟩ := hc.exists_main
  /- Ranks of the witness points do not change over `acl(k, E)`. -/
  have hrk : ∀ {X : Set K}, X ⊆ range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪
      range w.xTuple ∪ range w.yTuple ∪ range w.zTuple → X.Finite →
      erk (↥(racl k E)) ∅ X = erk k ∅ X := fun hX hfin ↦ by
    rw [erk_base_empty, erk_racl_base]
    have := hEind.symm hX hfin
    rwa [empty_union] at this
  refine ⟨E, hEfin, hEind, hmain, ?_, ?_⟩
  · rw [hrk (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))) (finite_range _), ha]
  · rw [hrk (fun _ h ↦ Or.inl (Or.inl (Or.inr h))) (finite_range _), hx]

end QWitness

end AclGeom
