/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SmoothCurveDifferentials
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Separating Parameter

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
universe u v
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- Choose a separating parameter in the actual one-variable field, internally.
Named consumer: the finite normalized two-chart proper model. -/
theorem exists_separating_parameter [PerfectField k]
    [IsFunctionFieldOneVar k F] :
    ∃ t : F, Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F := by
  classical
  obtain ⟨x, _, hfin⟩ := IsFunctionFieldOneVar.exists_transcendental_finite (k := k) (F := F)
  have : Algebra.EssFiniteType k (IntermediateField.adjoin k ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have := hfin
  have : Algebra.EssFiniteType k F :=
    Algebra.EssFiniteType.comp k (IntermediateField.adjoin k ({x} : Set F)) F
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, SmoothCurveStalks.trdeg_eq_one_of_oneVar] at h
    exact_mod_cast h
  obtain ⟨t, hsingle⟩ := Finset.card_eq_one.mp hcard
  subst s
  have ht : Transcendental k t := hs.1.transcendental ⟨t, Finset.mem_singleton_self _⟩
  have hset : (({t} : Finset F) : Set F) = ({t} : Set F) := Finset.coe_singleton t
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F :=
    (congrArg (fun S : Set F ↦ Algebra.IsSeparable (IntermediateField.adjoin k S) F) hset).mp hsep
  exact ⟨t, ht, finiteDimensional_adjoin_of_transcendental ht, hsep'⟩

end
end AclGeom.CurveCompletion
