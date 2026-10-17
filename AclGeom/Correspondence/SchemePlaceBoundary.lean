/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemePlaceAction

/-!
# An affine curve has a missing place

The global sections of an actual integral affine curve do not lie in every place of its
function field. A transcendental element of that field is a fraction of global sections;
some section has transcendental generic germ, and its pole place belongs to the boundary.

Named source consumer: the missing-place step in the affine-curve part of blueprint
`lem:affine-action`, together with `SchemePlaceAction.boundary_finite`. This does not identify
places with points of a completion or prove that a connected group fixes the boundary.

**Status:** proved; the actual scheme and affine-curve consumers are checked independently.
-/

namespace AclGeom.SchemePlaceAction

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The boundary of an actual integral affine curve is nonempty, over any base field.
The one-variable hypothesis and a transcendental global section are derived internally.
Named consumer: the missing-place step of blueprint `lem:affine-action`. -/
theorem boundary_nonempty {k : Type u} [Field k] (V : Over (Spec (.of k)))
    [IsIntegral V.left] [IsAffine V.left] [LocallyOfFiniteType V.hom]
    (hdim : topologicalKrullDim V.left = 1) :
    (Place.boundary (globalSections V)).Nonempty := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdim
  obtain ⟨t, ht, -⟩ :=
    IsFunctionFieldOneVar.exists_transcendental_finite (k := k) (F := V.left.functionField)
  obtain ⟨a, ha⟩ : ∃ a : Γ(V.left, ⊤),
      Transcendental k (algebraMap Γ(V.left, ⊤) V.left.functionField a) := by
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective Γ(V.left, ⊤) t
    by_cases ha : IsAlgebraic k (algebraMap Γ(V.left, ⊤) V.left.functionField a)
    · refine ⟨b, fun hb ↦ ht ?_⟩
      rw [← hab, div_eq_mul_inv]
      exact ha.mul hb.inv
    · exact ⟨a, ha⟩
  obtain ⟨P, hP⟩ := exists_place_one_lt_valuation ha
  refine ⟨P, ?_⟩
  change ¬ (globalSections V : Set V.left.functionField) ⊆ P.val
  intro h
  exact (not_le_of_gt hP) ((P.val.valuation_le_one_iff _).2 (h ⟨a, rfl⟩))

end

end AclGeom.SchemePlaceAction
