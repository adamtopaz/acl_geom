/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ProperNormalModel
import AclGeom.Correspondence.CurveCoordinateCover

/-!
# Model Function Field

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
open CategoryTheory AlgebraicGeometry
universe u
variable {k F : Type u} [Field k] [Field F] [Algebra k F]

set_option backward.isDefEq.respectTransparency false in
-- Match the actual affine normalization chart and its canonical generic-stalk algebras.
/-- The actual generic-stalk field of the constructed model is isomorphic over the SAME base to the
ORIGINAL given function field, via its actual affine normalization chart. Named consumer:
exists_proper_normal_completion. -/
theorem exists_model_functionField_equiv (t : F) (ht : t ≠ 0)
    (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    letI : Algebra k (model (k := k) t ht).functionField :=
      @ActionFunctionField.functionFieldAlgebra k _ (curve (k := k) t ht)
        (model_integral t ht)
    Nonempty ((model (k := k) t ht).functionField ≃ₐ[k] F) := by
  let A : CommRingCat.{u} := .of (normalizedRing (k := k) t)
  let : Algebra k A := normalizedBaseAlgebra (k := k) t
  let U := (Spec A).asOver (Spec (.of k))
  let M := curve (k := k) t ht
  have : IsIntegral U.left := inferInstanceAs (IsIntegral (Spec A))
  have : IsIntegral M.left := model_integral t ht
  let : Algebra A U.left.functionField := instAlgebraCarrierFunctionFieldSpec A
  have : IsFractionRing A U.left.functionField := functionField_isFractionRing_of_affine A
  let : Algebra k U.left.functionField := ActionFunctionField.functionFieldAlgebra U
  let : Algebra k M.left.functionField := ActionFunctionField.functionFieldAlgebra M
  let j : U ⟶ M := Over.homMk ((atlas (k := k) t ht).ι ⟨false⟩)
    (chart_modelHom t ht ⟨false⟩)
  have : IsOpenImmersion j.left := (atlas (k := k) t ht).ι_isOpenImmersion ⟨false⟩
  have : IsDominant j.left :=
    ⟨(IsOpenImmersion.isOpen_range j.left).dense (Set.range_nonempty j.left)⟩
  have : IsIso j.left.toPartialMap.functionFieldMap :=
    CurveCoordinateCover.isIso_functionFieldMap_of_isOpenImmersion j.left
  let Ej : M.left.functionField ≃ₐ[k] U.left.functionField :=
    AlgEquiv.ofRingEquiv
      (f := (asIso j.left.toPartialMap.functionFieldMap).commRingCatIsoToRingEquiv)
      (ActionFunctionField.functionFieldMap_algebraMap j)
  have : IsFractionRing A F := (normalizedRing_properties t htr).2.2.1
  have : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k A U.left.functionField :=
    CurveCoordinateCover.spec_functionField_isScalarTower k A
  let EA : U.left.functionField ≃ₐ[k] F :=
    IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.refl : A ≃ₐ[k] A)
  exact ⟨Ej.trans EA⟩

end
end AclGeom.CurveCompletion
