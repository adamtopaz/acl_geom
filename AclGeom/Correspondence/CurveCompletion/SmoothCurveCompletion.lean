/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.SeparatingParameter
import AclGeom.Correspondence.CurveCompletion.ModelFunctionField
import AclGeom.Correspondence.CurveCompletion.BirationalOpenEmbedding
import AclGeom.Correspondence.SmoothCurveStalks

/-!
# Smooth Curve Completion

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
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Every actual smooth separated integral curve over an algebraically closed field
has an actual open embedding into a proper normal integral curve of dimension one.
The model, function-field identification, local normality, extension and original-curve
embedding are all constructed internally. Projectivity and joint extension of families
remain separate obligations. Named source consumer: the completion step in `lem:affine-action`. -/
theorem exists_proper_normal_completion
    (X : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ (Y : Over (Spec (.of k))) (j : X ⟶ Y),
      IsIntegral Y.left ∧ IsProper Y.hom ∧ IsOpenImmersion j.left ∧
        topologicalKrullDim Y.left = 1 ∧
        (∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y)) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsFunctionFieldOneVar k X.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k X hdim
  obtain ⟨t, htr, hfinite, hsep⟩ :=
    exists_separating_parameter (k := k) (F := X.left.functionField)
  have ht : t ≠ 0 := by
    intro h
    apply htr
    rw [h]
    exact isAlgebraic_zero
  let Y := curve (k := k) t ht
  have : IsIntegral Y.left := model_integral t ht
  have : IsProper Y.hom := modelHom_isProper t ht htr
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : Y.left.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from Y.hom]
    infer_instance
  have hYdim : topologicalKrullDim Y.left ≤ 1 := model_dimension_le_one t ht htr
  have hYnormal (y : Y.left) : IsIntegrallyClosed (Y.left.presheaf.stalk y) :=
    (model_stalk_properties t ht htr y).1
  have hYval (y : Y.left) : ValuationRing (Y.left.presheaf.stalk y) := by
    have := hYnormal y
    exact ProperCurve.stalk_valuationRing Y.left hYdim y
  let : Algebra k (model (k := k) t ht).functionField :=
    @ActionFunctionField.functionFieldAlgebra k _ Y inferInstance
  obtain ⟨E⟩ := exists_model_functionField_equiv t ht htr
  let φ : (Spec X.left.functionField).asOver (Spec (.of k)) ⟶ Y :=
    (algSpec (.of k)).map (CommAlgCat.ofHom E.toAlgHom).op ≫
      SchemeGenericTranslate.genericParameter Y
  have hφ : φ.left = Scheme.functionFieldMorphism E.symm.toRingEquiv := rfl
  have hφbase : φ.left ≫ Y.hom =
      X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom :=
    (Over.w φ).trans (Over.w (SchemeGenericTranslate.genericParameter X)).symm
  let r := Scheme.RationalMap.ofFunctionField X.hom Y.hom φ.left hφbase
  have hr : r.fromFunctionField = Scheme.functionFieldMorphism E.symm.toRingEquiv :=
    (Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _).trans hφ
  have hrbase : r.compHom Y.hom = X.hom.toRationalMap :=
    ((Scheme.RationalMap.equivFunctionField X.hom Y.hom) ⟨φ.left, hφbase⟩).property
  have hrdom : r.IsDominant := by
    apply Scheme.RationalMap.isDominant_of_fromFunctionField_closedPoint
    rw [hr]
    exact Scheme.functionFieldMorphism_closedPoint _
  obtain ⟨f, hf, _⟩ := ProperCurve.existsUnique_extension hdim.le
    (SmoothCurveStalks.stalk_integrallyClosed X hdim) X.hom Y.hom r hrbase
  let j : X ⟶ Y := Over.homMk f hf.2
  have hfdom : f.toRationalMap.IsDominant := by rw [hf.1]; exact hrdom
  have : IsDominant f.toPartialMap.hom :=
    (Scheme.PartialMap.isDominant_toRationalMap_iff f.toPartialMap).mp hfdom
  have : IsDominant (X.left.topIso.hom ≫ f) := inferInstanceAs
    (IsDominant f.toPartialMap.hom)
  have : IsDominant f := IsDominant.of_comp X.left.topIso.hom f
  have : IsDominant j.left := inferInstanceAs (IsDominant f)
  have hfgeneric : f.toPartialMap.fromFunctionField =
      Scheme.functionFieldMorphism E.symm.toRingEquiv :=
    (congrArg Scheme.RationalMap.fromFunctionField hf.1).trans hr
  have hff : f.toPartialMap.functionFieldMap = CommRingCat.ofHom E.toRingHom :=
    Scheme.PartialMap.functionFieldMap_eq_of_fromFunctionField_eq
      f.toPartialMap E.symm.toRingEquiv hfgeneric
  have : IsIso f.toPartialMap.functionFieldMap := by
    rw [hff]
    exact (E.toRingEquiv.toCommRingCatIso).isIso_hom
  have : IsIso j.left.toPartialMap.functionFieldMap :=
    inferInstanceAs (IsIso f.toPartialMap.functionFieldMap)
  have hj : IsOpenImmersion j.left := isOpenImmersion_of_target_valuation X Y hYval j
  have hdimY : topologicalKrullDim Y.left = 1 := by
    apply le_antisymm hYdim
    rw [← hdim]
    exact j.left.isOpenEmbedding.isInducing.topologicalKrullDim_le
  exact ⟨Y, j, inferInstance, inferInstance, hj, hdimY, hYnormal⟩

end
end AclGeom.CurveCompletion
