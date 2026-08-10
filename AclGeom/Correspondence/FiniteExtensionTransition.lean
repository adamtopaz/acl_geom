/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteExtensionChart
import AclGeom.Correspondence.PrincipalLocalization
import AclGeom.Correspondence.FunctionFieldEquivalence
import AclGeom.Correspondence.BirationalGluing

/-!
# Principal-open maps between finite-extension charts

A field equivalence between the selected fraction fields of two
`FiniteExtensionChart`s restricts contravariantly to an embedding of the
target coordinate ring into the source fraction field.  Clearing the finitely
many target-generator denominators produces a dominant partial map from one
explicit dense principal open of the source chart to the target chart.

Applying this construction to an equivalence and its inverse is the algebraic
input for extracting a dense-open transition isomorphism.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry
open CategoryTheory
open scoped nonZeroDivisors

universe u v w

namespace FiniteExtensionTransition

variable {k K₁ K₂ L₁ L₂ : Type u} {ι₁ : Type v} {ι₂ : Type w}
  [Field k] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra k K₁] [Algebra K₁ L₁] [Algebra k L₁]
  [IsScalarTower k K₁ L₁] [FiniteDimensional K₁ L₁]
  [Algebra k K₂] [Algebra K₂ L₂] [Algebra k L₂]
  [IsScalarTower k K₂ L₂] [FiniteDimensional K₂ L₂]

/-- The target coordinate ring embedded in the source fraction field by the
inverse of a field equivalence. -/
def transitionAlgHom (a₂ : ι₂ → K₂) (e : L₁ ≃ₐ[k] L₂) :
    FiniteExtensionChart.coordinateRing
        (k := k) (K := K₂) (L := L₂) a₂ →ₐ[k] L₁ :=
  e.symm.toAlgHom.comp (Subalgebra.val _)

omit [Algebra k K₂] [IsScalarTower k K₂ L₂] in
/-- The coordinate-ring homomorphism induced by a field equivalence is
injective. -/
theorem transitionAlgHom_injective (a₂ : ι₂ → K₂) (e : L₁ ≃ₐ[k] L₂) :
    Function.Injective (transitionAlgHom (k := k) a₂ e) :=
  e.symm.injective.comp Subtype.val_injective

/-- A field equivalence between finite-extension charts spreads to a
dominant partial map on one dense principal open of the source chart. -/
noncomputable def partialMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₁) (L := L₁) a₁).PartialMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  exact PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (transitionAlgHom (k := k) a₂ e)
    (transitionAlgHom_injective (k := k) a₂ e)

/-- The principal-open map induced by a finite-extension field equivalence is
dominant. -/
instance partialMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    IsDominant (partialMap (k := k) a₁ a₂ ha₁ e).hom := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  change IsDominant (PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (transitionAlgHom (k := k) a₂ e)
    (transitionAlgHom_injective (k := k) a₂ e)).hom
  infer_instance

/-- The field equivalence between the scheme-theoretic function fields of
two finite-extension charts induced by an equivalence of their selected
ambient extension fields. -/
noncomputable def functionFieldAlgEquiv
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₁) (L := L₁) a₁).functionField ≃ₐ[k]
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂).functionField :=
  (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).trans <|
    e.trans (FiniteExtensionChart.functionFieldAlgEquiv a₂ ha₂).symm

set_option maxHeartbeats 1600000 in
/-- The explicit principal-open partial map has the generic-point morphism
prescribed by the conjugated chart function-field equivalence. -/
theorem partialMap_fromFunctionField [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (partialMap (k := k) a₁ a₂ ha₁ e).fromFunctionField =
      Scheme.functionFieldMorphism
        (functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e).toRingEquiv := by
  let A₁ := FiniteExtensionChart.coordinateRing
    (k := k) (K := K₁) (L := L₁) a₁
  let A₂ := FiniteExtensionChart.coordinateRing
    (k := k) (K := K₂) (L := L₂) a₂
  let X₁ := FiniteExtensionChart.scheme
    (k := k) (K := K₁) (L := L₁) a₁
  let X₂ := FiniteExtensionChart.scheme
    (k := k) (K := K₂) (L := L₂) a₂
  let b₂ := FiniteExtensionChart.coordinateGenerators
    (k := k) (K := K₂) (L := L₂) a₂
  let φ := transitionAlgHom (k := k) a₂ e
  let x : (ι₂ ⊕ Fin (Module.finrank K₂ L₂)) → L₁ := fun i ↦ φ (b₂ i)
  let d : A₁ := PrincipalLocalization.CommonDenominator.common (R := A₁) x
  have hd : d ≠ 0 :=
    PrincipalLocalization.CommonDenominator.common_ne_zero (R := A₁) x
  let ψ : A₂ →ₐ[k] Localization.Away d :=
    PrincipalLocalization.awayAlgHomOfGenerators (A := A₁) b₂
      (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
        (k := k) (K := K₂) (L := L₂) a₂) φ
  let q : Localization.Away d →+* X₁.functionField :=
    PrincipalLocalization.genericAwayMap d hd
  have hleft :
      (partialMap (k := k) a₁ a₂ ha₁ e).fromFunctionField =
        Spec.map (CommRingCat.ofHom (q.comp ψ.toRingHom)) := by
    change (PrincipalLocalization.partialMapOfGenerators b₂
      (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
        (k := k) (K := K₂) (L := L₂) a₂)
      φ (transitionAlgHom_injective (k := k) a₂ e)).fromFunctionField = _
    exact PrincipalLocalization.partialMap_fromFunctionField_eq _ _ _ _
  rw [hleft]
  unfold Scheme.functionFieldMorphism
  rw [Spec.fromSpecStalk_eq']
  rw [← Spec.map_comp]
  apply Spec.map_injective
  apply CommRingCat.hom_ext
  intro z
  change q (ψ z) = _
  apply (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).injective
  have hq :
      (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).toRingHom.comp q =
        (Localization.mapToFractionRing L₁ (Submonoid.powers d)
          (Localization.Away d)
          (powers_le_nonZeroDivisors_of_noZeroDivisors hd)).toRingHom := by
    letI : Algebra A₁ X₁.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A₁)
    letI : IsFractionRing A₁ X₁.functionField :=
      AlgebraicGeometry.functionField_isFractionRing_of_affine (.of A₁)
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro t
    simp only [RingHom.comp_apply]
    rw [PrincipalLocalization.genericAwayMap_comp_algebraMap]
    rw [FiniteExtensionChart.functionFieldAlgEquiv_toStalk]
    exact ((Localization.mapToFractionRing L₁ (Submonoid.powers d)
      (Localization.Away d)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd))).commutes t |>.symm
  rw [RingHom.congr_fun hq]
  rw [PrincipalLocalization.awayAlgHomOfGenerators_mapToFractionRing]
  change e.symm (z : L₂) = _
  simp [functionFieldAlgEquiv, FiniteExtensionChart.functionFieldAlgEquiv_toStalk]

set_option backward.isDefEq.respectTransparency false in
/-- The generic-point morphism induced by the chart function-field
equivalence is compatible with both chart structure maps to `Spec k`. -/
theorem functionFieldMorphism_comp_structureMap
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    let E := functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e
    Scheme.functionFieldMorphism E.toRingEquiv ≫
        FiniteExtensionChart.structureMap a₂ =
      (FiniteExtensionChart.scheme a₁).fromSpecStalk
          (genericPoint (FiniteExtensionChart.scheme a₁)) ≫
        FiniteExtensionChart.structureMap a₁ := by
  let E := functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e
  change Scheme.functionFieldMorphism E.toRingEquiv ≫
      FiniteExtensionChart.structureMap a₂ =
    (FiniteExtensionChart.scheme a₁).fromSpecStalk
        (genericPoint (FiniteExtensionChart.scheme a₁)) ≫
      FiniteExtensionChart.structureMap a₁
  unfold Scheme.functionFieldMorphism FiniteExtensionChart.structureMap
    FiniteExtensionChart.scheme
  rw [Category.assoc]
  rw [Spec.fromSpecStalk_eq, Spec.fromSpecStalk_eq]
  simp only [← Spec.map_comp]
  congr 1
  ext z
  exact E.symm.commutes z

/-- The rational map between finite-extension charts attached to an ambient
field equivalence.  It is characterized by the corresponding map of function
fields and is spread out over the ground field. -/
noncomputable def rationalMap [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    Scheme.RationalMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁)
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) :=
  Scheme.RationalMap.ofFunctionField
    (FiniteExtensionChart.structureMap
      (k := k) (K := K₁) (L := L₁) a₁)
    (FiniteExtensionChart.structureMap
      (k := k) (K := K₂) (L := L₂) a₂)
    (Scheme.functionFieldMorphism
      (functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e).toRingEquiv)
    (functionFieldMorphism_comp_structureMap a₁ a₂ ha₁ ha₂ e)

/-- The function-field morphism of the chart rational map is the one induced
by the selected ambient field equivalence. -/
theorem rationalMap_fromFunctionField [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (rationalMap a₁ a₂ ha₁ ha₂ e).fromFunctionField =
      Scheme.functionFieldMorphism
        (functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e).toRingEquiv := by
  unfold rationalMap
  exact Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _

/-- The canonical function-field rational map is represented by the explicit
dominant principal-open partial map obtained by clearing denominators. -/
theorem partialMap_toRationalMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (partialMap (k := k) a₁ a₂ ha₁ e).toRationalMap =
      rationalMap a₁ a₂ ha₁ ha₂ e := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  rw [partialMap_fromFunctionField, rationalMap_fromFunctionField]

/-- The chart rational map induced by a function-field equivalence is
dominant. -/
instance rationalMap_isDominant [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (rationalMap a₁ a₂ ha₁ ha₂ e).IsDominant := by
  apply Scheme.RationalMap.isDominant_of_fromFunctionField_closedPoint
  rw [rationalMap_fromFunctionField]
  exact Scheme.functionFieldMorphism_closedPoint _

/-- Reversing the ambient field equivalence reverses the induced
scheme-function-field equivalence. -/
theorem functionFieldAlgEquiv_symm
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    functionFieldAlgEquiv a₂ a₁ ha₂ ha₁ e.symm =
      (functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e).symm := by
  ext z
  simp [functionFieldAlgEquiv]

/-- The rational maps induced by an ambient field equivalence and its inverse
compose to the identity. -/
theorem rationalMap_comp_symm [Finite ι₁] [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (rationalMap a₁ a₂ ha₁ ha₂ e).comp
        (rationalMap a₂ a₁ ha₂ ha₁ e.symm) =
      Scheme.RationalMap.id (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁) := by
  let E := functionFieldAlgEquiv a₁ a₂ ha₁ ha₂ e
  apply Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq
    _ _ E.toRingEquiv
  · exact rationalMap_fromFunctionField a₁ a₂ ha₁ ha₂ e
  · rw [rationalMap_fromFunctionField, functionFieldAlgEquiv_symm]
    rfl

/-- The inverse composite of the two chart rational maps is also the
identity. -/
theorem rationalMap_symm_comp [Finite ι₁] [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (rationalMap a₂ a₁ ha₂ ha₁ e.symm).comp
        (rationalMap a₁ a₂ ha₁ ha₂ e) =
      Scheme.RationalMap.id (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) := by
  exact rationalMap_comp_symm a₂ a₁ ha₂ ha₁ e.symm

/-- A field equivalence between finite-extension charts therefore produces
an explicit isomorphism between dense open subschemes. -/
noncomputable def partialIso [Finite ι₁] [Finite ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₁) (L := L₁) a₁).PartialIso
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) :=
  BirationalGluing.partialIsoOfMutualInverseRationalMaps
    (rationalMap a₁ a₂ ha₁ ha₂ e)
    (rationalMap a₂ a₁ ha₂ ha₁ e.symm)
    (rationalMap_comp_symm a₁ a₂ ha₁ ha₂ e)
    (rationalMap_symm_comp a₁ a₂ ha₁ ha₂ e)

end FiniteExtensionTransition

end

end AclGeom
