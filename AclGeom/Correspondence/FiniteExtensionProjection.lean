/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteExtensionChart
import AclGeom.Correspondence.PrincipalLocalization
import AclGeom.Correspondence.FunctionFieldEquivalence

/-!
# Dominant rational projections between finite-extension charts

A ground-field embedding of the target function field into the source
function field is the contravariant datum of a dominant rational map.  This
file spreads such an embedding to one explicit principal-open partial map
between `FiniteExtensionChart`s by clearing denominators of a finite family
of target coordinate-ring generators.

Unlike a birational transition, the field map need not be surjective.  This
is the form needed for the three projections from a normalized
multiplication graph to its two input charts and its output chart.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry
open CategoryTheory
open scoped nonZeroDivisors

universe u v w

namespace FiniteExtensionProjection

variable {k K₁ K₂ L₁ L₂ : Type u} {ι₁ : Type v} {ι₂ : Type w}
  [Field k] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra k K₁] [Algebra K₁ L₁] [Algebra k L₁]
  [IsScalarTower k K₁ L₁] [FiniteDimensional K₁ L₁]
  [Algebra k K₂] [Algebra K₂ L₂] [Algebra k L₂]
  [IsScalarTower k K₂ L₂] [FiniteDimensional K₂ L₂]

/-- The target coordinate ring embedded in the source extension field. -/
def projectionAlgHom (a₂ : ι₂ → K₂) (e : L₂ →ₐ[k] L₁) :
    FiniteExtensionChart.coordinateRing
        (k := k) (K := K₂) (L := L₂) a₂ →ₐ[k] L₁ :=
  e.comp (Subalgebra.val _)

omit [Algebra k K₂] [IsScalarTower k K₂ L₂] in
/-- A field embedding is injective on the target coordinate ring. -/
theorem projectionAlgHom_injective (a₂ : ι₂ → K₂) (e : L₂ →ₐ[k] L₁) :
    Function.Injective (projectionAlgHom (k := k) a₂ e) :=
  e.injective.comp Subtype.val_injective

/-- The contravariant embedding between the scheme-theoretic function
fields induced by an embedding of the selected ambient extension fields. -/
def functionFieldAlgHom
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₂) (L := L₂) a₂).functionField →ₐ[k]
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁).functionField :=
  (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).symm.toAlgHom.comp
    (e.comp (FiniteExtensionChart.functionFieldAlgEquiv a₂ ha₂).toAlgHom)

/-- A ground-field embedding of the target function field into the source
function field spreads to a dominant map on one dense principal open. -/
def partialMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
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
    (projectionAlgHom (k := k) a₂ e)
    (projectionAlgHom_injective (k := k) a₂ e)

instance partialMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
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
    (projectionAlgHom (k := k) a₂ e)
    (projectionAlgHom_injective (k := k) a₂ e)).hom
  infer_instance

set_option maxHeartbeats 1600000 in
-- The proof extends the coordinate-ring embedding through two explicit
-- fraction-field localizations and is reduction-heavy.
/-- The explicit principal-open projection has the generic-point morphism
prescribed by the conjugated ambient field embedding. -/
theorem partialMap_fromFunctionField [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁) :
    (partialMap (k := k) a₁ a₂ ha₁ e).fromFunctionField =
      Scheme.functionFieldMorphismOfHom
        (CommRingCat.ofHom
          (functionFieldAlgHom a₁ a₂ ha₁ ha₂ e).toRingHom) := by
  let A₁ := FiniteExtensionChart.coordinateRing
    (k := k) (K := K₁) (L := L₁) a₁
  let A₂ := FiniteExtensionChart.coordinateRing
    (k := k) (K := K₂) (L := L₂) a₂
  letI : IsFractionRing A₁ L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  let b₂ := FiniteExtensionChart.coordinateGenerators
    (k := k) (K := K₂) (L := L₂) a₂
  let φ := projectionAlgHom (k := k) a₂ e
  let x : (ι₂ ⊕ Fin (Module.finrank K₂ L₂)) → L₁ := fun i ↦ φ (b₂ i)
  let d : A₁ := PrincipalLocalization.CommonDenominator.common (R := A₁) x
  have hd : d ≠ 0 :=
    PrincipalLocalization.CommonDenominator.common_ne_zero (R := A₁) x
  let ψ : A₂ →ₐ[k] Localization.Away d :=
    PrincipalLocalization.awayAlgHomOfGenerators (A := A₁) b₂
      (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
        (k := k) (K := K₂) (L := L₂) a₂) φ
  let q : Localization.Away d →+*
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁).functionField :=
    PrincipalLocalization.genericAwayMap d hd
  have hleft :
      (partialMap (k := k) a₁ a₂ ha₁ e).fromFunctionField =
        Spec.map (CommRingCat.ofHom (q.comp ψ.toRingHom)) := by
    change (PrincipalLocalization.partialMapOfGenerators b₂
      (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
        (k := k) (K := K₂) (L := L₂) a₂)
      φ (projectionAlgHom_injective (k := k) a₂ e)).fromFunctionField = _
    exact PrincipalLocalization.partialMap_fromFunctionField_eq _ _ _ _
  let H := functionFieldAlgHom a₁ a₂ ha₁ ha₂ e
  have hring : CommRingCat.ofHom (q.comp ψ.toRingHom) =
      CommRingCat.ofHom (StructureSheaf.toStalk A₂
          (genericPoint (FiniteExtensionChart.scheme
            (k := k) (K := K₂) (L := L₂) a₂))).hom ≫
        CommRingCat.ofHom H.toRingHom := by
    ext z
    simp only [ConcreteCategory.comp_apply]
    change q (ψ z) = _
    apply (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).injective
    have hq :
        (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).toRingHom.comp q =
          (Localization.mapToFractionRing L₁ (Submonoid.powers d)
            (Localization.Away d)
            (powers_le_nonZeroDivisors_of_noZeroDivisors hd)).toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      apply RingHom.ext
      intro t
      simp only [RingHom.comp_apply]
      change (FiniteExtensionChart.functionFieldAlgEquiv
          (k := k) (K := K₁) (L := L₁) a₁ ha₁).toRingEquiv.toRingHom
          ((q.comp (algebraMap A₁ (Localization.Away d))) t) = _
      rw [PrincipalLocalization.genericAwayMap_comp_algebraMap]
      exact (FiniteExtensionChart.functionFieldAlgEquiv_toStalk
        (k := k) (K := K₁) (L := L₁) a₁ ha₁ t).trans <|
          ((Localization.mapToFractionRing L₁ (Submonoid.powers d)
            (Localization.Away d)
            (powers_le_nonZeroDivisors_of_noZeroDivisors hd))).commutes t |>.symm
    have hz : (FiniteExtensionChart.functionFieldAlgEquiv
        (k := k) (K := K₁) (L := L₁) a₁ ha₁)
        (q (ψ z)) =
        (Localization.mapToFractionRing L₁ (Submonoid.powers d)
          (Localization.Away d)
          (powers_le_nonZeroDivisors_of_noZeroDivisors hd)) (ψ z) := by
      exact RingHom.congr_fun hq (ψ z)
    rw [hz]
    rw [PrincipalLocalization.awayAlgHomOfGenerators_mapToFractionRing]
    change e (z : L₂) = _
    have hz₂ := FiniteExtensionChart.functionFieldAlgEquiv_toStalk
      (k := k) (K := K₂) (L := L₂) a₂ ha₂ z
    change e (z : L₂) =
      (FiniteExtensionChart.functionFieldAlgEquiv
        (k := k) (K := K₁) (L := L₁) a₁ ha₁)
        ((FiniteExtensionChart.functionFieldAlgEquiv
          (k := k) (K := K₁) (L := L₁) a₁ ha₁).symm
          (e ((FiniteExtensionChart.functionFieldAlgEquiv
            (k := k) (K := K₂) (L := L₂) a₂ ha₂)
            ((StructureSheaf.toStalk A₂
              (genericPoint (FiniteExtensionChart.scheme a₂))) z))))
    rw [(FiniteExtensionChart.functionFieldAlgEquiv
      (k := k) (K := K₁) (L := L₁) a₁ ha₁).apply_symm_apply, hz₂]
  rw [hleft]
  unfold Scheme.functionFieldMorphismOfHom
  rw [Spec.fromSpecStalk_eq']
  exact (congrArg Spec.map hring).trans (Spec.map_comp _ _)

/-- The dominant rational map represented by the explicit principal-open
projection. -/
def rationalMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    Scheme.RationalMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁)
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) :=
  (partialMap (k := k) a₁ a₂ ha₁ e).toRationalMap

/-- The rational projection induces exactly the conjugated ambient field
embedding at the generic point. -/
theorem rationalMap_fromFunctionField [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁) :
    (rationalMap (k := k) a₁ a₂ ha₁ e).fromFunctionField =
      Scheme.functionFieldMorphismOfHom
        (CommRingCat.ofHom
          (functionFieldAlgHom a₁ a₂ ha₁ ha₂ e).toRingHom) := by
  unfold rationalMap
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  exact partialMap_fromFunctionField a₁ a₂ ha₁ ha₂ e

instance rationalMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    (rationalMap (k := k) a₁ a₂ ha₁ e).IsDominant := by
  unfold rationalMap
  infer_instance

/-- The contravariant function-field map recovered from the rational
projection is exactly the conjugated ambient field embedding. -/
theorem rationalMap_functionFieldMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁) :
    (rationalMap (k := k) a₁ a₂ ha₁ e).representative.functionFieldMap =
      CommRingCat.ofHom
        (functionFieldAlgHom a₁ a₂ ha₁ ha₂ e).toRingHom := by
  apply Scheme.RationalMap.functionFieldMap_representative_eq_of_fromFunctionField_eq_hom
  exact rationalMap_fromFunctionField a₁ a₂ ha₁ ha₂ e

end FiniteExtensionProjection

end

end AclGeom
