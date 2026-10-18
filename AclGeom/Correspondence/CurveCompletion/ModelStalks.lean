/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.AtlasFiniteType
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Model Stalks

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
attribute [local instance] specializationOrder
universe u
variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- Every actual affine normalization-chart stalk is integrally closed and has dimension at most
one. Named consumer: model_stalk_properties. -/
theorem chart_stalk_properties (t : F) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (b : Bool) (y : chart (k := k) t b) :
    IsIntegrallyClosed ((chart (k := k) t b).presheaf.stalk y) ∧
      ringKrullDim ((chart (k := k) t b).presheaf.stalk y) ≤ 1 := by
  have hinv := separating_inverse t htr
  have := hinv.2.1
  have := hinv.2.2
  cases b
  · change PrimeSpectrum (normalizedRing (k := k) t) at y
    change IsIntegrallyClosed ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) ∧
      ringKrullDim ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) ≤ 1
    have : IsDedekindDomain (normalizedRing (k := k) t) :=
      (normalizedRing_properties t htr).2.1
    have : IsIntegral (Spec (.of (normalizedRing (k := k) t))) := inferInstance
    let : Algebra (normalizedRing (k := k) t)
        ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra _ y
    have : IsLocalization.AtPrime
        ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) y.asIdeal :=
      AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk _ y
    have : IsDomain ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) :=
      IsLocalization.isDomain_of_atPrime _ y.asIdeal
    have : IsDedekindDomain ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y) :=
      IsLocalization.AtPrime.isDedekindDomain (normalizedRing (k := k) t) y.asIdeal _
    exact ⟨inferInstance, (Ring.krullDimLE_iff).mp
      (inferInstance : Ring.KrullDimLE 1
        ((Spec (.of (normalizedRing (k := k) t))).presheaf.stalk y))⟩
  · change PrimeSpectrum (normalizedRing (k := k) t⁻¹) at y
    change IsIntegrallyClosed ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) ∧
      ringKrullDim ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) ≤ 1
    have : IsDedekindDomain (normalizedRing (k := k) t⁻¹) :=
      (normalizedRing_properties t⁻¹ hinv.1).2.1
    have : IsIntegral (Spec (.of (normalizedRing (k := k) t⁻¹))) := inferInstance
    let : Algebra (normalizedRing (k := k) t⁻¹)
        ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra _ y
    have : IsLocalization.AtPrime
        ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) y.asIdeal :=
      AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk _ y
    have : IsDomain ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) :=
      IsLocalization.isDomain_of_atPrime _ y.asIdeal
    have : IsDedekindDomain ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y) :=
      IsLocalization.AtPrime.isDedekindDomain (normalizedRing (k := k) t⁻¹) y.asIdeal _
    exact ⟨inferInstance, (Ring.krullDimLE_iff).mp
      (inferInstance : Ring.KrullDimLE 1
        ((Spec (.of (normalizedRing (k := k) t⁻¹))).presheaf.stalk y))⟩

/-- Every actual stalk of the glued model is integrally closed and has dimension at most one, by its
actual chart stalk isomorphism. Named consumer: exists_proper_normal_completion. -/
theorem model_stalk_properties (t : F) (ht : t ≠ 0) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (x : model (k := k) t ht) :
    IsIntegrallyClosed ((model (k := k) t ht).presheaf.stalk x) ∧
      ringKrullDim ((model (k := k) t ht).presheaf.stalk x) ≤ 1 := by
  obtain ⟨i, y, rfl⟩ := (atlas (k := k) t ht).ι_jointly_surjective x
  have hchart := chart_stalk_properties t htr i.down y
  have : IsIntegrallyClosed
      (((atlas (k := k) t ht).U i).presheaf.stalk y) := hchart.1
  let e := (asIso (((atlas (k := k) t ht).ι i).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv e.symm, e.ringKrullDim.trans_le hchart.2⟩

/-- The underlying space of the actual normalization model has dimension at most one. Named
consumer: exists_proper_normal_completion. -/
theorem model_dimension_le_one (t : F) (ht : t ≠ 0) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    topologicalKrullDim (model (k := k) t ht) ≤ 1 := by
  have he : Order.krullDim (model (k := k) t ht) =
      topologicalKrullDim (model (k := k) t ht) :=
    (Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := model (k := k) t ht))).symm
  rw [← he, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  rw [← ringKrullDim_stalk_eq_coheight x]
  exact (model_stalk_properties t ht htr x).2

end
end AclGeom.CurveCompletion
