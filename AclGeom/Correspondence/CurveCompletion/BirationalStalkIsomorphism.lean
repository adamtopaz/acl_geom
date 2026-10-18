/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveStalkNaturality
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Birational Stalk Isomorphism

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

/-- A birational morphism is an isomorphism on every stalk whose target stalk is
already a valuation ring. Named consumer: the original curve's completion embedding. -/
theorem stalkMap_isIso_of_target_valuation
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsIso f.toPartialMap.functionFieldMap]
    (x : X) [ValuationRing (Y.presheaf.stalk (f x))] : IsIso (f.stalkMap x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let E := (asIso f.toPartialMap.functionFieldMap).commRingCatIsoToRingEquiv
  let : Algebra R X.functionField := (E.toRingHom.comp (algebraMap R Y.functionField)).toAlgebra
  have : IsFractionRing R X.functionField :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors R) E).mp inferInstance
  let φ : R →+* S := (f.stalkMap x).hom
  let g : S →+* X.functionField := algebraMap S X.functionField
  have hg : Function.Injective g := IsFractionRing.injective S X.functionField
  have hφ : g.comp φ = algebraMap R X.functionField := by
    exact (congrArg CommRingCat.Hom.hom
      (CurvePointsPlaces.functionFieldMap_stalkMap f x)).symm
  have hbij := bijective_rangeRestrict_comp_of_valuationRing φ g hφ
  have hf : Function.Bijective φ := by
    refine ⟨fun a b hab ↦ hbij.1 (congrArg g.rangeRestrict hab), ?_⟩
    intro s
    obtain ⟨r, hr⟩ := hbij.2 ⟨g s, ⟨s, rfl⟩⟩
    exact ⟨r, hg (congrArg Subtype.val hr)⟩
  exact (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mpr hf

end
end AclGeom.CurveCompletion
