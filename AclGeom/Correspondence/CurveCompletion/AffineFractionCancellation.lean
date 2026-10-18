/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Affine Fraction Cancellation

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

/-- Two actual maps from the spectrum of a ring to an affine scheme agree if they agree after
passage to its fraction field. Named consumer: chart_model_maps_eq_of_fraction_field. -/
theorem affine_hom_eq_of_fraction_field
    {O K A : Type u} [CommRing O] [CommRing A] [Field K]
    [Algebra O K] [IsFractionRing O K]
    (f g : Spec (.of O) ⟶ Spec (.of A))
    (h : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g) : f = g := by
  apply Spec.preimage_injective
  ext a
  apply IsFractionRing.injective O K
  have hh := congrArg Spec.preimage h
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at hh
  exact congrArg (fun q ↦ q a) hh

end
end AclGeom.CurveCompletion
