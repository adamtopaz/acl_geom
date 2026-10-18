/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ValuativeExistence
import AclGeom.Correspondence.CurveCompletion.AffineFractionCancellation
/-!
# Valuative Uniqueness

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
-- Match the actual atlas endpoints while comparing generic and integral chart maps.
/-- Two actual chart maps into the model that agree over the fraction field agree over the ring. The
actual gluing pullback forces an overlap via the reciprocal parameters. Named consumer:
modelHom_valuative_uniqueness. -/
theorem chart_model_maps_eq_of_fraction_field (t : F) (ht : t ≠ 0)
    {O K : Type u} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    (b c : Bool) (q : Spec (.of O) ⟶ chart (k := k) t b)
    (r : Spec (.of O) ⟶ chart (k := k) t c)
    (h : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫
        (q ≫ (atlas (k := k) t ht).ι ⟨b⟩) =
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫
        (r ≫ (atlas (k := k) t ht).ι ⟨c⟩)) :
    q ≫ (atlas (k := k) t ht).ι ⟨b⟩ = r ≫ (atlas (k := k) t ht).ι ⟨c⟩ := by
  let δ := Spec.map (CommRingCat.ofHom (algebraMap O K))
  by_cases hbc : b = c
  · subst c
    have hqr : q = r := by
      apply affine_hom_eq_of_fraction_field (K := K)
      apply (cancel_mono ((atlas (k := k) t ht).ι ⟨b⟩)).mp
      simpa only [Category.assoc] using h
    rw [hqr]
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    let H := overlap_isPullback (k := k) t ht b
    have he : (δ ≫ q) ≫ (atlas (k := k) t ht).ι ⟨b⟩ =
        (δ ≫ r) ≫ (atlas (k := k) t ht).ι ⟨!b⟩ := by
      simpa only [Category.assoc, δ] using h
    let z := H.lift (δ ≫ q) (δ ≫ r) he
    have hzq : z ≫ overlapToChart (k := k) t b = δ ≫ q := H.lift_fst _ _ _
    have hzr : z ≫ overlapToChart (k := k) t (!b) = δ ≫ r := H.lift_snd _ _ _
    let ρ : normalizedOverlap (k := k) t →+* K := (Spec.preimage z).hom
    let a : O := (Spec.preimage q).hom (chartParameter t b)
    let d : O := (Spec.preimage r).hom (chartParameter t (!b))
    have hqring : ρ.comp (chartToOverlap t b) =
        (algebraMap O K).comp (Spec.preimage q).hom := by
      have hx := congrArg Spec.preimage hzq
      rw [← chart_overlap_spec, Spec.preimage_comp, Spec.preimage_comp,
        Spec.preimage_map] at hx
      dsimp only [δ] at hx
      rw [Spec.preimage_map] at hx
      exact congrArg CommRingCat.Hom.hom hx
    have hrring : ρ.comp (chartToOverlap t (!b)) =
        (algebraMap O K).comp (Spec.preimage r).hom := by
      have hx := congrArg Spec.preimage hzr
      rw [← chart_overlap_spec, Spec.preimage_comp, Spec.preimage_comp,
        Spec.preimage_map] at hx
      dsimp only [δ] at hx
      rw [Spec.preimage_map] at hx
      exact congrArg CommRingCat.Hom.hom hx
    have had : a * d = 1 := by
      apply IsFractionRing.injective O K
      have hp := congrArg ρ (chart_parameters_mul (k := k) t ht b)
      rw [map_mul, map_one] at hp
      have hqa := RingHom.congr_fun hqring (chartParameter t b)
      have hrd := RingHom.congr_fun hrring (chartParameter t (!b))
      change ρ (chartToOverlap t b (chartParameter t b)) = algebraMap O K a at hqa
      change ρ (chartToOverlap t (!b) (chartParameter t (!b))) = algebraMap O K d at hrd
      rw [map_mul, map_one, ← hqa, ← hrd]
      exact hp
    obtain ⟨θ, hθ⟩ := exists_chart_overlap_lift_of_isUnit t ht b (Spec.preimage q).hom
      (IsUnit.of_mul_eq_one d had)
    let w := Spec.map (CommRingCat.ofHom θ)
    have hwq : w ≫ overlapToChart (k := k) t b = q := by
      rw [← chart_overlap_spec]
      dsimp only [w]
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (θ.comp (chartToOverlap t b))) = q
      rw [hθ]
      exact Spec.map_preimage q
    have hzw : δ ≫ w = z := by
      have : Mono (overlapToChart (k := k) t b) := by
        have := overlapToChart_isOpenImmersion (k := k) t ht b
        infer_instance
      apply (cancel_mono (overlapToChart (k := k) t b)).mp
      rw [Category.assoc, hwq, hzq]
    have hwr : w ≫ overlapToChart (k := k) t (!b) = r := by
      apply affine_hom_eq_of_fraction_field (K := K)
      change δ ≫ _ = δ ≫ r
      rw [← Category.assoc, hzw, hzr]
    rw [← hwq, Category.assoc, overlap_glue_condition_bool,
      ← Category.assoc, hwr]

set_option backward.isDefEq.respectTransparency false in
-- Compare the actual chart factorizations of two valuation-ring lifts.
/-- The actual normalization model satisfies the uniqueness half of the valuative criterion. Named
consumer: modelHom_isProper. -/
theorem modelHom_valuative_uniqueness (t : F) (ht : t ≠ 0) :
    ValuativeCriterion.Uniqueness (modelHom (k := k) t ht) := by
  intro S
  refine ⟨fun f g ↦ ?_⟩
  apply CommSq.LiftStruct.ext
  obtain ⟨⟨b⟩, q, hq⟩ := exists_chart_factor t ht S.R f.l
  obtain ⟨⟨c⟩, r, hr⟩ := exists_chart_factor t ht S.R g.l
  rw [← hq, ← hr]
  apply chart_model_maps_eq_of_fraction_field (K := S.K) t ht b c
  rw [hq, hr, f.fac_left, g.fac_left]

end
end AclGeom.CurveCompletion
