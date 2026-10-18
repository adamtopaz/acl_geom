/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.AtlasGeometry
import AclGeom.Correspondence.CurveCompletion.ChartAlgebra
import AclGeom.Correspondence.CurveCompletion.ChartSchemeLift
import Mathlib.RingTheory.Valuation.Integral

/-!
# Valuative Existence

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
attribute [local instance] normalizedBaseAlgebra


set_option backward.isDefEq.respectTransparency false in
-- Unfold the actual atlas endpoints during categorical matching; kernel checking is unchanged.
/-- Every actual valuation-ring diagram whose generic map lies in a normalization chart has a lift
to the actual model, choosing the opposite chart when necessary. Named consumer:
modelHom_valuative_existence. -/
theorem exists_model_lift_from_chart (t : F) (ht : t ≠ 0)
    (htr : Transcendental k t) (b : Bool)
    {O K : Type u} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K]
    (q : Spec (.of K) ⟶ chart (k := k) t b)
    (s : Spec (.of O) ⟶ Spec (.of k))
    (hq : q ≫ chartBaseHom (k := k) t b =
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s) :
    ∃ g : Spec (.of O) ⟶ model (k := k) t ht,
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g =
        q ≫ (atlas (k := k) t ht).ι ⟨b⟩ ∧ g ≫ modelHom (k := k) t ht = s := by
  have : IsIntegrallyClosed O := (ValuationRing.integers O K).isIntegrallyClosed
  let φ : chartRing (k := k) t b →+* K := (Spec.preimage q).hom
  by_cases hm : φ (chartParameter t b) ∈ (algebraMap O K).range
  · obtain ⟨g, hg, hgs⟩ := exists_chart_scheme_lift (chartValue t b)
      (chartValue_transcendental t htr b) q s
      (by simpa only [chart_base_spec] using hq) hm
    refine ⟨g ≫ (atlas (k := k) t ht).ι ⟨b⟩, ?_, ?_⟩
    · rw [← Category.assoc, hg]
    · rw [Category.assoc, chart_modelHom, ← chart_base_spec, hgs]
  · have hφ : φ (chartParameter t b) ≠ 0 := by
      intro hz
      apply hm
      rw [hz]
      exact ⟨0, map_zero _⟩
    obtain ⟨ρ, hρ, hrecip⟩ := exists_chart_overlap_lift t ht b φ hφ
    let qC := Spec.map (CommRingCat.ofHom ρ)
    let q' := qC ≫ overlapToChart (k := k) t (!b)
    have hqC : qC ≫ overlapToChart (k := k) t b = q := by
      rw [← chart_overlap_spec]
      dsimp only [qC]
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (ρ.comp (chartToOverlap t b))) = q
      rw [hρ]
      exact Spec.map_preimage q
    have hq' : q' ≫ chartBaseHom (k := k) t (!b) =
        Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s := by
      calc
        _ = qC ≫ overlapBaseHom (k := k) t := by
          dsimp only [q']
          rw [Category.assoc, overlap_chart_base_comm]
        _ = (qC ≫ overlapToChart (k := k) t b) ≫ chartBaseHom (k := k) t b := by
          rw [Category.assoc, overlap_chart_base_comm]
        _ = _ := by rw [hqC, hq]
    have hpre : (Spec.preimage q').hom = ρ.comp (chartToOverlap t (!b)) := by
      dsimp only [q']
      rw [← chart_overlap_spec, Spec.preimage_comp]
      simp only [qC, Spec.preimage_map]
      rfl
    have hmint : (φ (chartParameter t b))⁻¹ ∈ (algebraMap O K).range := by
      exact (ValuationRing.isInteger_or_isInteger O (φ (chartParameter t b))).resolve_left hm
    have hm' : (Spec.preimage q').hom (chartParameter t (!b)) ∈
        (algebraMap O K).range := by
      rw [hpre, hrecip]
      exact hmint
    obtain ⟨g, hg, hgs⟩ := exists_chart_scheme_lift (chartValue t (!b))
      (chartValue_transcendental t htr (!b)) q' s
      (by simpa only [chart_base_spec] using hq') hm'
    refine ⟨g ≫ (atlas (k := k) t ht).ι ⟨!b⟩, ?_, ?_⟩
    · rw [← Category.assoc, hg]
      change (qC ≫ overlapToChart t (!b)) ≫ _ = _
      rw [Category.assoc, ← overlap_glue_condition_bool t ht b, ← Category.assoc, hqC]
    · rw [Category.assoc, chart_modelHom, ← chart_base_spec, hgs]

set_option backward.isDefEq.respectTransparency false in
-- Match the actual gluing index and chart endpoints during categorical rewriting.
/-- The actual normalization model satisfies the existence half of the valuative criterion, with
every lift constructed internally. Named consumer: modelHom_isProper. -/
theorem modelHom_valuative_existence (t : F) (ht : t ≠ 0)
    (htr : Transcendental k t) :
    ValuativeCriterion.Existence (modelHom (k := k) t ht) := by
  intro S
  obtain ⟨⟨b⟩, q, hq⟩ := exists_chart_factor t ht S.K S.i₁
  have hqbase : q ≫ chartBaseHom (k := k) t b =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := by
    rw [← chart_modelHom t ht ⟨b⟩, ← Category.assoc, hq]
    exact S.commSq.w
  obtain ⟨g, hg, hgs⟩ := exists_model_lift_from_chart t ht htr b q S.i₂ hqbase
  exact ⟨⟨g, hg.trans hq, hgs⟩⟩

end
end AclGeom.CurveCompletion
