/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.OverlapParameters
/-!
# Chart Algebra

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

/-- The parameter t or its inverse, according to the actual chart index. Named consumer:
chartRing. -/
abbrev chartValue (t : F) (b : Bool) : F := if b then t⁻¹ else t
/-- The actual integral-closure coordinate ring of the chosen chart. Named consumer:
exists_model_lift_from_chart. -/
abbrev chartRing (t : F) (b : Bool) := normalizedRing (k := k) (chartValue t b)
/-- The literal parameter in the actual chosen chart ring. Named consumer:
exists_chart_overlap_lift. -/
abbrev chartParameter (t : F) (b : Bool) : chartRing (k := k) t b :=
  normalizedParameter (chartValue t b)

/-- The actual ring inclusion from either normalization chart into the SAME overlap. Named consumer:
chart_overlap_isLocalization. -/
def chartToOverlap (t : F) (b : Bool) :
    chartRing (k := k) t b →+* normalizedOverlap (k := k) t := by
  cases b
  · exact normalizedToOverlap t
  · exact inverseNormalizedToOverlap t

/-- The algebra induced by the actual chosen chart-to-overlap map. Named consumer:
chart_overlap_isLocalization. -/
@[instance_reducible]
def chartOverlapAlgebra (t : F) (b : Bool) :
    Algebra (chartRing (k := k) t b) (normalizedOverlap (k := k) t) :=
  (chartToOverlap t b).toAlgebra

/-- The SAME actual normalized overlap is the principal localization of either chart at its literal
parameter. Named consumer: exists_chart_overlap_lift_of_isUnit. -/
theorem chart_overlap_isLocalization (t : F) (ht : t ≠ 0) (b : Bool) :
    letI := chartOverlapAlgebra (k := k) t b
    IsLocalization.Away (chartParameter (k := k) t b) (normalizedOverlap (k := k) t) := by
  cases b
  · exact normalizedOverlap_isLocalization t ht
  · exact inverseNormalizedOverlap_isLocalization t ht

/-- Either chart parameter and the opposite chart parameter multiply to one in the actual overlap.
Named consumer: chart_model_maps_eq_of_fraction_field. -/
theorem chart_parameters_mul (t : F) (ht : t ≠ 0) (b : Bool) :
    chartToOverlap (k := k) t b (chartParameter t b) *
      chartToOverlap (k := k) t (!b) (chartParameter t (!b)) = 1 := by
  cases b
  · exact overlap_parameters_mul t ht
  · change inverseNormalizedToOverlap t (normalizedParameter t⁻¹) *
      normalizedToOverlap t (normalizedParameter t) = 1
    rw [mul_comm]
    exact overlap_parameters_mul t ht

/-- The actual ring inclusion induces precisely the overlap map used in gluing. Named consumer:
modelHom_valuative_existence. -/
theorem chart_overlap_spec (t : F) (b : Bool) :
    Spec.map (CommRingCat.ofHom (chartToOverlap (k := k) t b)) =
      overlapToChart (k := k) t b := by
  cases b <;> rfl

/-- The actual chart base algebra induces precisely the chart structure morphism used in gluing.
Named consumer: exists_model_lift_from_chart. -/
theorem chart_base_spec (t : F) (b : Bool) :
    letI := normalizedBaseAlgebra (k := k) (chartValue t b)
    Spec.algebraMap k (chartRing (k := k) t b) = chartBaseHom (k := k) t b := by
  cases b <;> rfl

/-- The literal chosen-chart parameter is transcendental whenever t is transcendental. Named
consumer: exists_model_lift_from_chart. -/
theorem chartValue_transcendental (t : F) (htr : Transcendental k t) (b : Bool) :
    Transcendental k (chartValue t b) := by
  cases b
  · exact htr
  · exact fun h ↦ htr (IsAlgebraic.inv_iff.mp h)

/-- A map from an actual normalization chart factors through the SAME overlap whenever its literal
parameter is a unit. Named consumer: chart_model_maps_eq_of_fraction_field. -/
theorem exists_chart_overlap_lift_of_isUnit (t : F) (ht : t ≠ 0) (b : Bool)
    {R : Type u} [CommRing R] (φ : chartRing (k := k) t b →+* R)
    (hφ : IsUnit (φ (chartParameter t b))) :
    ∃ ρ : normalizedOverlap (k := k) t →+* R,
      ρ.comp (chartToOverlap t b) = φ := by
  let := chartOverlapAlgebra (k := k) t b
  have : IsLocalization.Away (chartParameter (k := k) t b)
      (normalizedOverlap (k := k) t) := chart_overlap_isLocalization t ht b
  exact ⟨IsLocalization.Away.lift (chartParameter t b) hφ,
    IsLocalization.Away.lift_comp (S := normalizedOverlap (k := k) t)
      (g := φ) (chartParameter t b) hφ⟩

/-- A field-valued chart map with nonzero parameter extends to the SAME overlap, and the opposite
parameter evaluates to the literal reciprocal. Named consumer: exists_model_lift_from_chart. -/
theorem exists_chart_overlap_lift (t : F) (ht : t ≠ 0) (b : Bool)
    {K : Type u} [Field K] (φ : chartRing (k := k) t b →+* K)
    (hφ : φ (chartParameter t b) ≠ 0) :
    ∃ ρ : normalizedOverlap (k := k) t →+* K,
      ρ.comp (chartToOverlap t b) = φ ∧
        (ρ.comp (chartToOverlap t (!b))) (chartParameter t (!b)) =
          (φ (chartParameter t b))⁻¹ := by
  obtain ⟨ρ, hρ⟩ := exists_chart_overlap_lift_of_isUnit t ht b φ
    (isUnit_iff_ne_zero.mpr hφ)
  refine ⟨ρ, hρ, ?_⟩
  have hm := congrArg ρ (chart_parameters_mul (k := k) t ht b)
  rw [map_mul, map_one] at hm
  have ha : ρ (chartToOverlap t b (chartParameter t b)) =
      φ (chartParameter t b) := RingHom.congr_fun hρ _
  rw [ha] at hm
  change ρ (chartToOverlap t (!b) (chartParameter t (!b))) = _
  apply (mul_left_cancel₀ hφ)
  rw [hm, mul_inv_cancel₀ hφ]

end
end AclGeom.CurveCompletion
