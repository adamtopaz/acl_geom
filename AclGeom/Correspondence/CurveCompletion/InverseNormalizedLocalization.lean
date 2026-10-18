/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedLocalization
import AclGeom.Correspondence.CurveCompletion.InverseTower
/-!
# Inverse Normalized Localization

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
universe u v
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
attribute [local instance] inverseOverlapAlgebra inverse_parameter_fraction_tower

/-- An element integral over the inverse-parameter ring is integral over the SAME Laurent overlap.
Named consumer: inverseNormalizedToOverlap. -/
theorem inverseNormalized_mem (t : F) {x : F}
    (hx : IsIntegral (parameterRing (k := k) t⁻¹) x) :
    IsIntegral (overlapRing (k := k) t) x := hx.tower_top

/-- The actual inverse-normalization inclusion into the SAME normalized overlap. Named consumer:
inverseNormalizedOverlap_isLocalization. -/
def inverseNormalizedToOverlap (t : F) :
    normalizedRing (k := k) t⁻¹ →+* normalizedOverlap (k := k) t :=
  (algebraMap (normalizedRing (k := k) t⁻¹) F).codRestrict
    (normalizedOverlap (k := k) t) (fun x ↦ inverseNormalized_mem t x.property)

/-- The algebra defined by the actual inverse-normalization inclusion. Named consumer:
inverseNormalizedOverlap_isLocalization. -/
@[instance_reducible]
def inverseNormalizedOverlapAlgebra (t : F) :
    Algebra (normalizedRing (k := k) t⁻¹) (normalizedOverlap (k := k) t) :=
  (inverseNormalizedToOverlap t).toAlgebra

attribute [local instance] inverseNormalizedOverlapAlgebra

/-- The inverse-parameter ring, its normalization and the SAME overlap form the actual tower. Named
consumer: inverseNormalizedOverlap_isLocalization. -/
theorem inverseNormalized_parameter_tower (t : F) :
    IsScalarTower (parameterRing (k := k) t⁻¹) (normalizedRing (k := k) t⁻¹)
      (normalizedOverlap (k := k) t) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ Subtype.ext rfl)

attribute [local instance] inverseNormalized_parameter_tower

set_option maxHeartbeats 600000 in
-- Kernel reduction of the induced-field scalar dictionaries on the concrete integral-
-- closure subtypes needs more deterministic time; all proof checking remains enabled.
/-- The SAME actual normalized overlap also localizes the actual inverse normalization
chart. Named consumer: the actual two-chart proper-normal completion. -/
theorem inverseNormalizedOverlap_isLocalization (t : F) (ht : t ≠ 0) :
    IsLocalization.Away
      (algebraMap (parameterRing (k := k) t⁻¹) (normalizedRing (k := k) t⁻¹) (parameter t⁻¹))
      (normalizedOverlap (k := k) t) := by
  let : Algebra (normalizedRing (k := k) t⁻¹) F :=
    (algebraMap (normalizedRing (k := k) t⁻¹) F).toAlgebra
  let : Algebra (normalizedOverlap (k := k) t) F :=
    (algebraMap (normalizedOverlap (k := k) t) F).toAlgebra
  have : IsScalarTower (normalizedRing (k := k) t⁻¹) (normalizedOverlap (k := k) t) F :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsLocalization.Away (parameter (k := k) t⁻¹) (overlapRing (k := k) t) :=
    inverse_overlap_isLocalization t ht
  have : IsLocalization.Away (algebraMap (parameterRing (k := k) t⁻¹) F (parameter t⁻¹)) F :=
    IsLocalization.away_of_isUnit_of_bijective F
      (isUnit_iff_ne_zero.mpr (inv_ne_zero ht)) Function.bijective_id
  exact IsLocalization.Away.integralClosure (R := parameterRing (k := k) t⁻¹) (S := F)
    (Rf := overlapRing (k := k) t) (Sf := F) (parameter t⁻¹)

end
end AclGeom.CurveCompletion
