/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedMaps
/-!
# Normalized Localization

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
attribute [local instance] overlapAlgebra parameter_overlap_isScalarTower
  normalizedOverlapAlgebra normalized_overlap_parameter_tower

set_option maxHeartbeats 600000 in
-- Kernel reduction of the induced-field scalar dictionaries on these concrete integral-
-- closure subtypes needs more deterministic time; all proof checking remains enabled.
/-- The actual normalized common chart is the principal localization of the first
actual normalization chart. Named consumer: the actual two-chart proper model. -/
theorem normalizedOverlap_isLocalization (t : F) (ht : t ≠ 0) :
    IsLocalization.Away
      (algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t) (parameter t))
      (normalizedOverlap (k := k) t) := by
  let : Algebra (normalizedRing (k := k) t) F :=
    (algebraMap (normalizedRing (k := k) t) F).toAlgebra
  let : Algebra (normalizedOverlap (k := k) t) F :=
    (algebraMap (normalizedOverlap (k := k) t) F).toAlgebra
  have : IsScalarTower (normalizedRing (k := k) t) (normalizedOverlap (k := k) t) F :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsLocalization.Away (parameter (k := k) t) (overlapRing (k := k) t) :=
    overlap_isLocalization t ht
  have : IsLocalization.Away (algebraMap (parameterRing (k := k) t) F (parameter t)) F :=
    IsLocalization.away_of_isUnit_of_bijective F (isUnit_iff_ne_zero.mpr ht) Function.bijective_id
  exact IsLocalization.Away.integralClosure (R := parameterRing (k := k) t) (S := F)
    (Rf := overlapRing (k := k) t) (Sf := F) (parameter t)

end
end AclGeom.CurveCompletion
