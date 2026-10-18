/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedChart
import Mathlib.RingTheory.Localization.Integral

/-!
# Normalized Maps

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

/-- The integral closure of the actual Laurent parameter ring in the given field. Named consumer:
normalizedOverlap_isLocalization. -/
abbrev normalizedOverlap (t : F) := integralClosure (overlapRing (k := k) t) F

attribute [local instance] overlapAlgebra

/-- The polynomial parameter, Laurent overlap and ambient field form their actual inclusion tower.
Named consumer: normalizedClosure_le_overlap. -/
theorem parameter_overlap_isScalarTower (t : F) :
    IsScalarTower (parameterRing (k := k) t) (overlapRing (k := k) t) F :=
  Subalgebra.inclusion.isScalarTower_right (parameterRing_le_overlapRing t) F

attribute [local instance] parameter_overlap_isScalarTower

/-- Every element integral over k[t] is integral over the Laurent overlap. Named consumer:
normalizedToOverlap. -/
theorem normalizedClosure_le_overlap (t : F) :
    integralClosure (parameterRing (k := k) t) F ≤
      (integralClosure (overlapRing (k := k) t) F).restrictScalars (parameterRing (k := k) t) := by
  intro x hx
  exact hx.tower_top

/-- The actual integral-closure inclusion into the normalized overlap, retaining its raw ring
dictionaries. Named consumer: normalizedOverlap_isLocalization. -/
def normalizedToOverlap (t : F) :
    normalizedRing (k := k) t →+* normalizedOverlap (k := k) t :=
  (algebraMap (normalizedRing (k := k) t) F).codRestrict
    (normalizedOverlap (k := k) t) (fun x ↦ normalizedClosure_le_overlap t x.property)

/-- The algebra defined by the actual normalized-chart inclusion. Named consumer:
normalizedOverlap_isLocalization. -/
@[instance_reducible]
def normalizedOverlapAlgebra (t : F) :
    Algebra (normalizedRing (k := k) t) (normalizedOverlap (k := k) t) :=
  (normalizedToOverlap t).toAlgebra

attribute [local instance] normalizedOverlapAlgebra

/-- The original parameter ring, normalized chart and normalized overlap form the actual tower.
Named consumer: normalizedOverlap_isLocalization. -/
theorem normalized_overlap_parameter_tower (t : F) :
    IsScalarTower (parameterRing (k := k) t) (normalizedRing (k := k) t)
      (normalizedOverlap (k := k) t) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ Subtype.ext rfl)

end
end AclGeom.CurveCompletion
