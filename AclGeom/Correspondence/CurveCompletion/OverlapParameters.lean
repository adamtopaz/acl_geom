/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedAtlas
/-!
# Overlap Parameters

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
universe u v w
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
attribute [local instance] normalizedOverlapAlgebra inverseNormalizedOverlapAlgebra

/-- The literal parameter as an element of its actual integral-closure chart. Named consumer:
chartParameter. -/
abbrev normalizedParameter (t : F) : normalizedRing (k := k) t :=
  algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t) (parameter t)

/-- The literal parameters from the two normalization charts multiply to one in the SAME overlap.
Named consumer: chart_parameters_mul. -/
theorem overlap_parameters_mul (t : F) (ht : t ≠ 0) :
    normalizedToOverlap (k := k) t (normalizedParameter t) *
      inverseNormalizedToOverlap (k := k) t (normalizedParameter t⁻¹) = 1 := by
  apply Subtype.ext
  exact mul_inv_cancel₀ ht

end
end AclGeom.CurveCompletion
