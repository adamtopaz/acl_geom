/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.InverseOverlap
/-!
# Inverse Tower

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
attribute [local instance] inverseOverlapAlgebra

set_option maxHeartbeats 600000 in
-- Extra deterministic kernel time compares the transported and literal subtype scalar
-- dictionaries; both algebras and their equality are fully checked.
/-- The transported inverse algebra equals the literal inclusion algebra. This equality compares the
actual scalar dictionaries. Named consumer: inverse_parameter_fraction_tower. -/
theorem inverseAlgebra_eq_inclusion (t : F) :
    inverseOverlapAlgebra (k := k) t = (inverseParameterToOverlap (k := k) t).toRingHom.toAlgebra :=
  Algebra.algebra_ext (inverseOverlapAlgebra (k := k) t)
    ((inverseParameterToOverlap (k := k) t).toRingHom.toAlgebra)
    (fun _ ↦ Subtype.ext rfl)

/-- The inverse-parameter inclusion and the given ambient field form the actual scalar tower. Named
consumer: inverseNormalizedOverlap_isLocalization. -/
theorem inverse_parameter_fraction_tower (t : F) :
    IsScalarTower (parameterRing (k := k) t⁻¹) (overlapRing (k := k) t) F := by
  let P (a : Algebra (parameterRing (k := k) t⁻¹) (overlapRing (k := k) t)) : Prop :=
    letI := a
    IsScalarTower (parameterRing (k := k) t⁻¹) (overlapRing (k := k) t) F
  have hcanon : P ((inverseParameterToOverlap (k := k) t).toRingHom.toAlgebra) :=
    Subalgebra.inclusion.isScalarTower_right (inverseParameterRing_le_overlapRing t) F
  exact (congrArg P (inverseAlgebra_eq_inclusion (k := k) t)).mpr hcanon

end
end AclGeom.CurveCompletion
