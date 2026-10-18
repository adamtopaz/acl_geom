/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ParameterOverlap
/-!
# Inverse Overlap

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

/-- Inverting the parameter leaves the literal Laurent overlap unchanged. Named consumer:
inverseOverlapRingEquiv. -/
theorem overlapRing_inv (t : F) : overlapRing (k := k) t⁻¹ = overlapRing (k := k) t := by
  change Algebra.adjoin k ({t⁻¹, (t⁻¹)⁻¹} : Set F) = Algebra.adjoin k ({t, t⁻¹} : Set F)
  rw [inv_inv, Set.pair_comm]

/-- The inverse-parameter polynomial ring lies in the SAME Laurent overlap. Named consumer:
inverseParameterToOverlap. -/
theorem inverseParameterRing_le_overlapRing (t : F) :
    parameterRing (k := k) t⁻¹ ≤ overlapRing (k := k) t :=
  Algebra.adjoin_mono (Set.singleton_subset_iff.mpr
    (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The literal inclusion from the inverse-parameter polynomial ring. Named consumer:
inverseAlgebra_eq_inclusion. -/
def inverseParameterToOverlap (t : F) :
    parameterRing (k := k) t⁻¹ →ₐ[k] overlapRing (k := k) t :=
  Subalgebra.inclusion (inverseParameterRing_le_overlapRing t)

/-- The ring equivalence identifying the two presentations of the SAME overlap. Named consumer:
inverseOverlapAlgebra. -/
def inverseOverlapRingEquiv (t : F) :
    overlapRing (k := k) t⁻¹ ≃+* overlapRing (k := k) t :=
  (Subalgebra.equivOfEq _ _ (overlapRing_inv (k := k) t)).toRingEquiv

/-- The inverse parameter's actual transported algebra on the overlap. Named consumer:
inverseNormalizedOverlap_isLocalization. -/
@[instance_reducible]
def inverseOverlapAlgebra (t : F) :
    Algebra (parameterRing (k := k) t⁻¹) (overlapRing (k := k) t) :=
  ((inverseOverlapRingEquiv t).toRingHom.comp (parameterToOverlap (k := k) t⁻¹).toRingHom).toAlgebra

/-- The SAME literal overlap is also the principal localization of the inverse chart.
Named consumer: the actual two-chart proper-normal completion atlas. -/
theorem inverse_overlap_isLocalization (t : F) (ht : t ≠ 0) :
    let := inverseOverlapAlgebra (k := k) t
    IsLocalization.Away (parameter (k := k) t⁻¹) (overlapRing (k := k) t) := by
  let := overlapAlgebra (k := k) t⁻¹
  let := inverseOverlapAlgebra (k := k) t
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (M := Submonoid.powers (parameter (k := k) t⁻¹)) (inverseOverlapRingEquiv t)).mp
      (overlap_isLocalization (k := k) t⁻¹ (inv_ne_zero ht))

end
end AclGeom.CurveCompletion
