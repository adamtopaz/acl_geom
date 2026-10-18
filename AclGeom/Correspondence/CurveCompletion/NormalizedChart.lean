/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ParameterOverlap
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Algebraic.Basic


/-!
# Normalized Chart

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
open scoped IntermediateField.algebraAdjoinAdjoin
universe u v
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- A transcendental parameter makes its actual polynomial subalgebra a PID. Named consumer:
normalizedRing_properties. -/
theorem parameterRing_isPrincipal (t : F) (ht : Transcendental k t) :
    IsPrincipalIdealRing (parameterRing (k := k) t) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t ht).toRingHom
    (Polynomial.algEquivOfTranscendental k t ht).surjective


/-- The integral closure of the actual polynomial parameter ring in the given field. Named consumer:
normalizedRing_properties. -/
abbrev normalizedRing (t : F) := integralClosure (parameterRing (k := k) t) F

/-- The original base-field algebra on the actual integral-closure ring. Named consumer:
chartBaseHom. -/
@[instance_reducible]
def normalizedBaseAlgebra (t : F) : Algebra k (normalizedRing (k := k) t) :=
  ((algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t)).comp
    (algebraMap k (parameterRing (k := k) t))).toAlgebra

/-- The actual normalization is finite over k[t], Dedekind and finite type over k, with the SAME
fraction field. Separating finiteness and separability are retained explicitly. Named consumer:
modelHom_isProper. -/
theorem normalizedRing_properties (t : F) (ht : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    letI := normalizedBaseAlgebra (k := k) t
    Module.Finite (parameterRing (k := k) t) (normalizedRing (k := k) t) ∧
    IsDedekindDomain (normalizedRing (k := k) t) ∧
    IsFractionRing (normalizedRing (k := k) t) F ∧
    Algebra.FiniteType k (normalizedRing (k := k) t) := by
  let := normalizedBaseAlgebra (k := k) t
  let : Algebra (parameterRing (k := k) t) (IntermediateField.adjoin k ({t} : Set F)) :=
    inferInstanceAs (Algebra (Algebra.adjoin k ({t} : Set F))
      (IntermediateField.adjoin k ({t} : Set F)))
  have : IsFractionRing (parameterRing (k := k) t)
      (IntermediateField.adjoin k ({t} : Set F)) :=
    inferInstanceAs (IsFractionRing (Algebra.adjoin k ({t} : Set F))
      (IntermediateField.adjoin k ({t} : Set F)))
  have : IsScalarTower (parameterRing (k := k) t)
      (IntermediateField.adjoin k ({t} : Set F)) F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k (parameterRing (k := k) t) (normalizedRing (k := k) t) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsPrincipalIdealRing (parameterRing (k := k) t) := parameterRing_isPrincipal t ht
  have : Module.Finite (parameterRing (k := k) t) (normalizedRing (k := k) t) :=
    IsIntegralClosure.finite (parameterRing (k := k) t)
      (IntermediateField.adjoin k ({t} : Set F)) F (normalizedRing (k := k) t)
  have : IsDedekindDomain (normalizedRing (k := k) t) :=
    IsIntegralClosure.isDedekindDomain (parameterRing (k := k) t)
      (IntermediateField.adjoin k ({t} : Set F)) F (normalizedRing (k := k) t)
  have : IsFractionRing (normalizedRing (k := k) t) F :=
    IsIntegralClosure.isFractionRing_of_finite_extension (parameterRing (k := k) t)
      (IntermediateField.adjoin k ({t} : Set F)) F (normalizedRing (k := k) t)
  have : Algebra.FiniteType k (parameterRing (k := k) t) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)
  have : Algebra.FiniteType k (normalizedRing (k := k) t) :=
    Algebra.FiniteType.trans (R := k) (S := parameterRing (k := k) t)
      (A := normalizedRing (k := k) t) inferInstance inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end
end AclGeom.CurveCompletion
