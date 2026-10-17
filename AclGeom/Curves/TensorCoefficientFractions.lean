/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction-field compatibility of effective tensor actions

Named consumer: the actual effective-field action on the curve function field.

**Status:** proved; the actual consumer is `SchemeEffectiveFunctionField`.
-/

namespace AclGeom.TensorCoefficientDescent

noncomputable section

open scoped TensorProduct

universe u

variable {k C R : Type u} [Field k] [Field C] [Algebra k C]
  [CommRing R] [Algebra k R] [IsDomain (C ⊗[k] R)]

/-- Extend a descended tensor action to fraction fields, deriving the smaller tensor domain
and retaining its literal embedding and comparison. Named consumer: the actual regular
scheme action on the formal extension of its function field. -/
theorem exists_fractionTensorAut_comparison (C0 : IntermediateField k C)
    (τ : C0 ⊗[k] R ≃ₐ[C0] C0 ⊗[k] R)
    (σ : C ⊗[k] R ≃ₐ[C] C ⊗[k] R)
    (h : ∀ x, Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R) (τ x) =
      σ (Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R) x)) :
    ∃ h0 : IsDomain (C0 ⊗[k] R),
      letI := h0
      ∃ (J : FractionRing (C0 ⊗[k] R) →ₐ[C0] FractionRing (C ⊗[k] R))
        (τF : FractionRing (C0 ⊗[k] R) ≃ₐ[C0] FractionRing (C0 ⊗[k] R)),
        Function.Injective J ∧
        (∀ x, J (algebraMap (C0 ⊗[k] R) _ x) =
          algebraMap (C ⊗[k] R) _
            (Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R) x)) ∧
        (∀ x, τF (algebraMap (C0 ⊗[k] R) _ x) =
          algebraMap (C0 ⊗[k] R) _ (τ x)) ∧
        ∀ x, J (τF x) =
          (IsFractionRing.algEquivOfAlgEquiv σ :
            FractionRing (C ⊗[k] R) ≃ₐ[C] FractionRing (C ⊗[k] R)) (J x) := by
  let j : C0 ⊗[k] R →ₐ[C0] C ⊗[k] R :=
    Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R)
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) C0.val.toLinearMap
      C0.val.injective
  have : IsDomain (C0 ⊗[k] R) := Function.Injective.isDomain j hj
  let ψ : C0 ⊗[k] R →ₐ[C0] FractionRing (C ⊗[k] R) :=
    (IsScalarTower.toAlgHom C0 (C ⊗[k] R) (FractionRing (C ⊗[k] R))).comp j
  have hψ : Function.Injective ψ :=
    (IsFractionRing.injective (C ⊗[k] R) (FractionRing (C ⊗[k] R))).comp hj
  let J : FractionRing (C0 ⊗[k] R) →ₐ[C0] FractionRing (C ⊗[k] R) :=
    IsFractionRing.liftAlgHom hψ
  let τF : FractionRing (C0 ⊗[k] R) ≃ₐ[C0] FractionRing (C0 ⊗[k] R) :=
    IsFractionRing.algEquivOfAlgEquiv τ
  let σF : FractionRing (C ⊗[k] R) ≃ₐ[C] FractionRing (C ⊗[k] R) :=
    IsFractionRing.algEquivOfAlgEquiv σ
  have hJ (x : C0 ⊗[k] R) : J (algebraMap (C0 ⊗[k] R) _ x) =
      algebraMap (C ⊗[k] R) _ (j x) :=
    IsFractionRing.lift_algebraMap hψ x
  have hτF (x : C0 ⊗[k] R) : τF (algebraMap (C0 ⊗[k] R) _ x) =
      algebraMap (C0 ⊗[k] R) _ (τ x) :=
    IsFractionRing.algEquivOfAlgEquiv_algebraMap τ x
  have hσF (x : C ⊗[k] R) : σF (algebraMap (C ⊗[k] R) _ x) =
      algebraMap (C ⊗[k] R) _ (σ x) :=
    IsFractionRing.algEquivOfAlgEquiv_algebraMap σ x
  refine ⟨inferInstance, J, τF, J.injective, hJ, hτF, ?_⟩
  have hcomm : J.comp τF.toAlgHom = (σF.restrictScalars C0).toAlgHom.comp J := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (C0 ⊗[k] R))
    apply AlgHom.ext
    intro x
    change J (τF (algebraMap (C0 ⊗[k] R) _ x)) =
      σF (J (algebraMap (C0 ⊗[k] R) _ x))
    rw [hτF, hJ, hJ, hσF]
    exact congrArg (algebraMap (C ⊗[k] R) (FractionRing (C ⊗[k] R))) (h x)
  exact fun x ↦ AlgHom.congr_fun hcomm x

end

end AclGeom.TensorCoefficientDescent
