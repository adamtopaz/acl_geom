/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import AclGeom.Curves.DerivationExtension
import Mathlib.Tactic.FinCases

/-!
# Base change of independent derivations

Let `F` and `K` be field extensions of `C` with `K ⊗[C] F` a domain. Two `C`-linearly
independent `C`-derivations of `F` extend to two `K`-linearly independent `K`-derivations of
`Frac(K ⊗[C] F)` acting on `1 ⊗ F` as before (`exists_linearIndependent_derivations_baseChange`).

Each derivation is first extended to the pushout `K ⊗[C] F`, killing `K`, and then to its
fraction field through the formally étale localization. Independence is checked on `1 ⊗ F`
using a `C`-basis of `K`.

In the genus argument `F` is the function field of the curve over the coefficient field `C`,
and the derivations are the `C`-linear curve variations. They are not derivations of `C`, which
are never extended to the ambient field.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

open TensorProduct

noncomputable section


variable {C K F : Type*} [Field C] [Field K] [Field F] [Algebra C K] [Algebra C F]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base change to `Frac(K ⊗[C] F)` of a `C`-derivation of `F`, killing `K`. -/
private def baseChangeDerivation [IsDomain (K ⊗[C] F)] (D : Derivation C F F) :
    Derivation K (FractionRing (K ⊗[C] F)) (FractionRing (K ⊗[C] F)) :=
  ((Algebra.linearMap (K ⊗[C] F) (FractionRing (K ⊗[C] F))).compDer
    (D.extendOfPushout K (K ⊗[C] F))).extendOfFormallyEtale

private theorem baseChangeDerivation_one_tmul [IsDomain (K ⊗[C] F)] (D : Derivation C F F)
    (f : F) :
    baseChangeDerivation (K := K) D (algebraMap (K ⊗[C] F) _ ((1 : K) ⊗ₜ f)) =
      algebraMap (K ⊗[C] F) _ ((1 : K) ⊗ₜ D f) := by
  rw [baseChangeDerivation, Derivation.extendOfFormallyEtale_algebraMap]
  change algebraMap (K ⊗[C] F) _ (D.extendOfPushout K (K ⊗[C] F)
    (algebraMap F (K ⊗[C] F) f)) = _
  rw [Derivation.extendOfPushout_algebraMap]
  rfl

/-- **Base change of independent derivations.** Two `C`-linearly independent derivations of
`F` over `C` extend to two `K`-linearly independent derivations of `Frac(K ⊗[C] F)` over `K`,
acting on `1 ⊗ F` as before. -/
theorem exists_linearIndependent_derivations_baseChange [IsDomain (K ⊗[C] F)]
    (D : Fin 2 → Derivation C F F) (hD : LinearIndependent C D) :
    ∃ D' : Fin 2 → Derivation K (FractionRing (K ⊗[C] F)) (FractionRing (K ⊗[C] F)),
      LinearIndependent K D' ∧ ∀ i f, D' i (algebraMap (K ⊗[C] F) _ ((1 : K) ⊗ₜ f)) =
        algebraMap (K ⊗[C] F) _ ((1 : K) ⊗ₜ D i f) := by
  classical
  refine ⟨fun i ↦ baseChangeDerivation (D i), ?_, fun i f ↦ baseChangeDerivation_one_tmul (D i) f⟩
  have hD2 : D = ![D 0, D 1] := by
    ext i : 1
    fin_cases i <;> rfl
  have hpair : LinearIndependent C ![D 0, D 1] := by
    rw [← hD2]
    exact hD
  have hfun : (fun i ↦ baseChangeDerivation (K := K) (D i)) =
      ![baseChangeDerivation (D 0), baseChangeDerivation (D 1)] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [hfun, LinearIndependent.pair_iff]
  intro a b hab
  let β := Module.Basis.ofVectorSpace C K
  have hmul : ∀ (c : K) (g : F), algebraMap K (K ⊗[C] F) c * ((1 : K) ⊗ₜ g) = c ⊗ₜ g := by
    intro c g
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  -- The relation holds on every `1 ⊗ f`.
  have hf : ∀ f : F, a ⊗ₜ[C] D 0 f + b ⊗ₜ[C] D 1 f = 0 := by
    intro f
    apply IsFractionRing.injective (K ⊗[C] F) (FractionRing (K ⊗[C] F))
    have h := congrArg (fun D' : Derivation K (FractionRing (K ⊗[C] F))
      (FractionRing (K ⊗[C] F)) ↦ D' (algebraMap (K ⊗[C] F) _ ((1 : K) ⊗ₜ f))) hab
    simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.zero_apply,
      baseChangeDerivation_one_tmul] at h
    rw [Algebra.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply K (K ⊗[C] F) (FractionRing (K ⊗[C] F)) a,
      IsScalarTower.algebraMap_apply K (K ⊗[C] F) (FractionRing (K ⊗[C] F)) b, ← map_mul,
      ← map_mul, hmul, hmul, ← map_add] at h
    rw [h, map_zero]
  -- Hence every coordinate along a `C`-basis of `K` vanishes.
  have hcomp : ∀ j, β.repr a j = 0 ∧ β.repr b j = 0 := by
    intro j
    apply LinearIndependent.pair_iff.1 hpair
    ext f
    have h := congrArg (fun x ↦ TensorProduct.equivFinsuppOfBasisLeft β x j) (hf f)
    simp only [map_add, Finsupp.add_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      map_zero, Finsupp.zero_apply] at h
    simpa only [Derivation.add_apply, Derivation.smul_apply, Derivation.zero_apply] using h
  exact ⟨β.repr.map_eq_zero_iff.1 (Finsupp.ext fun j ↦ (hcomp j).1),
    β.repr.map_eq_zero_iff.1 (Finsupp.ext fun j ↦ (hcomp j).2)⟩

end

end AclGeom
