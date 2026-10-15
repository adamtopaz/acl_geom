/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Extending and transporting derivations

* `Derivation.extendOfFormallyEtale`: a derivation `A → B` extends to a derivation of `B`
  along a formally étale algebra `A → B`.
* `Derivation.extendOfPushout`: a derivation of `A` extends to the pushout `B` of `S` and `A`,
  killing `S`.
* `Derivation.transport`: a derivation transported along an algebra isomorphism.

The extensions are built from Kähler differentials, using
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` and
`KaehlerDifferential.tensorKaehlerEquiv`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#21). Shared by the constant extension steps of the genus argument.
-/

namespace Derivation

noncomputable section

section FormallyEtale

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra.FormallyEtale A B]

/-- Extend a derivation `A → B` to a derivation of `B`, along a formally étale `A → B`. -/
def extendOfFormallyEtale (D : Derivation R A B) : Derivation R B B :=
  ((D.liftKaehlerDifferential.liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap).compDer
      (KaehlerDifferential.D R B)

@[simp]
theorem extendOfFormallyEtale_algebraMap (D : Derivation R A B) (a : A) :
    D.extendOfFormallyEtale (algebraMap A B a) = D a := by
  change D.liftKaehlerDifferential.liftBaseChange B
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm
      (KaehlerDifferential.D R B (algebraMap A B a))) = D a
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

end FormallyEtale

section Pushout

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]

variable (S B) in
/-- Extend a derivation of `A` to the pushout `B` of `S` and `A`, killing `S`. -/
def extendOfPushout (D : Derivation R A A) : Derivation S B B :=
  ((((Algebra.linearMap A B).compDer D).liftKaehlerDifferential.liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm.toLinearMap).compDer
      (KaehlerDifferential.D S B)

@[simp]
theorem extendOfPushout_algebraMap (D : Derivation R A A) (a : A) :
    D.extendOfPushout S B (algebraMap A B a) = algebraMap A B (D a) := by
  change ((Algebra.linearMap A B).compDer D).liftKaehlerDifferential.liftBaseChange B
    ((KaehlerDifferential.tensorKaehlerEquiv R S A B).symm
      (KaehlerDifferential.D S B (algebraMap A B a))) = algebraMap A B (D a)
  have he : (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm
      (KaehlerDifferential.D S B (algebraMap A B a)) =
        (1 : B) ⊗ₜ[A] KaehlerDifferential.D R A a := by
    apply (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm_apply_eq.mpr
    simp only [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]
  rw [he, LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end Pushout

section Transport

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Transport a derivation along an algebra isomorphism. -/
def transport (D : Derivation R A A) (e : A ≃ₐ[R] B) : Derivation R B B where
  toFun y := e (D (e.symm y))
  map_add' x y := by simp only [_root_.map_add]
  map_smul' r x := by
    simp only [_root_.map_smul, Derivation.map_smul, RingHom.id_apply]
  map_one_eq_zero' := by
    change e (D (e.symm 1)) = 0
    rw [_root_.map_one, D.map_one_eq_zero, _root_.map_zero]
  leibniz' x y := by
    change e (D (e.symm (x * y))) = x • e (D (e.symm y)) + y • e (D (e.symm x))
    simp only [_root_.map_mul, Derivation.leibniz, _root_.map_add, smul_eq_mul,
      AlgEquiv.apply_symm_apply]

theorem transport_apply (D : Derivation R A A) (e : A ≃ₐ[R] B) (y : B) :
    D.transport e y = e (D (e.symm y)) := rfl

@[simp]
theorem transport_apply_apply (D : Derivation R A A) (e : A ≃ₐ[R] B) (x : A) :
    D.transport e (e x) = e (D x) := by
  rw [transport_apply, AlgEquiv.symm_apply_apply]

/-- Transport along an algebra isomorphism, as a linear map of derivation modules. -/
def transportLinear (e : A ≃ₐ[R] B) : Derivation R A A →ₗ[R] Derivation R B B where
  toFun D := D.transport e
  map_add' D₁ D₂ := by
    ext y
    exact _root_.map_add e _ _
  map_smul' c D := by
    ext y
    exact _root_.map_smul e c _

@[simp]
theorem transportLinear_apply (e : A ≃ₐ[R] B) (D : Derivation R A A) :
    transportLinear e D = D.transport e := rfl

theorem transportLinear_injective (e : A ≃ₐ[R] B) :
    Function.Injective (transportLinear e) := by
  intro D₁ D₂ h
  ext x
  apply e.injective
  have hx := Derivation.congr_fun h (e x)
  simpa only [transportLinear_apply, transport_apply_apply] using hx

end Transport

end

end Derivation
