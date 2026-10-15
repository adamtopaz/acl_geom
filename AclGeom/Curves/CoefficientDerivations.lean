/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Field
import AclGeom.Curves.DerivationExtension

/-!
# Independent derivations of a finitely generated field

Let `C` be a finitely generated field extension of a perfect field `k`, of transcendence degree
at least two. Then `C` has two `C`-linearly independent `k`-derivations
(`exists_linearIndependent_derivations`).

The derivations are the partial derivatives along a separating transcendence basis `s`. They
are defined on `k[s]`, extended to `k(s)` through the formally étale localization, and then
to `C` through the separable algebraic, hence formally étale, extension `C / k(s)`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

open MvPolynomial

noncomputable section


variable {k C : Type*} [Field k] [Field C] [Algebra k C]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

/-- The partial derivative `∂/∂Xᵢ` on the rational function field `k(X)`. -/
private def ratDerivation {σ : Type*} (i : σ) :
    Derivation k (FractionRing (MvPolynomial σ k)) (FractionRing (MvPolynomial σ k)) :=
  ((Algebra.linearMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))).compDer
    (pderiv i)).extendOfFormallyEtale

private theorem ratDerivation_X_self {σ : Type*} (i : σ) :
    ratDerivation (k := k) i
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (X i)) = 1 := by
  rw [ratDerivation, Derivation.extendOfFormallyEtale_algebraMap]
  change algebraMap (MvPolynomial σ k) _ (pderiv i (X i)) = _
  rw [pderiv_X_self, map_one]

private theorem ratDerivation_X_of_ne {σ : Type*} {i j : σ} (h : i ≠ j) :
    ratDerivation (k := k) i
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (X j)) = 0 := by
  rw [ratDerivation, Derivation.extendOfFormallyEtale_algebraMap]
  change algebraMap (MvPolynomial σ k) _ (pderiv i (X j)) = _
  rw [pderiv_X_of_ne (Ne.symm h), map_zero]

/-- The rational function field on a transcendence basis `s`, as the subfield `k(s)`. -/
private def basisEquiv (s : Finset C) (hs : AlgebraicIndependent k ((↑) : s → C)) :
    FractionRing (MvPolynomial s k) ≃ₐ[k] IntermediateField.adjoin k (s : Set C) :=
  hs.aevalEquivField.trans (IntermediateField.equivOfEq (by congr 1; ext; simp))

private theorem basisEquiv_X (s : Finset C) (hs : AlgebraicIndependent k ((↑) : s → C))
    (j : s) : basisEquiv s hs
      (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (X j)) =
      ⟨j, IntermediateField.subset_adjoin k _ j.2⟩ := by
  apply Subtype.ext
  change ((hs.aevalEquivField
      (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (X j)) :
    IntermediateField.adjoin k (Set.range ((↑) : s → C))) : C) = j
  rw [hs.aevalEquivField_algebraMap_apply_coe, aeval_X]

/-- The partial derivative `∂/∂j` along a separating transcendence basis `s`. -/
private def basisDerivation (s : Finset C) (hs : AlgebraicIndependent k ((↑) : s → C))
    [Algebra.IsSeparable (IntermediateField.adjoin k (s : Set C)) C] (i : s) :
    Derivation k C C :=
  ((Algebra.linearMap (IntermediateField.adjoin k (s : Set C)) C).compDer
    ((ratDerivation i).transport (basisEquiv s hs))).extendOfFormallyEtale

private theorem basisDerivation_apply (s : Finset C)
    (hs : AlgebraicIndependent k ((↑) : s → C))
    [Algebra.IsSeparable (IntermediateField.adjoin k (s : Set C)) C] (i j : s) :
    basisDerivation s hs i (j : C) = algebraMap (IntermediateField.adjoin k (s : Set C)) C
      (basisEquiv s hs (ratDerivation i
        (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (X j)))) := by
  have hj : (j : C) = algebraMap (IntermediateField.adjoin k (s : Set C)) C
      ⟨j, IntermediateField.subset_adjoin k _ j.2⟩ := rfl
  rw [hj, basisDerivation, Derivation.extendOfFormallyEtale_algebraMap]
  change algebraMap (IntermediateField.adjoin k (s : Set C)) C
    ((ratDerivation i).transport (basisEquiv s hs) ⟨j, _⟩) = _
  rw [Derivation.transport_apply, ← basisEquiv_X s hs j, AlgEquiv.symm_apply_apply]

private theorem basisDerivation_apply_self (s : Finset C)
    (hs : AlgebraicIndependent k ((↑) : s → C))
    [Algebra.IsSeparable (IntermediateField.adjoin k (s : Set C)) C] (i : s) :
    basisDerivation s hs i (i : C) = 1 := by
  rw [basisDerivation_apply, ratDerivation_X_self, map_one, map_one]

private theorem basisDerivation_apply_of_ne (s : Finset C)
    (hs : AlgebraicIndependent k ((↑) : s → C))
    [Algebra.IsSeparable (IntermediateField.adjoin k (s : Set C)) C] {i j : s} (h : i ≠ j) :
    basisDerivation s hs i (j : C) = 0 := by
  rw [basisDerivation_apply, ratDerivation_X_of_ne h, map_zero, map_zero]

/-- Two derivations dual to two elements of a separating transcendence basis. -/
private theorem exists_derivations_dual [PerfectField k] [Algebra.EssFiniteType k C]
    (h : 2 ≤ Algebra.trdeg k C) :
    ∃ (a b : C) (D₀ D₁ : Derivation k C C), D₀ a = 1 ∧ D₀ b = 0 ∧ D₁ a = 0 ∧ D₁ b = 1 := by
  classical
  obtain ⟨s, hs, _⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k C
  have h2 : (2 : Cardinal) ≤ (s.card : Cardinal) := by
    rw [← Cardinal.mk_coe_finset, hs.cardinalMk_eq_trdeg]
    exact h
  have hcard : 1 < s.card := by
    have : 2 ≤ s.card := by exact_mod_cast h2
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  have hne : (⟨a, ha⟩ : s) ≠ ⟨b, hb⟩ := fun e ↦ hab (congrArg Subtype.val e)
  refine ⟨a, b, basisDerivation s hs.1 ⟨a, ha⟩, basisDerivation s hs.1 ⟨b, hb⟩, ?_, ?_, ?_, ?_⟩
  · exact basisDerivation_apply_self s hs.1 ⟨a, ha⟩
  · exact basisDerivation_apply_of_ne s hs.1 (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) hne
  · exact basisDerivation_apply_of_ne s hs.1 (i := ⟨b, hb⟩) (j := ⟨a, ha⟩) hne.symm
  · exact basisDerivation_apply_self s hs.1 ⟨b, hb⟩

/-- **Two independent derivations.** A finitely generated field extension of a perfect field
of transcendence degree at least two has two linearly independent derivations. -/
theorem exists_linearIndependent_derivations [PerfectField k] [Algebra.EssFiniteType k C]
    (h : 2 ≤ Algebra.trdeg k C) : ∃ D : Fin 2 → Derivation k C C, LinearIndependent C D := by
  obtain ⟨a, b, D₀, D₁, h₀a, h₀b, h₁a, h₁b⟩ := exists_derivations_dual h
  refine ⟨![D₀, D₁], LinearIndependent.pair_iff.2 fun c d hcd ↦ ?_⟩
  have ha := congrArg (fun D : Derivation k C C ↦ D a) hcd
  have hb := congrArg (fun D : Derivation k C C ↦ D b) hcd
  simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.zero_apply, h₀a, h₁a, h₀b,
    h₁b, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at ha hb
  exact ⟨ha, hb⟩

end

end AclGeom
