/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Approximation

/-!
# Finiteness of zeros: toward divisors

The finiteness theorem for the divisor layer (Stichtenoth Corollary
1.3.4): a nonzero element of a one-variable function field has finitely
many zero places, bounded by `[F : k(f)]`.

The engine is the **uniform order** of a `k(z)`-element: the exponent in
`v w = (v z)^m` depends only on `w` (it is the difference of root
multiplicities at `0` of a fixed rational presentation), not on the place
(`exists_uniform_valuation_zpow`). Consequently, in a vanishing
`k(f)`-combination of weak-approximation witnesses, the term of *minimal
order* strictly dominates at its own place — no normalization needed —
and the ultrametric sum lemma yields a contradiction
(`finite_setOf_valuation_lt_one`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P2).
-/

namespace AclGeom

open Polynomial IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section UniformOrder

variable {O : ValuationSubring F}

/-- Explicit form of the polynomial-value computation: the exponent is
the root multiplicity at `0`. -/
theorem valuation_aeval_eq_pow_rootMultiplicity
    (hk : ∀ c : k, algebraMap k F c ∈ O) {z : F}
    (hz : O.valuation z < 1) {p : Polynomial k} (hp : p ≠ 0) :
    O.valuation (aeval z p) = O.valuation z ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hq, hqnd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  rw [map_zero, sub_zero] at hq hqnd
  have hq0 : q.coeff 0 ≠ 0 := fun h ↦ hqnd (Polynomial.X_dvd_iff.2 h)
  conv_lhs => rw [hq]
  rw [map_mul, map_pow, aeval_X, Valuation.map_mul, Valuation.map_pow,
    valuation_aeval_eq_one hk hz hq0, mul_one]

/-- **The uniform order** of an element of `k(z)`: a single integer `m`
with `v w = (v z)^m` at *every* place where `z` is small. The exponent is
read off a fixed rational presentation of `w`, independently of the
place. -/
theorem exists_uniform_valuation_zpow {z w : F}
    (hztr : Transcendental k z) (hw : w ∈ adjoin k ({z} : Set F))
    (hw0 : w ≠ 0) :
    ∃ m : ℤ, ∀ O : ValuationSubring F,
      (∀ c : k, algebraMap k F c ∈ O) → O.valuation z < 1 →
      O.valuation w = O.valuation z ^ m := by
  have hz0 : z ≠ 0 := fun h ↦ hztr (h ▸ isAlgebraic_zero)
  rw [IntermediateField.mem_adjoin_simple_iff] at hw
  obtain ⟨p, q, hpq⟩ := hw
  have hq0 : aeval z q ≠ 0 := by
    intro h0
    rw [hpq, h0, div_zero] at hw0
    exact hw0 rfl
  have hp0 : aeval z p ≠ 0 := by
    intro h0
    rw [hpq, h0, zero_div] at hw0
    exact hw0 rfl
  have hpne : p ≠ 0 := fun h ↦ hp0 (by rw [h, map_zero])
  have hqne : q ≠ 0 := fun h ↦ hq0 (by rw [h, map_zero])
  refine ⟨(p.rootMultiplicity 0 : ℤ) - (q.rootMultiplicity 0 : ℤ),
    fun O hk hz ↦ ?_⟩
  have hzv : O.valuation z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  rw [hpq, map_div₀,
    valuation_aeval_eq_pow_rootMultiplicity hk hz hpne,
    valuation_aeval_eq_pow_rootMultiplicity hk hz hqne,
    zpow_sub₀ hzv, zpow_natCast, zpow_natCast]

end UniformOrder

section Finiteness

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **Finiteness of zeros** (Stichtenoth Corollary 1.3.4): a nonzero
element of a one-variable function field has finitely many zero places.
Weak-approximation witnesses at distinct zeros are `k(f)`-linearly
independent — the minimal-uniform-order term dominates at its own
place — so the number of zeros is bounded by `[F : k(f)]`. -/
theorem finite_setOf_valuation_lt_one {f : F} (hf0 : f ≠ 0) :
    {P : Place k F | P.val.valuation f < 1}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- `f` is transcendental: it has a zero place.
  obtain ⟨P₁, hP₁⟩ := hinf.nonempty
  have htr : Transcendental k f :=
    transcendental_of_valuation_lt_one P₁.algebraMap_mem
      (fun y hy ↦ exists_algebraMap_eq_of_isAlgebraic hy) hf0 hP₁
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  set n := Module.finrank (↥(adjoin k ({f} : Set F))) F with hn
  -- Extract `n + 1` distinct zero places.
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (n + 1)
  set P : Fin (n + 1) → Place k F :=
    fun i ↦ (T.equivFin.symm (Fin.cast hTcard.symm i) : Place k F)
    with hPdef
  have hPinj : Function.Injective P := by
    intro i j hij
    have h1 := Subtype.ext hij
    have h2 := T.equivFin.symm.injective h1
    exact Fin.val_injective (by simpa using congrArg Fin.val h2)
  have hPzero : ∀ i, (P i).val.valuation f < 1 := fun i ↦
    hTsub (Finset.coe_mem _)
  -- Weak-approximation witnesses at each place.
  have hzex : ∀ i : Fin (n + 1), ∃ z : F,
      1 < (P i).val.valuation z ∧
      ∀ j : Fin n, (P (i.succAbove j)).val.valuation z < 1 := fun i ↦
    (P i).exists_one_lt_forall_lt_one (fun j ↦ P (i.succAbove j))
      (fun j ↦ fun h ↦ (Fin.succAbove_ne i j) (hPinj h).symm)
  choose z hz₁ hz₂ using hzex
  -- Values of the witnesses at all the places.
  have hzsmall : ∀ i i' : Fin (n + 1), i' ≠ i →
      (P i').val.valuation (z i) < 1 := by
    intro i i' hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have h1 := hz₂ i j
    rwa [hj] at h1
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h0
    have h1 := hz₁ i
    rw [h0, Valuation.map_zero] at h1
    simp at h1
  -- The witnesses are linearly independent over `k(f)`.
  have hind : LinearIndependent (↥(adjoin k ({f} : Set F))) z := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum i₀'
    by_contra hg₀
    set s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i ↦ g i ≠ 0)
      with hsdef
    have hi₀s : i₀' ∈ s := by simp [hsdef, hg₀]
    have hcoe0 : ∀ i ∈ s, ((g i : F)) ≠ 0 := by
      intro i hi
      rw [hsdef, Finset.mem_filter] at hi
      simpa using hi.2
    -- Uniform orders of the coefficients.
    have hords : ∀ i ∈ s, ∃ m : ℤ, ∀ O : ValuationSubring F,
        (∀ c : k, algebraMap k F c ∈ O) → O.valuation f < 1 →
        O.valuation ((g i : F)) = O.valuation f ^ m := by
      intro i hi
      exact exists_uniform_valuation_zpow htr (SetLike.coe_mem (g i))
        (hcoe0 i hi)
    choose! m hm using hords
    -- The index of minimal order dominates at its own place.
    obtain ⟨i₀, hi₀, hi₀min⟩ := s.exists_min_image m ⟨i₀', hi₀s⟩
    set Q := P i₀ with hQdef
    have hQz : Q.val.valuation f < 1 := hPzero i₀
    have hfv : Q.val.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf0
    have hfvpos : (0 : _) < Q.val.valuation f := zero_lt_iff.2 hfv
    have hdom : ∀ i ∈ s, i ≠ i₀ →
        Q.val.valuation ((g i : F) * z i) <
          Q.val.valuation ((g i₀ : F) * z i₀) := by
      intro i hi hne
      rw [Valuation.map_mul, Valuation.map_mul,
        hm i hi Q.val Q.algebraMap_mem hQz,
        hm i₀ hi₀ Q.val Q.algebraMap_mem hQz]
      have h1 : Q.val.valuation f ^ m i ≤ Q.val.valuation f ^ m i₀ :=
        zpow_le_zpow_right_of_le_one₀ hfvpos hQz.le (hi₀min i hi)
      have h2 : Q.val.valuation (z i) < 1 := hzsmall i i₀ hne.symm
      have h3 : (1 : _) < Q.val.valuation (z i₀) := hz₁ i₀
      calc Q.val.valuation f ^ m i * Q.val.valuation (z i)
          ≤ Q.val.valuation f ^ m i₀ * Q.val.valuation (z i) := by
            rcases eq_or_ne (Q.val.valuation (z i)) 0 with hz' | hz'
            · rw [hz', mul_zero, mul_zero]
            · exact (OrderIso.mulRight₀ _ (zero_lt_iff.2 hz')).monotone h1
        _ < Q.val.valuation f ^ m i₀ * 1 := by
            refine (OrderIso.mulLeft₀ _ (zero_lt_iff.2 ?_)).strictMono h2
            exact zpow_ne_zero _ hfv
        _ < Q.val.valuation f ^ m i₀ * Q.val.valuation (z i₀) := by
            refine (OrderIso.mulLeft₀ _ (zero_lt_iff.2 ?_)).strictMono h3
            exact zpow_ne_zero _ hfv
    -- The dominant term makes the vanishing sum nonzero.
    have hss : ∑ i ∈ s, (g i : F) * z i = 0 := by
      rw [← hsum]
      rw [show ∑ i : Fin (n + 1), g i • z i =
          ∑ i : Fin (n + 1), (g i : F) * z i from
        Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def]; rfl]
      refine Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ ?_
      rw [hsdef, Finset.mem_filter, not_and, not_not] at hi
      rw [hi (Finset.mem_univ i), ZeroMemClass.coe_zero, zero_mul]
    have h0 := valuation_sum_eq_of_forall_lt (f := fun i ↦ (g i : F) * z i)
      hi₀ hdom
    rw [hss, Valuation.map_zero] at h0
    have h4 : Q.val.valuation ((g i₀ : F) * z i₀) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact mul_ne_zero (hcoe0 i₀ hi₀) (hz0 i₀)
    exact h4 h0.symm
  -- The independence contradicts the finrank bound.
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

/-- Finiteness of poles: the zeros of the inverse. -/
theorem finite_setOf_one_lt_valuation {f : F} (hf0 : f ≠ 0) :
    {P : Place k F | 1 < P.val.valuation f}.Finite := by
  have h1 := finite_setOf_valuation_lt_one (k := k) (inv_ne_zero hf0)
  refine h1.subset fun P hP ↦ ?_
  rw [Set.mem_setOf_eq, map_inv₀]
  rw [Set.mem_setOf_eq] at hP
  have hfv : P.val.valuation f ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hf0
  rw [inv_lt_one₀ (zero_lt_iff.2 hfv)]
  exact hP

end Finiteness

end

end AclGeom
