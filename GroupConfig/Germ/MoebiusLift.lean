/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.MoebiusAction
import Mathlib.Data.Fintype.Parity
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Determinant-one lifts of the fractional linear Hrushovski–Weil action

Let `t` generate the function field of a curve carrying a Hrushovski–Weil datum. A matrix
`m ∈ SL₂(K)` lifts the action of a group member `γ` in the coordinate `t` if
`γ · t = (m₀₀ t + m₀₁) / (m₁₀ t + m₁₁)` (`GroupConfig.Germ.IsHW.IsMoebiusLift`).

Every member has a lift (`GroupConfig.Germ.IsHW.exists_generator_isMoebiusLift`), two lifts of
the same member differ by a sign (`IsMoebiusLift.eq_or_eq_neg`), lifts compose in the reversed
order (`IsMoebiusLift.mul`), and a lift determines its member (`IsMoebiusLift.injective`). These
hold in every characteristic.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

The complete actual constructible-lift consumer is
`GroupConfig.Germ.IsHWBij.exists_constructible_slLift`. These finite lifts supply an auxiliary
prerequisite for `lem:affine-action` in `sources/blueprint.tex`.

**Status:** the lifts, sign ambiguity and reversed composition are proved (#21). The actual
constructibility and rank comparison are proved in `GroupConfig.Constructible.SLLift`; the
affine classification and original scheme/action obligations remain open.
-/

namespace GroupConfig

open AclGeom Set Matrix
open scoped MatrixGroups

noncomputable section

/-! ### Linear forms in a transcendental element -/

section Transcendental

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {t : L}

/-- A quadratic relation over `K` in a transcendental element is trivial. -/
private theorem eq_zero_of_quadratic (ht : Transcendental K t) {α β γ : K}
    (h : algebraMap K L α * t ^ 2 + algebraMap K L β * t + algebraMap K L γ = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hp : Polynomial.aeval t
      (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ) = 0 := by
    simpa only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] using h
  have h0 := (transcendental_iff.1 ht) _ hp
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (Polynomial.coeff · 2) h0
  · simpa using congrArg (Polynomial.coeff · 1) h0
  · simpa using congrArg (Polynomial.coeff · 0) h0

/-- A nonzero linear form in a transcendental element is nonzero. -/
private theorem linear_ne_zero (ht : Transcendental K t) {c d : K} (hcd : c ≠ 0 ∨ d ≠ 0) :
    algebraMap K L c * t + algebraMap K L d ≠ 0 := by
  intro h
  have h' : algebraMap K L 0 * t ^ 2 + algebraMap K L c * t + algebraMap K L d = 0 := by
    rw [map_zero, zero_mul, zero_add, h]
  obtain ⟨-, hc, hd⟩ := eq_zero_of_quadratic ht h'
  exact hcd.elim (· hc) (· hd)

/-- The bottom row of a determinant-one matrix gives a nonzero linear form. -/
private theorem row_ne_zero (ht : Transcendental K t) (m : SL(2, K)) :
    algebraMap K L (m 1 0) * t + algebraMap K L (m 1 1) ≠ 0 := by
  refine linear_ne_zero ht ?_
  by_contra! h
  have hdet := m.det_coe
  rw [det_fin_two, h.1, h.2] at hdet
  simp at hdet

/-- Automorphisms agreeing on a generator agree. -/
private theorem algEquiv_ext_of_adjoin_eq_top (htop : IntermediateField.adjoin K {t} = ⊤)
    {φ ψ : L ≃ₐ[K] L} (h : φ t = ψ t) : φ = ψ := by
  refine AlgEquiv.ext fun x ↦ ?_
  have hx : x ∈ IntermediateField.adjoin K {t} := by
    rw [htop]
    trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [mem_singleton_iff.1 hx]
    exact h
  | algebraMap x => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end Transcendental

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

namespace Germ.IsHW

variable {g₀ : Germ k v v} (hw : IsHW g₀) (hv : erk k ∅ (range v) = 1)

/-- `m ∈ SL₂(K)` lifts the fractional linear action of `γ` in the coordinate `t`:
`γ · t = (m₀₀ t + m₀₁) / (m₁₀ t + m₁₁)`. -/
def IsMoebiusLift (t : LocusFunctionField k v) (γ : ↥hw.prodSubgroup) (m : SL(2, K)) : Prop :=
  algebraMap K _ (m 1 0) * t + algebraMap K _ (m 1 1) ≠ 0 ∧
    hw.functionFieldAction hv γ t * (algebraMap K _ (m 1 0) * t + algebraMap K _ (m 1 1)) =
      algebraMap K _ (m 0 0) * t + algebraMap K _ (m 0 1)

variable {hw hv} {t : LocusFunctionField k v}

/-- The identity is lifted by the identity matrix. -/
theorem isMoebiusLift_one (ht : Transcendental K t) : hw.IsMoebiusLift hv t 1 1 := by
  refine ⟨row_ne_zero ht 1, ?_⟩
  rw [map_one]
  simp

/-- The negative of a lift is a lift. -/
theorem IsMoebiusLift.neg {γ : ↥hw.prodSubgroup} {m : SL(2, K)} (h : hw.IsMoebiusLift hv t γ m) :
    hw.IsMoebiusLift hv t γ (-m) := by
  obtain ⟨hd, he⟩ := h
  refine ⟨fun h0 ↦ hd ?_, ?_⟩
  · simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, map_neg] at h0
    linear_combination -h0
  · simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, map_neg]
    linear_combination -he

/-- **Two lifts differ by a sign.** -/
theorem IsMoebiusLift.eq_or_eq_neg (ht : Transcendental K t) {γ : ↥hw.prodSubgroup}
    {m m' : SL(2, K)} (h : hw.IsMoebiusLift hv t γ m) (h' : hw.IsMoebiusLift hv t γ m') :
    m' = m ∨ m' = -m := by
  obtain ⟨hd, he⟩ := h
  obtain ⟨hd', he'⟩ := h'
  -- Cross-multiplying the two expressions of `γ · t` gives a quadratic relation in `t`.
  have hq : algebraMap K _ (m 0 0 * m' 1 0 - m' 0 0 * m 1 0) * t ^ 2 +
      algebraMap K _ (m 0 0 * m' 1 1 + m 0 1 * m' 1 0 - m' 0 0 * m 1 1 - m' 0 1 * m 1 0) * t +
      algebraMap K _ (m 0 1 * m' 1 1 - m' 0 1 * m 1 1) = 0 := by
    have hrel : (algebraMap K _ (m 0 0) * t + algebraMap K _ (m 0 1)) *
        (algebraMap K _ (m' 1 0) * t + algebraMap K _ (m' 1 1)) =
        (algebraMap K _ (m' 0 0) * t + algebraMap K _ (m' 0 1)) *
          (algebraMap K _ (m 1 0) * t + algebraMap K _ (m 1 1)) := by
      rw [← he, ← he']
      ring
    simp only [map_sub, map_add, map_mul]
    linear_combination hrel
  obtain ⟨h2, h1, h0⟩ := eq_zero_of_quadratic ht hq
  have hdet := m.det_coe
  have hdet' := m'.det_coe
  rw [det_fin_two] at hdet hdet'
  -- The matrix `m⁻¹ m'` is the scalar `l`.
  obtain ⟨l, hl⟩ : ∃ l, l = m 1 1 * m' 0 0 - m 0 1 * m' 1 0 := ⟨_, rfl⟩
  have e00 : m' 0 0 = l * m 0 0 := by
    linear_combination (-m' 0 0) * hdet + m 0 1 * h2 - m 0 0 * hl
  have e01 : m' 0 1 = l * m 0 1 := by
    linear_combination (-m' 0 1) * hdet - m 0 0 * h0 + m 0 1 * h1 - m 0 1 * hl
  have e10 : m' 1 0 = l * m 1 0 := by
    linear_combination (-m' 1 0) * hdet + m 1 1 * h2 - m 1 0 * hl
  have e11 : m' 1 1 = l * m 1 1 := by
    linear_combination (-m' 1 1) * hdet - m 1 0 * h0 + m 1 1 * h1 - m 1 1 * hl
  have hl2 : (l - 1) * (l + 1) = 0 := by
    rw [e00, e01, e10, e11] at hdet'
    linear_combination hdet' - l ^ 2 * hdet
  rcases mul_eq_zero.1 hl2 with hl1 | hl1
  · left
    have hl1' : l = 1 := sub_eq_zero.1 hl1
    refine SpecialLinearGroup.ext _ _ fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · simpa [hl1'] using e00
    · simpa [hl1'] using e01
    · simpa [hl1'] using e10
    · simpa [hl1'] using e11
  · right
    have hl1' : l = -1 := eq_neg_of_add_eq_zero_left hl1
    refine SpecialLinearGroup.ext _ _ fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · simpa [hl1'] using e00
    · simpa [hl1'] using e01
    · simpa [hl1'] using e10
    · simpa [hl1'] using e11

/-- **Lifts compose in the reversed order**: the action of `γ δ` is lifted by `n m`. -/
theorem IsMoebiusLift.mul (ht : Transcendental K t) {γ δ : ↥hw.prodSubgroup} {m n : SL(2, K)}
    (h : hw.IsMoebiusLift hv t γ m) (h' : hw.IsMoebiusLift hv t δ n) :
    hw.IsMoebiusLift hv t (γ * δ) (n * m) := by
  obtain ⟨-, he⟩ := h
  obtain ⟨-, he'⟩ := h'
  refine ⟨row_ne_zero ht _, ?_⟩
  -- Apply the action of `γ` to the formula for `δ`.
  have hG := congrArg (hw.functionFieldAction hv γ) he'
  simp only [map_mul, map_add, AlgEquiv.commutes] at hG
  rw [map_mul, AlgEquiv.mul_apply]
  simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, map_add, map_mul]
  linear_combination (algebraMap K _ (n 0 0) -
      hw.functionFieldAction hv γ (hw.functionFieldAction hv δ t) * algebraMap K _ (n 1 0)) * he +
    (algebraMap K _ (m 1 0) * t + algebraMap K _ (m 1 1)) * hG

/-- **A lift determines the member**, since the action is faithful and `t` generates. -/
theorem IsMoebiusLift.injective (htop : IntermediateField.adjoin K {t} = ⊤)
    {γ δ : ↥hw.prodSubgroup} {m : SL(2, K)} (h : hw.IsMoebiusLift hv t γ m)
    (h' : hw.IsMoebiusLift hv t δ m) : γ = δ := by
  obtain ⟨hd, he⟩ := h
  obtain ⟨-, he'⟩ := h'
  refine hw.functionFieldAction_injective hv (algEquiv_ext_of_adjoin_eq_top htop ?_)
  rw [← mul_left_inj' hd, he, he']

variable (hw hv) in
/-- **Every member has a lift** in a generator of the function field. -/
theorem exists_generator_isMoebiusLift (hr : 2 ≤ erk k ∅ (g₀.cb : Set K)) :
    ∃ t : LocusFunctionField k v, Transcendental K t ∧
      IntermediateField.adjoin K ({t} : Set (LocusFunctionField k v)) = ⊤ ∧
      ∀ γ : ↥hw.prodSubgroup, ∃ m : SL(2, K), hw.IsMoebiusLift hv t γ m := by
  obtain ⟨t, ht, htop, hγ⟩ := hw.exists_generator_moebius hv hr
  refine ⟨t, ht, htop, fun γ ↦ ?_⟩
  obtain ⟨a, b, c, d, hdet, hden, he⟩ := hγ γ
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a * d - b * c)⁻¹ (n := 2) two_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hs
    exact inv_ne_zero hdet hs.symm
  let m : SL(2, K) := ⟨!![s * a, s * b; s * c, s * d], by
    rw [det_fin_two_of]
    linear_combination (a * d - b * c) * hs + mul_inv_cancel₀ hdet⟩
  refine ⟨m, ?_, ?_⟩
  · change algebraMap K _ (s * c) * t + algebraMap K _ (s * d) ≠ 0
    rw [map_mul, map_mul, mul_assoc, ← mul_add]
    exact mul_ne_zero ((map_ne_zero _).2 hs0) hden
  · change hw.functionFieldAction hv γ t * (algebraMap K _ (s * c) * t + algebraMap K _ (s * d)) =
      algebraMap K _ (s * a) * t + algebraMap K _ (s * b)
    rw [map_mul, map_mul, map_mul, map_mul]
    linear_combination (algebraMap K (LocusFunctionField k v) s) * he

end Germ.IsHW

end

end GroupConfig
