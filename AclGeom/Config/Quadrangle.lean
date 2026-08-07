/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.WitnessTable

/-!
# The partial quadrangle of the soundness witness

Clause (vi) of Ψ at the table-7.1 witness: the six points
`(S, T, U, S', T', U') = ([a], [c], [ac], [b], [acb], [cb])` form a
partial quadrangle. Their monomial exponent vectors with respect to
`(a, c, b)` are

`(1,0,0), (0,1,0), (1,1,0), (0,0,1), (1,1,1), (0,1,1)`;

the four named triples are dependent because `U = S·T`, `T' = S·U'`,
`U' = S'·T`(-wise) and `T' = S'·U`, and every other triple recovers all
of `a, c, b` (unimodular exponent determinant), hence has rank three.

This file provides the tuple `qQuad`, the pairwise non-membership kit,
and its distinctness; the rank clauses complete in the next increment.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness, clause (vi)).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Distinct principal closures from one-sided non-algebraicity. -/
theorem point_ne_of_notMem {z w : K} (h : w ∉ racl k {z}) :
    ClosedIF.point k z ≠ ClosedIF.point k w := by
  intro heq
  exact h (ClosedIF.point_eq_point_iff.1 heq).2

/-- Distinct points from one-sided non-algebraicity, in `Point.mk'`
form (second generator over the first). -/
theorem Point.mk'_ne {z w : K} {hz : z ∉ (⊥ : ClosedIF k K)}
    {hw : w ∉ (⊥ : ClosedIF k K)} (h : w ∉ racl k {z}) :
    Point.mk' k z hz ≠ Point.mk' k w hw := by
  intro heq
  exact point_ne_of_notMem h (congrArg Subtype.val heq)

/-- Distinct points from one-sided non-algebraicity, in `Point.mk'`
form (first generator over the second). -/
theorem Point.mk'_ne' {z w : K} {hz : z ∉ (⊥ : ClosedIF k K)}
    {hw : w ∉ (⊥ : ClosedIF k K)} (h : z ∉ racl k {w}) :
    Point.mk' k z hz ≠ Point.mk' k w hw := by
  intro heq
  have h2 := ClosedIF.point_eq_point_iff.1 (congrArg Subtype.val heq)
  exact h h2.1

section QTable

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

theorem qtable_a_notMem_c : a ∉ racl k ({c} : Set K) := by
  have h : AlgebraicIndependent k ![a, c] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_a_notMem_bc' : a ∉ racl k ({b, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {1, 2}) (i := 0) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_a_notMem_cb : a ∉ racl k ({c, b} : Set K) := by
  rw [Set.pair_comm c b]
  exact qtable_a_notMem_bc' hind

/-! ### Non-membership of the quadrangle monomials in each other's
closures -/

/-- `ac ∉ racl{a}`: dividing by `a` would make `c` algebraic over `a`. -/
theorem qtable_ac_notMem_a : a * c ∉ racl k ({a} : Set K) := by
  intro hmem
  have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem (inv_mem ha) hmem
  rw [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h
  exact qtable_c_notMem_a hind h

/-- `ac ∉ racl{c}`. -/
theorem qtable_ac_notMem_c : a * c ∉ racl k ({c} : Set K) := by
  intro hmem
  have hc : c ∈ racl k ({c} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem hmem (inv_mem hc)
  rw [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at h
  exact qtable_a_notMem_c hind h

/-- `ac ∉ racl{b}`: dividing by `c` puts `a` in `racl{b, c}`. -/
theorem qtable_ac_notMem_b : a * c ∉ racl k ({b} : Set K) := by
  intro hmem
  have hsub : racl k ({b} : Set K) ≤ racl k ({b, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem) (inv_mem hc)
  rw [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at h
  exact qtable_a_notMem_bc' hind h

/-- `cb ∉ racl{a}`: dividing by `c` puts `b` in `racl{a, c}`. -/
theorem qtable_cb_notMem_a : c * b ∉ racl k ({a} : Set K) := by
  intro hmem
  have hsub : racl k ({a} : Set K) ≤ racl k ({a, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem hc) (hsub hmem)
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_ac hind h

/-- `cb ∉ racl{c}`. -/
theorem qtable_cb_notMem_c : c * b ∉ racl k ({c} : Set K) := by
  intro hmem
  have hc : c ∈ racl k ({c} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem (inv_mem hc) hmem
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_c hind h

/-- `cb ∉ racl{b}`. -/
theorem qtable_cb_notMem_b : c * b ∉ racl k ({b} : Set K) := by
  intro hmem
  have hb : b ∈ racl k ({b} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem hmem (inv_mem hb)
  rw [mul_inv_cancel_right₀ (qtable_b_ne_zero hind)] at h
  exact qtable_c_notMem_b hind h

/-- `cb ∉ racl{ac}`: the closure of `ac` sits inside `racl{a, c}`. -/
theorem qtable_cb_notMem_ac : c * b ∉ racl k ({a * c} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c} : Set K) ≤ racl k ({a, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem hc) (hsub hmem)
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{a}`. -/
theorem qtable_acb_notMem_a : a * c * b ∉ racl k ({a} : Set K) := by
  intro hmem
  have hsub : racl k ({a} : Set K) ≤ racl k ({a, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) (hsub hmem)
  rw [inv_mul_cancel_left₀ (mul_ne_zero (qtable_a_ne_zero hind)
    (qtable_c_ne_zero hind))] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{c}`: dividing by `cb` puts `a` in `racl{c, b}`. -/
theorem qtable_acb_notMem_c : a * c * b ∉ racl k ({c} : Set K) := by
  intro hmem
  have hsub : racl k ({c} : Set K) ≤ racl k ({c, b} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_cb hind h

/-- `acb ∉ racl{b}`. -/
theorem qtable_acb_notMem_b : a * c * b ∉ racl k ({b} : Set K) := by
  intro hmem
  have hsub : racl k ({b} : Set K) ≤ racl k ({b, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_bc' hind h

/-- `acb ∉ racl{ac}`. -/
theorem qtable_acb_notMem_ac : a * c * b ∉ racl k ({a * c} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c} : Set K) ≤ racl k ({a, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) (hsub hmem)
  rw [inv_mul_cancel_left₀ (mul_ne_zero (qtable_a_ne_zero hind)
    (qtable_c_ne_zero hind))] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{cb}`. -/
theorem qtable_acb_notMem_cb : a * c * b ∉ racl k ({c * b} : Set K) := by
  intro hmem
  have hsub : racl k ({c * b} : Set K) ≤ racl k ({c, b} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem hc hb
  have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_cb hind h

/-! ### The quadrangle tuple and its distinctness -/

/-- The six quadrangle points `(S, T, U, S', T', U')` of table 7.1/7.2:
`([a], [c], [ac], [b], [acb], [cb])`. -/
def qQuad : Fin 6 → Point k K :=
  ![Point.mk' k a (qtable_a_notMem_bot hind),
    Point.mk' k c (qtable_c_notMem_bot hind),
    Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind),
    Point.mk' k b (qtable_b_notMem_bot hind),
    Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind),
    Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)]

/-- The six quadrangle points are pairwise distinct. -/
theorem qQuad_injective : Function.Injective (qQuad hind) := by
  have hne : ∀ i j : Fin 6, i < j → qQuad hind i ≠ qQuad hind j := by
    intro i j hlt
    fin_cases i <;> fin_cases j
    · exact absurd hlt (by decide)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k c (qtable_c_notMem_bot hind)
      exact Point.mk'_ne (qtable_c_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
      exact Point.mk'_ne (qtable_ac_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne' (qtable_a_notMem_b hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_a hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
      exact Point.mk'_ne (qtable_ac_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne (qtable_b_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_c hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne' (qtable_ac_notMem_b hind)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_ac hind)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_ac hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k b (qtable_b_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_b hind)
    · show Point.mk' k b (qtable_b_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_b hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne' (qtable_acb_notMem_cb hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (hne i j h)
  · exact h
  · exact absurd hij.symm (hne j i h)

end QTable

end

end AclGeom
