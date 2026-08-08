/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic
import AclGeom.Correspondence.FunctionField

/-!
# Bidegree-(1,1) correspondences are Möbius graphs

The elementary classification at the heart of the rational-curve route to
the affine-action lemma (design issue on the project tracker): a bivariate
relation of degree at most one in each variable, vanishing at a pair with
transcendental first coordinate, expresses the second coordinate as a
Möbius function of the first. This replaces the `PGL₂`-analysis of
blueprint Lemma 8.4 at the level of correspondences on a rational curve —
no projective models or genus theory are involved.

* `eq_bilinear_of_degreeOf_le_one`: the four-coefficient normal form;
* `exists_moebius_of_bidegree_le_one`: the Möbius formula, with a nonzero
  denominator.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4a, issue #12 pipeline step 2 groundwork).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

section Bilinear

/-- Reconstruction of a `Fin 2`-finsupp from its two values. -/
theorem finsupp_fin_two_eq (m : Fin 2 →₀ ℕ) :
    m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  ext i
  fin_cases i <;> simp

private theorem exp_ne_zero_e10 :
    (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

private theorem exp_ne_zero_e01 :
    (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private theorem exp_ne_zero_e11 :
    (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

private theorem exp_ne_e10_e01 :
    (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

private theorem exp_ne_e10_e11 :
    (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private theorem exp_ne_e01_e11 :
    (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

/-- **The bilinear normal form**: a bivariate polynomial of degree at most
one in each variable has exactly four coefficients. -/
theorem eq_bilinear_of_degreeOf_le_one {F : MvPolynomial (Fin 2) k}
    (h0 : degreeOf 0 F ≤ 1) (h1 : degreeOf 1 F ≤ 1) :
    F = C (coeff 0 F) +
      C (coeff (Finsupp.single 0 1) F) * X 0 +
      C (coeff (Finsupp.single 1 1) F) * X 1 +
      C (coeff (Finsupp.single 0 1 + Finsupp.single 1 1) F) *
        (X 0 * X 1) := by
  classical
  have hX01 : (X 0 * X 1 : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [X, X, monomial_mul, one_mul]
  ext m
  rw [coeff_add, coeff_add, coeff_add, hX01, X, X,
    coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_monomial, coeff_monomial, coeff_monomial, coeff_C]
  by_cases hbig : m 0 ≤ 1 ∧ m 1 ≤ 1
  · obtain ⟨hm0, hm1⟩ := hbig
    have hrec := finsupp_fin_two_eq m
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm0 with h00 | h00 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm1 with h10 | h10
    · -- m = 0
      rw [h00, h10] at hrec
      simp only [Finsupp.single_zero, add_zero] at hrec
      subst hrec
      simp [exp_ne_zero_e10.symm ∘ Eq.symm, if_neg, exp_ne_zero_e10,
        exp_ne_zero_e01, exp_ne_zero_e11]
    · -- m = single 1 1
      rw [h00, h10] at hrec
      simp only [Finsupp.single_zero, zero_add] at hrec
      subst hrec
      have hn1 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 :=
        exp_ne_e10_e01
      have hn2 : (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
          Finsupp.single 1 1 := fun h ↦ exp_ne_e01_e11 h.symm
      have hn3 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun h ↦
        exp_ne_zero_e01 h.symm
      simp [if_neg hn1, if_neg hn2, if_neg hn3]
    · -- m = single 0 1
      rw [h00, h10] at hrec
      simp only [Finsupp.single_zero, add_zero] at hrec
      subst hrec
      have hn1 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 :=
        fun h ↦ exp_ne_e10_e01 h.symm
      have hn2 : (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
          Finsupp.single 0 1 := fun h ↦ exp_ne_e10_e11 h.symm
      have hn3 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := fun h ↦
        exp_ne_zero_e10 h.symm
      simp [if_neg hn1, if_neg hn2, if_neg hn3]
    · -- m = single 0 1 + single 1 1
      rw [h00, h10] at hrec
      subst hrec
      have hn1 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠
          Finsupp.single 0 1 + Finsupp.single 1 1 := exp_ne_e10_e11
      have hn2 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
          Finsupp.single 0 1 + Finsupp.single 1 1 := exp_ne_e01_e11
      have hn3 : (0 : Fin 2 →₀ ℕ) ≠
          Finsupp.single 0 1 + Finsupp.single 1 1 := fun h ↦
        exp_ne_zero_e11 h.symm
      simp [if_neg hn1, if_neg hn2, if_neg hn3]
  · -- Out-of-range exponents carry no coefficient on either side.
    have hLHS : coeff m F = 0 := by
      by_contra hc
      refine hbig ⟨?_, ?_⟩
      · exact degreeOf_le_iff.1 h0 m (mem_support_iff.2 hc)
      · exact degreeOf_le_iff.1 h1 m (mem_support_iff.2 hc)
    have hn0 : (0 : Fin 2 →₀ ℕ) ≠ m := by
      intro h
      refine hbig ?_
      rw [← h]
      simp
    have hn1 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ m := by
      intro h
      refine hbig ?_
      rw [← h]
      simp
    have hn2 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ m := by
      intro h
      refine hbig ?_
      rw [← h]
      simp
    have hn3 : (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
        m := by
      intro h
      refine hbig ?_
      rw [← h]
      simp
    rw [hLHS, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3]
    ring

end Bilinear

section Moebius

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **Bidegree-(1,1) correspondences are Möbius graphs**: a nonzero
bivariate relation of degree at most one in each variable, vanishing at a
pair with transcendental first coordinate, expresses the second coordinate
as a Möbius function of the first, with nonvanishing denominator. -/
theorem exists_moebius_of_bidegree_le_one {z w : Ω}
    (hz : z ∉ racl k (∅ : Set Ω))
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (h0 : degreeOf 0 F ≤ 1) (h1 : degreeOf 1 F ≤ 1)
    (hvan : aeval ![z, w] F = 0) :
    ∃ a b c d : k,
      algebraMap k Ω c * z + algebraMap k Ω d ≠ 0 ∧
      w * (algebraMap k Ω c * z + algebraMap k Ω d) =
        algebraMap k Ω a * z + algebraMap k Ω b := by
  classical
  set c₀₀ := coeff 0 F with hc00
  set c₁₀ := coeff (Finsupp.single 0 1) F with hc10
  set c₀₁ := coeff (Finsupp.single 1 1) F with hc01
  set c₁₁ := coeff (Finsupp.single 0 1 + Finsupp.single 1 1) F with hc11
  have hform := eq_bilinear_of_degreeOf_le_one h0 h1
  rw [← hc00, ← hc10, ← hc01, ← hc11] at hform
  -- Expand the vanishing along the normal form.
  have hexp : algebraMap k Ω c₀₀ + algebraMap k Ω c₁₀ * z +
      algebraMap k Ω c₀₁ * w + algebraMap k Ω c₁₁ * (z * w) = 0 := by
    have h := hvan
    rw [hform] at h
    simpa [map_add, map_mul, MvPolynomial.aeval_C] using h
  -- The transcendence of `z` refuses linear relations over `k`.
  have hlin : ∀ p q : k, algebraMap k Ω p * z + algebraMap k Ω q = 0 →
      p = 0 ∧ q = 0 := by
    intro p q hpq
    by_cases hp : p = 0
    · refine ⟨hp, ?_⟩
      rw [hp, map_zero, zero_mul, zero_add] at hpq
      have := (algebraMap k Ω).injective (hpq.trans (map_zero _).symm)
      exact this
    · exfalso
      refine hz ?_
      have hmap : algebraMap k Ω p ≠ 0 := fun h ↦
        hp ((algebraMap k Ω).injective (by rw [h, map_zero]))
      have h2 : algebraMap k Ω p * z = -(algebraMap k Ω q) := by
        have := congrArg (fun t ↦ t - algebraMap k Ω q) hpq
        simpa [add_sub_cancel_right] using this
      have hzval : z = algebraMap k Ω (-(q / p)) := by
        have h3 : z = (algebraMap k Ω p)⁻¹ * (algebraMap k Ω p * z) := by
          rw [inv_mul_cancel_left₀ hmap]
        rw [h3, h2, map_neg, map_div₀, mul_neg, div_eq_mul_inv, mul_comm]
      rw [hzval]
      exact IntermediateField.algebraMap_mem _ _
  refine ⟨-c₁₀, -c₀₀, c₁₁, c₀₁, ?_, ?_⟩
  · -- Nonzero denominator.
    intro hden
    obtain ⟨hc, hd⟩ := hlin c₁₁ c₀₁ hden
    rw [hc, hd] at hexp
    simp only [map_zero, zero_mul, add_zero, mul_zero] at hexp
    obtain ⟨hp, hq⟩ := hlin c₁₀ c₀₀ (by
      rw [add_comm] at hexp
      exact hexp)
    refine hF0 ?_
    rw [hform, hp, hq, hc, hd]
    simp
  · -- The Möbius identity.
    rw [map_neg, map_neg]
    calc w * (algebraMap k Ω c₁₁ * z + algebraMap k Ω c₀₁) =
          (algebraMap k Ω c₀₀ + algebraMap k Ω c₁₀ * z +
            algebraMap k Ω c₀₁ * w + algebraMap k Ω c₁₁ * (z * w)) -
          (algebraMap k Ω c₀₀ + algebraMap k Ω c₁₀ * z) := by
            ring
      _ = 0 - (algebraMap k Ω c₀₀ + algebraMap k Ω c₁₀ * z) := by
            rw [hexp]
      _ = -(algebraMap k Ω c₁₀) * z + -(algebraMap k Ω c₀₀) := by
            ring

end Moebius

end

end AclGeom
