/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Multivariate rational function fields: algebraic elements and squares

Two elementary facts about `K = FractionRing (MvPolynomial σ F)`, prerequisites for the planned #25 refutation of
arbitrary-field `Q` and `Q′` correctness (`AclGeom.Counterexamples.QDescent`).

* (M1) `F` is relatively algebraically closed in `K`
  (`mem_range_algebraMap_of_isAlgebraic_fractionRing`).  An element algebraic over `F` is integral
  over the integrally closed ring `MvPolynomial σ F`, which is a unique factorization domain, so it
  is a polynomial.  A polynomial integral over `F` is constant by a total-degree count
  (`mvPolynomial_eq_C_of_isIntegral`).
* (M2) A nonzero constant times a variable is not a square in `K`
  (`not_isSquare_algebraMap_C_mul_X`), because the `X i`-degree of a square is even.

**Status:** the displayed prerequisite lemmas are proved. The specific Q/Q′ refutations
remain open (#25).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open MvPolynomial

variable {σ F : Type*} [Field F]

/-- A multivariate polynomial that is integral over its coefficient field is a constant. -/
theorem mvPolynomial_eq_C_of_isIntegral {p : MvPolynomial σ F} (hp : IsIntegral F p) :
    p = C (p.coeff 0) := by
  classical
  refine totalDegree_eq_zero_iff_eq_C.1 ?_
  by_contra hD
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hD (by simp)
  obtain ⟨q, hq, hqp⟩ := hp
  have hn : q.natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hq h0, Polynomial.eval₂_one] at hqp
    exact one_ne_zero hqp
  -- Powers of `p` have exactly the expected total degree.
  have hpow : ∀ k : ℕ, (p ^ k).totalDegree = k * p.totalDegree := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero k hp0) hp0, ih, add_one_mul]
  -- Expand the monic relation: `p ^ n + ∑_{i < n} q_i p ^ i = 0`.
  have heval : Polynomial.eval₂ (algebraMap F (MvPolynomial σ F)) p q =
      p ^ q.natDegree + ∑ i ∈ Finset.range q.natDegree, C (q.coeff i) * p ^ i := by
    conv_lhs => rw [hq.as_sum]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, MvPolynomial.algebraMap_eq]
  -- The lower terms have total degree below that of `p ^ n`.
  have hlt : (∑ i ∈ Finset.range q.natDegree, C (q.coeff i) * p ^ i).totalDegree <
      (p ^ q.natDegree).totalDegree := by
    rw [hpow]
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hD))]
    intro i hi
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add, hpow]
    exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.1 hi) (Nat.pos_of_ne_zero hD)
  have hdeg := totalDegree_add_eq_left_of_totalDegree_lt hlt
  rw [← heval, hqp, totalDegree_zero, hpow] at hdeg
  exact Nat.mul_ne_zero hn hD hdeg.symm

/-- **(M1) The coefficient field is relatively algebraically closed in a multivariate rational
function field.** -/
theorem mem_range_algebraMap_of_isAlgebraic_fractionRing
    {x : FractionRing (MvPolynomial σ F)} (hx : IsAlgebraic F x) :
    ∃ c : F, algebraMap F (FractionRing (MvPolynomial σ F)) c = x := by
  have hint : IsIntegral F x := isAlgebraic_iff_isIntegral.1 hx
  obtain ⟨p, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (hint.tower_top (A := MvPolynomial σ F))
  have hp : IsIntegral F p := by
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))
      (IsFractionRing.injective _ _)).1 ?_
    exact hint
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)),
    MvPolynomial.algebraMap_eq, ← mvPolynomial_eq_C_of_isIntegral hp]

/-- **(M2) A nonzero constant times a variable is not a square** in a multivariate rational
function field: the `X i`-degree of a square of polynomials is even. -/
theorem not_isSquare_algebraMap_C_mul_X {c : F} (hc : c ≠ 0) (i : σ) :
    ¬ IsSquare (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (C c * X i)) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ F) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hC : (C c : MvPolynomial σ F) ≠ 0 := by simpa using hc
  have hcX : (C c * X i : MvPolynomial σ F) ≠ 0 := mul_ne_zero hC (X_ne_zero i)
  -- Clear the denominators: `a * a = C c * X i * (b * b)`.
  have hab : a * a = C c * X i * (b * b) := by
    apply IsFractionRing.injective (MvPolynomial σ F) (FractionRing (MvPolynomial σ F))
    rw [map_mul, map_mul (algebraMap _ _) (C c * X i), hy, map_mul, div_mul_div_comm,
      div_mul_cancel₀ _ (mul_ne_zero hbK hbK)]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hab
    exact mul_ne_zero hcX (mul_ne_zero hb0 hb0) hab.symm
  -- Compare `X i`-degrees: even on the left, odd on the right.
  have hdeg := congrArg (degreeOf i) hab
  rw [degreeOf_mul_eq ha0 ha0, degreeOf_mul_eq hcX (mul_ne_zero hb0 hb0),
    degreeOf_mul_eq hC (X_ne_zero i), degreeOf_mul_eq hb0 hb0, degreeOf_C,
    degreeOf_X_self] at hdeg
  omega

end AclGeom
