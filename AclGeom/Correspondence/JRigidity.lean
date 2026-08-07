/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Additive
import AclGeom.Correspondence.Multiplicative
import AclGeom.Correspondence.Binomial

/-!
# Simultaneous cosets and the rigidity of `j`

Assembly of blueprint Lemma `simultaneous-coset` (8.9) and Theorem
`jrigidity` (8.10) from the two correspondence theorems: the same pair of
curves carries the additive coset equations `Q(yᵢ) = P(xᵢ) + dᵢ` and the
multiplicative ones `xᵢ^a·yᵢ^b = cᵢ`; feeding both into the prime-associate
classification of `Binomial.lean` forces the common shape
`yᵢ = λ·xᵢ^(pʳ)`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3, checklist C7).
-/

namespace AclGeom

open MvPolynomial IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Membership

/-- The binomial of a multiplicative value relation lies in the vanishing
ideal of the pair. -/
theorem binomial_mem_idealOf {x y : Ω} {c : k} {m n : ℕ}
    (h : x ^ m = algebraMap k Ω c * y ^ n) :
    ((X 0 : MvPolynomial (Fin 2) k) ^ m - C c * X 1 ^ n) ∈
      idealOf k ![x, y] := by
  rw [mem_idealOf_iff, map_sub, map_mul, map_pow, map_pow, aeval_X, aeval_X,
    aeval_C]
  have h0 : (![x, y] : Fin 2 → Ω) 0 = x := rfl
  have h1 : (![x, y] : Fin 2 → Ω) 1 = y := rfl
  rw [h0, h1, h, sub_self]

/-- … and so does the mixed binomial of a same-sign relation. -/
theorem mixed_binomial_mem_idealOf {x y : Ω} {c : k} {m n : ℕ}
    (h : x ^ m * y ^ n = algebraMap k Ω c) :
    ((X 0 : MvPolynomial (Fin 2) k) ^ m * X 1 ^ n - C c) ∈
      idealOf k ![x, y] := by
  rw [mem_idealOf_iff, map_sub, map_mul, map_pow, map_pow, aeval_X, aeval_X,
    aeval_C]
  have h0 : (![x, y] : Fin 2 → Ω) 0 = x := rfl
  have h1 : (![x, y] : Fin 2 → Ω) 1 = y := rfl
  rw [h0, h1, h, sub_self]

/-- The shifted δ-curve generator lies in each correspondence-curve
ideal. -/
theorem shifted_gen_mem_idealOf {x y : Ω} {G : MvPolynomial (Fin 2) k}
    {d : k} (h : aeval ![x, y] G = algebraMap k Ω d) :
    (G - C d) ∈ idealOf k ![x, y] := by
  rw [mem_idealOf_iff, map_sub, aeval_C, h, sub_self]

end Membership

section SignCases

/-- Rewriting integer powers through the absolute value. -/
theorem zpow_natAbs_of_pos {x : Ω} {a : ℤ} (ha : 0 < a) :
    x ^ a = x ^ a.natAbs := by
  rw [← zpow_natCast, Int.natAbs_of_nonneg ha.le]

theorem zpow_natAbs_of_neg {x : Ω} {a : ℤ} (ha : a < 0) :
    x ^ a = (x ^ a.natAbs)⁻¹ := by
  rw [← zpow_natCast, ← zpow_neg, Int.ofNat_natAbs_of_nonpos ha.le,
    neg_neg]

/-- Sign normalization of an integer monomial relation: opposite signs
yield a polynomial binomial relation in one of the two orientations, equal
signs a mixed relation. -/
theorem sign_cases_of_zpow_relation {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) {c : k}
    (h : x ^ a * y ^ b = algebraMap k Ω c) :
    (0 < a ∧ b < 0 ∧ x ^ a.natAbs = algebraMap k Ω c * y ^ b.natAbs) ∨
    (a < 0 ∧ 0 < b ∧ y ^ b.natAbs = algebraMap k Ω c * x ^ a.natAbs) ∨
    (0 < a ∧ 0 < b ∧ x ^ a.natAbs * y ^ b.natAbs = algebraMap k Ω c) ∨
    (a < 0 ∧ b < 0 ∧ x ^ a.natAbs * y ^ b.natAbs = algebraMap k Ω c⁻¹) := by
  rcases lt_trichotomy a 0 with haneg | hzero | hapos
  · rcases lt_trichotomy b 0 with hbneg | hzero' | hbpos
    · -- both negative: invert the relation
      refine Or.inr (Or.inr (Or.inr ⟨haneg, hbneg, ?_⟩))
      rw [zpow_natAbs_of_neg haneg, zpow_natAbs_of_neg hbneg,
        ← mul_inv] at h
      rw [map_inv₀, ← h, inv_inv]
    · exact absurd hzero' hb
    · -- a negative, b positive
      refine Or.inr (Or.inl ⟨haneg, hbpos, ?_⟩)
      rw [zpow_natAbs_of_neg haneg, zpow_natAbs_of_pos hbpos, mul_comm,
        ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hx)] at h
      exact h
  · exact absurd hzero ha
  · rcases lt_trichotomy b 0 with hbneg | hzero' | hbpos
    · -- a positive, b negative
      refine Or.inl ⟨hapos, hbneg, ?_⟩
      rw [zpow_natAbs_of_pos hapos, zpow_natAbs_of_neg hbneg,
        ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hy)] at h
      exact h
    · exact absurd hzero' hb
    · -- both positive
      refine Or.inr (Or.inr (Or.inl ⟨hapos, hbpos, ?_⟩))
      rw [zpow_natAbs_of_pos hapos, zpow_natAbs_of_pos hbpos] at h
      exact h

end SignCases

end

end AclGeom
