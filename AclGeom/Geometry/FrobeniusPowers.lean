/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Points
import Mathlib.FieldTheory.Perfect

/-!
# Integral Frobenius powers

The integral Frobenius powers `n ↦ Frob^n` of a perfect field of exponential characteristic `q`
(`frobeniusZPow`), and their basic calculus.

* Natural powers raise to `q^n` (`frobeniusZPow_natCast_apply`).
* Quotients of powers are powers (`frobeniusZPow_sub`, `frobeniusZPow_sub_apply_of_pow_eq`).
* In characteristic zero every power is the identity (`frobeniusZPow_eq_one_of_eq_one`).
* They act trivially on the point geometry (`point_frobeniusZPow`).
* The natural two-sided twist relation `a' = a^{q^s} ∨ a = a'^{q^s}` is the integral one
  (`exists_frobeniusZPow_iff`).

The Frobenius kernel theorem (`AclGeom.Reconstruct.Kernel`), the existing perfection action
(`AclGeom.Perfection.Lattice`) and the conditional Frobenius-link correctness
(`AclGeom.Interpretation.FrobEqCorrect`) use this definition. Separation of exponents on
transcendental elements stays in the kernel, which needs `AclGeom.Transfer.Descent`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.

**Status:** Frobenius calculus and trivial point action for the kernel theorem (#9, U1), and
the natural/integral twist comparison for the Frobenius link (#23).
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section FrobeniusPowers

variable (K) (q : ℕ) [ExpChar K q] [PerfectRing K q]

/-- The integral Frobenius powers `n ↦ Frob^n` of a perfect field of
exponential characteristic `q`, as a group power of `frobeniusEquiv` in the
automorphism group.  In characteristic zero (`q = 1`) every power is the
identity. -/
def frobeniusZPow (n : ℤ) : RingAut K :=
  (frobeniusEquiv K q : RingAut K) ^ n

variable {K}

/-- Natural Frobenius powers raise to the corresponding power of `q`. -/
theorem frobeniusZPow_natCast_apply (n : ℕ) (x : K) :
    frobeniusZPow K q n x = x ^ q ^ n := by
  rw [frobeniusZPow, zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, frobeniusEquiv_apply, frobenius_def,
      ← pow_mul, pow_succ']

/-- The quotient of two Frobenius powers, as an automorphism. -/
theorem frobeniusZPow_sub (m n : ℤ) :
    frobeniusZPow K q (m - n) = (frobeniusZPow K q n)⁻¹ * frobeniusZPow K q m := by
  rw [frobeniusZPow, frobeniusZPow, frobeniusZPow, ← zpow_neg, ← zpow_add,
    neg_add_eq_sub]

/-- If `y^(q^v) = x^(q^u)` then `y` is the `(u - v)`-th Frobenius power of
`x`. -/
theorem frobeniusZPow_sub_apply_of_pow_eq {u v : ℕ} {x y : K}
    (h : y ^ q ^ v = x ^ q ^ u) :
    frobeniusZPow K q ((u : ℤ) - v) x = y := by
  have hv : frobeniusZPow K q v y = frobeniusZPow K q u x := by
    rw [frobeniusZPow_natCast_apply, frobeniusZPow_natCast_apply, h]
  rw [frobeniusZPow_sub, RingAut.mul_apply, ← hv]
  exact (frobeniusZPow K q v).symm_apply_apply y

/-- In exponential characteristic one (characteristic zero) every integral Frobenius power is
the identity (blueprint validation item TEST-1). -/
theorem frobeniusZPow_eq_one_of_eq_one (hq : q = 1) (n : ℤ) : frobeniusZPow K q n = 1 := by
  subst hq
  have h1 : (frobeniusEquiv K 1 : RingAut K) = 1 := by
    ext z
    simp [frobeniusEquiv_apply, frobenius_def]
  rw [frobeniusZPow, h1, one_zpow]

/-- Integral Frobenius powers act trivially on the point geometry
(blueprint validation item TEST-2): `[Frob^n z] = [z]` for every `z` and
every `n : ℤ`. -/
theorem point_frobeniusZPow (n : ℤ) (z : K) :
    ClosedIF.point k (frobeniusZPow K q n z) = ClosedIF.point k z := by
  have hnat : ∀ (m : ℕ) (w : K),
      ClosedIF.point k (frobeniusZPow K q m w) = ClosedIF.point k w := by
    intro m w
    apply Subtype.ext
    rw [ClosedIF.coe_point, ClosedIF.coe_point, frobeniusZPow_natCast_apply]
    have hq0 : q ^ m ≠ 0 := pow_ne_zero _ (expChar_pos K q).ne'
    simpa [Set.image_singleton] using
      racl_image_pow (k := k) hq0 ({w} : Set K)
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact hnat m z
  · set w := frobeniusZPow K q (-(m : ℤ)) z with hw
    have hz : frobeniusZPow K q m w = z := by
      rw [hw, ← RingAut.mul_apply, frobeniusZPow, frobeniusZPow, ← zpow_add,
        add_neg_cancel, zpow_zero]
      rfl
    rw [← hnat m w, hz]

/-- **Natural versus integral Frobenius twists** in a perfect field: `a'` is a natural Frobenius
power of `a` in one of the two directions exactly when it is an integral Frobenius power of `a`. -/
theorem exists_frobeniusZPow_iff {a a' : K} :
    (∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s) ↔ ∃ n : ℤ, a' = frobeniusZPow K q n a := by
  constructor
  · rintro ⟨s, h | h⟩
    · exact ⟨s, by rw [frobeniusZPow_natCast_apply, h]⟩
    · refine ⟨((0 : ℕ) : ℤ) - s, ?_⟩
      exact (frobeniusZPow_sub_apply_of_pow_eq q (u := 0) (v := s)
        (by rw [pow_zero, pow_one, h])).symm
  · rintro ⟨n, rfl⟩
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · exact ⟨m, Or.inl (frobeniusZPow_natCast_apply q m a)⟩
    · refine ⟨m, Or.inr ?_⟩
      rw [← frobeniusZPow_natCast_apply q m, ← RingAut.mul_apply, frobeniusZPow, frobeniusZPow,
        ← zpow_add, add_neg_cancel, zpow_zero]
      rfl

end FrobeniusPowers

end

end AclGeom
