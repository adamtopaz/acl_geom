/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.JRigidity
import AclGeom.Closure.Ambient

/-!
# Descent of j-semantics to a perfect subfield

The `(2) ⇒ (1)` arrow of the blueprint's descent theorem (§9.1): if all
five points of a semantic `j`-tuple in `Ω` have representatives in a
perfect subfield `K`, the underlying pair `(x, a)` already lies in `K`.

The formalization replaces the blueprint's automorphism argument — extend
conjugations to `Aut(Ω/K)`, iterate, and contradict finiteness of the
orbit — by *finite* Galois theory: for `σ` of finite order `r` in the
Galois group of a normal closure, the j-rigidity output
`(σ x)^{q^v} = x^{q^u}` telescopes to `x^{q^{rv}} = x^{q^{ru}}`, so the
two Frobenius exponents already agree (`orbit_exponent_eq`), and
injectivity of Frobenius powers forces `σ x = x` on the spot
(`ringEquiv_fix_of_pow_orbit`). No automorphism of `Ω` is ever
constructed, and no infinitude argument is needed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** WIP (M5 descent): the telescope kernel is complete; the
assembly with the normal closure and the perfectness endgame follows.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Telescope

/-- Distinct Frobenius-power exponents separate on any element that is
transcendental over the base: `x^{q^i} = x^{q^j}` forces `i = j` when
`q ≥ 2`. -/
theorem pow_pow_sep_of_notMem_racl_empty {x : Ω}
    (hx : x ∉ racl k (∅ : Set Ω)) {q : ℕ} (hq : 2 ≤ q) {i j : ℕ}
    (h : x ^ q ^ i = x ^ q ^ j) : i = j := by
  by_contra hij
  have hne : q ^ i ≠ q ^ j := (Nat.pow_right_injective hq).ne hij
  refine hx (mem_racl_empty_of_isAlgebraic ?_)
  refine ⟨Polynomial.X ^ q ^ i - Polynomial.X ^ q ^ j, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun p ↦ Polynomial.coeff p (q ^ i)) h0
    simp [Polynomial.coeff_X_pow, hne] at h1
  · rw [map_sub, map_pow, map_pow, Polynomial.aeval_X, sub_eq_zero]
    exact h

variable {L : Type*} [Field L]

/-- **The Galois telescope** (replacing the blueprint's orbit-infinitude
argument in §9.1): if `σ` has finite order `r > 0` and
`(σ x)^{q^v} = x^{q^u}`, then iterating `σ` through one full period gives
`x^{q^{rv}} = x^{q^{ru}}`; if Frobenius exponents separate on `x`, the two
exponents agree. -/
theorem orbit_exponent_eq {σ : L ≃+* L} {r : ℕ} (hr0 : 0 < r)
    (hσ : σ ^ r = 1) {x : L} {q u v : ℕ}
    (h : σ x ^ q ^ v = x ^ q ^ u)
    (hsep : ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j) : u = v := by
  have key : ∀ n : ℕ, ((σ ^ n) x) ^ q ^ (n * v) = x ^ q ^ (n * u) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := congrArg σ ih
      rw [map_pow, map_pow] at h1
      -- `σ ((σ ^ n) x) = (σ ^ (n + 1)) x`.
      have h2 : σ ((σ ^ n) x) = (σ ^ (n + 1)) x := by
        rw [pow_succ' σ n]
        rfl
      rw [h2] at h1
      -- Raise the telescoped identity to the `q ^ v`-th power and chain.
      have h3 := congrArg (fun z : L ↦ z ^ q ^ v) h1
      simp only [← pow_mul, ← pow_add] at h3
      have h4 := congrArg (fun z : L ↦ z ^ q ^ (n * u)) h
      simp only [← pow_mul, ← pow_add] at h4
      calc ((σ ^ (n + 1)) x) ^ q ^ ((n + 1) * v)
          = ((σ ^ (n + 1)) x) ^ q ^ (n * v + v) := by rw [Nat.succ_mul]
        _ = (σ x) ^ q ^ (n * u + v) := h3
        _ = (σ x) ^ q ^ (v + n * u) := by rw [add_comm]
        _ = x ^ q ^ (u + n * u) := h4
        _ = x ^ q ^ ((n + 1) * u) := by rw [Nat.succ_mul, add_comm]
  have hrr := key r
  rw [hσ, show (1 : L ≃+* L) x = x from rfl] at hrr
  have h5 := hsep (r * v) (r * u) hrr
  exact (Nat.eq_of_mul_eq_mul_left hr0 h5).symm

/-- **Fixing from the telescope**: a finite-order automorphism whose action
on `x` is a Frobenius-power twist fixes `x`. Exponent separation is only
consulted in positive characteristic; in characteristic zero (`q = 1`) the
twist is already the identity. -/
theorem ringEquiv_fix_of_pow_orbit {q : ℕ} [hq : ExpChar L q]
    {σ : L ≃+* L} {r : ℕ} (hr0 : 0 < r) (hσ : σ ^ r = 1) {x : L}
    {u v : ℕ} (h : σ x ^ q ^ v = x ^ q ^ u)
    (hsep : 2 ≤ q → ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j) :
    σ x = x := by
  rcases hq with _ | hp
  · simpa using h
  · haveI : ExpChar L q := ExpChar.prime hp
    have huv := orbit_exponent_eq hr0 hσ h (hsep hp.two_le)
    rw [huv] at h
    exact pow_expChar_pow_injective q v h

end Telescope

end

end AclGeom
