/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.Galois.Basic
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
(`ringHom_fix_of_pow_orbit`). No automorphism of `Ω` is ever
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
argument in §9.1): if iterating `σ` returns to `x` after `r > 0` steps and
`(σ x)^{q^v} = x^{q^u}`, then telescoping through one full period gives
`x^{q^{rv}} = x^{q^{ru}}`; if Frobenius exponents separate on `x`, the two
exponents agree. -/
theorem orbit_exponent_eq {σ : L →+* L} {x : L} {r : ℕ} (hr0 : 0 < r)
    (hσ : σ^[r] x = x) {q u v : ℕ}
    (h : σ x ^ q ^ v = x ^ q ^ u)
    (hsep : ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j) : u = v := by
  have key : ∀ n : ℕ, (σ^[n] x) ^ q ^ (n * v) = x ^ q ^ (n * u) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := congrArg σ ih
      rw [map_pow, map_pow, ← Function.iterate_succ_apply' σ n x] at h1
      -- Raise the telescoped identity to the `q ^ v`-th power and chain.
      have h3 := congrArg (fun z : L ↦ z ^ q ^ v) h1
      simp only [← pow_mul, ← pow_add] at h3
      have h4 := congrArg (fun z : L ↦ z ^ q ^ (n * u)) h
      simp only [← pow_mul, ← pow_add] at h4
      calc (σ^[n + 1] x) ^ q ^ ((n + 1) * v)
          = (σ^[n + 1] x) ^ q ^ (n * v + v) := by rw [Nat.succ_mul]
        _ = (σ x) ^ q ^ (n * u + v) := h3
        _ = (σ x) ^ q ^ (v + n * u) := by rw [add_comm]
        _ = x ^ q ^ (u + n * u) := h4
        _ = x ^ q ^ ((n + 1) * u) := by rw [Nat.succ_mul, add_comm]
  have hrr := key r
  rw [hσ] at hrr
  have h5 := hsep (r * v) (r * u) hrr
  exact (Nat.eq_of_mul_eq_mul_left hr0 h5).symm

/-- **Fixing from the telescope**: a ring endomorphism of finite order on
`x` whose action on `x` is a Frobenius-power twist fixes `x`. Exponent
separation is only consulted in positive characteristic; in characteristic
zero (`q = 1`) the twist is already the identity. -/
theorem ringHom_fix_of_pow_orbit {q : ℕ} [hq : ExpChar L q]
    {σ : L →+* L} {x : L} {r : ℕ} (hr0 : 0 < r) (hσ : σ^[r] x = x)
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

section GaloisFixing

/-- **The Galois fixing brick** for descent (§9.1, `(2) ⇒ (1)`): in a
finite Galois extension `L/F`, an element on which every `F`-automorphism
acts by a Frobenius-power twist lies in the base field. Combines the
telescope with the finite order of automorphisms and the Galois
correspondence — no automorphism of any ambient field is needed. -/
theorem mem_bot_of_forall_algEquiv_frobenius {F L : Type*} [Field F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {q : ℕ} [ExpChar L q] {x : L}
    (hsep : 2 ≤ q → ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j)
    (h : ∀ σ : L ≃ₐ[F] L, ∃ u v : ℕ, σ x ^ q ^ v = x ^ q ^ u) :
    x ∈ (⊥ : IntermediateField F L) := by
  rw [IsGalois.mem_bot_iff_fixed]
  intro σ
  obtain ⟨u, v, huv⟩ := h σ
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hiter : (⇑(σ : L →+* L))^[orderOf σ] x = x := by
    have h1 : ⇑(σ ^ orderOf σ) = (⇑σ)^[orderOf σ] := AlgEquiv.coe_pow σ _
    have h2 := congrFun h1 x
    rw [pow_orderOf_eq_one σ] at h2
    exact h2.symm.trans rfl
  exact ringHom_fix_of_pow_orbit hfin.orderOf_pos hiter huv hsep

end GaloisFixing

end

end AclGeom
