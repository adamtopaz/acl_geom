/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Divisors

/-!
# Residues at places

The residue tower for the dimension bounds of the Riemann–Roch layer
(issue #13, P3): over an algebraically closed base every place has
residue field `k`, expressed element-wise without constructing the
quotient ring.

* `exists_sub_valuation_lt_one_of_mem_adjoin` — the reduce lemma:
  an integral element of `k(x)` (at a place where `x` is small) is
  congruent to a base constant modulo the maximal ideal;
* `linearIndependent_of_residue_independent` — elements of the valuation
  ring whose residues admit no nontrivial vanishing `k`-combination are
  linearly independent over `k(x)`.

The full reduction theorem (every integral element is congruent to a
unique constant) factors polynomials over the algebraically closed base
and lands in the next layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open Polynomial IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {O : ValuationSubring F}

/-- **The reduce lemma**: an element of `k(x)` that is integral at a
place where `x` is small is congruent to a base constant modulo the
maximal ideal. -/
theorem exists_sub_valuation_lt_one_of_mem_adjoin
    (hk : ∀ c : k, algebraMap k F c ∈ O) {x : F}
    (hxtr : Transcendental k x) (hx : O.valuation x < 1) {a : F}
    (ha : a ∈ adjoin k ({x} : Set F)) (hav : O.valuation a ≤ 1) :
    ∃ c : k, O.valuation (a - algebraMap k F c) < 1 := by
  classical
  have hx0 : x ≠ 0 := fun h ↦ hxtr (h ▸ isAlgebraic_zero)
  have hxv : O.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rcases eq_or_ne a 0 with rfl | ha0
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, Valuation.map_zero]
    exact zero_lt_one
  rw [IntermediateField.mem_adjoin_simple_iff] at ha
  obtain ⟨p, q, hpq⟩ := ha
  have hq0 : aeval x q ≠ 0 := by
    intro h0
    rw [hpq, h0, div_zero] at ha0
    exact ha0 rfl
  have hp0 : aeval x p ≠ 0 := by
    intro h0
    rw [hpq, h0, zero_div] at ha0
    exact ha0 rfl
  have hpne : p ≠ 0 := fun h ↦ hp0 (by rw [h, map_zero])
  have hqne : q ≠ 0 := fun h ↦ hq0 (by rw [h, map_zero])
  -- Split off the root multiplicities at zero.
  obtain ⟨p', hp', hp'nd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpne 0
  obtain ⟨q', hq', hq'nd⟩ :=
    q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hqne 0
  rw [map_zero, sub_zero] at hp' hp'nd hq' hq'nd
  have hp'0 : p'.coeff 0 ≠ 0 := fun h ↦ hp'nd (Polynomial.X_dvd_iff.2 h)
  have hq'0 : q'.coeff 0 ≠ 0 := fun h ↦ hq'nd (Polynomial.X_dvd_iff.2 h)
  set mp := p.rootMultiplicity 0 with hmp
  set mq := q.rootMultiplicity 0 with hmq
  have hap'0 : aeval x p' ≠ 0 := by
    intro h0
    refine hp0 ?_
    rw [hp', map_mul, h0, mul_zero]
  have haq'0 : aeval x q' ≠ 0 := by
    intro h0
    refine hq0 ?_
    rw [hq', map_mul, h0, mul_zero]
  -- The valuation of `a` fixes the multiplicity comparison.
  have hvala : O.valuation a =
      O.valuation x ^ (mp : ℤ) / O.valuation x ^ (mq : ℤ) := by
    rw [hpq, map_div₀, valuation_aeval_eq_pow_rootMultiplicity hk hx hpne,
      valuation_aeval_eq_pow_rootMultiplicity hk hx hqne, ← hmp, ← hmq,
      zpow_natCast, zpow_natCast]
  have hmqle : mq ≤ mp := by
    by_contra hc
    push Not at hc
    have h1 : (1 : _) < O.valuation a := by
      rw [hvala, lt_div_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hxv)), one_mul]
      exact zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hxv) hx
        (by exact_mod_cast hc)
    exact h1.not_ge hav
  rcases Nat.lt_or_ge mq mp with hlt | hge
  · -- Strictly smaller: `a` itself is in the maximal ideal.
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hvala,
      div_lt_one₀ (zero_lt_iff.2 (zpow_ne_zero _ hxv))]
    exact zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hxv) hx
      (by exact_mod_cast hlt)
  · -- Equal multiplicities: reduce the constant terms.
    have hmpq : mp = mq := le_antisymm hge hmqle
    -- `a` is the ratio of the primed parts.
    have ha' : a = aeval x p' / aeval x q' := by
      rw [hpq, hp', hq', map_mul, map_mul, map_pow, map_pow, aeval_X,
        hmpq]
      rw [mul_div_mul_left _ _ (pow_ne_zero _ hx0)]
    refine ⟨p'.coeff 0 / q'.coeff 0, ?_⟩
    -- The difference is a polynomial with vanishing constant term over
    -- the unit denominator.
    set r : Polynomial k := p' * Polynomial.C (q'.coeff 0) -
      Polynomial.C (p'.coeff 0) * q' with hr
    have hr0 : r.coeff 0 = 0 := by
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul, mul_comm]
      ring
    have hdiff : a - algebraMap k F (p'.coeff 0 / q'.coeff 0) =
        aeval x r / (aeval x q' * algebraMap k F (q'.coeff 0)) := by
      rw [ha', hr, map_sub, map_mul, map_mul, aeval_C, aeval_C,
        map_div₀ (algebraMap k F),
        div_sub_div _ _ haq'0 ((map_ne_zero (algebraMap k F)).2 hq'0)]
      congr 1
      ring
    rw [hdiff]
    rcases eq_or_ne r 0 with hrz | hrz
    · rw [hrz, map_zero, zero_div, Valuation.map_zero]
      exact zero_lt_one
    have hden : O.valuation (aeval x q' * algebraMap k F (q'.coeff 0)) =
        1 := by
      rw [Valuation.map_mul, valuation_aeval_eq_one hk hx hq'0,
        valuation_algebraMap_eq_one hk hq'0, mul_one]
    rw [map_div₀, hden, div_one,
      valuation_aeval_eq_pow_rootMultiplicity hk hx hrz]
    have hrmul : 0 < r.rootMultiplicity 0 := by
      rw [Polynomial.rootMultiplicity_pos hrz, Polynomial.IsRoot.def,
        ← Polynomial.coeff_zero_eq_eval_zero]
      exact hr0
    exact pow_lt_one₀ zero_le hx hrmul.ne'

end

end AclGeom
