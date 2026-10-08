/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Multiplication
import AclGeom.Config.Semantic
import AclGeom.Correspondence.JRigidity
import AclGeom.Geometry.Representatives
import AclGeom.Transfer.Transcendence

/-!
# Semantic assembly of `J` over algebraically closed fields

The converse half of blueprint Theorem `j-acf-correct` ([EH95, Prop. 2.4]),
on the semantic side: over algebraically closed `k ⊆ Ω` of transcendence
degree at least five, a five-tuple whose `Q`-projection `(X, Q, R, A)` and
`Q′`-projections `(X, A, P, Q)`, `(X, A, P, R)` are semantic is a semantic
`j`-tuple (`jSem_of_qSem_q'Sem`).  Consequently completeness of geometric
`J` reduces to guarded completeness of geometric `Q` and completeness of `Q′`
(`jSem_of_jGeom_of_completeness`).

The blueprint's sketch puts the additive relation (from `P`) and the
multiplicative relation (from `Q`) on different pairs of witnesses.  The
proof here compares three witnesses: the shifted `Q` witness
`(x₀, z)` with `(X, Q, R, A) = ([x₀], [x₀z], [x₀(1+z)], [z])` and the two
`Q′` witnesses `(x, a)`, `(x', a')`.

* `(x, a)` and `(x', a')` are additive correspondences (shared `P`), and the
  `x`-curve is monomial, being multiplicatively related to `x₀` through
  both `Q′` witnesses.  Simultaneous cosets on that one curve force an
  affine Frobenius twist (`AddCorrSetup.exists_frobenius_affine`).
* The twist turns the `Q′` witnesses into a second shifted `Q` witness.
* Shifted `Q` rigidity (`exists_racl_add_eq_of_shifted`): two shifted
  witnesses differ by a Frobenius twist and a scalar on the first
  coordinate.  Its curve-level core is the polynomial identity
  `(1 + γXⁿ)ᵐ = c(1 + Xᵐ)ⁿ` (`shift_binomial_poly`), which forces
  `γ = c = 1` and `(m, n) = (qˢ, 1)` or `(1, qˢ)`.
* The `j`-witness is then `(ν x₀, z)` for a suitable scalar `ν`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (the semantic assembly); guarded ACF `Q` completeness and ACF `Q′`
completeness remain open (#27). The former unguarded `Q` input is refuted and superseded.
-/
namespace AclGeom

noncomputable section

section ShiftPoly

open Polynomial

variable {k : Type*} [Field k]

/-- Split off the exponential-characteristic part of a positive integer:
`m = q^s · m₀` with `m₀` nonzero in `k`. -/
theorem exists_eq_expChar_pow_mul_cast_ne_zero (q : ℕ) [hq : ExpChar k q] {m : ℕ}
    (hm : m ≠ 0) : ∃ s m₀ : ℕ, m = q ^ s * m₀ ∧ (m₀ : k) ≠ 0 := by
  rcases hq with _ | hp
  · exact ⟨0, m, by simp, by exact_mod_cast hm⟩
  · obtain ⟨s, m₀, hndvd, hm'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm q hp.ne_one
    refine ⟨s, m₀, hm', ?_⟩
    rwa [Ne, CharP.cast_eq_zero_iff k q]

/-- A polynomial identity `X^N · A = X^M · B` with `A(0), B(0) ≠ 0` forces
`N = M`. -/
theorem eq_of_X_pow_mul_eq_X_pow_mul {N M : ℕ} {A B : k[X]} (hA : A.eval 0 ≠ 0)
    (hB : B.eval 0 ≠ 0) (h : X ^ N * A = X ^ M * B) : N = M := by
  have key : ∀ {N M : ℕ} {A B : k[X]}, A.eval 0 ≠ 0 → X ^ N * A = X ^ M * B →
      ¬ N < M := by
    intro N M A B hA h hlt
    have hA' : A = X ^ (M - N) * B := by
      apply mul_left_cancel₀ (pow_ne_zero N (X_ne_zero (R := k)))
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
    apply hA
    rw [hA', eval_mul, eval_pow, eval_X, zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul]
  rcases lt_trichotomy N M with hlt | heq | hgt
  · exact absurd hlt (key hA h)
  · exact heq
  · exact absurd hgt (key hB h.symm)

/-- `(1 + Y)^M - 1 = Y · ∑_{i < M} (1 + Y)^i`. -/
theorem one_add_pow_sub_one (Y : k[X]) (M : ℕ) :
    (1 + Y) ^ M - 1 = Y * ∑ i ∈ Finset.range M, (1 + Y) ^ i := by
  rw [← geom_sum_mul (1 + Y) M]
  ring

theorem eval_zero_geom_sum_one_add {Y : k[X]} (hY : Y.eval 0 = 0) (M : ℕ) :
    (∑ i ∈ Finset.range M, (1 + Y) ^ i).eval 0 = M := by
  simp [eval_finsetSum, hY]

/-- **The shifted binomial identity**: `(1 + γXⁿ)ᵐ = c(1 + Xᵐ)ⁿ` with
coprime positive `m, n` forces `γ = c = 1` and `(m, n) = (qˢ, 1)` or
`(1, qˢ)`, where `q` is the exponential characteristic. -/
theorem shift_binomial_poly (q : ℕ) [ExpChar k q] {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hcop : Nat.Coprime m n) {γ c : k} (hγ : γ ≠ 0)
    (h : (1 + C γ * X ^ n) ^ m = C c * (1 + X ^ m) ^ n) :
    γ = 1 ∧ c = 1 ∧ ((∃ s, m = q ^ s ∧ n = 1) ∨ (∃ s, m = 1 ∧ n = q ^ s)) := by
  classical
  have hc : c = 1 := by
    have h0 := congrArg (eval 0) h
    simp [zero_pow hn, zero_pow hm] at h0
    exact h0.symm
  subst hc
  have : ExpChar k[X] q :=
    expChar_of_injective_ringHom (f := (C : k →+* k[X])) C_injective q
  have hq0 : 0 < q := expChar_pos k q
  obtain ⟨s, m₀, rfl, hm₀⟩ := exists_eq_expChar_pow_mul_cast_ne_zero (k := k) q hm
  obtain ⟨s', n₀, rfl, hn₀⟩ := exists_eq_expChar_pow_mul_cast_ne_zero (k := k) q hn
  set N := q ^ s' * n₀ * q ^ s with hN
  set M := q ^ s * m₀ * q ^ s' with hM
  have hL : (1 + C γ * X ^ (q ^ s' * n₀)) ^ (q ^ s * m₀) =
      (1 + C (γ ^ q ^ s) * X ^ N) ^ m₀ := by
    rw [pow_mul, add_pow_expChar_pow, one_pow, mul_pow, ← map_pow, ← pow_mul]
  have hR : (1 + (X : k[X]) ^ (q ^ s * m₀)) ^ (q ^ s' * n₀) = (1 + X ^ M) ^ n₀ := by
    rw [pow_mul, add_pow_expChar_pow, one_pow, ← pow_mul]
  rw [hL, map_one, one_mul, hR] at h
  have e1 := one_add_pow_sub_one (C (γ ^ q ^ s) * X ^ N) m₀
  have e2 := one_add_pow_sub_one ((X : k[X]) ^ M) n₀
  rw [h, e2] at e1
  have h2 : X ^ N * (C (γ ^ q ^ s) *
        ∑ i ∈ Finset.range m₀, (1 + C (γ ^ q ^ s) * X ^ N) ^ i) =
      X ^ M * ∑ i ∈ Finset.range n₀, (1 + (X : k[X]) ^ M) ^ i := by
    rw [e1]
    ring
  have hγq : γ ^ q ^ s ≠ 0 := pow_ne_zero _ hγ
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0.ne') (by
      rintro rfl; exact hn₀ (by simp))) (pow_ne_zero _ hq0.ne')
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0.ne') (by
      rintro rfl; exact hm₀ (by simp))) (pow_ne_zero _ hq0.ne')
  have hNM : N = M := by
    refine eq_of_X_pow_mul_eq_X_pow_mul ?_ ?_ h2
    · rw [eval_mul, eval_C, eval_zero_geom_sum_one_add (by simp [zero_pow hN0])]
      exact mul_ne_zero hγq hm₀
    · rw [eval_zero_geom_sum_one_add (by simp [zero_pow hM0])]
      exact hn₀
  -- Arithmetic of the exponents.
  have hnm : n₀ = m₀ := by
    have hpos : 0 < q ^ s * q ^ s' := Nat.mul_pos (pow_pos hq0 _) (pow_pos hq0 _)
    have : n₀ * (q ^ s * q ^ s') = m₀ * (q ^ s * q ^ s') := by
      have := hNM
      rw [hN, hM] at this
      linarith [this]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  subst hnm
  have hm₁ : n₀ = 1 := by
    have hdvd : n₀ ∣ Nat.gcd (q ^ s * n₀) (q ^ s' * n₀) :=
      Nat.dvd_gcd (dvd_mul_left _ _) (dvd_mul_left _ _)
    rw [hcop] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  subst hm₁
  simp only [mul_one] at *
  -- Now the identity reads `1 + γ^{q^s} X^N = 1 + X^M` with `N = M`.
  have hγ1 : γ ^ q ^ s = 1 := by
    have hc := congrArg (fun r ↦ coeff r N) h
    simp only [pow_one, coeff_add, coeff_one, coeff_C_mul, coeff_X_pow,
      ← hNM] at hc
    simpa [hN0] using hc
  have hγ' : γ = 1 := pow_expChar_pow_injective q s (by simpa using hγ1)
  refine ⟨hγ', by simp, ?_⟩
  -- Coprime powers of `q`: one exponent vanishes, or `q = 1`.
  rcases Nat.eq_zero_or_pos s with hs | hs
  · exact Or.inr ⟨s', by simp [hs], rfl⟩
  rcases Nat.eq_zero_or_pos s' with hs' | hs'
  · exact Or.inl ⟨s, rfl, by simp [hs']⟩
  have hq1 : q = 1 := by
    by_contra hq1
    have hdvd : q ∣ Nat.gcd (q ^ s) (q ^ s') :=
      Nat.dvd_gcd (dvd_pow_self q hs.ne') (dvd_pow_self q hs'.ne')
    rw [hcop] at hdvd
    exact hq1 (Nat.eq_one_of_dvd_one hdvd)
  exact Or.inl ⟨s, rfl, by simp [hq1]⟩

end ShiftPoly

section ShiftCurve

open Polynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- A transcendental `t` with `v = t^m` parametrizes the binomial curve
`u^m = c·v^n`: then `u = γ·t^n` for a nonzero constant `γ`. -/
theorem exists_param_of_binomial [IsAlgClosed k] [IsAlgClosed Ω] {u v : Ω}
    (hv : v ∉ racl k (∅ : Set Ω)) {m n : ℕ} (hm : m ≠ 0) {c : k} (hc : c ≠ 0)
    (h : u ^ m = algebraMap k Ω c * v ^ n) :
    ∃ (t : Ω) (γ : k), Transcendental k t ∧ γ ≠ 0 ∧ v = t ^ m ∧
      u = algebraMap k Ω γ * t ^ n := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq v (Nat.pos_of_ne_zero hm)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (zero_mem _)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at ht
    exact hv0 ht.symm
  have httr : Transcendental k t := by
    intro halg
    refine hv ?_
    have htm : t ∈ racl k (∅ : Set Ω) := (mem_racl_iff k).2 (halg.tower_top _)
    rw [← ht]
    exact pow_mem htm m
  have hum : (u * (t ^ n)⁻¹) ^ m = algebraMap k Ω c := by
    rw [mul_pow, inv_pow, ← pow_mul, h, ← ht, ← pow_mul, mul_comm m n]
    field_simp
  have hmem : u * (t ^ n)⁻¹ ∈ racl k (∅ : Set Ω) := by
    have h1 : (u * (t ^ n)⁻¹) ^ ((m : ℤ)) ∈ racl k (∅ : Set Ω) := by
      rw [zpow_natCast, hum]
      exact IntermediateField.algebraMap_mem _ _
    exact mem_racl_empty_of_zpow (by exact_mod_cast hm) h1
  obtain ⟨γ, hγ⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hmem)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hγ
    rcases hγ with hu | hu
    · rw [hu, zero_pow hm, eq_comm, mul_eq_zero] at h
      rcases h with h | h
      · exact hc ((map_eq_zero_iff _ (algebraMap k Ω).injective).1 h)
      · exact hv0 (pow_eq_zero_iff (n := n) (by
          rintro rfl; simp at h) |>.1 h)
    · exact inv_ne_zero (pow_ne_zero _ ht0) hu
  refine ⟨t, γ, httr, hγ0, ht.symm, ?_⟩
  rw [hγ]
  field_simp

/-- **Shifted binomial rigidity at a curve point**: if `u^m = c₁ vⁿ` and
`(1 + u)^m = c₂ (1 + v)ⁿ` with coprime positive exponents, then the pair is
an exact Frobenius twist. -/
theorem shift_binomial_at_curve [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ)
    [ExpChar k q] {u v : Ω} (hv : v ∉ racl k (∅ : Set Ω)) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hcop : Nat.Coprime m n) {c₁ c₂ : k} (hc₁ : c₁ ≠ 0)
    (h₁ : u ^ m = algebraMap k Ω c₁ * v ^ n)
    (h₂ : (1 + u) ^ m = algebraMap k Ω c₂ * (1 + v) ^ n) :
    ∃ s : ℕ, (m = q ^ s ∧ n = 1 ∧ v = u ^ q ^ s) ∨
      (m = 1 ∧ n = q ^ s ∧ u = v ^ q ^ s) := by
  obtain ⟨t, γ, httr, hγ0, rfl, rfl⟩ := exists_param_of_binomial hv hm hc₁ h₁
  have hpoly : (1 + C γ * X ^ n) ^ m = C c₂ * (1 + X ^ m) ^ n := by
    by_contra hne
    apply httr
    refine ⟨(1 + C γ * X ^ n) ^ m - C c₂ * (1 + X ^ m) ^ n, sub_ne_zero.2 hne, ?_⟩
    simp only [map_sub, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X]
    rw [h₂, sub_self]
  obtain ⟨rfl, -, hexp⟩ := shift_binomial_poly q hm hn hcop hγ0 hpoly
  rcases hexp with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
  · exact ⟨s, Or.inl ⟨rfl, rfl, by simp⟩⟩
  · exact ⟨s, Or.inr ⟨rfl, rfl, by simp⟩⟩

/-- **Mixed shifted rule-out**: `u^m vⁿ = c₁` and `(1 + u)^m (1 + v)ⁿ = c₂`
cannot both hold on a curve with transcendental coordinates. -/
theorem shift_mixed_absurd [IsAlgClosed k] [IsAlgClosed Ω] {u v : Ω}
    (hv : v ∉ racl k (∅ : Set Ω)) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {c₁ c₂ : k}
    (hc₁ : c₁ ≠ 0) (h₁ : u ^ m * v ^ n = algebraMap k Ω c₁)
    (h₂ : (1 + u) ^ m * (1 + v) ^ n = algebraMap k Ω c₂) : False := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (zero_mem _)
  have hvi : v⁻¹ ∉ racl k (∅ : Set Ω) := fun h ↦ hv (by simpa using inv_mem h)
  have hb : u ^ m = algebraMap k Ω c₁ * (v⁻¹) ^ n := by
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hv0), h₁]
  obtain ⟨t, γ, httr, hγ0, htv, rfl⟩ := exists_param_of_binomial hvi hm hc₁ hb
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact httr isAlgebraic_zero
  have hvt : v = (t ^ m)⁻¹ := by rw [← htv, inv_inv]
  have hpoly : (1 + C γ * X ^ n) ^ m * (X ^ m + 1) ^ n - C c₂ * X ^ (m * n) = 0 := by
    by_contra hne
    apply httr
    refine ⟨_, hne, ?_⟩
    simp only [map_sub, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X]
    rw [hvt] at h₂
    have h3 : (t ^ m + 1) ^ n = t ^ (m * n) * (1 + (t ^ m)⁻¹) ^ n := by
      rw [pow_mul, ← mul_pow]
      congr 1
      field_simp
    rw [h3, ← mul_assoc, mul_comm _ (t ^ (m * n)), mul_assoc, h₂]
    ring
  have h0 := congrArg (eval 0) hpoly
  simp [zero_pow hn, zero_pow hm, zero_pow (mul_ne_zero hm hn)] at h0

/-- **Uniqueness of the multiplicative coset exponents of a curve**: two
primitive monomial relations `x^a y^b = c`, `x^a' y^b' = c'` on a curve with
transcendental `x` have proportional exponents, hence equal up to sign. -/
theorem zpow_coset_exponents_eq {x y : Ω} (hx : x ∉ racl k (∅ : Set Ω))
    (hy0 : y ≠ 0) {a b a' b' : ℤ} (ha : a ≠ 0) (hcop : Int.gcd a b = 1)
    (hcop' : Int.gcd a' b' = 1) {c c' : k}
    (h : x ^ a * y ^ b = algebraMap k Ω c)
    (h' : x ^ a' * y ^ b' = algebraMap k Ω c') :
    (a' = a ∧ b' = b) ∨ (a' = -a ∧ b' = -b) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem _)
  -- Eliminating `y` leaves a constant power of `x`.
  have hpow : x ^ (a * b' - a' * b) =
      algebraMap k Ω (c ^ b' * (c' ^ b)⁻¹) := by
    have e1 := congrArg (· ^ b') h
    have e2 := congrArg (· ^ b) h'
    simp only [mul_zpow, ← zpow_mul, ← map_zpow₀] at e1 e2
    rw [map_mul, map_inv₀, ← e1, ← e2, zpow_sub₀ hx0]
    field_simp
    rw [mul_comm b' b]
  have hdet : a * b' = a' * b := by
    by_contra hne
    refine hx (mem_racl_empty_of_zpow (sub_ne_zero.2 hne) ?_)
    rw [hpow]
    exact IntermediateField.algebraMap_mem _ _
  -- Primitive proportional vectors agree up to sign.
  have hdvd : a ∣ a' := by
    have h1 : a ∣ a' * b := ⟨b', by rw [← hdet]⟩
    exact Int.dvd_of_dvd_mul_left_of_gcd_one h1 hcop
  have hdvd' : a' ∣ a := by
    have h1 : a' ∣ a * b' := ⟨b, by rw [hdet]⟩
    exact Int.dvd_of_dvd_mul_left_of_gcd_one h1 hcop'
  rcases Int.natAbs_eq_natAbs_iff.1 (Int.natAbs_eq_of_dvd_dvd hdvd' hdvd) with h1 | h1
  · subst h1
    exact Or.inl ⟨rfl, mul_left_cancel₀ ha (by rw [hdet])⟩
  · subst h1
    refine Or.inr ⟨rfl, mul_left_cancel₀ ha ?_⟩
    rw [hdet]
    ring

end ShiftCurve

section ShiftedRigidity

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Finishing step, first direction: `x₀ = λ y^{q^s}` and `z = b^{q^s}` make
`λ⁻¹ x₀ + z` a Frobenius power of `y + b`. -/
theorem racl_add_eq_of_frob_left (q : ℕ) [ExpChar k q] {x₀ z y b : Ω} {l : k}
    (hl : l ≠ 0) {s : ℕ} (hx : x₀ = algebraMap k Ω l * y ^ q ^ s)
    (hz : z = b ^ q ^ s) :
    racl k {algebraMap k Ω l⁻¹ * x₀ + z} = racl k {y + b} := by
  have : ExpChar Ω q := expChar_of_injective_ringHom (algebraMap k Ω).injective q
  rw [hx, hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, one_mul,
    ← add_pow_expChar_pow, racl_pow _ (pow_ne_zero _ (expChar_pos k q).ne')]

/-- Finishing step, second direction: `y = λ x₀^{q^s}` and `b = z^{q^s}`
make `y + b` a Frobenius power of `ν x₀ + z` for a `q^s`-th root `ν` of
`λ`. -/
theorem exists_racl_add_eq_of_frob_right [IsAlgClosed k] (q : ℕ) [ExpChar k q]
    {x₀ z y b : Ω} {l : k} (hl : l ≠ 0) {s : ℕ}
    (hx : y = algebraMap k Ω l * x₀ ^ q ^ s) (hz : b = z ^ q ^ s) :
    ∃ ν : k, ν ≠ 0 ∧ racl k {algebraMap k Ω ν * x₀ + z} = racl k {y + b} := by
  have : ExpChar Ω q := expChar_of_injective_ringHom (algebraMap k Ω).injective q
  have hqs : 0 < q ^ s := pow_pos (expChar_pos k q) s
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq l hqs
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hqs.ne'] at hν
    exact hl hν.symm
  refine ⟨ν, hν0, ?_⟩
  have hpow : (algebraMap k Ω ν * x₀ + z) ^ q ^ s = y + b := by
    rw [add_pow_expChar_pow, mul_pow, ← map_pow, hν, hx, hz]
  rw [← hpow, racl_pow _ hqs.ne']

/-- Transcendence passes along interalgebraicity. -/
theorem notMem_racl_empty_of_mem_singleton {w y : Ω}
    (hw : w ∉ racl k (∅ : Set Ω)) (h : w ∈ racl k {y}) : y ∉ racl k (∅ : Set Ω) :=
  fun hy ↦ hw (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hy) h)

theorem ne_zero_of_notMem_racl_empty {y : Ω} (hy : y ∉ racl k (∅ : Set Ω)) :
    y ≠ 0 := by
  rintro rfl
  exact hy (zero_mem _)

theorem one_add_notMem_racl_empty {y : Ω} (hy : y ∉ racl k (∅ : Set Ω)) :
    1 + y ∉ racl k (∅ : Set Ω) := fun h ↦
  hy (by simpa using sub_mem h (one_mem (racl k (∅ : Set Ω))))

/-- **Rigidity of the shifted `Q`-coordinates**: if two independent pairs
`(y, b)` and `(x₀, z)` have interalgebraic coordinates, products and
shifted products `x(1 + a)`, then, after rescaling `x₀`, their sums are
interalgebraic.  This is the semantic content of the `Q`-coordinates
`([x], [xa], [x + xa], [a])` of a `j`-tuple. -/
theorem exists_racl_add_eq_of_shifted [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ)
    [ExpChar k q] {y b x₀ z : Ω} (hind : AlgebraicIndependent k ![y, b])
    (h1 : x₀ ∈ racl k {y}) (h1' : y ∈ racl k {x₀})
    (h2 : z ∈ racl k {b}) (h2' : b ∈ racl k {z})
    (h3 : x₀ * z ∈ racl k {y * b}) (h3' : y * b ∈ racl k {x₀ * z})
    (h4 : x₀ * (1 + z) ∈ racl k {y * (1 + b)})
    (h4' : y * (1 + b) ∈ racl k {x₀ * (1 + z)})
    {s : Ω} (hs : s ∉ racl k {y, b}) :
    ∃ ν : k, ν ≠ 0 ∧ racl k {algebraMap k Ω ν * x₀ + z} = racl k {y + b} := by
  classical
  -- Transcendence and nonvanishing.
  have hy : y ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair' hind (racl_mono (Set.empty_subset _) h)
  have hb : b ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hind (racl_mono (Set.empty_subset _) h)
  have hx₀ : x₀ ∉ racl k (∅ : Set Ω) := notMem_racl_empty_of_mem_singleton hy h1'
  have hz : z ∉ racl k (∅ : Set Ω) := notMem_racl_empty_of_mem_singleton hb h2'
  have hz1 : 1 + z ∉ racl k (∅ : Set Ω) := one_add_notMem_racl_empty hz
  have hb1 : 1 + b ∉ racl k (∅ : Set Ω) := one_add_notMem_racl_empty hb
  have hx₀0 := ne_zero_of_notMem_racl_empty hx₀
  have hz0 := ne_zero_of_notMem_racl_empty hz
  have hz10 := ne_zero_of_notMem_racl_empty hz1
  have hb0 := ne_zero_of_notMem_racl_empty hb
  have hb10 := ne_zero_of_notMem_racl_empty hb1
  -- The shifted pair is again independent.
  have hind₂ : AlgebraicIndependent k ![y, 1 + b] := by
    refine algebraicIndependent_pair ?_ ?_
    · rw [racl_one_add]
      exact AlgebraicIndependent.notMem_racl_pair' hind
    · intro h
      apply AlgebraicIndependent.notMem_racl_pair hind
      simpa using sub_mem h (one_mem (racl k ({y} : Set Ω)))
  have hs₂ : s ∉ racl k {y, 1 + b} := by
    intro h
    refine hs (racl_le_of_subset_racl ?_ h)
    rintro w (rfl | rfl)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact add_mem (one_mem _) (subset_racl k _ (Set.mem_insert_of_mem _ rfl))
  -- The two multiplicative correspondences.
  let S₁ : MulCorrSetup k Ω :=
    { x₁ := y, y₁ := x₀, x₂ := b, y₂ := z, indep := hind, y₁_ne := hx₀0,
      y₂_ne := hz0, y₁_mem := h1, x₁_mem := h1', y₂_mem := h2, x₂_mem := h2',
      mul_mem := h3, mul_mem' := h3' }
  let S₂ : MulCorrSetup k Ω :=
    { x₁ := y, y₁ := x₀, x₂ := 1 + b, y₂ := 1 + z, indep := hind₂,
      y₁_ne := hx₀0, y₂_ne := hz10, y₁_mem := h1, x₁_mem := h1'
      y₂_mem := by rw [racl_one_add]; exact add_mem (one_mem _) h2
      x₂_mem := by rw [racl_one_add]; exact add_mem (one_mem _) h2'
      mul_mem := h4, mul_mem' := h4' }
  obtain ⟨α, β, c₁, c₂, hα, hβ, hcop, hc₁, hc₂, e₁, e₂⟩ :=
    S₁.exists_coset_equations_coprime hs
  obtain ⟨α', β', c₁', c₂', -, -, hcop', -, hc₂', e₁', e₂'⟩ :=
    S₂.exists_coset_equations_coprime hs₂
  -- Equal exponents on the first curve transfer to the shifted curve.
  obtain ⟨c₂'', hc₂'', e₂''⟩ : ∃ c : k, c ≠ 0 ∧
      (1 + b) ^ α * (1 + z) ^ β = algebraMap k Ω c := by
    rcases zpow_coset_exponents_eq hy hx₀0 hα hcop hcop' e₁ e₁' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨c₂', hc₂', e₂'⟩
    · refine ⟨c₂'⁻¹, inv_ne_zero hc₂', ?_⟩
      have e := e₂'
      simp only [zpow_neg, ← mul_inv] at e
      rw [map_inv₀, ← e, inv_inv]
  have hcopN : Nat.Coprime α.natAbs β.natAbs := hcop
  have hmA : α.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hα
  have hnA : β.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hβ
  rcases sign_cases_of_zpow_relation hb0 hz0 hα hβ e₂ with
    ⟨hap, hbn, hb₂⟩ | ⟨han, hbp, hb₂⟩ | ⟨hap, hbp, hm₂⟩ | ⟨han, hbn, hm₂⟩
  · -- `b^m = c zⁿ`.
    have hs₂b : (1 + b) ^ α.natAbs = algebraMap k Ω c₂'' * (1 + z) ^ β.natAbs := by
      rcases sign_cases_of_zpow_relation hb10 hz10 hα hβ e₂'' with
        ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨h, _, _⟩
      · exact h
      all_goals omega
    have hx₁ : y ^ α.natAbs = algebraMap k Ω c₁ * x₀ ^ β.natAbs := by
      rcases sign_cases_of_zpow_relation (ne_zero_of_notMem_racl_empty hy) hx₀0 hα hβ e₁
        with ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨h, _, _⟩
      · exact h
      all_goals omega
    obtain ⟨t, ⟨hm, hn, hzt⟩ | ⟨hm, hn, hbt⟩⟩ :=
      shift_binomial_at_curve q hz hmA hnA hcopN hc₂ hb₂ hs₂b
    · rw [hm, hn, pow_one] at hx₁
      refine ⟨c₁, hc₁, ?_⟩
      have hx₀' : x₀ = algebraMap k Ω c₁⁻¹ * y ^ q ^ t := by
        rw [hx₁, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc₁, map_one, one_mul]
      simpa using racl_add_eq_of_frob_left q (inv_ne_zero hc₁) hx₀' hzt
    · rw [hm, hn, pow_one] at hx₁
      exact exists_racl_add_eq_of_frob_right q hc₁ hx₁ hbt
  · -- `zⁿ = c b^m`.
    have hs₂b : (1 + z) ^ β.natAbs = algebraMap k Ω c₂'' * (1 + b) ^ α.natAbs := by
      rcases sign_cases_of_zpow_relation hb10 hz10 hα hβ e₂'' with
        ⟨h, _, _⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩
      · omega
      · exact h
      all_goals omega
    have hx₁ : x₀ ^ β.natAbs = algebraMap k Ω c₁ * y ^ α.natAbs := by
      rcases sign_cases_of_zpow_relation (ne_zero_of_notMem_racl_empty hy) hx₀0 hα hβ e₁
        with ⟨h, _, _⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩
      · omega
      · exact h
      all_goals omega
    obtain ⟨t, ⟨hn, hm, hbt⟩ | ⟨hn, hm, hzt⟩⟩ :=
      shift_binomial_at_curve q hb hnA hmA hcopN.symm hc₂ hb₂ hs₂b
    · rw [hm, hn, pow_one] at hx₁
      have hy' : y = algebraMap k Ω c₁⁻¹ * x₀ ^ q ^ t := by
        rw [hx₁, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc₁, map_one, one_mul]
      exact exists_racl_add_eq_of_frob_right q (inv_ne_zero hc₁) hy' hbt
    · rw [hm, hn, pow_one] at hx₁
      refine ⟨c₁⁻¹, inv_ne_zero hc₁, ?_⟩
      simpa using racl_add_eq_of_frob_left q hc₁ hx₁ hzt
  · -- Mixed signs are impossible.
    have hs₂m : (1 + b) ^ α.natAbs * (1 + z) ^ β.natAbs = algebraMap k Ω c₂'' := by
      rcases sign_cases_of_zpow_relation hb10 hz10 hα hβ e₂'' with
        ⟨_, h, _⟩ | ⟨h, _, _⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩
      all_goals first | exact h | omega
    exact (shift_mixed_absurd hz hmA hnA hc₂ hm₂ hs₂m).elim
  · have hs₂m : (1 + b) ^ α.natAbs * (1 + z) ^ β.natAbs = algebraMap k Ω c₂''⁻¹ := by
      rcases sign_cases_of_zpow_relation hb10 hz10 hα hβ e₂'' with
        ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨h, _, _⟩ | ⟨_, _, h⟩
      all_goals first | exact h | omega
    exact (shift_mixed_absurd hz hmA hnA (inv_ne_zero hc₂) hm₂ hs₂m).elim

end ShiftedRigidity

section AdditiveFrobenius

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- A monomial relation can be made primitive: over an algebraically closed
base, the gcd-th root of the monomial value is again a base constant. -/
theorem exists_zpow_relation_coprime [IsAlgClosed k] {x y : Ω} (hx : x ≠ 0)
    (hy : y ≠ 0) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) {c : k}
    (h : x ^ a * y ^ b = algebraMap k Ω c) :
    ∃ (a' b' : ℤ) (c' : k), a' ≠ 0 ∧ b' ≠ 0 ∧ Int.gcd a' b' = 1 ∧ c' ≠ 0 ∧
      x ^ a' * y ^ b' = algebraMap k Ω c' := by
  have hdpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha
  obtain ⟨a', b', hcop, ha', hb'⟩ := Int.exists_gcd_one hdpos
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha'
    exact ha ha'
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb'
    exact hb hb'
  have hzd : (x ^ a' * y ^ b') ^ ((Int.gcd a b : ℤ)) = algebraMap k Ω c := by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← ha', ← hb']
    exact h
  have hzne : x ^ a' * y ^ b' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy)
  have hz : x ^ a' * y ^ b' ∈ racl k (∅ : Set Ω) := by
    refine mem_racl_empty_of_zpow (Nat.cast_ne_zero.2 hdpos.ne') ?_
    rw [hzd]
    exact IntermediateField.algebraMap_mem _ _
  obtain ⟨c', hc'⟩ := mem_range_algebraMap_of_isAlgebraic (isAlgebraic_of_mem_racl_empty hz)
  refine ⟨a', b', c', ha'0, hb'0, hcop, fun h0 ↦ hzne ?_, hc'.symm⟩
  rw [← hc', h0, map_zero]

/-- Coprime powers of the exponential characteristic: one of them is `1`. -/
theorem expChar_pow_eq_one_of_coprime (q : ℕ) {r t : ℕ}
    (h : Nat.Coprime (q ^ r) (q ^ t)) : q ^ t = 1 ∨ q ^ r = 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact Or.inl (pow_zero q)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Or.inr (pow_zero q)
  have hq : q = 1 := by
    have hdvd : q ∣ Nat.gcd (q ^ r) (q ^ t) :=
      Nat.dvd_gcd (dvd_pow_self q hr.ne') (dvd_pow_self q ht.ne')
    rw [h] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  exact Or.inl (by rw [hq, one_pow])

/-- **Additive cosets on a monomial curve**: if two independent additive
finite correspondences share their additive coset structure and the first
curve also carries a monomial relation, then both curves are affine
Frobenius twists with a common slope: `y₁ = l x₁^{q^r}`,
`y₂ = l x₂^{q^r} + e`, or the same with the roles of `x` and `y`
exchanged. -/
theorem AddCorrSetup.exists_frobenius_affine [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ)
    [ExpChar k q] (S : AddCorrSetup k Ω) {s s' : Ω} (hs : s ∉ racl k {S.x₁, S.x₂})
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s}) {A B : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) {C : k}
    (hmon : S.x₁ ^ A * S.y₁ ^ B = algebraMap k Ω C) :
    ∃ (l e : k) (r : ℕ), l ≠ 0 ∧
      ((S.y₁ = algebraMap k Ω l * S.x₁ ^ q ^ r ∧
          S.y₂ = algebraMap k Ω l * S.x₂ ^ q ^ r + algebraMap k Ω e) ∨
        (S.x₁ = algebraMap k Ω l * S.y₁ ^ q ^ r ∧
          S.x₂ = algebraMap k Ω l * S.y₂ ^ q ^ r + algebraMap k Ω e)) := by
  classical
  obtain ⟨G, P, Q, hGp, hsplit, hP0, hQ0, hPne, -, hPadd, hQadd, d₁, d₂, hd₁, hd₂⟩ :=
    S.exists_delta_gen_data hs hss'
  have hx₁r : S.x₁ ∉ racl k (∅ : Set Ω) := fun h ↦
    S.x₁_notMem (racl_mono (Set.empty_subset _) h)
  have hx₁tr : Transcendental k S.x₁ := fun h ↦
    hx₁r ((mem_racl_iff k).2 (h.tower_top _))
  have hy₁r : S.y₁ ∉ racl k (∅ : Set Ω) :=
    notMem_racl_empty_of_mem_singleton hx₁r S.x₁_mem
  obtain ⟨G₁, hG₁p, hG₁span⟩ := exists_prime_span_idealOf k hx₁tr S.y₁_mem
  have hx₁0 := ne_zero_of_notMem_racl_empty hx₁r
  have hy₁0 := ne_zero_of_notMem_racl_empty hy₁r
  obtain ⟨a, b, c, ha, hb, hcop, hc, h₁⟩ :=
    exists_zpow_relation_coprime hx₁0 hy₁0 hA hB hmon
  have hval₁ : Polynomial.aeval S.x₁ P + Polynomial.aeval S.y₁ Q = algebraMap k Ω d₁ := by
    rw [← aeval_pair_of_split hsplit]
    exact hd₁
  have hval₂ : Polynomial.aeval S.x₂ P + Polynomial.aeval S.y₂ Q = algebraMap k Ω d₂ := by
    rw [← aeval_pair_of_split hsplit]
    exact hd₂
  have hmA : a.natAbs ≠ 0 := Int.natAbs_ne_zero.2 ha
  have hnA : b.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hb
  have hcopA : Nat.gcd a.natAbs b.natAbs = 1 := hcop
  rcases sign_cases_of_zpow_relation hx₁0 hy₁0 ha hb h₁ with
    ⟨-, -, hbin⟩ | ⟨-, -, hbin⟩ | ⟨-, -, hmix⟩ | ⟨-, -, hmix⟩
  · -- `x₁^m = c y₁ⁿ`.
    obtain ⟨-, l, hl, hP, hQ⟩ := simultaneous_coset_at_curve hG₁p hG₁span hGp hP0 hQ0
      hsplit hd₁ hc hmA hnA hcopA hbin
    obtain ⟨r, hr⟩ := monomial_isAdditive_expChar q hl (by rw [← hP]; exact hPadd)
    have hQform : Q = Polynomial.C (-(l * c)) * Polynomial.X ^ b.natAbs := by
      rw [hQ, map_neg, neg_mul]
    obtain ⟨t, ht⟩ := monomial_isAdditive_expChar q (neg_ne_zero.2 (mul_ne_zero hl hc))
      (by rw [← hQform]; exact hQadd)
    rw [hP, hQ] at hval₂
    simp only [map_mul, map_neg, Polynomial.aeval_C, Polynomial.aeval_X_pow, neg_mul] at hval₂
    rcases expChar_pow_eq_one_of_coprime q (hr ▸ ht ▸ hcopA) with hn1 | hm1
    · rw [← ht] at hn1
      rw [hn1, pow_one, hr] at hbin hval₂
      refine ⟨c⁻¹, -(d₂ * (l * c)⁻¹), r, inv_ne_zero hc, Or.inl ⟨?_, ?_⟩⟩
      · rw [hbin, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      · have hl' : algebraMap k Ω l ≠ 0 := (map_ne_zero _).2 hl
        have hc' : algebraMap k Ω c ≠ 0 := (map_ne_zero _).2 hc
        simp only [map_neg, map_mul, map_inv₀]
        field_simp
        linear_combination -hval₂
    · rw [← hr] at hm1
      rw [hm1, pow_one, ht] at hbin hval₂
      refine ⟨c, d₂ * l⁻¹, t, hc, Or.inr ⟨hbin, ?_⟩⟩
      have hl' : algebraMap k Ω l ≠ 0 := (map_ne_zero _).2 hl
      simp only [map_mul, map_inv₀]
      field_simp
      linear_combination hval₂
  · -- `y₁ⁿ = c x₁^m`.
    obtain ⟨-, l, hl, hQ, hP⟩ := simultaneous_coset_at_curve' hG₁p hG₁span hGp hP0 hQ0
      hsplit hd₁ hc hmA hnA hcopA hbin
    obtain ⟨t, ht⟩ := monomial_isAdditive_expChar q hl (by rw [← hQ]; exact hQadd)
    have hPform : P = Polynomial.C (-(l * c)) * Polynomial.X ^ a.natAbs := by
      rw [hP, map_neg, neg_mul]
    obtain ⟨r, hr⟩ := monomial_isAdditive_expChar q (neg_ne_zero.2 (mul_ne_zero hl hc))
      (by rw [← hPform]; exact hPadd)
    rw [hP, hQ] at hval₂
    simp only [map_mul, map_neg, Polynomial.aeval_C, Polynomial.aeval_X_pow, neg_mul] at hval₂
    rcases expChar_pow_eq_one_of_coprime q (hr ▸ ht ▸ hcopA) with hn1 | hm1
    · rw [← ht] at hn1
      rw [hn1, pow_one, hr] at hbin hval₂
      refine ⟨c, d₂ * l⁻¹, r, hc, Or.inl ⟨hbin, ?_⟩⟩
      have hl' : algebraMap k Ω l ≠ 0 := (map_ne_zero _).2 hl
      simp only [map_mul, map_inv₀]
      field_simp
      linear_combination hval₂
    · rw [← hr] at hm1
      rw [hm1, pow_one, ht] at hbin hval₂
      refine ⟨c⁻¹, -(d₂ * (l * c)⁻¹), t, inv_ne_zero hc, Or.inr ⟨?_, ?_⟩⟩
      · rw [hbin, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      · have hl' : algebraMap k Ω l ≠ 0 := (map_ne_zero _).2 hl
        have hc' : algebraMap k Ω c ≠ 0 := (map_ne_zero _).2 hc
        simp only [map_neg, map_mul, map_inv₀]
        field_simp
        linear_combination -hval₂
  · exact (rule_out_mixed_at_curve hx₁r hy₁r hc hmA hnA hmix hPne hP0 hQ0 hval₁).elim
  · exact (rule_out_mixed_at_curve hx₁r hy₁r (inv_ne_zero hc) hmA hnA hmix hPne hP0 hQ0
      hval₁).elim

end AdditiveFrobenius

section Assembly

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

open ClosedIF

/-- Equal principal points have equal closures. -/
theorem racl_singleton_eq_of_point_eq {u v : Ω} (h : point k u = point k v) :
    racl k {u} = racl k {v} :=
  congrArg Subtype.val h

/-- Equal closures give interalgebraicity. -/
theorem mem_racl_singleton_of_racl_eq {u v : Ω} (h : racl k {u} = racl k {v}) :
    u ∈ racl k {v} := by
  rw [← h]
  exact subset_racl k _ rfl

/-- Pair independence is a property of the two closures (the pair case of
`algebraicIndependent_congr_racl`). -/
theorem algebraicIndependent_pair_congr {u u' v v' : Ω} (hu : racl k {u} = racl k {u'})
    (hv : racl k {v} = racl k {v'}) (h : AlgebraicIndependent k ![u, v]) :
    AlgebraicIndependent k ![u', v'] :=
  (algebraicIndependent_congr_racl (v := ![u, v]) (w := ![u', v'])
    (Fin.forall_fin_two.2 ⟨hu, hv⟩)).1 h

/-- Scaling and Frobenius do not change a principal closure. -/
theorem racl_algebraMap_mul_pow {e : k} (he : e ≠ 0) (w : Ω) {n : ℕ} (hn : n ≠ 0) :
    racl k {algebraMap k Ω e * w ^ n} = racl k {w} := by
  rw [racl_algebraMap_mul he, racl_pow _ hn]

/-- The product and shifted product of an independent pair are not
interalgebraic. -/
theorem mul_one_add_notMem_racl_mul {x z : Ω} (hind : AlgebraicIndependent k ![x, z]) :
    x * (1 + z) ∉ racl k {x * z} := by
  intro h
  have hx : x ∉ racl k (∅ : Set Ω) := fun h' ↦
    AlgebraicIndependent.notMem_racl_pair' hind (racl_mono (Set.empty_subset _) h')
  have hx0 := ne_zero_of_notMem_racl_empty hx
  have hw : x * z ∈ racl k {x * z} := subset_racl k _ rfl
  have hxw : x ∈ racl k {x * z} := by
    have := sub_mem h hw
    rwa [show x * (1 + z) - x * z = x by ring] at this
  have hzw : z ∈ racl k {x * z} := by
    have := mul_mem (inv_mem hxw) hw
    rwa [inv_mul_cancel_left₀ hx0] at this
  have hwx : x * z ∈ racl k {x} := by
    have := racl_exchange (S := (∅ : Set Ω)) (by simpa using hxw) (by simpa using hx)
    simpa using this
  exact AlgebraicIndependent.notMem_racl_pair hind
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hwx) hzw)

/-- The `a`-shifted form of a semantic `Q`-tuple:
`(X, Q, R, A) = ([x₀], [x₀z], [x₀(1 + z)], [z])`. -/
theorem QSem.exists_shifted {X Q R A : Point k Ω} (h : QSem X Q R A) :
    ∃ x₀ z : Ω, AlgebraicIndependent k ![x₀, z] ∧ X.1 = point k x₀ ∧
      Q.1 = point k (x₀ * z) ∧ R.1 = point k (x₀ * (1 + z)) ∧ A.1 = point k z := by
  obtain ⟨u, v, hind, hX, hQ, hR, hA⟩ := h
  have hu : u ∉ racl k (∅ : Set Ω) := fun h' ↦
    AlgebraicIndependent.notMem_racl_pair' hind (racl_mono (Set.empty_subset _) h')
  have hu0 := ne_zero_of_notMem_racl_empty hu
  have hvu : v / u ∉ racl k {u} := by
    intro h'
    apply AlgebraicIndependent.notMem_racl_pair hind
    have := mul_mem (subset_racl k ({u} : Set Ω) rfl) h'
    rwa [mul_div_cancel₀ v hu0] at this
  refine ⟨u, v / u, algebraicIndependent_pair ?_ hvu, hX, ?_, ?_, ?_⟩
  · intro h'
    apply hvu
    have := racl_exchange (S := (∅ : Set Ω)) (by simpa using h') (by simpa using hu)
    simpa using this
  · rw [hQ, mul_div_cancel₀ v hu0]
  · rw [hR, mul_add, mul_one, mul_div_cancel₀ v hu0]
  · rw [hA, point_div_symm]

/-- A shifted `Q`-witness with a matching sum point is a semantic `j`-tuple:
`j(ν x₀, z)`. -/
theorem jSem_of_shifted {X P Q R A : Point k Ω} {x₀ z : Ω}
    (hind : AlgebraicIndependent k ![x₀, z]) (hX : X.1 = point k x₀)
    (hQ : Q.1 = point k (x₀ * z)) (hR : R.1 = point k (x₀ * (1 + z)))
    (hA : A.1 = point k z) {ν : k} (hν : ν ≠ 0)
    (hP : P.1 = point k (algebraMap k Ω ν * x₀ + z)) :
    JSem ![X, P, Q, R, A] := by
  have hνx : racl k {algebraMap k Ω ν * x₀} = racl k {x₀} := racl_algebraMap_mul hν x₀
  refine ⟨algebraMap k Ω ν * x₀, z, algebraicIndependent_pair_congr hνx.symm rfl hind,
    ?_, hP, ?_, ?_, hA⟩
  · change X.1 = _
    rw [hX, point_algebraMap_mul hν]
  · change Q.1 = _
    rw [hQ, mul_assoc, point_algebraMap_mul hν]
  · change R.1 = _
    rw [hR, show algebraMap k Ω ν * x₀ + algebraMap k Ω ν * x₀ * z =
      algebraMap k Ω ν * (x₀ * (1 + z)) by ring, point_algebraMap_mul hν]

/-- **Semantic assembly of `J`** (blueprint Theorem `j-acf-correct`,
converse direction, semantic part; [EH95, Prop. 2.4]): over algebraically
closed fields of transcendence degree at least five, a five-tuple whose
`Q`-projection `(X, Q, R, A)` and `Q′`-projections `(X, A, P, Q)`,
`(X, A, P, R)` are semantic is a semantic `j`-tuple.

The two `Q′` witnesses share `[x]`, `[a]` and the sum point `P`, so they are
additive correspondences; composing their multiplicative correspondences
with the shifted `Q` witness `(x₀, z)` makes the `x`-curve monomial, which
forces affine Frobenius twists (`AddCorrSetup.exists_frobenius_affine`).
The twist produces a second shifted `Q` witness, and the rigidity of the
shifted coordinates (`exists_racl_add_eq_of_shifted`) aligns its sum with
a rescaling of `(x₀, z)`. -/
theorem jSem_of_qSem_q'Sem [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k Ω) {X P Q R A : Point k Ω}
    (hQ : QSem X Q R A) (h₁ : Q'Sem X A P Q) (h₂ : Q'Sem X A P R) :
    JSem ![X, P, Q, R, A] := by
  classical
  have : ExpChar Ω q := expChar_of_injective_ringHom (algebraMap k Ω).injective q
  have hq0 : ∀ r : ℕ, q ^ r ≠ 0 := fun r ↦ pow_ne_zero _ (expChar_pos k q).ne'
  obtain ⟨x₀, z, hind₀, hX₀, hQ₀, hR₀, hA₀⟩ := hQ.exists_shifted
  obtain ⟨x, a, hind, hX, hA, hP, hQ'⟩ := h₁
  obtain ⟨x', a', hind', hX', hA', hP', hR'⟩ := h₂
  have pt : ∀ {Y : Point k Ω} {u v : Ω}, Y.1 = point k u → Y.1 = point k v →
      racl k {u} = racl k {v} := fun h h' ↦ racl_singleton_eq_of_point_eq (h.symm.trans h')
  have ia : ∀ {Y : Point k Ω} {u v : Ω}, Y.1 = point k u → Y.1 = point k v →
      u ∈ racl k {v} := fun h h' ↦ mem_racl_singleton_of_racl_eq (pt h h')
  -- Transcendence and nonvanishing of the shifted witness.
  have hx₀ : x₀ ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair' hind₀ (racl_mono (Set.empty_subset _) h)
  have hz : z ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hind₀ (racl_mono (Set.empty_subset _) h)
  have hx₀0 := ne_zero_of_notMem_racl_empty hx₀
  have hz0 := ne_zero_of_notMem_racl_empty hz
  have hz10 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hz)
  -- Fresh elements.
  obtain ⟨s, hs⟩ := fresh_four_of_five_le_trdeg htr {x, a}
    (Finset.card_le_two.trans (by norm_num))
  obtain ⟨s', hs'⟩ := fresh_four_of_five_le_trdeg htr {x, a, s}
    (Finset.card_le_three.trans (by norm_num))
  simp only [Finset.coe_insert, Finset.coe_singleton] at hs hs'
  have hsub : ∀ {y b : Ω}, y ∈ racl k {x, a} → b ∈ racl k {x, a} → s ∉ racl k {y, b} :=
    fun {y b} hy hb h ↦ hs (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hy
      · exact hb) h)
  have hxa : ∀ {u : Ω}, u ∈ racl k {x} → u ∈ racl k {x, a} := fun h ↦
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) h
  have haa : ∀ {u : Ω}, u ∈ racl k {a} → u ∈ racl k {x, a} := fun h ↦
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem x (Set.mem_singleton a))) h
  -- The additive correspondence between the two `Q′` witnesses.
  let S : AddCorrSetup k Ω :=
    { x₁ := x, y₁ := x', x₂ := a, y₂ := a', indep := hind, y₁_mem := ia hX' hX
      x₁_mem := ia hX hX', y₂_mem := ia hA' hA, x₂_mem := ia hA hA'
      sum_mem := ia hP' hP, sum_mem' := ia hP hP' }
  -- The two multiplicative correspondences with the shifted `Q` witness.
  let T₁ : MulCorrSetup k Ω :=
    { x₁ := x, y₁ := x₀, x₂ := a, y₂ := z, indep := hind, y₁_ne := hx₀0, y₂_ne := hz0
      y₁_mem := ia hX₀ hX, x₁_mem := ia hX hX₀, y₂_mem := ia hA₀ hA
      x₂_mem := ia hA hA₀, mul_mem := ia hQ₀ hQ', mul_mem' := ia hQ' hQ₀ }
  let T₂ : MulCorrSetup k Ω :=
    { x₁ := x', y₁ := x₀, x₂ := a', y₂ := 1 + z, indep := hind', y₁_ne := hx₀0
      y₂_ne := hz10, y₁_mem := ia hX₀ hX', x₁_mem := ia hX' hX₀
      y₂_mem := add_mem (one_mem _) (ia hA₀ hA')
      x₂_mem := by rw [racl_one_add]; exact ia hA' hA₀
      mul_mem := ia hR₀ hR', mul_mem' := ia hR' hR₀ }
  obtain ⟨α, β, c₁, -, hα, hβ, -, hc₁, -, e₁, -⟩ := T₁.exists_coset_equations_coprime hs
  obtain ⟨α', β', c₁', -, hα', hβ', -, hc₁', -, e₁', -⟩ :=
    T₂.exists_coset_equations_coprime (hsub (hxa (ia hX' hX)) (haa (ia hA' hA)))
  change x ^ α * x₀ ^ β = _ at e₁
  change x' ^ α' * x₀ ^ β' = _ at e₁'
  -- Composing through `x₀`: a monomial relation between `x` and `x'`.
  have hmon : x ^ (α * β') * x' ^ (-(α' * β)) =
      algebraMap k Ω (c₁ ^ β' * (c₁' ^ β)⁻¹) := by
    have E1 := congrArg (· ^ β') e₁
    have E2 := congrArg (· ^ β) e₁'
    simp only [mul_zpow, ← zpow_mul, ← map_zpow₀] at E1 E2
    rw [mul_comm β' β] at E2
    rw [map_mul, map_inv₀, ← E1, ← E2, zpow_neg]
    have hx'0 : x' ≠ 0 := ne_zero_of_notMem_racl_empty
      (notMem_racl_empty_of_mem_singleton hx₀ (ia hX₀ hX'))
    field_simp
  obtain ⟨l, e, r, hl, hcase⟩ := S.exists_frobenius_affine q hs hs'
    (mul_ne_zero hα hβ') (neg_ne_zero.2 (mul_ne_zero hα' hβ)) hmon
  have hQR : ¬ racl k {x₀ * (1 + z)} = racl k {x₀ * z} := fun h ↦
    mul_one_add_notMem_racl_mul hind₀ (mem_racl_singleton_of_racl_eq h)
  have mem : ∀ {u v : Ω}, racl k {u} = racl k {v} → u ∈ racl k {v} :=
    fun h ↦ mem_racl_singleton_of_racl_eq h
  have ptEq : ∀ {u v : Ω}, racl k {u} = racl k {v} → point k u = point k v :=
    fun h ↦ Subtype.ext h
  rcases hcase with ⟨hx'e, ha'e⟩ | ⟨hxe, hae⟩
  · -- The second `Q′` witness is an affine Frobenius twist of the first.
    change x' = _ at hx'e
    change a' = _ at ha'e
    have he : e ≠ 0 := by
      rintro rfl
      apply hQR
      rw [pt hR₀ hR', pt hQ₀ hQ', hx'e, ha'e, map_zero, add_zero,
        show algebraMap k Ω l * x ^ q ^ r * (algebraMap k Ω l * a ^ q ^ r) =
          algebraMap k Ω (l * l) * (x * a) ^ q ^ r by rw [map_mul, mul_pow]; ring,
        racl_algebraMap_mul_pow (mul_ne_zero hl hl) _ (hq0 r)]
    set ε : k := l / e with hεdef
    have hε : ε ≠ 0 := div_ne_zero hl he
    set y := algebraMap k Ω ε * x ^ q ^ r with hydef
    set b := algebraMap k Ω ε * a ^ q ^ r with hbdef
    have hy : racl k {y} = racl k {x} := racl_algebraMap_mul_pow hε x (hq0 r)
    have hb : racl k {b} = racl k {a} := racl_algebraMap_mul_pow hε a (hq0 r)
    have hyb : racl k {y * b} = racl k {x * a} := by
      rw [show y * b = algebraMap k Ω (ε * ε) * (x * a) ^ q ^ r by
        rw [hydef, hbdef, map_mul, mul_pow]; ring]
      exact racl_algebraMap_mul_pow (mul_ne_zero hε hε) _ (hq0 r)
    have hy1b : racl k {y * (1 + b)} = racl k {x' * a'} := by
      have he' : algebraMap k Ω e ≠ 0 := (map_ne_zero _).2 he
      rw [show x' * a' = algebraMap k Ω (e * e) * (y * (1 + b)) by
        rw [hx'e, ha'e, hydef, hbdef, hεdef, map_mul, map_div₀]
        field_simp
        ring]
      exact (racl_algebraMap_mul (mul_ne_zero he he) _).symm
    obtain ⟨ν, hν, hνeq⟩ := exists_racl_add_eq_of_shifted q
      (algebraicIndependent_pair_congr hy.symm hb.symm hind)
      (mem ((pt hX₀ hX).trans hy.symm)) (mem (hy.trans (pt hX hX₀)))
      (mem ((pt hA₀ hA).trans hb.symm)) (mem (hb.trans (pt hA hA₀)))
      (mem ((pt hQ₀ hQ').trans hyb.symm)) (mem (hyb.trans (pt hQ' hQ₀)))
      (mem ((pt hR₀ hR').trans hy1b.symm)) (mem (hy1b.trans (pt hR' hR₀)))
      (hsub (hxa (mem hy)) (haa (mem hb)))
    have hsum : racl k {y + b} = racl k {x + a} := by
      rw [show y + b = algebraMap k Ω ε * (x + a) ^ q ^ r by
        rw [hydef, hbdef, add_pow_expChar_pow]; ring]
      exact racl_algebraMap_mul_pow hε _ (hq0 r)
    refine jSem_of_shifted hind₀ hX₀ hQ₀ hR₀ hA₀ hν ?_
    rw [hP]
    exact ptEq (hsum.symm.trans hνeq.symm)
  · -- The first `Q′` witness is an affine Frobenius twist of the second.
    change x = _ at hxe
    change a = _ at hae
    have he : e ≠ 0 := by
      rintro rfl
      apply hQR
      rw [pt hR₀ hR', pt hQ₀ hQ', hxe, hae, map_zero, add_zero,
        show algebraMap k Ω l * x' ^ q ^ r * (algebraMap k Ω l * a' ^ q ^ r) =
          algebraMap k Ω (l * l) * (x' * a') ^ q ^ r by rw [map_mul, mul_pow]; ring,
        racl_algebraMap_mul_pow (mul_ne_zero hl hl) _ (hq0 r)]
    set ε : k := l / e with hεdef
    have hε : ε ≠ 0 := div_ne_zero hl he
    set y := algebraMap k Ω ε * x' ^ q ^ r with hydef
    set b := algebraMap k Ω ε * a' ^ q ^ r with hbdef
    set z' := -1 - z with hz'def
    have hy : racl k {y} = racl k {x'} := racl_algebraMap_mul_pow hε x' (hq0 r)
    have hb : racl k {b} = racl k {a'} := racl_algebraMap_mul_pow hε a' (hq0 r)
    have hyb : racl k {y * b} = racl k {x' * a'} := by
      rw [show y * b = algebraMap k Ω (ε * ε) * (x' * a') ^ q ^ r by
        rw [hydef, hbdef, map_mul, mul_pow]; ring]
      exact racl_algebraMap_mul_pow (mul_ne_zero hε hε) _ (hq0 r)
    have hy1b : racl k {y * (1 + b)} = racl k {x * a} := by
      have he' : algebraMap k Ω e ≠ 0 := (map_ne_zero _).2 he
      rw [show x * a = algebraMap k Ω (e * e) * (y * (1 + b)) by
        rw [hxe, hae, hydef, hbdef, hεdef, map_mul, map_div₀]
        field_simp
        ring]
      exact (racl_algebraMap_mul (mul_ne_zero he he) _).symm
    have hz' : racl k {z'} = racl k {z} := by
      rw [hz'def, show -1 - z = -(z + algebraMap k Ω 1) by rw [map_one]; ring,
        racl_neg, racl_add_algebraMap]
    have hx₀z' : racl k {x₀ * z'} = racl k {x₀ * (1 + z)} := by
      rw [hz'def, show x₀ * (-1 - z) = -(x₀ * (1 + z)) by ring, racl_neg]
    have hx₀1z' : racl k {x₀ * (1 + z')} = racl k {x₀ * z} := by
      rw [hz'def, show x₀ * (1 + (-1 - z)) = -(x₀ * z) by ring, racl_neg]
    obtain ⟨ν, hν, hνeq⟩ := exists_racl_add_eq_of_shifted q
      (algebraicIndependent_pair_congr hy.symm hb.symm hind')
      (mem ((pt hX₀ hX').trans hy.symm)) (mem (hy.trans (pt hX' hX₀)))
      (mem (hz'.trans ((pt hA₀ hA').trans hb.symm)))
      (mem (hb.trans ((pt hA' hA₀).trans hz'.symm)))
      (mem (hx₀z'.trans ((pt hR₀ hR').trans hyb.symm)))
      (mem (hyb.trans ((pt hR' hR₀).trans hx₀z'.symm)))
      (mem (hx₀1z'.trans ((pt hQ₀ hQ').trans hy1b.symm)))
      (mem (hy1b.trans ((pt hQ' hQ₀).trans hx₀1z'.symm)))
      (hsub (hxa (mem (hy.trans (pt hX' hX)))) (haa (mem (hb.trans (pt hA' hA)))))
    have hsum : racl k {y + b} = racl k {x' + a'} := by
      rw [show y + b = algebraMap k Ω ε * (x' + a') ^ q ^ r by
        rw [hydef, hbdef, add_pow_expChar_pow]; ring]
      exact racl_algebraMap_mul_pow hε _ (hq0 r)
    have hshift : racl k {algebraMap k Ω (-ν) * x₀ + z} =
        racl k {algebraMap k Ω ν * x₀ + z'} := by
      rw [show algebraMap k Ω (-ν) * x₀ + z =
          -(algebraMap k Ω ν * x₀ + z' + algebraMap k Ω 1) by
        rw [hz'def, map_neg, map_one]; ring, racl_neg, racl_add_algebraMap]
    refine jSem_of_shifted hind₀ hX₀ hQ₀ hR₀ hA₀ (neg_ne_zero.2 hν) ?_
    rw [hP']
    exact ptEq (hsum.symm.trans (hνeq.symm.trans hshift.symm))

/-- **Completeness of geometric `J` over algebraically closed fields**,
reduced to guarded completeness of geometric `Q` and completeness of `Q′`. The necessary
outer `Q` guard comes from the first multiplication diagram, not a new hypothesis on `J` (#27). -/
theorem jSem_of_jGeom_of_completeness [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ)
    [ExpChar k q] (htr : (5 : Cardinal) ≤ Algebra.trdeg k Ω)
    (hQc : ∀ P D Y I : Point k Ω, QGeom P D Y I → I ≠ D → I ≠ P → QSem P D Y I)
    (hQ'c : ∀ X Y S E : Point k Ω, Q'Geom X Y S E → Q'Sem X Y S E)
    {X : Fin 5 → Point k Ω} (h : JGeom (X 0) (X 1) (X 2) (X 3) (X 4)) :
    JSem X := by
  have hX : X = ![X 0, X 1, X 2, X 3, X 4] := by
    funext i
    fin_cases i <;> rfl
  rw [hX]
  exact jSem_of_qSem_q'Sem q htr (hQc _ _ _ _ h.1 h.2.1.ne.symm h.2.1.snd_ne_fst)
    (hQ'c _ _ _ _ h.2.1) (hQ'c _ _ _ _ h.2.2)

end Assembly

/-- Completeness of geometric `J` over `K/k`: the open `(3) ⇒ (2)` arrow
of blueprint Theorem `j-descent`, i.e. the completeness half of Theorem
`j-acf-correct` when `k` and `K` are algebraically closed.  The generic
assembly `jGeom_iff_jSem_of_lift` requests it for an arbitrary algebraic
base `K₀`; the canonical form `jGeom_iff_jSem` requests it only for the
algebraically closed pair `k̄ ⊆ K̄`. -/
def JCompletenessACF (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ X : Fin 5 → Point k K, JGeom (X 0) (X 1) (X 2) (X 3) (X 4) → JSem X

/-- `JCompletenessACF` follows from guarded geometric `Q` completeness and geometric `Q′`
completeness over the same ACF pair of rank at least five. Both remain explicit open inputs
(#27); the necessary guard is already forced by `JGeom`. -/
theorem jCompletenessACF_of_completeness {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k Ω)
    (hQc : ∀ P D Y I : Point k Ω, QGeom P D Y I → I ≠ D → I ≠ P → QSem P D Y I)
    (hQ'c : ∀ X Y S E : Point k Ω, Q'Geom X Y S E → Q'Sem X Y S E) :
    JCompletenessACF k Ω :=
  fun _ h ↦ jSem_of_jGeom_of_completeness q htr hQc hQ'c h


end

end AclGeom
