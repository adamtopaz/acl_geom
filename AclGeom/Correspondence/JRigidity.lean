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

section PerCurve

/-- If a prime binomial and another polynomial both lie in a prime
principal ideal, the binomial divides the polynomial. -/
theorem dvd_of_both_mem_span {R : Type*} [CommRing R] [IsDomain R]
    {g b a : R} (hg : Prime g) (hb : Prime b)
    (hbmem : b ∈ Ideal.span {g}) (hamem : a ∈ Ideal.span {g}) :
    b ∣ a := by
  have h1 : g ∣ b := Ideal.mem_span_singleton.1 hbmem
  have h2 : g ∣ a := Ideal.mem_span_singleton.1 hamem
  exact (hg.associated_of_dvd hb h1).symm.dvd.trans h2

/-- **Simultaneous cosets at one curve, first orientation**: a curve
carrying both the additive coset equation of the axes-supported prime
δ-generator and a multiplicative binomial equation `x^m = c·y^n` forces
the coset constant to vanish and the two one-variable parts to be exact
monomials. -/
theorem simultaneous_coset_at_curve [IsAlgClosed k]
    {x y : Ω} {G₂ : MvPolynomial (Fin 2) k} (hG₂p : Prime G₂)
    (hG₂span : idealOf k ![x, y] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    {P Q : Polynomial k} (hP0 : P.coeff 0 = 0) (hQ0 : Q.coeff 0 = 0)
    (hsplit : G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q)
    {d : k} (hval : aeval ![x, y] G = algebraMap k Ω d)
    {c : k} (hc : c ≠ 0) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.gcd m n = 1)
    (hbin : x ^ m = algebraMap k Ω c * y ^ n) :
    d = 0 ∧ ∃ l : k, l ≠ 0 ∧ P = Polynomial.C l * Polynomial.X ^ m ∧
      Q = -(Polynomial.C (l * c)) * Polynomial.X ^ n := by
  have hBmem : ((X 0 : MvPolynomial (Fin 2) k) ^ m - C c * X 1 ^ n) ∈
      Ideal.span {G₂} := by
    rw [← hG₂span]
    exact binomial_mem_idealOf hbin
  have hAmem : (G - C d) ∈ Ideal.span {G₂} := by
    rw [← hG₂span]
    exact shifted_gen_mem_idealOf hval
  have hdvd := dvd_of_both_mem_span hG₂p (mvBinomial_prime hc hm hn hcop)
    hBmem hAmem
  exact eq_smul_binomial_of_dvd_shift hGp hP0 hQ0 hsplit hc hm hn hcop hdvd

/-- Swapping the coordinates exchanges the two one-variable parts of an
axes-supported polynomial. -/
theorem rename_swap_split {P Q : Polynomial k}
    {G : MvPolynomial (Fin 2) k}
    (hsplit : G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q) :
    rename (Equiv.swap (0 : Fin 2) 1) G =
      Polynomial.aeval (X 0) Q + Polynomial.aeval (X 1) P := by
  have h0 : (rename (Equiv.swap (0 : Fin 2) 1)).comp
      (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k)) =
      Polynomial.aeval (X 1) := by
    refine Polynomial.algHom_ext ?_
    rw [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.aeval_X, rename_X]
    norm_num
  have h1 : (rename (Equiv.swap (0 : Fin 2) 1)).comp
      (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k)) =
      Polynomial.aeval (X 0) := by
    refine Polynomial.algHom_ext ?_
    rw [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.aeval_X, rename_X]
    norm_num
  rw [hsplit, map_add]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, h0, h1]
  ring

/-- The vanishing ideal of the swapped pair is spanned by the renamed
generator. -/
theorem idealOf_swap_pair {x y : Ω} {G₂ : MvPolynomial (Fin 2) k}
    (hG₂span : idealOf k ![x, y] = Ideal.span {G₂}) :
    idealOf k ![y, x] =
      Ideal.span {rename (Equiv.swap (0 : Fin 2) 1) G₂} := by
  ext f
  rw [mem_idealOf_iff]
  have htuple : ((![x, y] : Fin 2 → Ω) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) =
      ![y, x] := by
    funext j
    fin_cases j <;> simp
  have hswap : aeval ![y, x] f =
      aeval ![x, y] (rename (Equiv.swap (0 : Fin 2) 1) f) := by
    rw [aeval_rename, htuple]
  rw [hswap, ← mem_idealOf_iff, hG₂span, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  have hswapswap : ∀ g : MvPolynomial (Fin 2) k,
      rename (Equiv.swap (0 : Fin 2) 1)
        (rename (Equiv.swap (0 : Fin 2) 1) g) = g := by
    intro g
    rw [rename_rename]
    have hcomp : (⇑(Equiv.swap (0 : Fin 2) 1) ∘
        ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
      funext i
      simp
    rw [hcomp, rename_id]
    rfl
  constructor
  · intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨rename (Equiv.swap (0 : Fin 2) 1) t, ?_⟩
    have h := congrArg (rename (Equiv.swap (0 : Fin 2) 1)) ht
    rw [hswapswap, map_mul] at h
    exact h
  · intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨rename (Equiv.swap (0 : Fin 2) 1) t, ?_⟩
    have h := congrArg (rename (Equiv.swap (0 : Fin 2) 1)) ht
    rw [map_mul, hswapswap] at h
    exact h

/-- **Simultaneous cosets at one curve, second orientation**: the binomial
equation `y^n = c·x^m` forces the same conclusions with the roles of the
two one-variable parts exchanged. -/
theorem simultaneous_coset_at_curve' [IsAlgClosed k]
    {x y : Ω} {G₂ : MvPolynomial (Fin 2) k} (hG₂p : Prime G₂)
    (hG₂span : idealOf k ![x, y] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    {P Q : Polynomial k} (hP0 : P.coeff 0 = 0) (hQ0 : Q.coeff 0 = 0)
    (hsplit : G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q)
    {d : k} (hval : aeval ![x, y] G = algebraMap k Ω d)
    {c : k} (hc : c ≠ 0) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.gcd m n = 1)
    (hbin : y ^ n = algebraMap k Ω c * x ^ m) :
    d = 0 ∧ ∃ l : k, l ≠ 0 ∧ Q = Polynomial.C l * Polynomial.X ^ n ∧
      P = -(Polynomial.C (l * c)) * Polynomial.X ^ m := by
  have hG₂p' : Prime (rename (Equiv.swap (0 : Fin 2) 1) G₂) := by
    have h := (MulEquiv.prime_iff
      (renameEquiv k (Equiv.swap (0 : Fin 2) 1))).2 hG₂p
    simpa [renameEquiv] using h
  have hGp' : Prime (rename (Equiv.swap (0 : Fin 2) 1) G) := by
    have h := (MulEquiv.prime_iff
      (renameEquiv k (Equiv.swap (0 : Fin 2) 1))).2 hGp
    simpa [renameEquiv] using h
  have hspan' := idealOf_swap_pair hG₂span
  have hsplit' := rename_swap_split hsplit
  have hval' : aeval ![y, x] (rename (Equiv.swap (0 : Fin 2) 1) G) =
      algebraMap k Ω d := by
    rw [aeval_rename]
    have ht : ((![y, x] : Fin 2 → Ω) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) =
        ![x, y] := by
      funext j
      fin_cases j <;> simp
    rw [ht]
    exact hval
  exact simultaneous_coset_at_curve hG₂p' hspan' hGp' hQ0 hP0 hsplit' hval'
    hc hn hm ((Nat.gcd_comm n m).trans hcop) hbin

end PerCurve

section MixedRuleOut

/-- **Mixed-sign rule-out**: an axes-supported relation with nonzero first
one-variable part is incompatible with a mixed monomial parametrization at
a transcendental parameter — clearing denominators produces a nonzero
polynomial vanishing at the transcendental. -/
theorem no_mixed_relation {t : Ω} (htr : Transcendental k t)
    {γ : k} (hγ : γ ≠ 0) {p q : Polynomial k} (hp : p ≠ 0)
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0) {d : k}
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hval : Polynomial.aeval (algebraMap k Ω γ * t ^ n) p +
      Polynomial.aeval ((t ^ m)⁻¹) q = algebraMap k Ω d) :
    False := by
  classical
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htr (isAlgebraic_zero)
  set N : ℕ := m * q.natDegree with hN
  set R : Polynomial k :=
    (Finset.range (p.natDegree + 1)).sum
      (fun i ↦ Polynomial.C (p.coeff i * γ ^ i) *
        Polynomial.X ^ (N + n * i)) +
    (Finset.range (q.natDegree + 1)).sum
      (fun j ↦ Polynomial.C (q.coeff j) * Polynomial.X ^ (N - m * j)) -
    Polynomial.C d * Polynomial.X ^ N with hR
  -- The cleared relation evaluates to zero at `t`.
  have haev : Polynomial.aeval t R = 0 := by
    have hmul := congrArg (fun z ↦ t ^ N * z) hval
    simp only [mul_add] at hmul
    have hp' : t ^ N * Polynomial.aeval (algebraMap k Ω γ * t ^ n) p =
        (Finset.range (p.natDegree + 1)).sum
          (fun i ↦ algebraMap k Ω (p.coeff i * γ ^ i) * t ^ (N + n * i)) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.smul_def, mul_pow, ← map_pow, pow_add, pow_mul]
      rw [map_mul]
      ring
    have hq' : t ^ N * Polynomial.aeval ((t ^ m)⁻¹) q =
        (Finset.range (q.natDegree + 1)).sum
          (fun j ↦ algebraMap k Ω (q.coeff j) * t ^ (N - m * j)) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Algebra.smul_def, inv_pow, ← pow_mul]
      have hle : m * j ≤ N := by
        rw [hN]
        exact Nat.mul_le_mul_left m (Nat.lt_succ_iff.1
          (Finset.mem_range.1 hj))
      have hsplitpow : t ^ N = t ^ (m * j) * t ^ (N - m * j) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [hsplitpow]
      field_simp
    rw [hp', hq'] at hmul
    rw [hR]
    rw [map_sub, map_add, map_sum, map_sum]
    have hterm1 : ∀ i ∈ Finset.range (p.natDegree + 1),
        Polynomial.aeval t (Polynomial.C (p.coeff i * γ ^ i) *
          Polynomial.X ^ (N + n * i)) =
        algebraMap k Ω (p.coeff i * γ ^ i) * t ^ (N + n * i) := by
      intro i _
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    have hterm2 : ∀ j ∈ Finset.range (q.natDegree + 1),
        Polynomial.aeval t (Polynomial.C (q.coeff j) *
          Polynomial.X ^ (N - m * j)) =
        algebraMap k Ω (q.coeff j) * t ^ (N - m * j) := by
      intro j _
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [Finset.sum_congr rfl hterm1, Finset.sum_congr rfl hterm2,
      map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, hmul]
    ring
  -- Transcendence forces the polynomial to vanish identically.
  have hR0 : R = 0 := by
    by_contra hRne
    exact htr ⟨R, hRne, haev⟩
  -- Extract the top coefficient of the `p`-part.
  have hi₀ : 1 ≤ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | h
    · exfalso
      have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [hC, hp0, map_zero] at hp
      exact hp rfl
    · exact h
  have hcoeff := congrArg (fun r ↦ Polynomial.coeff r (N + n * p.natDegree))
    hR0
  simp only [Polynomial.coeff_zero] at hcoeff
  rw [hR] at hcoeff
  rw [Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at hcoeff
  have hsum1 : ((Finset.range (p.natDegree + 1)).sum fun i ↦
      (Polynomial.C (p.coeff i * γ ^ i) *
        Polynomial.X ^ (N + n * i)).coeff (N + n * p.natDegree)) =
      p.coeff p.natDegree * γ ^ p.natDegree := by
    rw [Finset.sum_eq_single p.natDegree]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
        mul_one]
    · intro i _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by
          intro heq
          exact hne (by
            have := Nat.add_left_cancel heq.symm
            exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) this)),
        mul_zero]
    · intro hnotmem
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) hnotmem
  have hsum2 : ((Finset.range (q.natDegree + 1)).sum fun j ↦
      (Polynomial.C (q.coeff j) *
        Polynomial.X ^ (N - m * j)).coeff (N + n * p.natDegree)) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro heq
    have h1 : N - m * j ≤ N := Nat.sub_le _ _
    have h2 : N < N + n * p.natDegree := by
      have := Nat.mul_le_mul (Nat.pos_of_ne_zero hn) hi₀
      omega
    omega
  have hsum3 : (Polynomial.C d *
      Polynomial.X ^ N).coeff (N + n * p.natDegree) = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    have := Nat.mul_le_mul (Nat.pos_of_ne_zero hn) hi₀
    omega
  rw [hsum1, hsum2, hsum3, add_zero, sub_zero] at hcoeff
  have hlead : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp
  exact hlead (by
    have := mul_eq_zero.1 hcoeff
    rcases this with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hγ))

/-- **Mixed rule-out at a curve point**: a pair satisfying a same-sign
monomial relation cannot satisfy an axes-supported relation with nonzero
first part — parametrize the point by a transcendental root and apply the
denominator-clearing contradiction. -/
theorem rule_out_mixed_at_curve [IsAlgClosed k] [IsAlgClosed Ω]
    {x y : Ω} (hxr : x ∉ racl k (∅ : Set Ω)) (hyr : y ∉ racl k (∅ : Set Ω))
    {c' : k} (hc' : c' ≠ 0) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmix : x ^ m * y ^ n = algebraMap k Ω c')
    {p q : Polynomial k} (hp : p ≠ 0) (hp0 : p.coeff 0 = 0)
    (hq0 : q.coeff 0 = 0) {d : k}
    (hval : Polynomial.aeval x p + Polynomial.aeval y q =
      algebraMap k Ω d) :
    False := by
  classical
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyr (zero_mem _)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxr (zero_mem _)
  -- A transcendental root parametrizing the second coordinate.
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (y⁻¹)
    (Nat.pos_of_ne_zero hm)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at ht
    exact hy0 (by rw [← inv_inv y, ← ht, inv_zero])
  have hyt : y = (t ^ m)⁻¹ := by
    rw [ht, inv_inv]
  have httr : Transcendental k t := by
    intro halg
    refine hyr ?_
    have htm : t ∈ racl k (∅ : Set Ω) :=
      (mem_racl_iff k).2 (halg.tower_top _)
    rw [hyt]
    exact inv_mem (pow_mem htm m)
  -- The coefficient of the parametrization is algebraic, hence in `k`.
  have hxm : x ^ m = algebraMap k Ω c' * t ^ (m * n) := by
    have h1 : y ^ n = (t ^ (m * n))⁻¹ := by
      rw [hyt, ← inv_pow, ← pow_mul, inv_pow]
    rw [h1, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ ht0)] at hmix
    exact hmix
  have hγΩ : (x * (t ^ n)⁻¹) ^ m = algebraMap k Ω c' := by
    rw [mul_pow, inv_pow, ← pow_mul, hxm, mul_comm m n]
    field_simp
  have hγmem : x * (t ^ n)⁻¹ ∈ racl k (∅ : Set Ω) := by
    have h1 : (x * (t ^ n)⁻¹) ^ ((m : ℤ)) ∈ racl k (∅ : Set Ω) := by
      rw [zpow_natCast, hγΩ]
      exact IntermediateField.algebraMap_mem _ _
    exact mem_racl_empty_of_zpow (by exact_mod_cast hm) h1
  obtain ⟨γ, hγeq⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hγmem)
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hγeq
    exact (mul_ne_zero hx0 (inv_ne_zero (pow_ne_zero _ ht0))) hγeq.symm
  have hxt : x = algebraMap k Ω γ * t ^ n := by
    rw [hγeq]
    field_simp
  exact no_mixed_relation httr hγ0 hp hp0 hq0 hm hn
    (by rw [← hxt, ← hyt]; exact hval)

end MixedRuleOut

section PPower

open Polynomial

/-- The exponent of a nonzero additive monomial in characteristic zero
is one. -/
theorem monomial_isAdditive_charZero [CharZero k] {l : k} (hl : l ≠ 0)
    {m : ℕ} (h : IsAdditive (Polynomial.C l * Polynomial.X ^ m)) :
    m = 1 := by
  by_contra hne
  have hC := h.eq_C_mul_X
  have hc := congrArg (fun r ↦ Polynomial.coeff r m) hC
  have hlhs : Polynomial.coeff (Polynomial.C l * Polynomial.X ^ m) m = l := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hrhs : Polynomial.coeff (Polynomial.C
      ((Polynomial.C l * Polynomial.X ^ m).coeff 1) * Polynomial.X) m = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X,
      if_neg (fun h ↦ hne h.symm), mul_zero]
  rw [hlhs, hrhs] at hc
  exact hl hc

/-- The exponent of a nonzero additive monomial in characteristic `p` is a
`p`-power. -/
theorem monomial_isAdditive_charP (p : ℕ) [CharP k p] (hp : p.Prime)
    [Infinite k] {l : k} (hl : l ≠ 0) {m : ℕ}
    (h : IsAdditive (Polynomial.C l * Polynomial.X ^ m)) :
    ∃ r : ℕ, m = p ^ r := by
  by_contra hne
  push Not at hne
  have h0 := h.coeff_eq_zero_of_ne_pow p hp hne
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
    mul_one] at h0
  exact hl h0

end PPower

section Master

/-- Additive monomials are classified by the exponential characteristic. -/
theorem monomial_isAdditive_expChar (q : ℕ) [hq : ExpChar k q] [Infinite k]
    {l : k} (hl : l ≠ 0) {m : ℕ}
    (h : IsAdditive (Polynomial.C l * Polynomial.X ^ m)) :
    ∃ r : ℕ, m = q ^ r := by
  rcases hq with _ | hp
  · exact ⟨0, by rw [pow_zero]; exact monomial_isAdditive_charZero hl h⟩
  · exact monomial_isAdditive_charP _ hp hl h

/-- Evaluating an axes split at a pair. -/
theorem aeval_pair_of_split {G : MvPolynomial (Fin 2) k}
    {P Q : Polynomial k}
    (hsplit : G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q)
    (u v : Ω) :
    aeval ![u, v] G = Polynomial.aeval u P + Polynomial.aeval v Q := by
  rw [hsplit, map_add, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.aeval_algHom_apply, aeval_X, aeval_X]
  have h0 : (![u, v] : Fin 2 → Ω) 0 = u := rfl
  have h1 : (![u, v] : Fin 2 → Ω) 1 = v := rfl
  rw [h0, h1]

/-- **Simultaneous additive–multiplicative cosets** (blueprint
Lemma 8.9): two independent finite correspondences whose sums and products
are both interalgebraic satisfy a common monomial relation, in one of the
two orientations, with exponents that are powers of the exponential
characteristic and a common constant. -/
theorem simultaneous_coset [IsAlgClosed k] [IsAlgClosed Ω]
    (q : ℕ) [ExpChar k q] (S : AddCorrSetup k Ω)
    (hy₁0 : S.y₁ ≠ 0) (hy₂0 : S.y₂ ≠ 0)
    (hmul : S.y₁ * S.y₂ ∈ racl k {S.x₁ * S.x₂})
    (hmul' : S.x₁ * S.x₂ ∈ racl k {S.y₁ * S.y₂})
    {s s' : Ω}
    (hs : s ∉ racl k {S.x₁, S.x₂}) (hss' : s' ∉ racl k {S.x₁, S.x₂, s}) :
    ∃ (c : k) (m n r t : ℕ), c ≠ 0 ∧ m = q ^ r ∧ n = q ^ t ∧
      ((S.x₁ ^ m = algebraMap k Ω c * S.y₁ ^ n ∧
        S.x₂ ^ m = algebraMap k Ω c * S.y₂ ^ n) ∨
       (S.y₁ ^ n = algebraMap k Ω c * S.x₁ ^ m ∧
        S.y₂ ^ n = algebraMap k Ω c * S.x₂ ^ m)) := by
  classical
  -- The structured additive data.
  obtain ⟨G, P, Q, hGp, hsplit, hP0, hQ0, hPne, hQne, hPadd, hQadd,
    d₁, d₂, hd₁, hd₂⟩ := S.exists_delta_gen_data hs hss'
  -- The multiplicative data on the same pairs.
  obtain ⟨a, b, c₁, c₂, ha0, hb0, hcop, hc₁0, hc₂0, h₁raw, h₂raw⟩ :=
    (⟨S.x₁, S.y₁, S.x₂, S.y₂, S.indep, hy₁0, hy₂0, S.y₁_mem, S.x₁_mem,
      S.y₂_mem, S.x₂_mem, hmul, hmul'⟩ :
      MulCorrSetup k Ω).exists_coset_equations_coprime hs
  have h₁ : S.x₁ ^ a * S.y₁ ^ b = algebraMap k Ω c₁ := h₁raw
  have h₂ : S.x₂ ^ a * S.y₂ ^ b = algebraMap k Ω c₂ := h₂raw
  -- The curve generators.
  have hx₁tr : Transcendental k S.x₁ := fun h ↦
    S.x₁_notMem (racl_mono (Set.empty_subset _)
      ((mem_racl_iff k).2 (h.tower_top _)))
  have hx₂tr : Transcendental k S.x₂ := fun h ↦
    S.x₂_notMem (racl_mono (Set.empty_subset _)
      ((mem_racl_iff k).2 (h.tower_top _)))
  obtain ⟨G₁, hG₁p, hG₁span⟩ := exists_prime_span_idealOf k hx₁tr S.y₁_mem
  obtain ⟨G₂, hG₂p, hG₂span⟩ := exists_prime_span_idealOf k hx₂tr S.y₂_mem
  -- Transcendence bookkeeping and split values, for the mixed rule-out.
  have hx₁r : S.x₁ ∉ racl k (∅ : Set Ω) := fun h ↦
    S.x₁_notMem (racl_mono (Set.empty_subset _) h)
  have hx₂r : S.x₂ ∉ racl k (∅ : Set Ω) := fun h ↦
    S.x₂_notMem (racl_mono (Set.empty_subset _) h)
  have hy₁r : S.y₁ ∉ racl k (∅ : Set Ω) := by
    intro h
    have h2 := racl_insert_of_mem (S := (∅ : Set Ω)) h
    refine hx₁r ?_
    have h3 : S.x₁ ∈ racl k (insert S.y₁ (∅ : Set Ω)) := by
      have hins : (insert S.y₁ (∅ : Set Ω)) = {S.y₁} := by simp
      rw [hins]
      exact S.x₁_mem
    rwa [h2] at h3
  have hy₂r : S.y₂ ∉ racl k (∅ : Set Ω) := by
    intro h
    have h2 := racl_insert_of_mem (S := (∅ : Set Ω)) h
    refine hx₂r ?_
    have h3 : S.x₂ ∈ racl k (insert S.y₂ (∅ : Set Ω)) := by
      have hins : (insert S.y₂ (∅ : Set Ω)) = {S.y₂} := by simp
      rw [hins]
      exact S.x₂_mem
    rwa [h2] at h3
  have hval₁ : Polynomial.aeval S.x₁ P + Polynomial.aeval S.y₁ Q =
      algebraMap k Ω d₁ := by
    rw [← aeval_pair_of_split hsplit]
    exact hd₁
  have hx₁0 : S.x₁ ≠ 0 := fun h0 ↦ hx₁r (by rw [h0]; exact zero_mem _)
  have hx₂0 : S.x₂ ≠ 0 := fun h0 ↦ hx₂r (by rw [h0]; exact zero_mem _)
  -- Exponent data.
  have hmA : a.natAbs ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnA : b.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hb0
  have hcopA : Nat.gcd a.natAbs b.natAbs = 1 := hcop
  -- Case on the shared signs of the exponents.
  rcases sign_cases_of_zpow_relation hx₁0 hy₁0 ha0 hb0 h₁ with
    ⟨hap, hbn, hbin₁⟩ | ⟨han, hbp, hbin₁⟩ | ⟨hap, hbp, hmix₁⟩ |
    ⟨han, hbn, hmix₁⟩
  · -- First orientation: `x^m = c·y^n` at both curves.
    have hbin₂ : S.x₂ ^ a.natAbs = algebraMap k Ω c₂ * S.y₂ ^ b.natAbs := by
      rcases sign_cases_of_zpow_relation hx₂0 hy₂0 ha0 hb0 h₂ with
        ⟨_, _, hb⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨h, _, _⟩
      · exact hb
      · exact absurd h (asymm hap)
      · exact absurd h (asymm hbn)
      · exact absurd h (asymm hap)
    obtain ⟨hd₁0, l₁, hl₁0, hP₁, hQ₁⟩ := simultaneous_coset_at_curve hG₁p
      hG₁span hGp hP0 hQ0 hsplit hd₁ hc₁0 hmA hnA hcopA hbin₁
    obtain ⟨hd₂0, l₂, hl₂0, hP₂, hQ₂⟩ := simultaneous_coset_at_curve hG₂p
      hG₂span hGp hP0 hQ0 hsplit hd₂ hc₂0 hmA hnA hcopA hbin₂
    have hll : l₁ = l₂ := by
      have h := hP₁.symm.trans hP₂
      have hc := congrArg (fun r ↦ Polynomial.coeff r a.natAbs) h
      simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc
    have hcc : c₁ = c₂ := by
      have h := hQ₁.symm.trans hQ₂
      have hc : l₁ * c₁ = l₂ * c₂ := by
        have h1 := congrArg (fun r ↦ Polynomial.coeff r b.natAbs) h
        simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_assoc]
          using h1
      rw [hll] at hc
      exact mul_left_cancel₀ hl₂0 hc
    obtain ⟨r, hr⟩ := monomial_isAdditive_expChar q hl₁0 (by
      rw [← hP₁]; exact hPadd)
    have hQform : Q = Polynomial.C (-(l₁ * c₁)) * Polynomial.X ^ b.natAbs := by
      rw [hQ₁, map_neg]
    obtain ⟨t, ht⟩ := monomial_isAdditive_expChar q
      (neg_ne_zero.2 (mul_ne_zero hl₁0 hc₁0)) (by
        rw [← hQform]; exact hQadd)
    refine ⟨c₁, a.natAbs, b.natAbs, r, t, hc₁0, hr, ht, Or.inl ⟨hbin₁, ?_⟩⟩
    rw [hcc]
    exact hbin₂
  · -- Second orientation: `y^n = c·x^m` at both curves.
    have hbin₂ : S.y₂ ^ b.natAbs = algebraMap k Ω c₂ * S.x₂ ^ a.natAbs := by
      rcases sign_cases_of_zpow_relation hx₂0 hy₂0 ha0 hb0 h₂ with
        ⟨h, _, _⟩ | ⟨_, _, hb⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩
      · exact absurd h (asymm han)
      · exact hb
      · exact absurd h (asymm han)
      · exact absurd h (asymm hbp)
    obtain ⟨hd₁0, l₁, hl₁0, hQ₁, hP₁⟩ := simultaneous_coset_at_curve' hG₁p
      hG₁span hGp hP0 hQ0 hsplit hd₁ hc₁0 hmA hnA hcopA hbin₁
    obtain ⟨hd₂0, l₂, hl₂0, hQ₂, hP₂⟩ := simultaneous_coset_at_curve' hG₂p
      hG₂span hGp hP0 hQ0 hsplit hd₂ hc₂0 hmA hnA hcopA hbin₂
    have hll : l₁ = l₂ := by
      have h := hQ₁.symm.trans hQ₂
      have hc := congrArg (fun r ↦ Polynomial.coeff r b.natAbs) h
      simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc
    have hcc : c₁ = c₂ := by
      have h := hP₁.symm.trans hP₂
      have hc : l₁ * c₁ = l₂ * c₂ := by
        have h1 := congrArg (fun r ↦ Polynomial.coeff r a.natAbs) h
        simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_assoc]
          using h1
      rw [hll] at hc
      exact mul_left_cancel₀ hl₂0 hc
    obtain ⟨t, ht⟩ := monomial_isAdditive_expChar q hl₁0 (by
      rw [← hQ₁]; exact hQadd)
    have hPform : P = Polynomial.C (-(l₁ * c₁)) * Polynomial.X ^ a.natAbs := by
      rw [hP₁, map_neg]
    obtain ⟨r, hr⟩ := monomial_isAdditive_expChar q
      (neg_ne_zero.2 (mul_ne_zero hl₁0 hc₁0)) (by
        rw [← hPform]; exact hPadd)
    refine ⟨c₁, a.natAbs, b.natAbs, r, t, hc₁0, hr, ht, Or.inr ⟨hbin₁, ?_⟩⟩
    rw [hcc]
    exact hbin₂
  · -- Mixed signs are impossible.
    exact absurd hval₁ (fun hv ↦ rule_out_mixed_at_curve hx₁r hy₁r hc₁0
      hmA hnA hmix₁ hPne hP0 hQ0 hv)
  · exact absurd hval₁ (fun hv ↦ rule_out_mixed_at_curve hx₁r hy₁r
      (inv_ne_zero hc₁0) hmA hnA hmix₁ hPne hP0 hQ0 hv)

end Master

section BaseRatio

/-- **The base-ratio lemma** (blueprint Corollary of Theorem 8.9): two
interalgebraic nonzero elements whose products with a common independent
transcendental are interalgebraic differ by a constant. Obtained from the
multiplicative correspondence theorem applied to the pair and the
degenerate correspondence `(t, t)`: the second coset equation forces the
exponents to cancel, and the first then bounds the ratio. -/
theorem base_ratio [IsAlgClosed k] [IsAlgClosed Ω] {u₁ u₂ t : Ω}
    (hind : AlgebraicIndependent k ![u₁, t]) (hu₂0 : u₂ ≠ 0)
    (hu₂ : u₂ ∈ racl k {u₁}) (hu₁ : u₁ ∈ racl k {u₂})
    (hmul : u₂ * t ∈ racl k {u₁ * t}) (hmul' : u₁ * t ∈ racl k {u₂ * t})
    {s : Ω} (hs : s ∉ racl k {u₁, t}) :
    ∃ e : k, e ≠ 0 ∧ u₂ = algebraMap k Ω e * u₁ := by
  classical
  have ht0 : t ≠ 0 := by
    intro h0
    have h := AlgebraicIndependent.notMem_racl_pair hind
    rw [h0] at h
    exact h (zero_mem _)
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    have h := AlgebraicIndependent.notMem_racl_pair' hind
    rw [h0] at h
    exact h (zero_mem _)
  have htt : t ∈ racl k ({t} : Set Ω) := subset_racl k _ rfl
  obtain ⟨a, b, c₁, c₂, ha0, hb0, hc₁0, hc₂0, h₁raw, h₂raw⟩ :=
    (⟨u₁, u₂, t, t, hind, hu₂0, ht0, hu₂, hu₁, htt, htt, hmul, hmul'⟩ :
      MulCorrSetup k Ω).exists_coset_equations hs
  have h₁ : u₁ ^ a * u₂ ^ b = algebraMap k Ω c₁ := h₁raw
  have h₂ : t ^ a * t ^ b = algebraMap k Ω c₂ := h₂raw
  -- The degenerate pair forces the exponents to cancel.
  have httr : t ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hind
      (racl_mono (Set.empty_subset _) h)
  have hab : a + b = 0 := by
    by_contra hne
    rw [← zpow_add₀ ht0] at h₂
    refine httr (mem_racl_empty_of_zpow hne ?_)
    rw [h₂]
    exact IntermediateField.algebraMap_mem _ _
  have hbeq : b = -a := by omega
  -- The ratio has a constant power, hence is a constant.
  have hratio : (u₁ * u₂⁻¹) ^ a = algebraMap k Ω c₁ := by
    rw [mul_zpow, ← h₁, hbeq, zpow_neg, inv_zpow]
  have hrmem : u₁ * u₂⁻¹ ∈ racl k (∅ : Set Ω) := by
    refine mem_racl_empty_of_zpow ha0 ?_
    rw [hratio]
    exact IntermediateField.algebraMap_mem _ _
  obtain ⟨e', he'⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hrmem)
  have he'0 : e' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at he'
    exact (mul_ne_zero hu₁0 (inv_ne_zero hu₂0)) he'.symm
  refine ⟨e'⁻¹, inv_ne_zero he'0, ?_⟩
  rw [map_inv₀, he', mul_inv, inv_inv]
  field_simp

end BaseRatio

end

end AclGeom
