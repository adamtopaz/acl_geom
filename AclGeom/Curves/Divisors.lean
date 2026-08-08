/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Approximation

/-!
# Finiteness of zeros: toward divisors

The finiteness theorem for the divisor layer (Stichtenoth Corollary
1.3.4): a nonzero element of a one-variable function field has finitely
many zero places, bounded by `[F : k(f)]`.

The engine is the **uniform order** of a `k(z)`-element: the exponent in
`v w = (v z)^m` depends only on `w` (it is the difference of root
multiplicities at `0` of a fixed rational presentation), not on the place
(`exists_uniform_valuation_zpow`). Consequently, in a vanishing
`k(f)`-combination of weak-approximation witnesses, the term of *minimal
order* strictly dominates at its own place — no normalization needed —
and the ultrametric sum lemma yields a contradiction
(`finite_setOf_valuation_lt_one`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P2).
-/

namespace AclGeom

open Polynomial IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section UniformOrder

variable {O : ValuationSubring F}

/-- Explicit form of the polynomial-value computation: the exponent is
the root multiplicity at `0`. -/
theorem valuation_aeval_eq_pow_rootMultiplicity
    (hk : ∀ c : k, algebraMap k F c ∈ O) {z : F}
    (hz : O.valuation z < 1) {p : Polynomial k} (hp : p ≠ 0) :
    O.valuation (aeval z p) = O.valuation z ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hq, hqnd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  rw [map_zero, sub_zero] at hq hqnd
  have hq0 : q.coeff 0 ≠ 0 := fun h ↦ hqnd (Polynomial.X_dvd_iff.2 h)
  conv_lhs => rw [hq]
  rw [map_mul, map_pow, aeval_X, Valuation.map_mul, Valuation.map_pow,
    valuation_aeval_eq_one hk hz hq0, mul_one]

/-- **The uniform order** of an element of `k(z)`: a single integer `m`
with `v w = (v z)^m` at *every* place where `z` is small. The exponent is
read off a fixed rational presentation of `w`, independently of the
place. -/
theorem exists_uniform_valuation_zpow {z w : F}
    (hztr : Transcendental k z) (hw : w ∈ adjoin k ({z} : Set F))
    (hw0 : w ≠ 0) :
    ∃ m : ℤ, ∀ O : ValuationSubring F,
      (∀ c : k, algebraMap k F c ∈ O) → O.valuation z < 1 →
      O.valuation w = O.valuation z ^ m := by
  have hz0 : z ≠ 0 := fun h ↦ hztr (h ▸ isAlgebraic_zero)
  rw [IntermediateField.mem_adjoin_simple_iff] at hw
  obtain ⟨p, q, hpq⟩ := hw
  have hq0 : aeval z q ≠ 0 := by
    intro h0
    rw [hpq, h0, div_zero] at hw0
    exact hw0 rfl
  have hp0 : aeval z p ≠ 0 := by
    intro h0
    rw [hpq, h0, zero_div] at hw0
    exact hw0 rfl
  have hpne : p ≠ 0 := fun h ↦ hp0 (by rw [h, map_zero])
  have hqne : q ≠ 0 := fun h ↦ hq0 (by rw [h, map_zero])
  refine ⟨(p.rootMultiplicity 0 : ℤ) - (q.rootMultiplicity 0 : ℤ),
    fun O hk hz ↦ ?_⟩
  have hzv : O.valuation z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  rw [hpq, map_div₀,
    valuation_aeval_eq_pow_rootMultiplicity hk hz hpne,
    valuation_aeval_eq_pow_rootMultiplicity hk hz hqne,
    zpow_sub₀ hzv, zpow_natCast, zpow_natCast]

end UniformOrder

section Finiteness

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **Finiteness of zeros** (Stichtenoth Corollary 1.3.4): a nonzero
element of a one-variable function field has finitely many zero places.
Weak-approximation witnesses at distinct zeros are `k(f)`-linearly
independent — the minimal-uniform-order term dominates at its own
place — so the number of zeros is bounded by `[F : k(f)]`. -/
theorem finite_setOf_valuation_lt_one {f : F} (hf0 : f ≠ 0) :
    {P : Place k F | P.val.valuation f < 1}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- `f` is transcendental: it has a zero place.
  obtain ⟨P₁, hP₁⟩ := hinf.nonempty
  have htr : Transcendental k f :=
    transcendental_of_valuation_lt_one P₁.algebraMap_mem
      (fun y hy ↦ exists_algebraMap_eq_of_isAlgebraic hy) hf0 hP₁
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  set n := Module.finrank (↥(adjoin k ({f} : Set F))) F with hn
  -- Extract `n + 1` distinct zero places.
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (n + 1)
  set P : Fin (n + 1) → Place k F :=
    fun i ↦ (T.equivFin.symm (Fin.cast hTcard.symm i) : Place k F)
    with hPdef
  have hPinj : Function.Injective P := by
    intro i j hij
    have h1 := Subtype.ext hij
    have h2 := T.equivFin.symm.injective h1
    exact Fin.val_injective (by simpa using congrArg Fin.val h2)
  have hPzero : ∀ i, (P i).val.valuation f < 1 := fun i ↦
    hTsub (Finset.coe_mem _)
  -- Weak-approximation witnesses at each place.
  have hzex : ∀ i : Fin (n + 1), ∃ z : F,
      1 < (P i).val.valuation z ∧
      ∀ j : Fin n, (P (i.succAbove j)).val.valuation z < 1 := fun i ↦
    (P i).exists_one_lt_forall_lt_one (fun j ↦ P (i.succAbove j))
      (fun j ↦ fun h ↦ (Fin.succAbove_ne i j) (hPinj h).symm)
  choose z hz₁ hz₂ using hzex
  -- Values of the witnesses at all the places.
  have hzsmall : ∀ i i' : Fin (n + 1), i' ≠ i →
      (P i').val.valuation (z i) < 1 := by
    intro i i' hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have h1 := hz₂ i j
    rwa [hj] at h1
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h0
    have h1 := hz₁ i
    rw [h0, Valuation.map_zero] at h1
    simp at h1
  -- The witnesses are linearly independent over `k(f)`.
  have hind : LinearIndependent (↥(adjoin k ({f} : Set F))) z := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum i₀'
    by_contra hg₀
    set s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i ↦ g i ≠ 0)
      with hsdef
    have hi₀s : i₀' ∈ s := by simp [hsdef, hg₀]
    have hcoe0 : ∀ i ∈ s, ((g i : F)) ≠ 0 := by
      intro i hi
      rw [hsdef, Finset.mem_filter] at hi
      simpa using hi.2
    -- Uniform orders of the coefficients.
    have hords : ∀ i ∈ s, ∃ m : ℤ, ∀ O : ValuationSubring F,
        (∀ c : k, algebraMap k F c ∈ O) → O.valuation f < 1 →
        O.valuation ((g i : F)) = O.valuation f ^ m := by
      intro i hi
      exact exists_uniform_valuation_zpow htr (SetLike.coe_mem (g i))
        (hcoe0 i hi)
    choose! m hm using hords
    -- The index of minimal order dominates at its own place.
    obtain ⟨i₀, hi₀, hi₀min⟩ := s.exists_min_image m ⟨i₀', hi₀s⟩
    set Q := P i₀ with hQdef
    have hQz : Q.val.valuation f < 1 := hPzero i₀
    have hfv : Q.val.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf0
    have hfvpos : (0 : _) < Q.val.valuation f := zero_lt_iff.2 hfv
    have hdom : ∀ i ∈ s, i ≠ i₀ →
        Q.val.valuation ((g i : F) * z i) <
          Q.val.valuation ((g i₀ : F) * z i₀) := by
      intro i hi hne
      rw [Valuation.map_mul, Valuation.map_mul,
        hm i hi Q.val Q.algebraMap_mem hQz,
        hm i₀ hi₀ Q.val Q.algebraMap_mem hQz]
      have h1 : Q.val.valuation f ^ m i ≤ Q.val.valuation f ^ m i₀ :=
        zpow_le_zpow_right_of_le_one₀ hfvpos hQz.le (hi₀min i hi)
      have h2 : Q.val.valuation (z i) < 1 := hzsmall i i₀ hne.symm
      have h3 : (1 : _) < Q.val.valuation (z i₀) := hz₁ i₀
      calc Q.val.valuation f ^ m i * Q.val.valuation (z i)
          ≤ Q.val.valuation f ^ m i₀ * Q.val.valuation (z i) := by
            rcases eq_or_ne (Q.val.valuation (z i)) 0 with hz' | hz'
            · rw [hz', mul_zero, mul_zero]
            · exact (OrderIso.mulRight₀ _ (zero_lt_iff.2 hz')).monotone h1
        _ < Q.val.valuation f ^ m i₀ * 1 := by
            refine (OrderIso.mulLeft₀ _ (zero_lt_iff.2 ?_)).strictMono h2
            exact zpow_ne_zero _ hfv
        _ < Q.val.valuation f ^ m i₀ * Q.val.valuation (z i₀) := by
            refine (OrderIso.mulLeft₀ _ (zero_lt_iff.2 ?_)).strictMono h3
            exact zpow_ne_zero _ hfv
    -- The dominant term makes the vanishing sum nonzero.
    have hss : ∑ i ∈ s, (g i : F) * z i = 0 := by
      rw [← hsum]
      rw [show ∑ i : Fin (n + 1), g i • z i =
          ∑ i : Fin (n + 1), (g i : F) * z i from
        Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def]; rfl]
      refine Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ ?_
      rw [hsdef, Finset.mem_filter, not_and, not_not] at hi
      rw [hi (Finset.mem_univ i), ZeroMemClass.coe_zero, zero_mul]
    have h0 := valuation_sum_eq_of_forall_lt (f := fun i ↦ (g i : F) * z i)
      hi₀ hdom
    rw [hss, Valuation.map_zero] at h0
    have h4 : Q.val.valuation ((g i₀ : F) * z i₀) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact mul_ne_zero (hcoe0 i₀ hi₀) (hz0 i₀)
    exact h4 h0.symm
  -- The independence contradicts the finrank bound.
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

/-- Finiteness of poles: the zeros of the inverse. -/
theorem finite_setOf_one_lt_valuation {f : F} (hf0 : f ≠ 0) :
    {P : Place k F | 1 < P.val.valuation f}.Finite := by
  have h1 := finite_setOf_valuation_lt_one (k := k) (inv_ne_zero hf0)
  refine h1.subset fun P hP ↦ ?_
  rw [Set.mem_setOf_eq, map_inv₀]
  rw [Set.mem_setOf_eq] at hP
  have hfv : P.val.valuation f ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hf0
  rw [inv_lt_one₀ (zero_lt_iff.2 hfv)]
  exact hP

end Finiteness

section Ord

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

namespace Place

/-- Packaged uniformizer existence for a place. -/
theorem exists_uniformizer (P : Place k F) :
    ∃ t : F, P.val.valuation t ≠ 0 ∧ P.val.valuation t < 1 ∧
      ∀ w : F, P.val.valuation w ≠ 0 → P.val.valuation w < 1 →
        P.val.valuation w ≤ P.val.valuation t := by
  obtain ⟨z, hz0, hz⟩ := exists_valuation_lt_one_of_ne_top P.ne_top
  have htr := transcendental_of_valuation_lt_one P.algebraMap_mem
    (fun y hy ↦ exists_algebraMap_eq_of_isAlgebraic hy) hz0 hz
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  exact exists_valuation_uniformizer P.algebraMap_mem hz0 hz

/-- A chosen uniformizer for a place: an element whose value is the
maximum among nonzero values below one. -/
noncomputable def pi (P : Place k F) : F := P.exists_uniformizer.choose

theorem pi_valuation_ne_zero (P : Place k F) :
    P.val.valuation P.pi ≠ 0 := P.exists_uniformizer.choose_spec.1

theorem pi_valuation_lt_one (P : Place k F) :
    P.val.valuation P.pi < 1 := P.exists_uniformizer.choose_spec.2.1

theorem le_pi_valuation (P : Place k F) {w : F}
    (hw0 : P.val.valuation w ≠ 0) (hwlt : P.val.valuation w < 1) :
    P.val.valuation w ≤ P.val.valuation P.pi :=
  P.exists_uniformizer.choose_spec.2.2 w hw0 hwlt

theorem pi_valuation_pos (P : Place k F) :
    (0 : _) < P.val.valuation P.pi :=
  zero_lt_iff.2 P.pi_valuation_ne_zero

/-- Every nonzero element's value is a unique integer power of the
uniformizer's value. -/
theorem existsUnique_zpow_valuation (P : Place k F) {f : F}
    (hf : f ≠ 0) : ∃! m : ℤ,
      P.val.valuation f = P.val.valuation P.pi ^ m := by
  have hfv : P.val.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  have huniq : ∀ m m' : ℤ, P.val.valuation P.pi ^ m =
      P.val.valuation P.pi ^ m' → m = m' := fun m m' h ↦
    zpow_left_injective_of_lt_one P.pi_valuation_pos
      P.pi_valuation_lt_one h
  -- Existence by trichotomy, through the value classification.
  obtain ⟨z, hz0, hz⟩ := exists_valuation_lt_one_of_ne_top P.ne_top
  have htr := transcendental_of_valuation_lt_one P.algebraMap_mem
    (fun y hy ↦ exists_algebraMap_eq_of_isAlgebraic hy) hz0 hz
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  have hclass : ∀ w : F, P.val.valuation w ≠ 0 → P.val.valuation w < 1 →
      ∃ j : ℕ, 0 < j ∧
        P.val.valuation w = P.val.valuation P.pi ^ j :=
    fun w hw0 hwlt ↦ valuation_eq_pow_uniformizer P.algebraMap_mem hz0 hz
      P.pi_valuation_ne_zero P.pi_valuation_lt_one
      (fun w' h1 h2 ↦ P.le_pi_valuation h1 h2) hw0 hwlt
  rcases lt_trichotomy (P.val.valuation f) 1 with hlt | heq | hgt
  · obtain ⟨j, -, hj⟩ := hclass f hfv hlt
    refine ⟨(j : ℤ), ?_, fun m hm ↦ huniq m j ?_⟩
    · change P.val.valuation f = P.val.valuation P.pi ^ ((j : ℕ) : ℤ)
      rw [hj, zpow_natCast]
    · have hm' : P.val.valuation f = P.val.valuation P.pi ^ m := hm
      rw [← hm', hj, zpow_natCast]
  · refine ⟨0, ?_, fun m hm ↦ huniq m 0 ?_⟩
    · change P.val.valuation f = P.val.valuation P.pi ^ (0 : ℤ)
      rw [heq, zpow_zero]
    · have hm' : P.val.valuation f = P.val.valuation P.pi ^ m := hm
      rw [← hm', heq, zpow_zero]
  · have hfv' : P.val.valuation f⁻¹ ≠ 0 := by
      rw [map_inv₀]
      exact inv_ne_zero hfv
    have hlt' : P.val.valuation f⁻¹ < 1 := by
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 hfv)]
      exact hgt
    obtain ⟨j, -, hj⟩ := hclass f⁻¹ hfv' hlt'
    rw [map_inv₀] at hj
    refine ⟨-(j : ℤ), ?_, fun m hm ↦ huniq m (-(j : ℤ)) ?_⟩
    · change P.val.valuation f = P.val.valuation P.pi ^ (-(j : ℤ))
      rw [zpow_neg, zpow_natCast, ← hj, inv_inv]
    · have hm' : P.val.valuation f = P.val.valuation P.pi ^ m := hm
      rw [← hm', zpow_neg, zpow_natCast, ← hj, inv_inv]

open Classical in
/-- The **order** of `f` at a place: the integer exponent of the
uniformizer's value, positive at zeros, negative at poles, `0` at units
(and junk `0` at `f = 0`). -/
noncomputable def ord (P : Place k F) (f : F) : ℤ :=
  if hf : f = 0 then 0
  else (P.existsUnique_zpow_valuation hf).exists.choose

theorem valuation_eq_zpow_ord (P : Place k F) {f : F} (hf : f ≠ 0) :
    P.val.valuation f = P.val.valuation P.pi ^ P.ord f := by
  rw [ord, dif_neg hf]
  exact (P.existsUnique_zpow_valuation hf).exists.choose_spec

theorem ord_eq_of_valuation_eq_zpow (P : Place k F) {f : F} (hf : f ≠ 0)
    {m : ℤ} (h : P.val.valuation f = P.val.valuation P.pi ^ m) :
    P.ord f = m := by
  have h1 := P.valuation_eq_zpow_ord hf
  exact zpow_left_injective_of_lt_one P.pi_valuation_pos
    P.pi_valuation_lt_one (h1.symm.trans h)

/-- Additivity of the order. -/
theorem ord_mul (P : Place k F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f * g) = P.ord f + P.ord g := by
  refine P.ord_eq_of_valuation_eq_zpow (mul_ne_zero hf hg) ?_
  rw [Valuation.map_mul, P.valuation_eq_zpow_ord hf,
    P.valuation_eq_zpow_ord hg,
    zpow_add₀ P.pi_valuation_ne_zero]

theorem ord_inv (P : Place k F) {f : F} (hf : f ≠ 0) :
    P.ord f⁻¹ = -P.ord f := by
  refine P.ord_eq_of_valuation_eq_zpow (inv_ne_zero hf) ?_
  rw [map_inv₀, P.valuation_eq_zpow_ord hf, ← zpow_neg]

theorem ord_eq_zero_iff (P : Place k F) {f : F} (hf : f ≠ 0) :
    P.ord f = 0 ↔ P.val.valuation f = 1 := by
  constructor
  · intro h0
    have h1 := P.valuation_eq_zpow_ord hf
    rw [h0, zpow_zero] at h1
    exact h1
  · intro h1
    exact P.ord_eq_of_valuation_eq_zpow hf (by rw [h1, zpow_zero])

theorem ord_pos_iff (P : Place k F) {f : F} (hf : f ≠ 0) :
    0 < P.ord f ↔ P.val.valuation f < 1 := by
  have h1 := P.valuation_eq_zpow_ord hf
  constructor
  · intro h0
    rw [h1]
    calc P.val.valuation P.pi ^ P.ord f
        < P.val.valuation P.pi ^ (0 : ℤ) :=
          zpow_lt_zpow_right_of_lt_one₀ P.pi_valuation_pos
            P.pi_valuation_lt_one h0
      _ = 1 := zpow_zero _
  · intro hlt
    by_contra hc
    push Not at hc
    have h2 : P.val.valuation P.pi ^ (0 : ℤ) ≤
        P.val.valuation P.pi ^ P.ord f := by
      rcases eq_or_lt_of_le hc with heq | hlt'
      · rw [heq]
      · exact (zpow_lt_zpow_right_of_lt_one₀ P.pi_valuation_pos
          P.pi_valuation_lt_one hlt').le
    rw [zpow_zero] at h2
    rw [h1] at hlt
    exact hlt.not_ge h2

theorem pi_ne_zero (P : Place k F) : P.pi ≠ 0 := fun h ↦
  P.pi_valuation_ne_zero (by rw [h, Valuation.map_zero])

theorem ord_pi (P : Place k F) : P.ord P.pi = 1 :=
  P.ord_eq_of_valuation_eq_zpow P.pi_ne_zero (by rw [zpow_one])

/-- Order of an integer power. -/
theorem ord_zpow (P : Place k F) {f : F} (hf : f ≠ 0) (n : ℤ) :
    P.ord (f ^ n) = n * P.ord f := by
  refine P.ord_eq_of_valuation_eq_zpow (zpow_ne_zero n hf) ?_
  rw [map_zpow₀, P.valuation_eq_zpow_ord hf, ← zpow_mul, mul_comm]

/-- Nonzero constants have order zero everywhere. -/
theorem ord_algebraMap (P : Place k F) {c : k} (hc : c ≠ 0) :
    P.ord (algebraMap k F c) = 0 :=
  (P.ord_eq_zero_iff ((map_ne_zero (algebraMap k F)).2 hc)).2
    (valuation_algebraMap_eq_one P.algebraMap_mem hc)

/-- Negation preserves the order. -/
theorem ord_neg (P : Place k F) {f : F} (hf : f ≠ 0) :
    P.ord (-f) = P.ord f := by
  refine P.ord_eq_of_valuation_eq_zpow (neg_ne_zero.2 hf) ?_
  rw [Valuation.map_neg, P.valuation_eq_zpow_ord hf]

/-- Nonnegative order characterizes integrality. -/
theorem ord_nonneg_iff (P : Place k F) {f : F} (hf : f ≠ 0) :
    0 ≤ P.ord f ↔ P.val.valuation f ≤ 1 := by
  have h1 := P.valuation_eq_zpow_ord hf
  constructor
  · intro h0
    rw [h1]
    calc P.val.valuation P.pi ^ P.ord f
        ≤ P.val.valuation P.pi ^ (0 : ℤ) :=
          zpow_le_zpow_right_of_le_one₀ P.pi_valuation_pos
            P.pi_valuation_lt_one.le h0
      _ = 1 := zpow_zero _
  · intro hle
    by_contra hc
    push Not at hc
    have h2 : P.val.valuation P.pi ^ (0 : ℤ) <
        P.val.valuation P.pi ^ P.ord f :=
      zpow_lt_zpow_right_of_lt_one₀ P.pi_valuation_pos
        P.pi_valuation_lt_one hc
    rw [zpow_zero, ← h1] at h2
    exact h2.not_ge hle

/-- The order reverses the valuation comparison. -/
theorem valuation_le_valuation_iff (P : Place k F) {f g : F} (hf : f ≠ 0)
    (hg : g ≠ 0) :
    P.val.valuation f ≤ P.val.valuation g ↔ P.ord g ≤ P.ord f := by
  rw [P.valuation_eq_zpow_ord hf, P.valuation_eq_zpow_ord hg]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact ((zpow_lt_zpow_right_of_lt_one₀ P.pi_valuation_pos
      P.pi_valuation_lt_one hc).not_ge h).elim
  · intro h
    exact zpow_le_zpow_right_of_le_one₀ P.pi_valuation_pos
      P.pi_valuation_lt_one.le h

/-- Ultrametric superadditivity of the order. -/
theorem min_ord_le_ord_add (P : Place k F) {f g : F} (hf : f ≠ 0)
    (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  have hmax := P.val.valuation.map_add f g
  rcases max_cases (P.val.valuation f) (P.val.valuation g) with
    ⟨hmx, -⟩ | ⟨hmx, -⟩
  · rw [hmx] at hmax
    have h1 := (P.valuation_le_valuation_iff hfg hf).1 hmax
    exact le_trans (min_le_left _ _) h1
  · rw [hmx] at hmax
    have h1 := (P.valuation_le_valuation_iff hfg hg).1 hmax
    exact le_trans (min_le_right _ _) h1

end Place

/-- A **divisor** on the places of `F/k`: a finitely supported integer
combination of places. -/
abbrev Divisor (k F : Type*) [Field k] [Field F] [Algebra k F] :=
  Place k F →₀ ℤ

/-- The **degree** of a divisor: the sum of its coefficients. -/
noncomputable def Divisor.deg (D : Divisor k F) : ℤ := D.sum fun _ m ↦ m

variable (k) in
/-- The **principal divisor** of a nonzero element: orders at all places
(junk `0` at `f = 0`). -/
noncomputable def divisorOf (f : F) : Divisor k F := by
  classical
  exact if hf : f = 0 then 0 else
    Finsupp.ofSupportFinite (fun P ↦ P.ord f) (by
      refine Set.Finite.subset ((finite_setOf_valuation_lt_one hf).union
        (finite_setOf_one_lt_valuation hf)) ?_
      intro P hP
      rw [Function.mem_support] at hP
      rcases lt_trichotomy (P.val.valuation f) 1 with hlt | heq | hgt
      · exact Or.inl hlt
      · exact absurd ((P.ord_eq_zero_iff hf).2 heq) hP
      · exact Or.inr hgt)

theorem divisorOf_apply {f : F} (hf : f ≠ 0) (P : Place k F) :
    divisorOf k f P = P.ord f := by
  rw [divisorOf, dif_neg hf]
  rfl

/-- Principal divisors are additive. -/
theorem divisorOf_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf k (f * g) = divisorOf k f + divisorOf k g := by
  ext P
  rw [Finsupp.add_apply, divisorOf_apply (mul_ne_zero hf hg),
    divisorOf_apply hf, divisorOf_apply hg]
  exact P.ord_mul hf hg

end Ord

section RefinedApproximation

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **Refined indicators**: at a place distinct from finitely many
others, an element within any prescribed uniformizer power of `1` there
and of `0` at the others. -/
theorem Place.exists_indicator {r : ℕ} (P₀ : Place k F)
    (Ps : Fin r → Place k F) (hne : ∀ j, P₀ ≠ Ps j) (m : ℕ) :
    ∃ χ : F,
      P₀.val.valuation (χ - 1) ≤ P₀.val.valuation P₀.pi ^ m ∧
      ∀ j, (Ps j).val.valuation χ ≤
        (Ps j).val.valuation ((Ps j).pi) ^ m := by
  classical
  obtain ⟨y, hy₀, hyj⟩ := P₀.exists_one_lt_forall_lt_one Ps hne
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hy₀
    simp at hy₀
  have hyv : P₀.val.valuation y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  -- Per-place exponents beating the target, then a common one.
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, P₀.val.valuation y⁻¹ ^ n <
      P₀.val.valuation (P₀.pi ^ m) := by
    refine P₀.exists_pow_valuation_lt (inv_ne_zero hy0) ?_
      (pow_ne_zero m P₀.pi_ne_zero)
    rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 hyv)]
    exact hy₀
  rw [Valuation.map_pow] at hn₀
  have hjarch : ∀ j, ∃ n : ℕ, (Ps j).val.valuation y ^ n <
      (Ps j).val.valuation ((Ps j).pi ^ m) := fun j ↦
    (Ps j).exists_pow_valuation_lt hy0 (hyj j)
      (pow_ne_zero m (Ps j).pi_ne_zero)
  choose ns hns using hjarch
  set n : ℕ := max n₀ (Finset.univ.sup ns) + 1 with hn
  have hn0 : n ≠ 0 := Nat.succ_ne_zero _
  refine ⟨y ^ n / (1 + y ^ n), ?_, ?_⟩
  · -- At `P₀`: the indicator error is `v(y)⁻¹ ^ n`.
    have hden : (1 : F) + y ^ n ≠ 0 := by
      intro h0
      have h2 := valuation_indicator_of_gt_one (O := P₀.val) hy₀ hn0
      rw [h0, div_zero, Valuation.map_zero] at h2
      exact zero_ne_one h2
    have h1 : y ^ n / (1 + y ^ n) - 1 = -(1 / (1 + y ^ n)) := by
      field_simp
      ring
    have hden_val : P₀.val.valuation (1 + y ^ n) =
        P₀.val.valuation (y ^ n) := by
      refine Valuation.map_add_eq_of_lt_right _ ?_
      rw [Valuation.map_one, Valuation.map_pow]
      exact one_lt_pow₀ hy₀ hn0
    rw [h1, Valuation.map_neg, one_div, map_inv₀, hden_val,
      Valuation.map_pow, ← inv_pow, ← map_inv₀]
    have h4 : P₀.val.valuation y⁻¹ ^ n ≤ P₀.val.valuation y⁻¹ ^ n₀ :=
      pow_le_pow_right_of_le_one' (by
        rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hyv)]
        exact hy₀.le) (by omega)
    exact le_trans h4 hn₀.le
  · -- At the other places: the indicator itself is small.
    intro j
    rw [valuation_indicator_of_lt_one (hyj j) hn0]
    have h5 : (Ps j).val.valuation y ^ n ≤
        (Ps j).val.valuation y ^ ns j :=
      pow_le_pow_right_of_le_one' (hyj j).le
        (le_trans (Finset.le_sup (Finset.mem_univ j))
          (by omega))
    have h6 := hns j
    rw [Valuation.map_pow] at h6
    exact le_trans h5 h6.le


/-- **Full approximation** (Stichtenoth Theorem 1.3.1): prescribed
target values at finitely many distinct places, matched to any prescribed
uniformizer power. The approximant is `∑ aᵢ χᵢ` for indicators of order
beating the pole orders of the targets. -/
theorem Place.exists_forall_sub_valuation_le {r : ℕ}
    (P : Fin r → Place k F) (hinj : Function.Injective P)
    (a : Fin r → F) (m : ℕ) :
    ∃ z : F, ∀ i, (P i).val.valuation (z - a i) ≤
      (P i).val.valuation ((P i).pi) ^ m := by
  classical
  rcases r with _ | r'
  · exact ⟨0, fun i ↦ i.elim0⟩
  set B : ℕ := Finset.univ.sup
    (fun p : Fin (r' + 1) × Fin (r' + 1) ↦
      (-(P p.1).ord (a p.2)).toNat) with hB
  set M : ℕ := m + B with hM
  have hord_bound : ∀ i j : Fin (r' + 1), a j ≠ 0 →
      -(B : ℤ) ≤ (P i).ord (a j) := by
    intro i j _
    have h1 : (-(P i).ord (a j)).toNat ≤ B :=
      Finset.le_sup (f := fun p : Fin (r' + 1) × Fin (r' + 1) ↦
        (-(P p.1).ord (a p.2)).toNat) (Finset.mem_univ (i, j))
    omega
  have hχex : ∀ i : Fin (r' + 1), ∃ χ : F,
      (P i).val.valuation (χ - 1) ≤
        (P i).val.valuation ((P i).pi) ^ M ∧
      ∀ j : Fin r', (P (i.succAbove j)).val.valuation χ ≤
        (P (i.succAbove j)).val.valuation
          ((P (i.succAbove j)).pi) ^ M :=
    fun i ↦ (P i).exists_indicator (fun j ↦ P (i.succAbove j))
      (fun j h ↦ (Fin.succAbove_ne i j) (hinj h).symm) M
  choose χ hχ₁ hχ₂ using hχex
  have hχsmall : ∀ i i' : Fin (r' + 1), i' ≠ i →
      (P i).val.valuation (χ i') ≤
        (P i).val.valuation ((P i).pi) ^ M := by
    intro i i' hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have h1 := hχ₂ i' j
    rwa [hj] at h1
  -- Each summand is bounded by the final target.
  have hterm : ∀ i i' : Fin (r' + 1),
      (P i).val.valuation (a i') *
        (P i).val.valuation ((P i).pi) ^ M ≤
      (P i).val.valuation ((P i).pi) ^ m := by
    intro i i'
    rcases eq_or_ne (a i') 0 with h0 | h0
    · rw [h0, Valuation.map_zero, zero_mul]
      exact zero_le
    have h1 : (P i).val.valuation (a i') ≤
        (P i).val.valuation ((P i).pi) ^ (-(B : ℤ)) := by
      rw [(P i).valuation_eq_zpow_ord h0]
      exact zpow_le_zpow_right_of_le_one₀ (P i).pi_valuation_pos
        (P i).pi_valuation_lt_one.le (hord_bound i i' h0)
    calc (P i).val.valuation (a i') *
        (P i).val.valuation ((P i).pi) ^ M
        ≤ (P i).val.valuation ((P i).pi) ^ (-(B : ℤ)) *
          (P i).val.valuation ((P i).pi) ^ M := by
          rcases eq_or_ne ((P i).val.valuation ((P i).pi) ^ M) 0 with
            hz | hz
          · rw [hz, mul_zero, mul_zero]
          · exact (OrderIso.mulRight₀ _ (zero_lt_iff.2 hz)).monotone h1
      _ = (P i).val.valuation ((P i).pi) ^ (m : ℤ) := by
          rw [← zpow_natCast ((P i).val.valuation ((P i).pi)) M,
            ← zpow_add₀ (P i).pi_valuation_ne_zero]
          congr 1
          omega
      _ = (P i).val.valuation ((P i).pi) ^ m := zpow_natCast _ m
  refine ⟨∑ i', a i' * χ i', fun i ↦ ?_⟩
  have hsplit : (∑ i', a i' * χ i') - a i =
      a i * (χ i - 1) + ∑ i' ∈ Finset.univ.erase i, a i' * χ i' := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  rw [hsplit]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    refine le_trans ?_ (hterm i i)
    gcongr
    exact hχ₁ i
  · refine Valuation.map_sum_le _ fun i' hi' ↦ ?_
    rw [Valuation.map_mul]
    refine le_trans ?_ (hterm i i')
    gcongr
    exact hχsmall i i' (Finset.ne_of_mem_erase hi')

end RefinedApproximation


end

end AclGeom
