/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.AtomClause
import AclGeom.Config.JAssembly
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Frobenius rigidity from concurrent closure lines

The direct Frobenius link between `j(x, a)` and `j(y, a')` puts its multiplier point on the three
lines `[x] ⊔ [y]`, `[ax] ⊔ [a'y]` and `[(1+a)x] ⊔ [(1+a')y]` (`FrobLinkIncidence`).  This file
proves the algebraic incidence-rigidity theorem used by blueprint Lemma `frobeq-correct`.
The direct-link and conditional two-link consumers are in `FrobLinkSemantic` and `FrobEqForward`.
The incidence target is EH95 Lemma 2.8; this proof uses a different, purely algebraic route.

The proof runs over the base `M`, the algebraic closure of `k(p)`, and has four parts.

* **Signed characters** (`frobenius_of_signed_characters`): two monomial relations with the *same*
  signed exponents, `u^d v^e = c` and `(1 + u)^d (1 + v)^e = c'`, force `u, v` to be Frobenius
  twists of each other.  One common `gcd` extraction makes the exponents primitive, so both
  relations keep the same primitive exponents.
* **Scaled loci** (`exists_character_of_scaled_locus`): each pair `(x, y)` and `(s x, t y)` has
  mutually interalgebraic coordinates over `M`. After extending to the field containing the
  scaling factors, their rescaled generators define the same ideal. Comparing their coefficient
  ratios for two support monomials gives a signed character in `M`.
* **Rank facts** (`notMem_racl_of_indep_three`, `false_of_zpow_eq_algebraMap`, ...): the
  independence and transcendence facts used along the way, stated as separate lemmas.
* **Assembly** (`frobenius_of_concurrent_lines`): the lines `[ax] ⊔ [a'y]` and
  `[(1+a)x] ⊔ [(1+a')y]` give two characters with the same exponents, read off from the curve of
  `(x, y)`.  Each character is algebraic over both `p` and `a`, hence constant.

**Status:** the incidence-rigidity theorem and its algebraic prerequisites are proved.
Unconditional geometric bridge completeness remains open (#23).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

section SignedCharacter

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Over an algebraically closed base, an element with a nonzero power in the base lies in the
base. -/
theorem exists_eq_algebraMap_of_pow_eq [IsAlgClosed k] {w : Ω} {g : ℕ} (hg : g ≠ 0) {c : k}
    (h : w ^ g = algebraMap k Ω c) : ∃ c₀ : k, w = algebraMap k Ω c₀ := by
  have halg : IsAlgebraic k w := by
    refine ⟨Polynomial.X ^ g - Polynomial.C c, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hg) c
    · simp [h]
  obtain ⟨c₀, hc₀⟩ := mem_range_algebraMap_of_isAlgebraic halg
  exact ⟨c₀, hc₀.symm⟩

/-- **Common primitive exponents.** If `x^d y^e` and `x'^d y'^e` both lie in the base, then so do
`x^{d'} y^{e'}` and `x'^{d'} y'^{e'}` for the *same* primitive pair `(d', e') = (d, e) / gcd`. -/
theorem exists_common_primitive [IsAlgClosed k] {x y x' y' : Ω} (hx : x ≠ 0) (hy : y ≠ 0)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) {d e : ℤ} (hd : d ≠ 0) {c c' : k}
    (h : x ^ d * y ^ e = algebraMap k Ω c) (h' : x' ^ d * y' ^ e = algebraMap k Ω c') :
    ∃ (d' e' : ℤ) (c₀ c₀' : k), d' ≠ 0 ∧ Int.gcd d' e' = 1 ∧
      (d' * Int.gcd d e = d ∧ e' * Int.gcd d e = e) ∧
      x ^ d' * y ^ e' = algebraMap k Ω c₀ ∧ x' ^ d' * y' ^ e' = algebraMap k Ω c₀' := by
  have hgpos : 0 < Int.gcd d e := Int.gcd_pos_of_ne_zero_left e hd
  obtain ⟨d', e', hcop, hd', he'⟩ := Int.exists_gcd_one hgpos
  have hd'0 : d' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hd'
    exact hd hd'
  have hpow : ∀ {u v : Ω} {c₁ : k}, u ≠ 0 → v ≠ 0 →
      u ^ d * v ^ e = algebraMap k Ω c₁ →
      ∃ c₂ : k, u ^ d' * v ^ e' = algebraMap k Ω c₂ := by
    intro u v c₁ hu hv huv
    have hz : (u ^ d' * v ^ e') ^ (Int.gcd d e) = algebraMap k Ω c₁ := by
      rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, ← hd', ← he']
      exact huv
    exact exists_eq_algebraMap_of_pow_eq hgpos.ne' hz
  obtain ⟨c₀, hc₀⟩ := hpow hx hy h
  obtain ⟨c₀', hc₀'⟩ := hpow hx' hy' h'
  exact ⟨d', e', c₀, c₀', hd'0, hcop, ⟨hd'.symm, he'.symm⟩, hc₀, hc₀'⟩

/-- **The signed-character endpoint.**  If `u, v` are transcendental over the algebraically closed
base and `u^d v^e`, `(1 + u)^d (1 + v)^e` both lie in the base for the same nonzero exponents, then
one of `u, v` is a Frobenius twist `(·)^{q^s}` of the other.  Same-sign exponents are impossible
(`shift_mixed_absurd`); opposite signs give the exact twist (`shift_binomial_at_curve`). -/
theorem frobenius_of_signed_characters [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ) [ExpChar k q]
    {u v : Ω} (hu : u ∉ racl k (∅ : Set Ω)) (hv : v ∉ racl k (∅ : Set Ω)) {d e : ℤ}
    (hd : d ≠ 0) (he : e ≠ 0) {c c' : k}
    (h₁ : u ^ d * v ^ e = algebraMap k Ω c)
    (h₂ : (1 + u) ^ d * (1 + v) ^ e = algebraMap k Ω c') :
    ∃ s : ℕ, v = u ^ q ^ s ∨ u = v ^ q ^ s := by
  have hu0 : u ≠ 0 := ne_zero_of_notMem_racl_empty hu
  have hv0 : v ≠ 0 := ne_zero_of_notMem_racl_empty hv
  have hu1 : 1 + u ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hu)
  have hv1 : 1 + v ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hv)
  obtain ⟨d', e', c₀, c₀', hd'0, hcop, ⟨hd', he'⟩, h₁', h₂'⟩ :=
    exists_common_primitive hu0 hv0 hu1 hv1 hd h₁ h₂
  have he'0 : e' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at he'
    exact he he'.symm
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at h₁'
    exact mul_ne_zero (zpow_ne_zero _ hu0) (zpow_ne_zero _ hv0) h₁'
  have hc₀' : c₀' ≠ 0 := by
    rintro rfl
    rw [map_zero] at h₂'
    exact mul_ne_zero (zpow_ne_zero _ hu1) (zpow_ne_zero _ hv1) h₂'
  -- Write the primitive exponents as signed naturals.
  rcases lt_or_gt_of_ne hd'0 with hdn | hdp <;> rcases lt_or_gt_of_ne he'0 with hen | hep
  · -- both negative: invert and rule out
    exfalso
    obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hdn.le
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hen.le
    subst hm hn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hdn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hen
    refine shift_mixed_absurd (k := k) (u := u) hv hm0 hn0 (inv_ne_zero hc₀) (c₂ := c₀'⁻¹) ?_ ?_
    · rw [map_inv₀, ← h₁', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_inv]
      rw [inv_inv, inv_inv]
    · rw [map_inv₀, ← h₂', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_inv]
      rw [inv_inv, inv_inv]
  · -- `d' < 0 < e'`: `v^{e'} = c₀ u^{-d'}`
    obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hdn.le
    lift e' to ℕ using hep.le with n
    subst hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hdn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hep
    have hcopnm : Nat.Coprime n m := by
      have := hcop
      rw [Int.gcd_comm, Int.gcd_neg] at this
      simpa [Int.gcd_natCast_natCast] using this
    have e1 : v ^ n = algebraMap k Ω c₀ * u ^ m := by
      have := congrArg (· * u ^ m) h₁'
      simp only [zpow_neg, zpow_natCast] at this
      rw [← this]
      field_simp
    have e2 : (1 + v) ^ n = algebraMap k Ω c₀' * (1 + u) ^ m := by
      have := congrArg (· * (1 + u) ^ m) h₂'
      simp only [zpow_neg, zpow_natCast] at this
      rw [← this]
      field_simp
    obtain ⟨s, hs⟩ := shift_binomial_at_curve (k := k) q hu hn0 hm0 hcopnm hc₀ e1 e2
    rcases hs with ⟨-, -, hs⟩ | ⟨-, -, hs⟩
    · exact ⟨s, Or.inr hs⟩
    · exact ⟨s, Or.inl hs⟩
  · -- `e' < 0 < d'`: `u^{d'} = c₀ v^{-e'}`
    lift d' to ℕ using hdp.le with m
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hen.le
    subst hn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hdp
    have hn0 : n ≠ 0 := by rintro rfl; simp at hen
    have hcopmn : Nat.Coprime m n := by
      have := hcop
      rw [Int.gcd_neg] at this
      simpa [Int.gcd_natCast_natCast] using this
    have e1 : u ^ m = algebraMap k Ω c₀ * v ^ n := by
      have := congrArg (· * v ^ n) h₁'
      simp only [zpow_neg, zpow_natCast] at this
      rw [← this]
      field_simp
    have e2 : (1 + u) ^ m = algebraMap k Ω c₀' * (1 + v) ^ n := by
      have := congrArg (· * (1 + v) ^ n) h₂'
      simp only [zpow_neg, zpow_natCast] at this
      rw [← this]
      field_simp
    obtain ⟨s, hs⟩ := shift_binomial_at_curve (k := k) q hv hm0 hn0 hcopmn hc₀ e1 e2
    rcases hs with ⟨-, -, hs⟩ | ⟨-, -, hs⟩
    · exact ⟨s, Or.inl hs⟩
    · exact ⟨s, Or.inr hs⟩
  · -- both positive: rule out
    exfalso
    lift d' to ℕ using hdp.le with m
    lift e' to ℕ using hep.le with n
    have hm0 : m ≠ 0 := by rintro rfl; simp at hdp
    have hn0 : n ≠ 0 := by rintro rfl; simp at hep
    refine shift_mixed_absurd (k := k) (u := u) hv hm0 hn0 hc₀ (c₂ := c₀') ?_ ?_
    · simpa only [zpow_natCast] using h₁'
    · simpa only [zpow_natCast] using h₂'

end SignedCharacter

section ScaledLoci

open _root_.MvPolynomial

/-- **Coefficient ratios of associated scaled generators.**  If the scaling of `G` by a nowhere-zero
vector `c` generates the same ideal as `F`, then the monomial values of `c` are, up to one common
constant, the coefficient ratios of `F` and `G`. -/
theorem exists_scale_coeff_eq {σ K : Type*} [Field K] {c : σ → K}
    {F G : MvPolynomial σ K} (h : Ideal.span {scale c G} = Ideal.span {F}) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ m : σ →₀ ℕ,
      lam * (m.prod fun j e ↦ c j ^ e) * G.coeff m = F.coeff m := by
  classical
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  obtain ⟨lam, hlamUnit, hlam⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  have hlam0 : lam ≠ 0 := isUnit_iff_ne_zero.1 hlamUnit
  refine ⟨lam, hlam0, fun m ↦ ?_⟩
  have h1 := congrArg (fun g ↦ g.coeff m) hu
  simp only [hlam, mul_comm (scale c G), coeff_C_mul, coeff_scale] at h1
  rw [← h1, mul_assoc]

end ScaledLoci

section ScaledCharacter

open _root_.MvPolynomial

variable {M Ω : Type*} [Field M] [Field Ω] [Algebra M Ω]

/-- The monomial value of a two-variable scaling vector. -/
theorem finsupp_prod_fin_two {R : Type*} [CommMonoid R] (c : Fin 2 → R) (m : Fin 2 →₀ ℕ) :
    (m.prod fun j e ↦ c j ^ e) = c 0 ^ m 0 * c 1 ^ m 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fin.prod_univ_two]

/-- **One multiplicative character from a scaled locus.**  Let `M` be an algebraically closed base
and `N` an intermediate field over it containing nonzero `s, t`.  Suppose the plane points `(x, y)`
and `(s x, t y)` are interalgebraic over `M` and transcendental over `N`, and `F` generates the
locus of `(x, y)` over `M`.  Then for any two support monomials `m₁, m₂` of `F`, the signed monomial
`s^{m₁ - m₂}` (in the two scaling factors) lies in `M`. -/
theorem exists_character_of_scaled_locus [IsAlgClosed M] {N : IntermediateField M Ω}
    {x y s t : Ω} (hs : s ∈ N) (ht : t ∈ N) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hx : Transcendental ↥N x) (hy : Transcendental ↥N y)
    (hyx : y ∈ racl M {x}) (hxy : x ∈ racl M {y})
    (hsx : Transcendental ↥N (s * x)) (hty : Transcendental ↥N (t * y))
    (htysx : t * y ∈ racl M {s * x}) (hsxty : s * x ∈ racl M {t * y})
    {F : MvPolynomial (Fin 2) M} (hF0 : F ≠ 0) (hF : idealOf M ![x, y] = Ideal.span {F})
    {m₁ m₂ : Fin 2 →₀ ℕ} (hm₁ : m₁ ∈ F.support) (hm₂ : m₂ ∈ F.support) :
    ∃ r : M, s ^ ((m₁ 0 : ℤ) - m₂ 0) * t ^ ((m₁ 1 : ℤ) - m₂ 1) = algebraMap M Ω r := by
  classical
  have hsxM : Transcendental M (s * x) := fun h ↦ hsx (h.tower_top _)
  obtain ⟨G, hGp, hG⟩ := exists_prime_span_idealOf M hsxM htysx
  have hG0 : G ≠ 0 := hGp.ne_zero
  have hFN := idealOf_map_eq_span hx hyx hy hxy hF0 hF
  have hGN := idealOf_map_eq_span hsx htysx hty hsxty hG0 hG
  set c : Fin 2 → ↥N := ![⟨s, hs⟩, ⟨t, ht⟩] with hcdef
  have hc : ∀ j, c j ≠ 0 := by
    intro j
    fin_cases j
    · exact fun h ↦ hs0 (congrArg Subtype.val h)
    · exact fun h ↦ ht0 (congrArg Subtype.val h)
  have hpt : (fun j ↦ (![s * x, t * y] : Fin 2 → Ω) j / algebraMap (↥N) Ω (c j)) = ![x, y] := by
    funext j
    fin_cases j
    · change s * x / s = x
      field_simp
    · change t * y / t = y
      field_simp
  have hscale := idealOf_scale_span hc hGN
  rw [hpt, hFN] at hscale
  obtain ⟨lam, hlam0, hcoeff⟩ := exists_scale_coeff_eq hscale.symm
  -- Read off the two monomials.
  have hmono : ∀ m : Fin 2 →₀ ℕ, (m.prod fun j e ↦ c j ^ e) =
      (⟨s, hs⟩ : ↥N) ^ m 0 * (⟨t, ht⟩ : ↥N) ^ m 1 := fun m ↦ finsupp_prod_fin_two c m
  have hF₁ : F.coeff m₁ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₁
  have hF₂ : F.coeff m₂ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₂
  have key : ∀ m : Fin 2 →₀ ℕ, lam * ((⟨s, hs⟩ : ↥N) ^ m 0 * (⟨t, ht⟩ : ↥N) ^ m 1) *
      algebraMap M ↥N (G.coeff m) = algebraMap M ↥N (F.coeff m) := by
    intro m
    have := hcoeff m
    rw [hmono, _root_.MvPolynomial.coeff_map, _root_.MvPolynomial.coeff_map] at this
    exact this
  have hG₁ : G.coeff m₁ ≠ 0 := by
    intro h0
    have := key m₁
    rw [h0, (algebraMap M ↥N).map_zero, mul_zero] at this
    exact hF₁ ((map_eq_zero _).1 this.symm)
  have hG₂ : G.coeff m₂ ≠ 0 := by
    intro h0
    have := key m₂
    rw [h0, (algebraMap M ↥N).map_zero, mul_zero] at this
    exact hF₂ ((map_eq_zero _).1 this.symm)
  refine ⟨(F.coeff m₁ * G.coeff m₂) / (F.coeff m₂ * G.coeff m₁), ?_⟩
  -- Transport the two coefficient identities to `Ω`.
  have kΩ : ∀ m : Fin 2 →₀ ℕ, algebraMap (↥N) Ω lam * (s ^ m 0 * t ^ m 1) *
      algebraMap M Ω (G.coeff m) = algebraMap M Ω (F.coeff m) := by
    intro m
    have := congrArg (algebraMap (↥N) Ω) (key m)
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply] at this
    exact this
  have hlamΩ : algebraMap (↥N) Ω lam ≠ 0 := (map_ne_zero _).2 hlam0
  have h₁ := kΩ m₁
  have h₂ := kΩ m₂
  have hGΩ₁ : algebraMap M Ω (G.coeff m₁) ≠ 0 := (map_ne_zero _).2 hG₁
  have hGΩ₂ : algebraMap M Ω (G.coeff m₂) ≠ 0 := (map_ne_zero _).2 hG₂
  have hFΩ₂ : algebraMap M Ω (F.coeff m₂) ≠ 0 := (map_ne_zero _).2 hF₂
  rw [zpow_sub₀ hs0, zpow_sub₀ ht0, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    map_div₀, map_mul, map_mul, ← h₁, ← h₂]
  have hs2 : s ^ m₂ 0 ≠ 0 := pow_ne_zero _ hs0
  have ht2 : t ^ m₂ 1 ≠ 0 := pow_ne_zero _ ht0
  field_simp

end ScaledCharacter

section RankFacts

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The three exclusions carried by an independent triple. -/
theorem notMem_racl_of_indep_three {x y a : Ω} (h : AlgebraicIndependent k ![x, y, a]) :
    x ∉ racl k ({y, a} : Set Ω) ∧ y ∉ racl k ({x, a} : Set Ω) ∧ a ∉ racl k ({x, y} : Set Ω) := by
  have hall := algebraicIndependent_iff_forall_notMem_racl.1 h
  have i0 : (![x, y, a] '' {(0 : Fin 3)}ᶜ) = ({y, a} : Set Ω) := by
    ext z
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i
      · exact absurd rfl hi
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  have i1 : (![x, y, a] '' {(1 : Fin 3)}ᶜ) = ({x, a} : Set Ω) := by
    ext z
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact absurd rfl hi
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  have i2 : (![x, y, a] '' {(2 : Fin 3)}ᶜ) = ({x, y} : Set Ω) := by
    ext z
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hi
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  rw [i0] at h0
  rw [i1] at h1
  rw [i2] at h2
  exact ⟨h0, h1, h2⟩

/-- Three independent elements cannot all be algebraic over two elements. -/
theorem false_of_indep_three_mem_racl_pair {x y a u v : Ω}
    (h : AlgebraicIndependent k ![x, y, a]) (hx : x ∈ racl k ({u, v} : Set Ω))
    (hy : y ∈ racl k ({u, v} : Set Ω)) (ha : a ∈ racl k ({u, v} : Set Ω)) : False := by
  obtain ⟨hx', hy', ha'⟩ := notMem_racl_of_indep_three h
  have hyx : y ∉ racl k ({x} : Set Ω) := fun hm ↦ hy' (racl_mono (by simp) hm)
  -- Replace one generator by `x`, then the other by `y`.
  have step : ∀ {u v : Ω}, x ∈ racl k (insert u ({v} : Set Ω)) → x ∉ racl k ({v} : Set Ω) →
      y ∈ racl k (insert u ({v} : Set Ω)) → a ∈ racl k (insert u ({v} : Set Ω)) → False := by
    intro u v hxuv hxv hyuv hauv
    have hu : u ∈ racl k (insert x ({v} : Set Ω)) := racl_exchange hxuv hxv
    have hsub : (insert u ({v} : Set Ω)) ⊆ racl k (insert x ({v} : Set Ω)) := by
      rintro z (rfl | rfl)
      · exact hu
      · exact subset_racl k _ (by simp)
    have hy2 : y ∈ racl k (insert v ({x} : Set Ω)) := by
      have := racl_le_of_subset_racl hsub hyuv
      rwa [Set.pair_comm] at this
    have hv : v ∈ racl k (insert y ({x} : Set Ω)) := racl_exchange hy2 hyx
    have hsub2 : (insert x ({v} : Set Ω)) ⊆ racl k ({x, y} : Set Ω) := by
      rintro z (rfl | rfl)
      · exact subset_racl k _ (by simp)
      · rw [Set.pair_comm]; exact hv
    exact ha' (racl_le_of_subset_racl hsub2 (racl_le_of_subset_racl hsub hauv))
  by_cases hxv : x ∈ racl k ({v} : Set Ω)
  · have hxu : x ∉ racl k ({u} : Set Ω) := by
      intro hxu
      -- `x` algebraic over both `u` and `v` alone forces `x` algebraic over `k`:
      -- then `x ∉ racl {y, a}` fails.
      by_cases hv0 : v ∈ racl k (∅ : Set Ω)
      · have hx0 : x ∈ racl k (∅ : Set Ω) := by
          refine racl_le_of_subset_racl ?_ hxv
          rintro z rfl; exact hv0
        exact hx' (racl_mono (Set.empty_subset _) hx0)
      · -- otherwise `v` is algebraic over `x`, hence over `u`, so everything lies in `racl {u}`
        have hvx : v ∈ racl k ({x} : Set Ω) := by
          have := racl_exchange (S := ∅) (by simpa using hxv) (fun h0 ↦ hx' (racl_mono
            (Set.empty_subset _) h0))
          simpa using this
        have hvu : v ∈ racl k ({u} : Set Ω) :=
          racl_le_of_subset_racl (by rintro z rfl; exact hxu) hvx
        have hsub : ({u, v} : Set Ω) ⊆ racl k ({u} : Set Ω) := by
          rintro z (rfl | rfl)
          · exact subset_racl k _ rfl
          · exact hvu
        have hy1 := racl_le_of_subset_racl hsub hy
        have hx1 := racl_le_of_subset_racl hsub hx
        have hux : u ∈ racl k ({x} : Set Ω) := by
          have := racl_exchange (S := ∅) (x := x) (y := u) (by simpa using hx1)
            (fun h0 ↦ hx' (racl_mono (Set.empty_subset _) h0))
          simpa using this
        exact hyx (racl_le_of_subset_racl (by rintro z rfl; exact hux) hy1)
    rw [Set.pair_comm] at hx hy ha
    exact step hx hxu hy ha
  · exact step hx hxv hy ha

/-- A transcendental element has no nonzero integer power in the base. -/
theorem false_of_zpow_eq_algebraMap {z : Ω} (hz : z ∉ racl k (∅ : Set Ω)) {n : ℤ} (hn : n ≠ 0)
    {c : k} (h : z ^ n = algebraMap k Ω c) : False := by
  have key : ∀ m : ℕ, m ≠ 0 → ∀ c' : k, z ^ m = algebraMap k Ω c' → False := by
    intro m hm c' h'
    apply hz
    apply mem_racl_empty_of_isAlgebraic
    exact ⟨Polynomial.X ^ m - Polynomial.C c',
      Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hm) c', by simp [h']⟩
  rcases Int.natAbs_eq n with hn' | hn'
  · refine key n.natAbs (Int.natAbs_ne_zero.2 hn) c ?_
    rw [← zpow_natCast, ← hn']
    exact h
  · refine key n.natAbs (Int.natAbs_ne_zero.2 hn) c⁻¹ ?_
    have h2 : z ^ (-(n.natAbs : ℤ)) = algebraMap k Ω c := by
      rw [← hn']
      exact h
    rw [zpow_neg, zpow_natCast] at h2
    rw [map_inv₀, ← h2, inv_inv]

end RankFacts

section Assembly

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Closure over the algebraic closure of `k(p)` is closure over `k` with `p` adjoined. -/
theorem mem_racl_algClosure_adjoin_iff {p z : Ω} {S : Set Ω} :
    z ∈ racl ↥(algebraicClosure ↥(adjoin k ({p} : Set Ω)) Ω) S ↔ z ∈ racl k (insert p S) := by
  rw [mem_racl_base_iff_of_algebraic (fun y hy ↦ mem_algebraicClosure_iff.1 hy),
    mem_racl_adjoin_base_iff, Set.singleton_union]

/-- Elements of the algebraic closure of `k(p)` lie in `racl k {p}`. -/
theorem mem_racl_of_mem_algClosure_adjoin {p z : Ω}
    (hz : z ∈ algebraicClosure ↥(adjoin k ({p} : Set Ω)) Ω) : z ∈ racl k ({p} : Set Ω) :=
  (mem_racl_iff k).2 (mem_algebraicClosure_iff.1 hz)

/-- Exchange in the pair form used below: from `p ∈ racl {u, v}` and `p ∉ racl {u}` we get
`v ∈ racl {p, u}`. -/
theorem mem_racl_pair_of_exchange {p u v : Ω} (hp : p ∈ racl k ({u, v} : Set Ω))
    (hpu : p ∉ racl k ({u} : Set Ω)) : v ∈ racl k ({p, u} : Set Ω) := by
  have h : p ∈ racl k (insert v ({u} : Set Ω)) := by rwa [Set.pair_comm] at hp
  exact racl_exchange h hpu

/-- **The converse of the direct Frobenius link** (route C′).  Over an algebraically closed base
inside an algebraically closed ambient field, let `x, y, a` be independent, `[a'] = [a]`, and let
`p` represent a point lying on the three lines `[x] ⊔ [y]`, `[ax] ⊔ [a'y]` and
`[(1+a)x] ⊔ [(1+a')y]` (the concurrency proved in `FrobLinkIncidence`).  Then `a, a'` are Frobenius
twists of each other. -/
theorem frobenius_of_concurrent_lines [IsAlgClosed k] [IsAlgClosed Ω] (q : ℕ) [ExpChar k q]
    {x y a a' p : Ω} (hind : AlgebraicIndependent k ![x, y, a])
    (ha'a : a' ∈ racl k ({a} : Set Ω)) (haa' : a ∈ racl k ({a'} : Set Ω))
    (hp0 : p ∉ racl k (∅ : Set Ω))
    (hL1 : p ∈ racl k ({x, y} : Set Ω)) (hL2 : p ∈ racl k ({a * x, a' * y} : Set Ω))
    (hL3 : p ∈ racl k ({(1 + a) * x, (1 + a') * y} : Set Ω)) :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s := by
  classical
  obtain ⟨hx_ya, hy_xa, ha_xy⟩ := notMem_racl_of_indep_three hind
  -- Transcendence of the generic elements.
  have hx0 : x ∉ racl k (∅ : Set Ω) := fun h ↦ hx_ya (racl_mono (Set.empty_subset _) h)
  have hy0 : y ∉ racl k (∅ : Set Ω) := fun h ↦ hy_xa (racl_mono (Set.empty_subset _) h)
  have ha0 : a ∉ racl k (∅ : Set Ω) := fun h ↦ ha_xy (racl_mono (Set.empty_subset _) h)
  have ha'0 : a' ∉ racl k (∅ : Set Ω) := fun h ↦
    ha0 (racl_le_of_subset_racl (by rintro z rfl; exact h) haa')
  have hxne : x ≠ 0 := ne_zero_of_notMem_racl_empty hx0
  have hyne : y ≠ 0 := ne_zero_of_notMem_racl_empty hy0
  have hane : a ≠ 0 := ne_zero_of_notMem_racl_empty ha0
  have ha'ne : a' ≠ 0 := ne_zero_of_notMem_racl_empty ha'0
  have ha1ne : 1 + a ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty ha0)
  have ha'1ne : 1 + a' ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty ha'0)
  -- The closures used repeatedly.
  have hpxy : (racl k ({p} : Set Ω) : Set Ω) ⊆ racl k ({x, y} : Set Ω) := by
    have := racl_le_of_subset_racl (S := ({x, y} : Set Ω)) (T := {p}) (by rintro z rfl; exact hL1)
    exact this
  have hdiv : ∀ {S : Set Ω} {u w : Ω}, w ≠ 0 → u * w ∈ racl k S → w ∈ racl k S →
      u ∈ racl k S := by
    intro S u w hw huw hwS
    have := div_mem huw hwS
    rwa [mul_div_cancel_right₀ _ hw] at this
  -- Rank facts: the point `P` is none of the six coordinate points.
  have hpx : p ∉ racl k ({x} : Set Ω) := by
    intro hpx
    have hxp : x ∈ racl k ({p} : Set Ω) := by
      have := racl_exchange (S := ∅) (by simpa using hpx) hp0
      simpa using this
    have hsub : (racl k ({p} : Set Ω) : Set Ω) ⊆ racl k ({a * x, a' * y} : Set Ω) :=
      racl_le_of_subset_racl (by rintro z rfl; exact hL2)
    have hxL : x ∈ racl k ({a * x, a' * y} : Set Ω) := hsub hxp
    have haL : a ∈ racl k ({a * x, a' * y} : Set Ω) :=
      hdiv hxne (subset_racl k _ (by simp)) hxL
    have ha'L : a' ∈ racl k ({a * x, a' * y} : Set Ω) :=
      racl_le_of_subset_racl (by rintro z rfl; exact haL) ha'a
    have hyL : y ∈ racl k ({a * x, a' * y} : Set Ω) :=
      hdiv ha'ne (by rw [mul_comm y a']; exact subset_racl k _ (by simp)) ha'L
    exact false_of_indep_three_mem_racl_pair hind hxL hyL haL
  have hpy : p ∉ racl k ({y} : Set Ω) := by
    intro hpy
    have hyp : y ∈ racl k ({p} : Set Ω) := by
      have := racl_exchange (S := ∅) (by simpa using hpy) hp0
      simpa using this
    have hsub : (racl k ({p} : Set Ω) : Set Ω) ⊆ racl k ({a * x, a' * y} : Set Ω) :=
      racl_le_of_subset_racl (by rintro z rfl; exact hL2)
    have hyL : y ∈ racl k ({a * x, a' * y} : Set Ω) := hsub hyp
    have ha'L : a' ∈ racl k ({a * x, a' * y} : Set Ω) :=
      hdiv hyne (subset_racl k _ (by simp)) hyL
    have haL : a ∈ racl k ({a * x, a' * y} : Set Ω) :=
      racl_le_of_subset_racl (by rintro z rfl; exact ha'L) haa'
    have hxL : x ∈ racl k ({a * x, a' * y} : Set Ω) :=
      hdiv hane (by rw [mul_comm x a]; exact subset_racl k _ (by simp)) haL
    exact false_of_indep_three_mem_racl_pair hind hxL hyL haL
  -- `P` is not a scaled coordinate point either: those lie off the line `[x] ⊔ [y]`.
  have hoff : ∀ {w : Ω}, w ∉ racl k ({x, y} : Set Ω) → p ∉ racl k ({w} : Set Ω) := by
    intro w hw hpw
    apply hw
    have hwp : w ∈ racl k ({p} : Set Ω) := by
      have := racl_exchange (S := ∅) (by simpa using hpw) hp0
      simpa using this
    exact hpxy hwp
  have hxyS : x ∈ racl k ({x, y} : Set Ω) := subset_racl k _ (by simp)
  have hyyS : y ∈ racl k ({x, y} : Set Ω) := subset_racl k _ (by simp)
  have ha'_xy : a' ∉ racl k ({x, y} : Set Ω) := fun h ↦
    ha_xy (racl_le_of_subset_racl (by rintro z rfl; exact h) haa')
  have hpax : p ∉ racl k ({a * x} : Set Ω) :=
    hoff fun h ↦ ha_xy (hdiv hxne h hxyS)
  have hpa'y : p ∉ racl k ({a' * y} : Set Ω) :=
    hoff fun h ↦ ha'_xy (hdiv hyne h hyyS)
  have hpa1x : p ∉ racl k ({(1 + a) * x} : Set Ω) := by
    refine hoff fun h ↦ ha_xy ?_
    have h1 : 1 + a ∈ racl k ({x, y} : Set Ω) := hdiv hxne h hxyS
    have := sub_mem h1 (one_mem _)
    rwa [add_sub_cancel_left] at this
  have hpa'1y : p ∉ racl k ({(1 + a') * y} : Set Ω) := by
    refine hoff fun h ↦ ha'_xy ?_
    have h1 : 1 + a' ∈ racl k ({x, y} : Set Ω) := hdiv hyne h hyyS
    have := sub_mem h1 (one_mem _)
    rwa [add_sub_cancel_left] at this
  -- `x` and `y` are off the closure of `p, a`.
  have hx_pa : x ∉ racl k ({p, a} : Set Ω) := by
    intro hx
    have hxa : x ∉ racl k ({a} : Set Ω) := fun h ↦ hx_ya (racl_mono (by simp) h)
    have hp_xa : p ∈ racl k (insert x ({a} : Set Ω)) := by
      have h' : x ∈ racl k (insert p ({a} : Set Ω)) := hx
      exact racl_exchange h' hxa
    have hp_x : p ∈ racl k ({x} : Set Ω) := by
      refine mem_racl_of_mem_racl_insert (A := {x}) (a := a) (b := y) ?_ ?_ ?_
      · rwa [Set.pair_comm] at hp_xa
      · rwa [Set.pair_comm] at hL1
      · rw [Set.pair_comm]; exact hy_xa
    exact hpx hp_x
  have hy_pa : y ∉ racl k ({p, a} : Set Ω) := by
    intro hy
    have hya : y ∉ racl k ({a} : Set Ω) := fun h ↦ hy_xa (racl_mono (by simp) h)
    have hp_ya : p ∈ racl k (insert y ({a} : Set Ω)) := by
      have h' : y ∈ racl k (insert p ({a} : Set Ω)) := hy
      exact racl_exchange h' hya
    have hp_y : p ∈ racl k ({y} : Set Ω) := by
      refine mem_racl_of_mem_racl_insert (A := {y}) (a := a) (b := x) ?_ ?_ ?_
      · rwa [Set.pair_comm] at hp_ya
      · exact hL1
      · rw [Set.pair_comm]; exact hx_ya
    exact hpy hp_y
  have ha_p : a ∉ racl k ({p} : Set Ω) := fun h ↦ ha_xy (hpxy h)
  -- The base `M`: the algebraic closure of `k(p)`, and the intermediate field `N = M(a)^alg`.
  set M := algebraicClosure ↥(adjoin k ({p} : Set Ω)) Ω with hMdef
  have : IsAlgClosed ↥M := IsAlgClosure.isAlgClosed ↥(adjoin k ({p} : Set Ω))
  have hM : ∀ {z : Ω} {S : Set Ω}, z ∈ racl ↥M S ↔ z ∈ racl k (insert p S) :=
    mem_racl_algClosure_adjoin_iff
  set N := racl ↥M ({a} : Set Ω) with hNdef
  have hN : ∀ {z : Ω}, z ∉ racl k ({p, a} : Set Ω) → Transcendental ↥N z := by
    intro z hz
    refine transcendental_racl_of_notMem ?_
    rw [hM]
    exact hz
  have hpa_sub : ∀ {z w : Ω}, w ∈ racl k ({p, a} : Set Ω) → w ≠ 0 →
      z ∉ racl k ({p, a} : Set Ω) → w * z ∉ racl k ({p, a} : Set Ω) := by
    intro z w hw hw0 hz hwz
    exact hz (hdiv hw0 (by rw [mul_comm]; exact hwz) hw)
  have ha_pa : a ∈ racl k ({p, a} : Set Ω) := subset_racl k _ (by simp)
  have ha'_pa : a' ∈ racl k ({p, a} : Set Ω) :=
    racl_mono (by simp) ha'a
  have ha1_pa : 1 + a ∈ racl k ({p, a} : Set Ω) := add_mem (one_mem _) ha_pa
  have ha'1_pa : 1 + a' ∈ racl k ({p, a} : Set Ω) := add_mem (one_mem _) ha'_pa
  have hmemN : ∀ {z : Ω}, z ∈ racl k ({p, a} : Set Ω) → z ∈ N := fun hz ↦ hM.2 hz
  -- The locus of `(x, y)` over `M` and two of its support monomials.
  have hxN : Transcendental ↥N x := hN hx_pa
  have hyN : Transcendental ↥N y := hN hy_pa
  have hxM : Transcendental ↥M x := fun h ↦ hxN (h.tower_top _)
  have hyx : y ∈ racl ↥M ({x} : Set Ω) := hM.2 (mem_racl_pair_of_exchange hL1 hpx)
  have hxy : x ∈ racl ↥M ({y} : Set Ω) := by
    refine hM.2 (mem_racl_pair_of_exchange (u := y) (v := x) ?_ hpy)
    rwa [Set.pair_comm] at hL1
  obtain ⟨F, hFp, hF⟩ := exists_prime_span_idealOf ↥M hxM hyx
  have hF0 : F ≠ 0 := hFp.ne_zero
  have hFx : MvPolynomial.aeval ![x, y] F = 0 :=
    (mem_idealOf_iff ↥M).1 (hF ▸ Ideal.subset_span rfl)
  obtain ⟨m₁, hm₁, m₂, hm₂, hm₁₂⟩ := exists_support_pair_of_aeval_eq_zero
    (v := ![x, y]) (fun j ↦ by fin_cases j <;> simpa) hF0 hFx
  set d : ℤ := (m₁ 0 : ℤ) - m₂ 0 with hd
  set e : ℤ := (m₁ 1 : ℤ) - m₂ 1 with he
  -- A character in `M` that is also algebraic over `a` is a constant.
  have hconst : ∀ {w : Ω} {r : ↥M}, w = algebraMap (↥M) Ω r → w ∈ racl k ({a} : Set Ω) →
      ∃ c : k, w = algebraMap k Ω c := by
    intro w r hwr hwa
    have hwp : w ∈ racl k ({p} : Set Ω) := by
      rw [hwr]
      exact mem_racl_of_mem_algClosure_adjoin r.2
    have hw0 : w ∈ racl k (∅ : Set Ω) := by
      refine mem_racl_of_mem_racl_insert (A := ∅) (a := p) (b := a) ?_ ?_ ?_
      · simpa using hwp
      · simpa using hwa
      · simpa using ha_p
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isAlgebraic (isAlgebraic_of_mem_racl_empty hw0)
    exact ⟨c, hc.symm⟩
  have hzpow : ∀ {u v : Ω}, u ∈ racl k ({a} : Set Ω) → v ∈ racl k ({a} : Set Ω) →
      u ^ d * v ^ e ∈ racl k ({a} : Set Ω) := fun hu hv ↦
    mul_mem (zpow_mem hu _) (zpow_mem hv _)
  have haa : a ∈ racl k ({a} : Set Ω) := subset_racl k _ rfl
  -- First character, from the line `[ax] ⊔ [a'y]`.
  have hax : a * x ∉ racl k ({p, a} : Set Ω) := hpa_sub ha_pa hane hx_pa
  have ha'y : a' * y ∉ racl k ({p, a} : Set Ω) := hpa_sub ha'_pa ha'ne hy_pa
  obtain ⟨r₁, hr₁⟩ := exists_character_of_scaled_locus (N := N) (hmemN ha_pa) (hmemN ha'_pa)
    hane ha'ne hxN hyN hyx hxy (hN hax) (hN ha'y)
    (hM.2 (mem_racl_pair_of_exchange hL2 hpax))
    (hM.2 (mem_racl_pair_of_exchange (u := a' * y) (v := a * x)
      (by rwa [Set.pair_comm] at hL2) hpa'y))
    hF0 hF hm₁ hm₂
  obtain ⟨c₁, hc₁⟩ := hconst hr₁ (hzpow haa ha'a)
  -- Second character, from the line `[(1+a)x] ⊔ [(1+a')y]`, with the same exponents.
  have ha1x : (1 + a) * x ∉ racl k ({p, a} : Set Ω) := hpa_sub ha1_pa ha1ne hx_pa
  have ha'1y : (1 + a') * y ∉ racl k ({p, a} : Set Ω) := hpa_sub ha'1_pa ha'1ne hy_pa
  obtain ⟨r₂, hr₂⟩ := exists_character_of_scaled_locus (N := N) (hmemN ha1_pa) (hmemN ha'1_pa)
    ha1ne ha'1ne hxN hyN hyx hxy (hN ha1x) (hN ha'1y)
    (hM.2 (mem_racl_pair_of_exchange hL3 hpa1x))
    (hM.2 (mem_racl_pair_of_exchange (u := (1 + a') * y) (v := (1 + a) * x)
      (by rwa [Set.pair_comm] at hL3) hpa'1y))
    hF0 hF hm₁ hm₂
  obtain ⟨c₂, hc₂⟩ := hconst hr₂ (hzpow (add_mem (one_mem _) haa) (add_mem (one_mem _) ha'a))
  change a ^ d * a' ^ e = _ at hc₁
  change (1 + a) ^ d * (1 + a') ^ e = _ at hc₂
  -- Both exponents are nonzero.
  have hde : ¬ (d = 0 ∧ e = 0) := by
    rintro ⟨hd0, he0⟩
    apply hm₁₂
    ext j
    fin_cases j
    · simpa [hd, sub_eq_zero] using hd0
    · simpa [he, sub_eq_zero] using he0
  have hd0 : d ≠ 0 := by
    intro hd0
    have he0 : e ≠ 0 := fun he0 ↦ hde ⟨hd0, he0⟩
    rw [hd0, zpow_zero, one_mul] at hc₁
    exact false_of_zpow_eq_algebraMap ha'0 he0 hc₁
  have he0 : e ≠ 0 := by
    intro he0
    rw [he0, zpow_zero, mul_one] at hc₁
    exact false_of_zpow_eq_algebraMap ha0 hd0 hc₁
  exact frobenius_of_signed_characters q ha0 ha'0 hd0 he0 hc₁ hc₂

end Assembly

end AclGeom
