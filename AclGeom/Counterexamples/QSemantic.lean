/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.MultiplicativeQuotient
import AclGeom.Correspondence.WeightedSupport
import AclGeom.Interpretation.FrobLinkRigidity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Semantic obstruction for the Q/Q′ counterexamples

For independent `(s, t)` over a characteristic-zero field `k`, representatives satisfying
`[x] = [s]`, `[y] = [s t²]`, `[x + y] = [s(1+t)²]`, and `[x/y] = [t]` force `s/x²`
to be algebraic over `k` (`isAlgebraic_div_sq_of_qPair`). A Q′-pair with an independent
fresh element has the same ratio (`point_div_eq_of_q'Pair`). Thus both semantic relations fail
whenever `s/x²` is transcendental for every nonzero `x`.

The algebraic core works over the relative algebraic closure `M` of the base in an algebraic
closure of the ambient field. It fixes one polynomial for the curve of `(s, x)` before both
scalings. The scalings `(t², y/x)` and `((1+t)², 1+y/x)` give characters with the same support
exponents. Characteristic zero makes the signed-character conclusion `y/x = t`. Every support
pair then has weight difference zero for `(2,1)`, and weighted homogeneity makes `s/x²`
algebraic. Algebraic-base invariance and ambient transport pull this conclusion back to `k`.
The Q′ ratio uses `MulCorrSetup.interalgebraic_div` with the explicit fresh element.

**Status:** the displayed semantic obstruction lemmas are proved. Their concrete consumers
are in Counterexamples/QRefutation. Explicit geometric witnesses are proved separately in
Counterexamples/QDescent; the geometric predicates retain their original definitions.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

noncomputable section

section Scaling

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Scaling by a nonzero element of `racl k {t}` keeps an element outside `racl k {t}`. -/
theorem mul_notMem_racl_singleton {s t c : K} (hs : s ∉ racl k ({t} : Set K))
    (hc : c ∈ racl k ({t} : Set K)) (hc0 : c ≠ 0) : s * c ∉ racl k ({t} : Set K) := fun h ↦
  hs (by simpa only [mul_div_cancel_right₀ s hc0] using div_mem h hc)

/-- For an independent pair `(s, t)` and `c ∈ racl k {t}` nonzero, `s c` generates a point. -/
theorem mul_notMem_bot {s t c : K} (hst : AlgebraicIndependent k ![s, t])
    (hc : c ∈ racl k ({t} : Set K)) (hc0 : c ≠ 0) : s * c ∉ (⊥ : ClosedIF k K) := fun h ↦
  mul_notMem_racl_singleton (AlgebraicIndependent.notMem_racl_pair' hst) hc hc0
    (racl_mono (Set.empty_subset _) (mem_racl_empty_of_isAlgebraic (mem_bot_iff.1 h)))

end Scaling

section Core

variable {M Ω : Type*} [Field M] [Field Ω] [Algebra M Ω]

/-- **The semantic core of the #25 `Q`-refutation.**  Over an algebraically closed base `M` of
characteristic zero inside an algebraically closed `Ω`, let `S, T` be independent, and let `U, V`
satisfy `[U] = [S]`, `[V] = [S T²]`, `[U + V] = [S (1 + T)²]` and `[V / U] = [T]`.  Then `S / U²`
is algebraic over `M`. -/
theorem isAlgebraic_div_sq_of_qLocus [IsAlgClosed M] [CharZero M] [IsAlgClosed Ω]
    {S T U V : Ω} (hST : AlgebraicIndependent M ![S, T])
    (hUS : U ∈ racl M ({S} : Set Ω)) (hSU : S ∈ racl M ({U} : Set Ω))
    (hVW : V ∈ racl M ({S * T ^ 2} : Set Ω)) (hWV : S * T ^ 2 ∈ racl M ({V} : Set Ω))
    (hZ : U + V ∈ racl M ({S * (1 + T) ^ 2} : Set Ω))
    (hZ' : S * (1 + T) ^ 2 ∈ racl M ({U + V} : Set Ω))
    (hGT : V / U ∈ racl M ({T} : Set Ω)) (hTG : T ∈ racl M ({V / U} : Set Ω)) :
    IsAlgebraic M (S / U ^ 2) := by
  classical
  -- Rank facts over `M` and over `N = racl M {T}`.
  have hS_T : S ∉ racl M ({T} : Set Ω) := AlgebraicIndependent.notMem_racl_pair' hST
  have hTe : T ∉ racl M (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hST (racl_mono (Set.empty_subset _) h)
  have hGe : V / U ∉ racl M (∅ : Set Ω) := notMem_racl_empty_of_mem_singleton hTe hTG
  have hT0 : T ≠ 0 := ne_zero_of_notMem_racl_empty hTe
  have h1T0 : 1 + T ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hTe)
  have hG0 : V / U ≠ 0 := ne_zero_of_notMem_racl_empty hGe
  have h1G0 : 1 + V / U ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hGe)
  have hTT : T ∈ racl M ({T} : Set Ω) := subset_racl M _ rfl
  have hnot : ∀ {z w : Ω}, z ∈ racl M ({w} : Set Ω) → z ∉ racl M ({T} : Set Ω) →
      w ∉ racl M ({T} : Set Ω) := fun hzw hz hw ↦
    hz (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hw) hzw)
  have hU_T : U ∉ racl M ({T} : Set Ω) := hnot hSU hS_T
  have hW_T : S * T ^ 2 ∉ racl M ({T} : Set Ω) :=
    mul_notMem_racl_singleton hS_T (pow_mem hTT 2) (pow_ne_zero 2 hT0)
  have hZ_T : S * (1 + T) ^ 2 ∉ racl M ({T} : Set Ω) :=
    mul_notMem_racl_singleton hS_T (pow_mem (add_mem (one_mem _) hTT) 2) (pow_ne_zero 2 h1T0)
  have hV_T : V ∉ racl M ({T} : Set Ω) := hnot hWV hW_T
  have hUV_T : U + V ∉ racl M ({T} : Set Ω) := hnot hZ' hZ_T
  have hS0 : S ≠ 0 := fun h ↦ hS_T (by rw [h]; exact zero_mem _)
  have hU0 : U ≠ 0 := fun h ↦ hU_T (by rw [h]; exact zero_mem _)
  have hNt : ∀ {z : Ω}, z ∉ racl M ({T} : Set Ω) →
      Transcendental ↥(racl M ({T} : Set Ω)) z := fun hz ↦ transcendental_racl_of_notMem hz
  have hSM : Transcendental M S := fun h ↦ hNt hS_T (h.tower_top _)
  -- The curve of `(S, U)` over `M`: one generator, fixed before both scalings.
  obtain ⟨F, hFp, hF⟩ := exists_prime_span_idealOf M hSM hUS
  have hF0 : F ≠ 0 := hFp.ne_zero
  have hFx : MvPolynomial.aeval ![S, U] F = 0 :=
    (mem_idealOf_iff M).1 (hF ▸ Ideal.subset_span rfl)
  have hGU : V / U * U = V := div_mul_cancel₀ V hU0
  have h1GU : (1 + V / U) * U = U + V := by rw [add_mul, one_mul, hGU]
  -- The characters of the scalings `(T², G)` and `((1 + T)², 1 + G)`, at every support pair.
  have hchar₁ : ∀ {m₁ m₂ : Fin 2 →₀ ℕ}, m₁ ∈ F.support → m₂ ∈ F.support →
      ∃ r : M, (T ^ 2) ^ ((m₁ 0 : ℤ) - m₂ 0) * (V / U) ^ ((m₁ 1 : ℤ) - m₂ 1) =
        algebraMap M Ω r := fun hm₁ hm₂ ↦
    exists_character_of_scaled_locus (pow_mem hTT 2) hGT (pow_ne_zero 2 hT0) hG0
      (hNt hS_T) (hNt hU_T) hUS hSU
      (hNt (by rw [mul_comm (T ^ 2) S]; exact hW_T)) (hNt (by rw [hGU]; exact hV_T))
      (by rw [hGU, mul_comm (T ^ 2) S]; exact hVW) (by rw [hGU, mul_comm (T ^ 2) S]; exact hWV)
      hF0 hF hm₁ hm₂
  have hchar₂ : ∀ {m₁ m₂ : Fin 2 →₀ ℕ}, m₁ ∈ F.support → m₂ ∈ F.support →
      ∃ r : M, ((1 + T) ^ 2) ^ ((m₁ 0 : ℤ) - m₂ 0) * (1 + V / U) ^ ((m₁ 1 : ℤ) - m₂ 1) =
        algebraMap M Ω r := fun hm₁ hm₂ ↦
    exists_character_of_scaled_locus (pow_mem (add_mem (one_mem _) hTT) 2)
      (add_mem (one_mem _) hGT) (pow_ne_zero 2 h1T0) h1G0 (hNt hS_T) (hNt hU_T) hUS hSU
      (hNt (by rw [mul_comm ((1 + T) ^ 2) S]; exact hZ_T)) (hNt (by rw [h1GU]; exact hUV_T))
      (by rw [h1GU, mul_comm ((1 + T) ^ 2) S]; exact hZ)
      (by rw [h1GU, mul_comm ((1 + T) ^ 2) S]; exact hZ') hF0 hF hm₁ hm₂
  have hsq : ∀ (z : Ω) (n : ℤ), (z ^ 2) ^ n = z ^ (2 * n) := fun z n ↦ by
    rw [← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  -- One support pair: the signed-character endpoint gives `G = T`.
  obtain ⟨m₁, hm₁, m₂, hm₂, hm₁₂⟩ := exists_support_pair_of_aeval_eq_zero
    (v := ![S, U]) (fun j ↦ by fin_cases j <;> simpa) hF0 hFx
  have hGT' : V / U = T := by
    obtain ⟨r₁, hr₁⟩ := hchar₁ hm₁ hm₂
    obtain ⟨r₂, hr₂⟩ := hchar₂ hm₁ hm₂
    rw [hsq] at hr₁ hr₂
    set d : ℤ := (m₁ 0 : ℤ) - m₂ 0 with hd
    set e : ℤ := (m₁ 1 : ℤ) - m₂ 1 with he
    have hde : ¬ (d = 0 ∧ e = 0) := by
      rintro ⟨hd0, he0⟩
      apply hm₁₂
      ext j
      fin_cases j
      · simpa [hd, sub_eq_zero] using hd0
      · simpa [he, sub_eq_zero] using he0
    have hd0 : 2 * d ≠ 0 := by
      intro h2d
      have he0 : e ≠ 0 := fun he0 ↦ hde ⟨by omega, he0⟩
      rw [h2d, zpow_zero, one_mul] at hr₁
      exact false_of_zpow_eq_algebraMap hGe he0 hr₁
    have he0 : e ≠ 0 := by
      intro he0
      rw [he0, zpow_zero, mul_one] at hr₁
      exact false_of_zpow_eq_algebraMap hTe hd0 hr₁
    obtain ⟨n, hn | hn⟩ := frobenius_of_signed_characters 1 hTe hGe hd0 he0 hr₁ hr₂
    · simpa using hn
    · simpa using hn.symm
  -- Every support pair now has character `T^{2d' + e'}`, so `F` is weighted homogeneous.
  have hpairs : ∀ m₁ ∈ F.support, ∀ m₂ ∈ F.support,
      2 * ((m₁ 0 : ℤ) - m₂ 0) + ((m₁ 1 : ℤ) - m₂ 1) = 0 := by
    intro m₁ hm₁ m₂ hm₂
    obtain ⟨r, hr⟩ := hchar₁ hm₁ hm₂
    rw [hsq, hGT', ← zpow_add₀ hT0] at hr
    by_contra hne
    exact false_of_zpow_eq_algebraMap hTe hne hr
  obtain ⟨W, hW⟩ := isWeightedHomogeneous_of_support_pairs hF0 hpairs
  exact isAlgebraic_div_sq_of_isWeightedHomogeneous hF0 hW hU0 hFx

end Core

section Semantic

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Interalgebraicity over `k` in `K` is interalgebraicity over `k̄ = algebraicClosure k Ω` in
`Ω`. -/
theorem algHom_mem_racl_algebraicClosure_iff {Ω : Type*} [Field Ω] [Algebra k Ω]
    (ι : K →ₐ[k] Ω) {z w : K} :
    ι z ∈ racl (↥(algebraicClosure k Ω)) ({ι w} : Set Ω) ↔ z ∈ racl k ({w} : Set K) :=
  (mem_racl_base_iff_of_algebraic fun _ hy ↦ (mem_algebraicClosure_iff (F := k)).1 hy).trans
    (algHom_mem_racl_singleton_iff ι)

/-- Equal principal points of `K/k` have mutually interalgebraic images over `k̄`. -/
theorem algHom_mem_racl_algebraicClosure_of_point_eq {Ω : Type*} [Field Ω] [Algebra k Ω]
    (ι : K →ₐ[k] Ω) {a b : K} (h : point k a = point k b) :
    ι a ∈ racl (↥(algebraicClosure k Ω)) ({ι b} : Set Ω) ∧
      ι b ∈ racl (↥(algebraicClosure k Ω)) ({ι a} : Set Ω) :=
  ⟨(algHom_mem_racl_algebraicClosure_iff ι).2 (point_eq_point_iff.1 h).1,
    (algHom_mem_racl_algebraicClosure_iff ι).2 (point_eq_point_iff.1 h).2⟩

/-- **A #25 `Q`-pair is a scaled square root of `s`.**  If `(s, t)` is independent over `k` of
characteristic zero, and `[x] = [s]`, `[y] = [s t²]`, `[x + y] = [s (1 + t)²]` and `[x / y] = [t]`,
then `s / x²` is algebraic over `k`. -/
theorem isAlgebraic_div_sq_of_qPair [CharZero k] {s t x y : K}
    (hst : AlgebraicIndependent k ![s, t]) (hx : point k x = point k s)
    (hy : point k y = point k (s * t ^ 2)) (hxy : point k (x + y) = point k (s * (1 + t) ^ 2))
    (hq : point k (x / y) = point k t) : IsAlgebraic k (s / x ^ 2) := by
  let ι : K →ₐ[k] AlgebraicClosure K := IsScalarTower.toAlgHom k K (AlgebraicClosure K)
  obtain ⟨hU, hS⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hx
  obtain ⟨hV, hW⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hy
  obtain ⟨hZ, hZ'⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hxy
  obtain ⟨hG, hT⟩ :=
    algHom_mem_racl_algebraicClosure_of_point_eq ι ((point_div_symm y x).trans hq)
  simp only [map_mul, map_pow, map_add, map_one, map_div₀] at hV hW hZ hZ' hG hT
  set M := algebraicClosure k (AlgebraicClosure K)
  have : IsAlgClosed ↥M := IsAlgClosure.isAlgClosed k
  have : CharZero ↥M := charZero_of_injective_algebraMap (algebraMap k ↥M).injective
  have halg : ∀ z ∈ M, IsAlgebraic k z := fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz
  have hST : AlgebraicIndependent ↥M ![ι s, ι t] :=
    algebraicIndependent_pair
      ((algHom_mem_racl_algebraicClosure_iff ι).not.2 (AlgebraicIndependent.notMem_racl_pair' hst))
      ((algHom_mem_racl_algebraicClosure_iff ι).not.2 (AlgebraicIndependent.notMem_racl_pair hst))
  have hcore := isAlgebraic_div_sq_of_qLocus hST hU hS hV hW hZ hZ' hG hT
  rw [← map_pow ι, ← map_div₀ ι] at hcore
  exact isAlgebraic_of_mem_racl_empty ((algHom_mem_racl_empty_iff ι).1
    ((mem_racl_base_iff_of_algebraic halg).1 (mem_racl_empty_of_isAlgebraic hcore)))

/-- **A #25 `Q′`-pair has the `Q`-ratio.**  If `(s, t, e)` is independent over `k` and `x, y ≠ 0`
satisfy `[x] = [s]`, `[y] = [s t²]` and `[x y] = [s t]`, then `[x / y] = [t]`.  Over `k̄`, the
pairs `(s, x)` and `(s t², y)` form a multiplicative correspondence setup with `e` fresh, and its
quotient lemma gives `[x / y] = [s / (s t²)] = [t]`. -/
theorem point_div_eq_of_q'Pair {s t e x y : K} (hste : AlgebraicIndependent k ![s, t, e])
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : point k x = point k s)
    (hy : point k y = point k (s * t ^ 2)) (hm : point k (x * y) = point k (s * t)) :
    point k (x / y) = point k t := by
  let ι : K →ₐ[k] AlgebraicClosure K := IsScalarTower.toAlgHom k K (AlgebraicClosure K)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  obtain ⟨hU, hS⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hx
  obtain ⟨hV, hW⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hy
  obtain ⟨hP, hP'⟩ := algHom_mem_racl_algebraicClosure_of_point_eq ι hm
  simp only [map_mul, map_pow] at hV hW hP hP'
  set M := algebraicClosure k (AlgebraicClosure K)
  have : IsAlgClosed ↥M := IsAlgClosure.isAlgClosed k
  -- Independence over `k̄`.
  have h3 : AlgebraicIndependent ↥M ![ι s, ι t, ι e] := by
    have h := AlgebraicIndependent.extendScalars ↥M (hste.map' hinj)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have h2 : AlgebraicIndependent ↥M ![ι s, ι t] := by
    have h := h3.comp ![0, 1] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨-, -, he_st⟩ := notMem_racl_of_indep_three h3
  have hS0 : ι s ≠ 0 := AlgebraicIndependent.ne_zero h2 0
  have hsS : ι s ∈ racl ↥M (Set.range ![ι s, ι t]) := subset_racl _ _ ⟨0, rfl⟩
  have htS : ι t ∈ racl ↥M (Set.range ![ι s, ι t]) := subset_racl _ _ ⟨1, rfl⟩
  have hsW : ι s ∈ racl ↥M (Set.range ![ι s, ι s * ι t ^ 2]) := subset_racl _ _ ⟨0, rfl⟩
  have hwW : ι s * ι t ^ 2 ∈ racl ↥M (Set.range ![ι s, ι s * ι t ^ 2]) :=
    subset_racl _ _ ⟨1, rfl⟩
  have ht2W : ι t ^ 2 ∈ racl ↥M (Set.range ![ι s, ι s * ι t ^ 2]) :=
    by simpa only [mul_div_cancel_left₀ _ hS0] using (div_mem hwW hsW)
  have hsq : ι s * (ι s * ι t ^ 2) = (ι s * ι t) ^ 2 := by ring
  -- The multiplicative correspondence setup `(s, x), (s t², y)` over `k̄`.
  let C : MulCorrSetup (↥M) (AlgebraicClosure K) :=
    { x₁ := ι s
      y₁ := ι x
      x₂ := ι s * ι t ^ 2
      y₂ := ι y
      indep := by
        refine AlgebraicIndependent.of_racl_range_eq h2
          (racl_range_eq_of_mem (fun j ↦ ?_) (fun i ↦ ?_))
        · fin_cases j
          · exact hsS
          · exact mul_mem hsS (pow_mem htS 2)
        · fin_cases i
          · exact hsW
          · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht2W)
              (mem_racl_singleton_pow two_ne_zero)
      y₁_ne := (map_ne_zero ι).2 hx0
      y₂_ne := (map_ne_zero ι).2 hy0
      y₁_mem := hU
      x₁_mem := hS
      y₂_mem := hV
      x₂_mem := hW
      mul_mem := by
        rw [hsq, racl_pow _ two_ne_zero]
        exact hP
      mul_mem' := by
        rw [hsq]
        exact pow_mem hP' 2 }
  -- `e` is fresh over the two generic points.
  have hfresh : ι e ∉ racl ↥M ({ι s, ι s * ι t ^ 2} : Set (AlgebraicClosure K)) := fun h ↦
    he_st (racl_le_of_subset_racl (Set.insert_subset_iff.2
      ⟨subset_racl _ _ (by simp), Set.singleton_subset_iff.2
        (mul_mem (subset_racl _ _ (by simp)) (pow_mem (subset_racl _ _ (by simp)) 2))⟩) h)
  obtain ⟨h₁, h₂⟩ := C.interalgebraic_div hfresh
  change ι x / ι y ∈ racl ↥M ({ι s / (ι s * ι t ^ 2)} : Set (AlgebraicClosure K)) at h₁
  change ι s / (ι s * ι t ^ 2) ∈ racl ↥M ({ι x / ι y} : Set (AlgebraicClosure K)) at h₂
  rw [div_mul_cancel_left₀ hS0, racl_inv, racl_pow _ two_ne_zero, ← map_div₀ ι] at h₁
  rw [div_mul_cancel_left₀ hS0, ← map_div₀ ι] at h₂
  have h₂' : ι t ∈ racl ↥M ({ι (x / y)} : Set (AlgebraicClosure K)) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 (by simpa using inv_mem h₂))
      (mem_racl_singleton_pow two_ne_zero)
  exact point_eq_point_iff.2 ⟨(algHom_mem_racl_algebraicClosure_iff ι).1 h₁,
    (algHom_mem_racl_algebraicClosure_iff ι).1 h₂'⟩

end Semantic

section Refutation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Semantic `Q` fails for the #25 tuple** `([s], [s t²], [s (1 + t)²], [t])` when `s / x²` is
transcendental for every `x ≠ 0`. -/
theorem not_qSem_of_indep [CharZero k] {s t : K} (hst : AlgebraicIndependent k ![s, t])
    (hsq : ∀ x : K, x ≠ 0 → ¬ IsAlgebraic k (s / x ^ 2)) {P D Y I : Point k K}
    (hP : P.1 = point k s) (hD : D.1 = point k (s * t ^ 2))
    (hY : Y.1 = point k (s * (1 + t) ^ 2)) (hI : I.1 = point k t) : ¬ QSem P D Y I := by
  rintro ⟨x, y, hxy, hPx, hDy, hYxy, hIxy⟩
  exact hsq x (AlgebraicIndependent.ne_zero hxy 0)
    (isAlgebraic_div_sq_of_qPair hst (hPx.symm.trans hP) (hDy.symm.trans hD)
      (hYxy.symm.trans hY) (hIxy.symm.trans hI))

/-- **Semantic `Q′` fails for the #25 tuple** `([s], [s t²], [s (1 + t)²], [s t])` when `s / x²`
is transcendental for every `x ≠ 0`: a `Q′`-pair has the `Q`-ratio (`point_div_eq_of_q'Pair`), so
it is a `Q`-pair. -/
theorem not_q'Sem_of_indep [CharZero k] {s t e : K} (hste : AlgebraicIndependent k ![s, t, e])
    (hsq : ∀ x : K, x ≠ 0 → ¬ IsAlgebraic k (s / x ^ 2)) {X Y S E : Point k K}
    (hX : X.1 = point k s) (hY : Y.1 = point k (s * t ^ 2))
    (hS : S.1 = point k (s * (1 + t) ^ 2)) (hE : E.1 = point k (s * t)) : ¬ Q'Sem X Y S E := by
  rintro ⟨x, y, hxy, hXx, hYy, hSxy, hExy⟩
  have hst : AlgebraicIndependent k ![s, t] := by
    have h := hste.comp ![0, 1] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hq := point_div_eq_of_q'Pair hste (AlgebraicIndependent.ne_zero hxy 0)
    (AlgebraicIndependent.ne_zero hxy 1) (hXx.symm.trans hX) (hYy.symm.trans hY)
    (hExy.symm.trans hE)
  exact hsq x (AlgebraicIndependent.ne_zero hxy 0)
    (isAlgebraic_div_sq_of_qPair hst (hXx.symm.trans hX) (hYy.symm.trans hY)
      (hSxy.symm.trans hS) hq)


end Refutation

end

end AclGeom
