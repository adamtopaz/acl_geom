/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Divisors

/-!
# The pole-order bound

The pole-side of Stichtenoth Theorem 1.4.11: the total pole order of `f`
over any finite set of poles is at most `[F : k(f)]`
(`sum_pole_orders_le_finrank`). The witnesses are prescribed-order
elements `u i j` with order `-j` at the `i`-th pole and order `1` at the
other listed poles; coefficients from `k(f)` shift orders at the `i`-th
pole by multiples of the pole order `e i` (the uniform order applied to
`f⁻¹`), so after normalizing the minimal coefficient order to zero, the
cross-place terms have positive order while the same-place terms have
distinct nonpositive orders by Euclidean uniqueness — a strictly dominant
term.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, toward deg-div-zero).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Adjoining an element and its inverse give the same subfield. -/
theorem adjoin_inv_eq (f : F) :
    adjoin k ({f⁻¹} : Set F) = adjoin k ({f} : Set F) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [inv_zero]
  refine le_antisymm ?_ ?_
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact inv_mem (subset_adjoin k _ rfl)
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    have h1 : f⁻¹ ∈ adjoin k ({f⁻¹} : Set F) := subset_adjoin k _ rfl
    have h2 := inv_mem h1
    rwa [inv_inv] at h2

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **The pole-order bound** (the pole side of Stichtenoth Theorem
1.4.11): the total pole order of `f` over finitely many distinct poles is
at most `[F : k(f)]`. -/
theorem sum_pole_orders_le_finrank {s : ℕ} (P : Fin s → Place k F)
    (hinj : Function.Injective P) {f : F}
    (htr : Transcendental k f)
    (hpole : ∀ i, (P i).ord f < 0) :
    (∑ i, (-(P i).ord f).toNat) ≤
      Module.finrank (↥(adjoin k ({f} : Set F))) F := by
  classical
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  have hf0 : f ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have hftr' : Transcendental k f⁻¹ := fun h ↦
    htr (IsAlgebraic.inv_iff.1 h)
  have hfinv0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  -- Pole places are exactly where `f⁻¹` is small.
  have hinvlt : ∀ i, (P i).val.valuation f⁻¹ < 1 := by
    intro i
    have h1 : 0 < (P i).ord f⁻¹ := by
      rw [(P i).ord_inv hf0]
      have := hpole i
      omega
    exact ((P i).ord_pos_iff hfinv0).1 h1
  have hordinv : ∀ i, (P i).ord f⁻¹ = -(P i).ord f := fun i ↦
    (P i).ord_inv hf0
  -- The witnesses with prescribed orders.
  set e : Fin s → ℕ := fun i ↦ (-(P i).ord f).toNat with he
  have he_pos : ∀ i, 0 < e i := by
    intro i
    show 0 < (-(P i).ord f).toNat
    have := hpole i
    omega
  set ι := (Σ i : Fin s, Fin (e i)) with hι
  have huex : ∀ x : ι, ∃ w : F, w ≠ 0 ∧
      ∀ i, (P i).ord w = if i = x.1 then -(x.2 : ℤ) else 1 := by
    intro x
    exact Place.exists_forall_ord_eq P hinj
      (fun i ↦ if i = x.1 then -(x.2 : ℤ) else 1)
  choose u hu0 hu using huex
  -- The witnesses are linearly independent over `k(f)`.
  have hind : LinearIndependent (↥(adjoin k ({f} : Set F))) u := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum x₀'
    by_contra hg₀
    set S : Finset ι := Finset.univ.filter (fun x ↦ g x ≠ 0) with hS
    have hx₀S : x₀' ∈ S := by simp [hS, hg₀]
    have hcoe0 : ∀ x ∈ S, ((g x : F)) ≠ 0 := by
      intro x hx
      rw [hS, Finset.mem_filter] at hx
      simpa using hx.2
    -- Uniform coefficient orders relative to `f⁻¹`.
    have hords : ∀ x ∈ S, ∃ m : ℤ, ∀ O : ValuationSubring F,
        (∀ c : k, algebraMap k F c ∈ O) → O.valuation f⁻¹ < 1 →
        O.valuation ((g x : F)) = O.valuation f⁻¹ ^ m := by
      intro x hx
      refine exists_uniform_valuation_zpow hftr' ?_ (hcoe0 x hx)
      rw [adjoin_inv_eq]
      exact SetLike.coe_mem (g x)
    choose! m hm using hords
    -- Order of a summand at a listed place.
    have hterm_ord : ∀ x ∈ S, ∀ i : Fin s,
        (P i).ord ((g x : F) * u x) =
          m x * (e i : ℤ) + (if i = x.1 then -(x.2 : ℤ) else 1) := by
      intro x hx i
      rw [(P i).ord_mul (hcoe0 x hx) (hu0 x), hu x i]
      congr 1
      have h1 := hm x hx (P i).val (P i).algebraMap_mem (hinvlt i)
      have h2 : (P i).ord ((g x : F)) = m x * (P i).ord f⁻¹ := by
        refine (P i).ord_eq_of_valuation_eq_zpow (hcoe0 x hx) ?_
        rw [h1, (P i).valuation_eq_zpow_ord hfinv0, ← zpow_mul,
          mul_comm]
      rw [h2, hordinv i]
      have h3 : ((e i : ℕ) : ℤ) = -(P i).ord f := by
        show (((-(P i).ord f).toNat : ℕ) : ℤ) = -(P i).ord f
        have := hpole i
        omega
      rw [h3]
    -- The dominant summand: minimal coefficient order, then minimal
    -- term order at its own place.
    obtain ⟨x₀, hx₀S', hx₀min⟩ := S.exists_min_image m ⟨x₀', hx₀S⟩
    set i₀ : Fin s := x₀.1 with hi₀
    set T : Finset ι := S.filter (fun x ↦ x.1 = i₀) with hT
    have hx₀T : x₀ ∈ T := by
      rw [hT, Finset.mem_filter]
      exact ⟨hx₀S', rfl⟩
    obtain ⟨y₀, hy₀T, hy₀min⟩ := T.exists_min_image
      (fun x ↦ (P i₀).ord ((g x : F) * u x)) ⟨x₀, hx₀T⟩
    have hy₀S : y₀ ∈ S := (Finset.mem_filter.1 hy₀T).1
    have hy₀place : y₀.1 = i₀ := (Finset.mem_filter.1 hy₀T).2
    -- The order of the dominant term is at most `m x₀ * e i₀`.
    have hy₀le : (P i₀).ord ((g y₀ : F) * u y₀) ≤
        m x₀ * (e i₀ : ℤ) := by
      have h1 := hy₀min x₀ hx₀T
      have h2 := hterm_ord x₀ hx₀S' i₀
      rw [if_pos rfl] at h2
      have h3 : (0 : ℤ) ≤ (x₀.2 : ℤ) := by positivity
      omega
    -- Every other summand has strictly larger order at `P i₀`.
    have hdom : ∀ x ∈ S, x ≠ y₀ →
        (P i₀).val.valuation ((g x : F) * u x) <
          (P i₀).val.valuation ((g y₀ : F) * u y₀) := by
      intro x hx hxne
      have hordlt : (P i₀).ord ((g y₀ : F) * u y₀) <
          (P i₀).ord ((g x : F) * u x) := by
        rcases eq_or_ne x.1 i₀ with hplace | hplace
        · -- Same place: Euclidean uniqueness of the order.
          have hxT : x ∈ T := by
            rw [hT, Finset.mem_filter]
            exact ⟨hx, hplace⟩
          have h1 := hy₀min x hxT
          have h2 : (P i₀).ord ((g x : F) * u x) ≠
              (P i₀).ord ((g y₀ : F) * u y₀) := by
            intro heq
            have h3 := hterm_ord x hx i₀
            have h4 := hterm_ord y₀ hy₀S i₀
            rw [if_pos hplace.symm] at h3
            rw [if_pos hy₀place.symm] at h4
            have h5 : ((x.2 : ℕ) : ℤ) < (e i₀ : ℤ) := by
              have h5a : (x.2 : ℕ) < e x.1 := x.2.2
              have h5b : e x.1 = e i₀ := by rw [hplace]
              omega
            have h5' : ((y₀.2 : ℕ) : ℤ) < (e i₀ : ℤ) := by
              have h5a : (y₀.2 : ℕ) < e y₀.1 := y₀.2.2
              have h5b : e y₀.1 = e i₀ := by rw [hy₀place]
              omega
            have hepos : (0 : ℤ) < (e i₀ : ℤ) := by
              have := he_pos i₀
              omega
            have hkey : (m x - m y₀) * (e i₀ : ℤ) =
                ((x.2 : ℕ) : ℤ) - ((y₀.2 : ℕ) : ℤ) := by
              linear_combination -h3 + h4 + heq
            have hmm : m x - m y₀ = 0 := by
              by_contra hmm0
              rcases lt_or_gt_of_ne hmm0 with hlt | hgt
              · have h6 : (m x - m y₀) * (e i₀ : ℤ) ≤
                    (-1) * (e i₀ : ℤ) :=
                  mul_le_mul_of_nonneg_right (by omega) (by omega)
                omega
              · have h6 : (1 : ℤ) * (e i₀ : ℤ) ≤
                    (m x - m y₀) * (e i₀ : ℤ) :=
                  mul_le_mul_of_nonneg_right (by omega) (by omega)
                omega
            have hme : m x = m y₀ ∧
                ((x.2 : ℕ) : ℤ) = ((y₀.2 : ℕ) : ℤ) := by
              constructor
              · omega
              · rw [hmm, zero_mul] at hkey
                omega
            refine hxne ?_
            have hfst : x.1 = y₀.1 := by rw [hplace, hy₀place]
            refine Sigma.ext hfst ?_
            refine (Fin.heq_ext_iff (by rw [hfst])).2 ?_
            have := hme.2
            omega
          omega
        · -- Cross place: positive order beats the nonpositive minimum.
          have h1 := hterm_ord x hx i₀
          rw [if_neg (fun h ↦ hplace h.symm)] at h1
          have h2 := hx₀min x hx
          have h3 : m x₀ * (e i₀ : ℤ) ≤ m x * (e i₀ : ℤ) := by
            refine mul_le_mul_of_nonneg_right h2 ?_
            have := he_pos i₀
            omega
          omega
      -- Convert the order comparison to valuations.
      by_contra hc
      push Not at hc
      have h6 := ((P i₀).valuation_le_valuation_iff
        (mul_ne_zero (hcoe0 y₀ hy₀S) (hu0 y₀))
        (mul_ne_zero (hcoe0 x hx) (hu0 x))).1 hc
      omega
    -- The vanishing sum has a nonzero value: contradiction.
    have hSsum : ∑ x ∈ S, (g x : F) * u x = 0 := by
      rw [← hsum]
      rw [show ∑ x : ι, g x • u x = ∑ x : ι, (g x : F) * u x from
        Finset.sum_congr rfl fun x _ ↦ by rw [Algebra.smul_def]; rfl]
      refine Finset.sum_subset (Finset.subset_univ S) fun x _ hx ↦ ?_
      rw [hS, Finset.mem_filter, not_and, not_not] at hx
      rw [hx (Finset.mem_univ x), ZeroMemClass.coe_zero, zero_mul]
    have h0 := valuation_sum_eq_of_forall_lt (O := (P i₀).val)
      (f := fun x ↦ (g x : F) * u x) hy₀S hdom
    rw [hSsum, Valuation.map_zero] at h0
    exact (Valuation.ne_zero_iff _).2
      (mul_ne_zero (hcoe0 y₀ hy₀S) (hu0 y₀)) h0.symm
  have hcard := hind.fintype_card_le_finrank
  rwa [Fintype.card_sigma, Finset.sum_congr rfl
    (fun i _ ↦ Fintype.card_fin (e i))] at hcard

end

end AclGeom
