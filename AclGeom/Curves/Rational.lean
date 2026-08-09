/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Genus

/-!
# Rational function fields have genus zero

The converse of the genus-zero checkpoint. A generator `t` has a single
simple pole `P∞`; each shift `t − a` has a single simple zero and the
same pole, and every place away from `P∞` is such a zero (residues), so
divisors of degree zero are principal by taking products of shifts —
partial fractions in divisor form. Every defect then reduces to that of
a multiple of `P∞`, where the powers of `t` fill the Riemann–Roch space:
all defects are `≤ 0` and the genus is zero.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]
variable {t : F}

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- A generator witnesses `[F : k(t)] = 1`. -/
theorem finrank_adjoin_eq_one_of_eq_top
    (htop : adjoin k ({t} : Set F) = ⊤) :
    Module.finrank (↥(adjoin k ({t} : Set F))) F = 1 := by
  rw [htop]
  exact IntermediateField.finrank_top

/-- The pole divisor of a generator is a single place. -/
theorem exists_poleDivisor_eq_single (htr : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) :
    ∃ P : Place k F, poleDivisor k t = Finsupp.single P 1 := by
  apply Divisor.eq_single_of_deg_eq_one (poleDivisor_nonneg t)
  rw [deg_poleDivisor_eq_finrank htr,
    finrank_adjoin_eq_one_of_eq_top htop]
  exact Nat.cast_one

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Shifting by a constant preserves transcendence. -/
theorem transcendental_sub_algebraMap (htr : Transcendental k t)
    (a : k) : Transcendental k (t - algebraMap k F a) := by
  intro halg
  refine htr ?_
  have h1 : IsIntegral k (t - algebraMap k F a + algebraMap k F a) :=
    halg.isIntegral.add isIntegral_algebraMap
  rw [show t - algebraMap k F a + algebraMap k F a = t by ring] at h1
  exact h1.isAlgebraic

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Shifting by a constant preserves the generator property. -/
theorem adjoin_sub_algebraMap_eq_top
    (htop : adjoin k ({t} : Set F) = ⊤) (a : k) :
    adjoin k ({t - algebraMap k F a} : Set F) = ⊤ := by
  rw [eq_top_iff, ← htop, adjoin_le_iff, Set.singleton_subset_iff]
  have h1 : t - algebraMap k F a ∈
      adjoin k ({t - algebraMap k F a} : Set F) := subset_adjoin k _ rfl
  have h2 := add_mem h1
    (IntermediateField.algebraMap_mem
      (adjoin k ({t - algebraMap k F a} : Set F)) a)
  rw [show t - algebraMap k F a + algebraMap k F a = t by ring] at h2
  exact h2

/-- The order of the generator at its pole is `−1`. -/
theorem ord_eq_neg_one_of_poleDivisor {P : Place k F}
    (htr : Transcendental k t)
    (hpd : poleDivisor k t = Finsupp.single P 1) :
    P.ord t = -1 := by
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have h2 : poleDivisor k t P = 1 := by
    rw [hpd, Finsupp.single_eq_same]
  rw [poleDivisor_apply ht0] at h2
  rcases le_total (-(P.ord t)) 0 with h | h
  · rw [max_eq_right h] at h2
    omega
  · rw [max_eq_left h] at h2
    omega

/-- The generator is integral away from its pole. -/
theorem ord_nonneg_of_poleDivisor {P : Place k F}
    (htr : Transcendental k t)
    (hpd : poleDivisor k t = Finsupp.single P 1) {Q : Place k F}
    (hQ : Q ≠ P) : 0 ≤ Q.ord t := by
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have h2 : poleDivisor k t Q = 0 := by
    rw [hpd, Finsupp.single_eq_of_ne hQ]
  rw [poleDivisor_apply ht0] at h2
  rcases le_total (-(Q.ord t)) 0 with h | h
  · omega
  · rw [max_eq_left h] at h2
    omega

/-- The pole divisor is unchanged by constant shifts. -/
theorem poleDivisor_sub_algebraMap {P : Place k F}
    (htr : Transcendental k t)
    (hpd : poleDivisor k t = Finsupp.single P 1) (a : k) :
    poleDivisor k (t - algebraMap k F a) = Finsupp.single P 1 := by
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have hta0 : t - algebraMap k F a ≠ 0 := fun h ↦
    (transcendental_sub_algebraMap htr a) (h ▸ isAlgebraic_zero)
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [map_zero, sub_zero, hpd]
  have hc0 : algebraMap k F a ≠ 0 := (map_ne_zero _).2 ha0
  ext Q
  rw [poleDivisor_apply hta0]
  rcases eq_or_ne Q P with rfl | hQ
  · have h1 := ord_eq_neg_one_of_poleDivisor htr hpd
    have h3 : Q.ord (t + -(algebraMap k F a)) = Q.ord t := by
      refine Q.ord_add_eq_left ht0 (neg_ne_zero.2 hc0) ?_
      rw [Q.ord_neg hc0, Q.ord_algebraMap ha0, h1]
      omega
    rw [sub_eq_add_neg, h3, h1, Finsupp.single_eq_same,
      show -(-1 : ℤ) = 1 by norm_num, max_eq_left (by norm_num)]
  · have h1 := ord_nonneg_of_poleDivisor htr hpd hQ
    have h4 : 0 ≤ Q.ord (t - algebraMap k F a) := by
      have h5 := Q.min_ord_le_ord_add (f := t)
        (g := -(algebraMap k F a)) ht0 (neg_ne_zero.2 hc0)
        (by rw [← sub_eq_add_neg]; exact hta0)
      rw [Q.ord_neg hc0, Q.ord_algebraMap ha0, ← sub_eq_add_neg] at h5
      rcases min_cases (Q.ord t) (0 : ℤ) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
        rw [hm] at h5 <;> omega
    rw [Finsupp.single_eq_of_ne hQ, max_eq_right (by omega)]

/-- The divisor of a shifted generator: one simple zero minus the
pole. -/
theorem exists_divisorOf_sub_algebraMap (htr : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) {P : Place k F}
    (hpd : poleDivisor k t = Finsupp.single P 1) (a : k) :
    ∃ Pa : Place k F, divisorOf k (t - algebraMap k F a) =
      Finsupp.single Pa 1 - Finsupp.single P 1 := by
  have hta0 : t - algebraMap k F a ≠ 0 := fun h ↦
    (transcendental_sub_algebraMap htr a) (h ▸ isAlgebraic_zero)
  have htr' := transcendental_sub_algebraMap htr a
  have htop' := adjoin_sub_algebraMap_eq_top htop a
  have hinv_tr : Transcendental k (t - algebraMap k F a)⁻¹ := fun h ↦
    htr' (IsAlgebraic.inv_iff.1 h)
  have hz : ∃ Pa : Place k F,
      poleDivisor k (t - algebraMap k F a)⁻¹ = Finsupp.single Pa 1 := by
    apply Divisor.eq_single_of_deg_eq_one (poleDivisor_nonneg _)
    rw [deg_poleDivisor_eq_finrank hinv_tr, adjoin_inv_eq, htop',
      IntermediateField.finrank_top]
    exact Nat.cast_one
  obtain ⟨Pa, hPa⟩ := hz
  refine ⟨Pa, ?_⟩
  rw [divisorOf_eq_poleDivisor_inv_sub hta0, hPa,
    poleDivisor_sub_algebraMap htr hpd a]

/-- Every place away from the pole is a zero of some shift. -/
theorem exists_ord_sub_algebraMap_pos (htr : Transcendental k t)
    {P : Place k F} (hpd : poleDivisor k t = Finsupp.single P 1)
    {Q : Place k F} (hQ : Q ≠ P) :
    ∃ a : k, 0 < Q.ord (t - algebraMap k F a) := by
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have h1 := ord_nonneg_of_poleDivisor htr hpd hQ
  have h3 : Q.val.valuation t ≤ 1 := (Q.ord_nonneg_iff ht0).1 h1
  obtain ⟨a, ha⟩ := Q.exists_residue h3
  refine ⟨a, ?_⟩
  have hta0 : t - algebraMap k F a ≠ 0 := fun h ↦
    (transcendental_sub_algebraMap htr a) (h ▸ isAlgebraic_zero)
  exact (Q.ord_pos_iff hta0).2 ha

/-- **Partial fractions in divisor form**: on a rational function
field, every degree-zero divisor is principal — a product of shifts of
the generator. -/
theorem exists_divisorOf_eq_of_deg_eq_zero (htr : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) {P : Place k F}
    (hpd : poleDivisor k t = Finsupp.single P 1)
    {D : Divisor k F} (hdeg : D.deg = 0) :
    ∃ f : F, f ≠ 0 ∧ divisorOf k f = D := by
  classical
  have hzero : ∀ Q : Place k F, Q ≠ P → ∃ a : k,
      divisorOf k (t - algebraMap k F a) =
        Finsupp.single Q 1 - Finsupp.single P 1 := by
    intro Q hQ
    obtain ⟨a, ha⟩ := exists_ord_sub_algebraMap_pos htr hpd hQ
    obtain ⟨Pa, hPa⟩ := exists_divisorOf_sub_algebraMap htr htop hpd a
    have hta0 : t - algebraMap k F a ≠ 0 := fun h ↦
      (transcendental_sub_algebraMap htr a) (h ▸ isAlgebraic_zero)
    have h1 : 0 < divisorOf k (t - algebraMap k F a) Q := by
      rw [divisorOf_apply hta0]
      exact ha
    rw [hPa, Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ,
      sub_zero] at h1
    have h2 : Pa = Q := by
      by_contra hne
      rw [Finsupp.single_eq_of_ne (Ne.symm hne)] at h1
      omega
    rw [h2] at hPa
    exact ⟨a, hPa⟩
  choose b hb using hzero
  set S := D.support.erase P with hS
  set f : F := ∏ Q ∈ S.attach,
    (t - algebraMap k F (b ↑Q (Finset.mem_erase.1 Q.2).1)) ^ (D ↑Q)
    with hf
  have hfac0 : ∀ Q : {x // x ∈ S},
      t - algebraMap k F (b ↑Q (Finset.mem_erase.1 Q.2).1) ≠ 0 :=
    fun Q h ↦
      (transcendental_sub_algebraMap htr _) (h ▸ isAlgebraic_zero)
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact Finset.prod_ne_zero_iff.2 fun Q _ ↦ zpow_ne_zero _ (hfac0 Q)
  refine ⟨f, hf0, ?_⟩
  rw [hf, divisorOf_prod_zpow _ _ _ fun Q _ ↦ hfac0 Q]
  have hsum : ∑ Q ∈ S.attach, (D ↑Q) •
      divisorOf k
        (t - algebraMap k F (b ↑Q (Finset.mem_erase.1 Q.2).1)) =
      ∑ Q ∈ S.attach, (D ↑Q) •
        (Finsupp.single (↑Q : Place k F) 1 - Finsupp.single P 1) := by
    refine Finset.sum_congr rfl fun Q _ ↦ ?_
    rw [hb ↑Q (Finset.mem_erase.1 Q.2).1]
  rw [hsum, Finset.sum_attach S fun Q ↦ (D Q) •
    ((Finsupp.single Q 1 - Finsupp.single P 1) : Divisor k F)]
  have hdegS : ∑ Q ∈ S, D Q = -(D P) := by
    have h2 : D.deg = ∑ Q ∈ D.support, D Q := rfl
    by_cases hP : P ∈ D.support
    · have h1 := Finset.sum_erase_add D.support (fun Q ↦ D Q) hP
      rw [← hS] at h1
      omega
    · have h1 : S = D.support := by
        rw [hS]
        exact Finset.erase_eq_of_notMem hP
      have h3 : D P = 0 := Finsupp.notMem_support_iff.1 hP
      rw [h1]
      omega
  ext R
  rw [Finsupp.finsetSum_apply]
  rcases eq_or_ne R P with rfl | hR
  · have h1 : ∀ Q ∈ S, ((D Q) •
        ((Finsupp.single Q 1 - Finsupp.single R 1) : Divisor k F)) R =
        -(D Q) := by
      intro Q hQ
      have hQP : Q ≠ R := (Finset.mem_erase.1 hQ).1
      rw [Finsupp.smul_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm hQP), Finsupp.single_eq_same,
        smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl h1]
    rw [Finset.sum_neg_distrib, hdegS, neg_neg]
  · rw [Finset.sum_eq_single R]
    · rw [Finsupp.smul_apply, Finsupp.sub_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hR,
        smul_eq_mul]
      ring
    · intro Q hQ hne
      rw [Finsupp.smul_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm hne),
        Finsupp.single_eq_of_ne hR, smul_eq_mul]
      ring
    · intro hRS
      have h3 : D R = 0 := by
        by_contra h4
        exact hRS (Finset.mem_erase.2 ⟨hR, Finsupp.mem_support_iff.2 h4⟩)
      rw [h3, zero_smul, Finsupp.coe_zero, Pi.zero_apply]

/-- The defect of any multiple of the pole place is nonpositive: the
powers of the generator fill the Riemann–Roch space. -/
theorem defect_smul_single_nonpos (htr : Transcendental k t)
    {P : Place k F} (hpd : poleDivisor k t = Finsupp.single P 1)
    (n : ℤ) :
    ((n • Finsupp.single P 1 : Divisor k F)).defect ≤ 0 := by
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have hdeg : Divisor.deg (n • Finsupp.single P 1 : Divisor k F) = n := by
    rw [Divisor.deg_smul,
      show Divisor.deg (Finsupp.single P 1 : Divisor k F) = 1 from by
        rw [Divisor.deg, Finsupp.sum_single_index rfl],
      mul_one]
  rcases lt_or_ge n 0 with hn | hn
  · rw [Divisor.defect, hdeg,
      riemannSpace_eq_bot_of_deg_neg (by rw [hdeg]; omega), finrank_bot]
    omega
  · lift n to ℕ using hn with N
    have hmem : ∀ j : Fin (N + 1), t ^ (j : ℕ) ∈
        RiemannSpace ((N : ℤ) • Finsupp.single P 1) := by
      intro j
      have h1 := pow_mem_riemannSpace_smul_poleDivisor (k := k)
        (f := t) ht0 j.is_le
      rwa [hpd] at h1
    have hw : LinearIndependent k fun j : Fin (N + 1) ↦
        (⟨t ^ (j : ℕ), hmem j⟩ :
          ↥(RiemannSpace ((N : ℤ) • Finsupp.single P 1))) := by
      apply LinearIndependent.of_comp
        (RiemannSpace ((N : ℤ) • Finsupp.single P 1)).subtype
      exact linearIndependent_pow_of_transcendental htr (N + 1)
    have hcard := hw.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    rw [Divisor.defect, hdeg]
    omega

/-- **Rational function fields have genus zero** — the converse of the
genus-zero checkpoint. -/
theorem genus_eq_zero_of_adjoin_eq_top (htr : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) : genus k F = 0 := by
  obtain ⟨P, hpd⟩ := exists_poleDivisor_eq_single htr htop
  refine le_antisymm ?_ genus_nonneg
  rw [genus]
  refine csSup_le ⟨_, ⟨0, rfl⟩⟩ ?_
  rintro r ⟨D, rfl⟩
  change Divisor.defect D ≤ 0
  have hdegE : (D - D.deg • Finsupp.single P 1).deg = 0 := by
    rw [Divisor.deg_sub, Divisor.deg_smul,
      show Divisor.deg (Finsupp.single P 1 : Divisor k F) = 1 from by
        rw [Divisor.deg, Finsupp.sum_single_index rfl]]
    ring
  obtain ⟨f, hf0, hfD⟩ :=
    exists_divisorOf_eq_of_deg_eq_zero htr htop hpd hdegE
  have hD : D = D.deg • Finsupp.single P 1 + divisorOf k f := by
    rw [hfD]
    abel
  rw [hD, Divisor.defect_add_divisorOf _ hf0]
  exact defect_smul_single_nonpos htr hpd D.deg

/-- **The genus-zero classification**: a one-variable function field
over an algebraically closed base has genus zero exactly when it is
rational. -/
theorem genus_eq_zero_iff_exists_generator :
    genus k F = 0 ↔ ∃ t : F, Transcendental k t ∧
      adjoin k ({t} : Set F) = ⊤ := by
  constructor
  · intro hg
    obtain ⟨P⟩ := (inferInstance : Nonempty (Place k F))
    obtain ⟨t, htr, -, htop⟩ := exists_generator_of_genus_eq_zero hg P
    exact ⟨t, htr, htop⟩
  · rintro ⟨t, htr, htop⟩
    exact genus_eq_zero_of_adjoin_eq_top htr htop

end

end AclGeom
