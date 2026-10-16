/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConfigurationBaseChange
import GroupConfig.ClosureCounterexample
import GroupConfig.Constructible.Generic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Constructible rank-two subgroups of SL₂

An actual subgroup of `SL₂(K)` constructible over an algebraically closed universal-domain
base, whose entry-ranks are at most two and attain two, is conjugate to the full upper Borel
(`GroupConfig.exists_borel_conj_of_constructible_rank_two`). This holds in every characteristic.
Its consumer is the actual HW affine generator in `GroupConfig.Germ.AffineGenerator` (#21).

The proof first finds an element with trace outside the base. Its eigenvalues give infinitely
many points of a torus; constructibility gives the full torus. Conjugating coefficients enter
an internally chosen small algebraically closed field before ranks are compared. A fresh
actual element retains rank two over that field. Two tori with disjoint fixed pairs force rank
three, while two distinct tori sharing a point generate the upper Borel. Matrix case analysis
then gives the classification, without a fixed-point or generation certificate.

This supplies an auxiliary function-field classification for `lem:affine-action` in
`sources/blueprint.tex`. The original scheme/action, normal-subgroup, algebraization and
original-field descent statements remain obligations.

**Status:** the complete constructible subgroup classification is proved, with an actual HW
consumer. The entry set `slEntries` and the entry lemmas `sl_mul_apply`, `sl_mul_entries_mem`,
`sl_inv_entries_mem`, `sq_ne_one_of_transcendental` and
`mem_range_of_isAlgebraic_of_isAlgClosed` are shared with the upper-triangular curve analysis
in `GroupConfig.Constructible.SLUpperCurve` and `GroupConfig.Constructible.SLAffineMultiplier`;
the other supporting lemmas here are private.
-/

namespace GroupConfig

open AclGeom Set Matrix
open scoped MatrixGroups

private theorem subgroup_eq_top_of_finite_compl {G : Type*} [Group G] [Infinite G]
    (S : Subgroup G) (hS : (S : Set G)ᶜ.Finite) : S = ⊤ := by
  apply top_unique
  intro x _
  have hpre : ((fun y : G ↦ x * y) ⁻¹' (S : Set G)ᶜ).Finite :=
    hS.preimage (mul_right_injective x).injOn
  obtain ⟨y, hy⟩ := (hS.union hpre).exists_notMem
  have hyS : y ∈ S := by
    have hy' : y ∉ (S : Set G)ᶜ := fun h ↦ hy (Or.inl h)
    simpa only [mem_compl_iff, not_not, SetLike.mem_coe] using hy'
  have hxyS : x * y ∈ S := by
    have hy' : y ∉ (fun y : G ↦ x * y) ⁻¹' (S : Set G)ᶜ := fun h ↦ hy (Or.inr h)
    simpa only [mem_preimage, mem_compl_iff, not_not, SetLike.mem_coe] using hy'
  exact (S.mul_mem_cancel_right hyS).1 hxyS

private theorem constructible_units_subgroup_eq_top {k K : Type*}
    [Field k] [Field K] [Algebra k K] [Infinite Kˣ]
    (S : Subgroup Kˣ) (hInf : (S : Set Kˣ).Infinite)
    (hS : IsConstructibleOver k {x : Fin 1 → K | ∃ a : Kˣ, a ∈ S ∧ (a : K) = x 0}) :
    S = ⊤ := by
  let f : Kˣ → Fin 1 → K := fun a _ ↦ a
  have hf : Function.Injective f := fun a b h ↦ Units.ext (congrFun h 0)
  have hpre : f ⁻¹' {x : Fin 1 → K | ∃ a : Kˣ, a ∈ S ∧ (a : K) = x 0} =
      (S : Set Kˣ) := by
    ext a
    change (∃ b : Kˣ, b ∈ S ∧ (b : K) = a) ↔ a ∈ S
    constructor
    · rintro ⟨b, hb, hab⟩
      exact (Units.ext hab : b = a) ▸ hb
    · exact fun ha ↦ ⟨a, ha, rfl⟩
  rcases hS.finite_or_finite_compl with hfin | hfin
  · exact (hInf (hpre ▸ hfin.preimage hf.injOn)).elim
  · apply subgroup_eq_top_of_finite_compl S
    rw [← hpre, ← preimage_compl]
    exact hfin.preimage hf.injOn

private theorem algebraicIndependent_of_erk_range_eq {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ} (u : Fin n → K)
    (h : erk k ∅ (range u) = n) : AlgebraicIndependent k u := by
  apply AclGeom.algebraicIndependent_of_rankEq_iSup_point
  rw [AclGeom.rankEq_iff_eRk]
  change (AlgebraicIndependent.matroid k K).eRk
    (((⨆ i, AclGeom.ClosedIF.point k (u i)).1 : IntermediateField k K) : Set K) = n
  rw [AclGeom.coe_iSup_point, ← erk_empty_eq]
  have hr := erk_racl k (∅ : Set K) (range u)
  simp only [empty_union] at hr
  exact hr.trans h

/-- The set of the four entries of a matrix in `SL₂(K)`. -/
abbrev slEntries {K : Type*} [Field K] (m : SpecialLinearGroup (Fin 2) K) : Set K :=
  range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2

private theorem slEntries_subset_racl_pair_of_trace {k K : Type*}
    [Field k] [Field K] [Algebra k K] (m : SpecialLinearGroup (Fin 2) K) (α : k)
    (hα : m 0 0 + m 1 1 = algebraMap k K α) (hb : m 0 1 ≠ 0) :
    slEntries m ⊆ racl k ({m 0 0, m 0 1} : Set K) := by
  let F := racl k ({m 0 0, m 0 1} : Set K)
  have ha : m 0 0 ∈ F := subset_racl k _ (by simp)
  have hbF : m 0 1 ∈ F := subset_racl k _ (by simp)
  have hmd : m 1 1 = algebraMap k K α - m 0 0 := by linear_combination hα
  have hd : m 1 1 ∈ F := by
    rw [hmd]
    exact F.sub_mem (F.algebraMap_mem α) ha
  have hm : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using m.prop
  have hmc : m 1 0 = (m 0 0 * m 1 1 - 1) / m 0 1 := by
    apply (eq_div_iff hb).2
    linear_combination -hm
  have hc : m 1 0 ∈ F := by
    rw [hmc]
    exact F.div_mem (F.sub_mem (F.mul_mem ha hd) F.one_mem) hbF
  rintro x ⟨⟨i, j⟩, rfl⟩
  fin_cases i <;> fin_cases j
  exacts [ha, hbF, hc, hd]

private theorem slEntries_rank_le_one_of_trace_of_upper_zero {k K : Type*}
    [Field k] [Field K] [Algebra k K] (m : SpecialLinearGroup (Fin 2) K) (α : k)
    (hα : m 0 0 + m 1 1 = algebraMap k K α) (hb : m 0 1 = 0) :
    erk k ∅ (slEntries m) ≤ 1 := by
  have hm : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using m.prop
  have halg : IsAlgebraic k (m 0 0) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C α * Polynomial.X + 1, ?_, ?_⟩
    · intro hp
      have hc := congrArg (fun p : Polynomial k ↦ p.coeff 2) hp
      simp [Polynomial.coeff_one] at hc
    · simp only [map_add, map_sub, map_pow, map_mul, map_one,
        Polynomial.aeval_X, Polynomial.aeval_C]
      rw [hb, zero_mul, sub_zero] at hm
      linear_combination (m 0 0) * hα - hm
  let F := racl k ({m 1 0} : Set K)
  have ha : m 0 0 ∈ F := racl_mono (empty_subset _) (mem_racl_empty_of_isAlgebraic halg)
  have hmd : m 1 1 = algebraMap k K α - m 0 0 := by linear_combination hα
  have hd : m 1 1 ∈ F := by
    rw [hmd]
    exact F.sub_mem (F.algebraMap_mem α) ha
  have hc : m 1 0 ∈ F := subset_racl k _ (by simp)
  have hsub : slEntries m ⊆ F := by
    rintro x ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact ha
    · change m 0 1 ∈ F
      rw [hb]
      exact F.zero_mem
    · exact hc
    · exact hd
  have hr := (erk_mono k ∅ hsub).trans_eq (by
    simpa only [empty_union] using erk_racl k (∅ : Set K) ({m 1 0} : Set K))
  exact hr.trans ((erk_le_encard k ∅ _).trans (by simp))

private theorem trace_product_not_in_base {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m n : SpecialLinearGroup (Fin 2) K) (α β ζ : k)
    (hα : m 0 0 + m 1 1 = algebraMap k K α)
    (hβ : n 0 0 + n 1 1 = algebraMap k K β)
    (hind : AlgebraicIndependent k ![m 0 0, m 0 1, n 0 0, n 0 1]) :
    (m * n) 0 0 + (m * n) 1 1 ≠ algebraMap k K ζ := by
  intro hζ
  let P : MvPolynomial (Fin 4) k :=
    (MvPolynomial.C ζ - MvPolynomial.X 0 * MvPolynomial.X 2 -
      (MvPolynomial.C α - MvPolynomial.X 0) *
        (MvPolynomial.C β - MvPolynomial.X 2)) * MvPolynomial.X 1 * MvPolynomial.X 3 -
      MvPolynomial.X 1 ^ 2 *
        (MvPolynomial.X 2 * (MvPolynomial.C β - MvPolynomial.X 2) - 1) -
      MvPolynomial.X 3 ^ 2 *
        (MvPolynomial.X 0 * (MvPolynomial.C α - MvPolynomial.X 0) - 1)
  have hP : P ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval ![0, 1, 0, 0]) h
    simp [P] at h'
  apply hP
  apply hind.eq_zero_of_aeval_eq_zero
  have hm : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using m.prop
  have hn : n 0 0 * n 1 1 - n 0 1 * n 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using n.prop
  have hmd : m 1 1 = algebraMap k K α - m 0 0 := by linear_combination hα
  have hnd : n 1 1 = algebraMap k K β - n 0 0 := by linear_combination hβ
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hζ
  simp only [P, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  rw [hmd] at hm hζ
  rw [hnd] at hn hζ
  linear_combination -(m 0 1 * n 0 1) * hζ - (m 0 1) ^ 2 * hn - (n 0 1) ^ 2 * hm

private theorem trace_product_not_in_base_of_independent_rank_two {k K : Type*}
    [Field k] [Field K] [Algebra k K] (m n : SpecialLinearGroup (Fin 2) K) (α β : k)
    (hα : m 0 0 + m 1 1 = algebraMap k K α)
    (hβ : n 0 0 + n 1 1 = algebraMap k K β)
    (hmr : erk k ∅ (slEntries m) = 2) (hnr : erk k ∅ (slEntries n) = 2)
    (hind : IndepOver k ∅ (slEntries m) (slEntries n)) (ζ : k) :
    (m * n) 0 0 + (m * n) 1 1 ≠ algebraMap k K ζ := by
  have hmb : m 0 1 ≠ 0 := by
    intro hb
    have h := slEntries_rank_le_one_of_trace_of_upper_zero m α hα hb
    rw [hmr] at h
    norm_num at h
  have hnb : n 0 1 ≠ 0 := by
    intro hb
    have h := slEntries_rank_le_one_of_trace_of_upper_zero n β hβ hb
    rw [hnr] at h
    norm_num at h
  let u : Fin 4 → K := ![m 0 0, m 0 1, n 0 0, n 0 1]
  have hunion : erk k ∅ (slEntries m ∪ slEntries n) = 4 := by
    rw [erk_union_eq, hind.symm.erk_eq (subset_refl _) (finite_range _), hmr, hnr]
    norm_num
  have hsub : slEntries m ∪ slEntries n ⊆ racl k (range u) := by
    apply union_subset
    · apply (slEntries_subset_racl_pair_of_trace m α hα hmb).trans
      apply racl_mono
      rintro x (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    · apply (slEntries_subset_racl_pair_of_trace n β hβ hnb).trans
      apply racl_mono
      rintro x (rfl | rfl)
      exacts [⟨2, rfl⟩, ⟨3, rfl⟩]
  have hle : 4 ≤ erk k ∅ (range u) := by
    rw [← hunion]
    exact (erk_mono k ∅ hsub).trans_eq (by
      simpa only [empty_union] using erk_racl k (∅ : Set K) (range u))
  have hu : erk k ∅ (range u) = 4 := by
    apply le_antisymm _ hle
    apply (erk_le_encard k ∅ _).trans
    simpa using encard_image_le u (univ : Set (Fin 4))
  exact trace_product_not_in_base m n α β ζ hα hβ
    (algebraicIndependent_of_erk_range_eq u hu)

private abbrev slCarrier {K : Type*} [Field K] (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) :
    Set ((Fin 2 × Fin 2) → K) := {u | ∃ m ∈ Γ, ∀ i j, m i j = u (i, j)}

private theorem exists_nonbase_trace_of_constructible_rank_two {k K : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hΓ : IsConstructibleOver k (slCarrier Γ))
    (hr : ∃ m ∈ Γ, erk k ∅ (slEntries m) = 2) :
    ∃ m ∈ Γ, m 0 0 + m 1 1 ∉ range (algebraMap k K) := by
  by_contra! h
  obtain ⟨m, hm, hmr⟩ := hr
  let a : Fin 2 × Fin 2 → K := fun ij ↦ m ij.1 ij.2
  let N := racl k (range a)
  have hN : IsSmall k (N : Set K) := (IsSmall.of_finite (finite_range a)).racl
  obtain ⟨u, hu⟩ := exists_isGenericOver hN a
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := k) hu.idealOf_eq.symm
  let n := SpecialLinearGroup.map σ.toRingHom m
  have hncoeff (i j : Fin 2) : n i j = u (i, j) := hσ (i, j)
  have hna : slEntries n = range u := by
    change range (fun ij : Fin 2 × Fin 2 ↦ n ij.1 ij.2) = _
    congr 1
    funext ij
    exact hncoeff ij.1 ij.2
  have hnr : erk k ∅ (slEntries n) = 2 := by
    rw [hna, hu.erk_empty_eq]
    exact hmr
  have hn : n ∈ Γ := by
    have hm' : a ∈ slCarrier Γ := ⟨m, hm, fun _ _ ↦ rfl⟩
    have hn' := (hΓ.mem_comp_algEquiv_iff σ a).2 hm'
    obtain ⟨n', hn', heq⟩ := hn'
    have he : n' = n := by
      apply SpecialLinearGroup.ext
      intro i j
      exact heq i j
    exact he ▸ hn'
  have hind : IndepOver k ∅ (slEntries m) (slEntries n) := by
    rw [hna]
    exact (hu.indepOver.mono_right (subset_racl k (range a))).symm
  obtain ⟨α, hα⟩ := h m hm
  obtain ⟨β, hβ⟩ := h n hn
  obtain ⟨ζ, hζ⟩ := h (m * n) (Γ.mul_mem hm hn)
  exact trace_product_not_in_base_of_independent_rank_two m n α β hα.symm hβ.symm
    hmr hnr hind ζ hζ.symm

private def slDiag {K : Type*} [Field K] : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun r := ⟨!![(r : K), 0; 0, (r : K)⁻¹], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' r s := by
    apply Subtype.ext
    change (!![((r * s : Kˣ) : K), 0; 0, (((r * s : Kˣ) : K))⁻¹] :
      Matrix (Fin 2) (Fin 2) K) = !![(r : K), 0; 0, (r : K)⁻¹] *
        !![(s : K), 0; 0, (s : K)⁻¹]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, _root_.mul_inv_rev, mul_comm]

private theorem slDiag_mul_left {K : Type*} [Field K] (r : Kˣ)
    (A : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    (slDiag r * A) i j = (if i = 0 then (r : K) else (r : K)⁻¹) * A i j := by
  change (∑ x : Fin 2, !![(r : K), 0; 0, (r : K)⁻¹] i x * A x j) = _
  fin_cases i <;> simp [Fin.sum_univ_two]

private theorem slDiag_mul_right {K : Type*} [Field K] (r : Kˣ)
    (A : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    (A * slDiag r) i j = A i j * (if j = 0 then (r : K) else (r : K)⁻¹) := by
  change (∑ x : Fin 2, A i x * !![(r : K), 0; 0, (r : K)⁻¹] x j) = _
  fin_cases j <;> simp [Fin.sum_univ_two]

private theorem sl_torus_conjugate_entries {K : Type*} [Field K]
    (R : SpecialLinearGroup (Fin 2) K) (s : Kˣ) :
    let B := R * slDiag s * R⁻¹
    B 0 0 = R 0 0 * R 1 1 * (s : K) - R 0 1 * R 1 0 / (s : K) ∧
      B 0 1 = R 0 0 * R 0 1 * ((s : K)⁻¹ - (s : K)) ∧
      B 1 0 = R 1 0 * R 1 1 * ((s : K) - (s : K)⁻¹) := by
  rcases R with ⟨A, hA⟩
  change ((A * !![(s : K), 0; 0, (s : K)⁻¹]) * Matrix.adjugate A) 0 0 =
      A 0 0 * A 1 1 * (s : K) - A 0 1 * A 1 0 / (s : K) ∧
    ((A * !![(s : K), 0; 0, (s : K)⁻¹]) * Matrix.adjugate A) 0 1 =
      A 0 0 * A 0 1 * ((s : K)⁻¹ - (s : K)) ∧
    ((A * !![(s : K), 0; 0, (s : K)⁻¹]) * Matrix.adjugate A) 1 0 =
      A 1 0 * A 1 1 * ((s : K) - (s : K)⁻¹)
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem sl_torus_triple_entries {K : Type*} [Field K]
    (R : SpecialLinearGroup (Fin 2) K) (r s t : Kˣ) :
    let B := R * slDiag s * R⁻¹
    let m := slDiag r * R * slDiag s * R⁻¹ * slDiag t
    m 0 0 = (r : K) * B 0 0 * (t : K) ∧
      m 0 1 = (r : K) * B 0 1 * (t : K)⁻¹ ∧
      m 1 0 = (r : K)⁻¹ * B 1 0 * (t : K) := by
  dsimp only
  rw [show slDiag r * R * slDiag s * R⁻¹ * slDiag t =
    slDiag r * (R * slDiag s * R⁻¹) * slDiag t by simp only [mul_assoc]]
  simp [slDiag_mul_right, slDiag_mul_left]

private theorem sl_torus_triple_quartic {K : Type*} [Field K]
    (R : SpecialLinearGroup (Fin 2) K) (r s t : Kˣ) :
    let m := slDiag r * R * slDiag s * R⁻¹ * slDiag t
    R 0 0 * R 0 1 * R 1 0 * R 1 1 * ((s : K) ^ 2 - 1) ^ 2 +
      (s : K) ^ 2 * m 0 1 * m 1 0 = 0 := by
  dsimp only
  obtain ⟨_, hm01, hm10⟩ := sl_torus_triple_entries R r s t
  obtain ⟨_, hB01, hB10⟩ := sl_torus_conjugate_entries R s
  rw [hm01, hm10, hB01, hB10]
  field_simp
  ring

private theorem sl_torus_triple_recovery {K : Type*} [Field K]
    (R : SpecialLinearGroup (Fin 2) K) (r s t : Kˣ) :
    let B := R * slDiag s * R⁻¹
    let m := slDiag r * R * slDiag s * R⁻¹ * slDiag t
    (r : K) ^ 2 * B 0 0 * B 0 1 = m 0 0 * m 0 1 ∧
      (t : K) ^ 2 * B 0 0 * B 1 0 = m 0 0 * m 1 0 := by
  dsimp only
  obtain ⟨hm00, hm01, hm10⟩ := sl_torus_triple_entries R r s t
  rw [hm00, hm01, hm10]
  constructor <;> field_simp


noncomputable section

/-- A coordinate of a tuple of full rank over `C` is transcendental over `C`. -/
private theorem notMem_racl_of_erk_range_eq_three {k K : Type*} [Field k] [Field K] [Algebra k K]
    {C : Set K} {u : Fin 3 → K} (h : erk k C (range u) = 3) (i : Fin 3) :
    u i ∉ racl k C := by
  intro hi
  have hsub : range u ⊆ racl k (C ∪ (range u \ {u i})) := by
    rintro _ ⟨j, rfl⟩
    by_cases hj : u j = u i
    · rw [hj]
      exact racl_mono (k := k) subset_union_left hi
    · exact subset_racl k _ (Or.inr ⟨⟨j, rfl⟩, hj⟩)
  have hle : erk k C (range u) ≤ erk k C (range u \ {u i}) :=
    (erk_mono k C hsub).trans_eq (erk_racl k C _)
  have henc : (range u \ {u i}).encard + 1 = (range u).encard :=
    encard_sdiff_singleton_add_one ⟨i, rfl⟩
  have hr3 : (range u).encard ≤ 3 := by
    simpa using encard_image_le u (univ : Set (Fin 3))
  have hfin : (range u \ {u i}).Finite := (finite_range u).subset sdiff_subset
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (range u \ {u i}).encard = n :=
    ⟨_, hfin.encard_eq_coe_toFinset_card⟩
  rw [hn] at henc
  have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ (3 : ℕ) := by
    push_cast
    rw [henc]
    exact hr3
  have h3' : n + 1 ≤ 3 := by exact_mod_cast h3
  have h2 : (range u \ {u i}).encard ≤ 2 := by
    rw [hn]
    exact_mod_cast (by omega : n ≤ 2)
  have := (h.symm.le.trans hle).trans ((erk_le_encard k C _).trans h2)
  norm_num at this

/-- **Two tori with disjoint fixed pairs force rank three.** If a subgroup of `SL₂(K)` contains
the full diagonal torus and its conjugate by a matrix `R` with all entries nonzero, then it
contains a matrix whose entries have rank at least three. -/
private theorem exists_rank_three_of_two_tori {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) (R : SpecialLinearGroup (Fin 2) K)
    (hR : ∀ i j, R i j ≠ 0) (hT : ∀ r : Kˣ, slDiag r ∈ Γ)
    (hRT : ∀ s : Kˣ, R * slDiag s * R⁻¹ ∈ Γ) :
    ∃ m ∈ Γ, 3 ≤ erk k ∅ (slEntries m) := by
  -- Three independent units over the entries of `R`.
  have hC : IsSmall k (slEntries R) := IsSmall.of_finite (finite_range _)
  obtain ⟨u, hu⟩ := exists_erk_range_eq hC 3
  have htr := notMem_racl_of_erk_range_eq_three hu
  have hne : ∀ i, u i ≠ 0 := fun i h ↦ htr i (h ▸ (racl k (slEntries R)).zero_mem)
  obtain ⟨r, hr⟩ : ∃ r : Kˣ, (r : K) = u 0 := ⟨Units.mk0 _ (hne 0), rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Kˣ, (s : K) = u 1 := ⟨Units.mk0 _ (hne 1), rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, (t : K) = u 2 := ⟨Units.mk0 _ (hne 2), rfl⟩
  have hsC : (s : K) ∉ racl k (slEntries R) := hs ▸ htr 1
  -- The word in the two tori.
  obtain ⟨m, hmdef⟩ : ∃ m, m = slDiag r * R * slDiag s * R⁻¹ * slDiag t := ⟨_, rfl⟩
  have hm : m ∈ Γ := by
    rw [hmdef, show slDiag r * R * slDiag s * R⁻¹ * slDiag t =
      slDiag r * (R * slDiag s * R⁻¹) * slDiag t by simp only [mul_assoc]]
    exact Γ.mul_mem (Γ.mul_mem (hT r) (hRT s)) (hT t)
  refine ⟨m, hm, ?_⟩
  -- The closure of the entries of `R` and `m`.
  obtain ⟨E, hEdef⟩ : ∃ E : IntermediateField k K, E = racl k (slEntries R ∪ slEntries m) :=
    ⟨_, rfl⟩
  have hERAC : IsRAC E := hEdef ▸ isRAC_racl _
  have hRE : ∀ i j, R i j ∈ E := fun i j ↦ hEdef ▸ subset_racl k _ (Or.inl ⟨(i, j), rfl⟩)
  have hmE : ∀ i j, m i j ∈ E := fun i j ↦ hEdef ▸ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)
  have hCE : racl k (slEntries R) ≤ E := hEdef ▸ racl_mono (k := k) subset_union_left
  -- `s` is algebraic over `E` by the quartic.
  have hq := sl_torus_triple_quartic R r s t
  dsimp only at hq
  rw [← hmdef] at hq
  have hsE : (s : K) ∈ E := by
    apply hERAC.mem_of_isAlgebraic
    let a : E := ⟨R 0 0 * R 0 1 * R 1 0 * R 1 1, E.mul_mem (E.mul_mem (E.mul_mem (hRE 0 0)
      (hRE 0 1)) (hRE 1 0)) (hRE 1 1)⟩
    let b : E := ⟨m 0 1 * m 1 0, E.mul_mem (hmE 0 1) (hmE 1 0)⟩
    refine ⟨Polynomial.C a * (Polynomial.X ^ 2 - 1) ^ 2 + Polynomial.C b * Polynomial.X ^ 2,
      fun h0 ↦ ?_, ?_⟩
    · have hc := congrArg (Polynomial.eval 0) h0
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero] at hc
      have ha0 : a = 0 := by simpa using hc
      have : R 0 0 * R 0 1 * R 1 0 * R 1 1 = 0 := congrArg Subtype.val ha0
      simp only [mul_eq_zero] at this
      rcases this with ((h | h) | h) | h
      exacts [hR 0 0 h, hR 0 1 h, hR 1 0 h, hR 1 1 h]
    · simp only [map_add, map_mul, map_pow, map_sub, map_one, Polynomial.aeval_C,
        Polynomial.aeval_X, IntermediateField.algebraMap_apply]
      linear_combination hq
  -- The middle conjugate has entries in `E`, nonzero since `s` is transcendental.
  obtain ⟨B, hBdef⟩ : ∃ B, B = R * slDiag s * R⁻¹ := ⟨_, rfl⟩
  have hBe := sl_torus_conjugate_entries R s
  dsimp only at hBe
  rw [← hBdef] at hBe
  obtain ⟨hB00, hB01, hB10⟩ := hBe
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hs2 : (s : K) ^ 2 ≠ 1 := fun h ↦ hsC (by
    refine racl_mono (k := k) (empty_subset _) (mem_racl_empty_of_isAlgebraic ?_)
    refine ⟨Polynomial.X ^ 2 - 1, fun h0 ↦ ?_, by simp [h]⟩
    have hc := congrArg (Polynomial.coeff · 2) h0
    simp [Polynomial.coeff_one] at hc)
  have hsinv : (s : K)⁻¹ - (s : K) ≠ 0 := by
    intro h
    apply hs2
    have h' : (s : K)⁻¹ = s := sub_eq_zero.1 h
    calc (s : K) ^ 2 = s * s := sq _
      _ = s * (s : K)⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ hs0
  have hB01ne : B 0 1 ≠ 0 := by
    rw [hB01]
    exact mul_ne_zero (mul_ne_zero (hR 0 0) (hR 0 1)) hsinv
  have hB10ne : B 1 0 ≠ 0 := by
    rw [hB10]
    refine mul_ne_zero (mul_ne_zero (hR 1 0) (hR 1 1)) fun h ↦ hsinv ?_
    linear_combination -h
  have hB00ne : B 0 0 ≠ 0 := by
    rw [hB00]
    intro h
    apply hsC
    have h' : R 0 0 * R 1 1 * (s : K) ^ 2 = R 0 1 * R 1 0 := by
      have h'' := congrArg (· * (s : K)) h
      simp only [sub_mul, zero_mul, div_mul_cancel₀ _ hs0] at h''
      linear_combination h''
    have hsq : (s : K) ^ 2 = R 0 1 * R 1 0 / (R 0 0 * R 1 1) := by
      rw [eq_div_iff (mul_ne_zero (hR 0 0) (hR 1 1))]
      linear_combination h'
    have hmem : R 0 1 * R 1 0 / (R 0 0 * R 1 1) ∈ racl k (slEntries R) := by
      have hRC : ∀ i j, R i j ∈ racl k (slEntries R) := fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩
      exact div_mem (mul_mem (hRC 0 1) (hRC 1 0)) (mul_mem (hRC 0 0) (hRC 1 1))
    exact (isRAC_racl _).mem_of_pow_mem two_ne_zero (hsq ▸ hmem)
  -- The three entries of the middle conjugate used by the recovery lie in `E`.
  have hs' : (s : K)⁻¹ ∈ E := E.inv_mem hsE
  have hB00E : B 0 0 ∈ E := by
    rw [hB00]
    exact E.sub_mem (E.mul_mem (E.mul_mem (hRE 0 0) (hRE 1 1)) hsE)
      (E.div_mem (E.mul_mem (hRE 0 1) (hRE 1 0)) hsE)
  have hB01E : B 0 1 ∈ E := by
    rw [hB01]
    exact E.mul_mem (E.mul_mem (hRE 0 0) (hRE 0 1)) (E.sub_mem hs' hsE)
  have hB10E : B 1 0 ∈ E := by
    rw [hB10]
    exact E.mul_mem (E.mul_mem (hRE 1 0) (hRE 1 1)) (E.sub_mem hsE hs')
  -- `r` and `t` are algebraic over `E` by the square recovery.
  have hrec := sl_torus_triple_recovery R r s t
  dsimp only at hrec
  rw [← hBdef, ← hmdef] at hrec
  obtain ⟨hr2, ht2⟩ := hrec
  have hrE : (r : K) ∈ E := by
    have hsq : (r : K) ^ 2 = m 0 0 * m 0 1 / (B 0 0 * B 0 1) := by
      rw [eq_div_iff (mul_ne_zero hB00ne hB01ne)]
      linear_combination hr2
    refine hERAC.mem_of_pow_mem two_ne_zero ?_
    rw [hsq]
    exact E.div_mem (E.mul_mem (hmE 0 0) (hmE 0 1)) (E.mul_mem hB00E hB01E)
  have htE : (t : K) ∈ E := by
    have hsq : (t : K) ^ 2 = m 0 0 * m 1 0 / (B 0 0 * B 1 0) := by
      rw [eq_div_iff (mul_ne_zero hB00ne hB10ne)]
      linear_combination ht2
    refine hERAC.mem_of_pow_mem two_ne_zero ?_
    rw [hsq]
    exact E.div_mem (E.mul_mem (hmE 0 0) (hmE 1 0)) (E.mul_mem hB00E hB10E)
  -- The rank of the entries of `m`.
  have hsubE : range u ⊆ racl k (slEntries R ∪ slEntries m) := by
    rw [← hEdef]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hr ▸ hrE
    · exact hs ▸ hsE
    · exact ht ▸ htE
  calc (3 : ℕ∞) = erk k (slEntries R) (range u) := hu.symm
    _ ≤ erk k (slEntries R) (slEntries m) :=
      (erk_mono k (slEntries R) hsubE).trans_eq (erk_racl k _ _)
    _ ≤ erk k ∅ (slEntries m) := erk_base_mono k (empty_subset _) _

private theorem fin_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- The upper transvection of `SL₂` as an explicit matrix. -/
private theorem upper_transvection_coe {K : Type*} [Field K] (x : K) :
    ((SpecialLinearGroup.transvection fin_zero_ne_one x : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe]

/-- The diagonal element as an explicit matrix. -/
private theorem slDiag_coe {K : Type*} [Field K] (r : Kˣ) :
    ((slDiag r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(r : K), 0; 0, (r : K)⁻¹] := rfl

/-- The commutator of the diagonal torus and its conjugate by `U(b)` is a translation. -/
private theorem slDiag_inv_mul_conj {K : Type*} [Field K] (b : K) (r : Kˣ) :
    slDiag r⁻¹ * (SpecialLinearGroup.transvection fin_zero_ne_one b * slDiag r *
      SpecialLinearGroup.transvection fin_zero_ne_one (-b)) =
      SpecialLinearGroup.transvection fin_zero_ne_one (b * ((r : K)⁻¹ ^ 2 - 1)) := by
  apply Subtype.ext
  change ((slDiag r⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((SpecialLinearGroup.transvection fin_zero_ne_one b : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * ((slDiag r : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *
        ((SpecialLinearGroup.transvection fin_zero_ne_one (-b) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) = _
  rw [upper_transvection_coe, upper_transvection_coe, upper_transvection_coe, slDiag_coe,
    slDiag_coe, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Units.val_inv_eq_inv_val, inv_inv]
  have hr : (r : K) ≠ 0 := r.ne_zero
  have hi1 : (r : K)⁻¹ * (r : K) = 1 := inv_mul_cancel₀ hr
  have hi2 : (r : K) * (r : K)⁻¹ = 1 := mul_inv_cancel₀ hr
  have h1 : (r : K)⁻¹ * ((1 * (r : K) + b * 0) * 1 + (1 * 0 + b * (r : K)⁻¹) * 0) +
      0 * ((0 * (r : K) + 1 * 0) * 1 + (0 * 0 + 1 * (r : K)⁻¹) * 0) = 1 := by
    linear_combination hi1
  have h2 : (r : K)⁻¹ * ((1 * (r : K) + b * 0) * -b + (1 * 0 + b * (r : K)⁻¹) * 1) +
      0 * ((0 * (r : K) + 1 * 0) * -b + (0 * 0 + 1 * (r : K)⁻¹) * 1) =
        b * ((r : K)⁻¹ ^ 2 - 1) := by
    linear_combination (-b) * hi1
  have h3 : 0 * ((1 * (r : K) + b * 0) * 1 + (1 * 0 + b * (r : K)⁻¹) * 0) +
      (r : K) * ((0 * (r : K) + 1 * 0) * 1 + (0 * 0 + 1 * (r : K)⁻¹) * 0) = 0 := by ring
  have h4 : 0 * ((1 * (r : K) + b * 0) * -b + (1 * 0 + b * (r : K)⁻¹) * 1) +
      (r : K) * ((0 * (r : K) + 1 * 0) * -b + (0 * 0 + 1 * (r : K)⁻¹) * 1) = 1 := by
    linear_combination hi2
  rw [h1, h2, h3, h4]

/-- Conjugating a translation by a diagonal element scales it by a square. -/
private theorem slDiag_conj_transvection {K : Type*} [Field K] (a : Kˣ) (x : K) :
    slDiag a * SpecialLinearGroup.transvection fin_zero_ne_one x * slDiag a⁻¹ =
      SpecialLinearGroup.transvection fin_zero_ne_one ((a : K) ^ 2 * x) := by
  apply Subtype.ext
  change ((slDiag a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((SpecialLinearGroup.transvection fin_zero_ne_one x : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *
      ((slDiag a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [upper_transvection_coe, upper_transvection_coe, slDiag_coe, slDiag_coe, Matrix.mul_fin_two,
    Matrix.mul_fin_two, Units.val_inv_eq_inv_val, inv_inv]
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hi1 : (a : K) * (a : K)⁻¹ = 1 := mul_inv_cancel₀ ha
  have hi2 : (a : K)⁻¹ * (a : K) = 1 := inv_mul_cancel₀ ha
  have h1 : ((a : K) * 1 + 0 * 0) * (a : K)⁻¹ + ((a : K) * x + 0 * 1) * 0 = 1 := by
    linear_combination hi1
  have h2 : ((a : K) * 1 + 0 * 0) * 0 + ((a : K) * x + 0 * 1) * (a : K) = (a : K) ^ 2 * x := by
    ring
  have h3 : (0 * 1 + (a : K)⁻¹ * 0) * (a : K)⁻¹ + (0 * x + (a : K)⁻¹ * 1) * 0 = 0 := by ring
  have h4 : (0 * 1 + (a : K)⁻¹ * 0) * 0 + (0 * x + (a : K)⁻¹ * 1) * (a : K) = 1 := by
    linear_combination hi2
  rw [h1, h2, h3, h4]

/-- An upper triangular element is a translation times a diagonal element. -/
private theorem eq_transvection_mul_slDiag {K : Type*} [Field K]
    (g : SpecialLinearGroup (Fin 2) K) (hg : g 1 0 = 0) :
    ∃ a : Kˣ, g = SpecialLinearGroup.transvection fin_zero_ne_one (g 0 1 * g 0 0) * slDiag a ∧
      (a : K) = g 0 0 := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hg, mul_zero, sub_zero] using g.prop
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha, ?_, rfl⟩
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) K) =
    ((SpecialLinearGroup.transvection fin_zero_ne_one (g 0 1 * g 0 0) :
      SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      !![g 0 0, 0; 0, (g 0 0)⁻¹]
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hi : g 0 0 * (g 0 0)⁻¹ = 1 := mul_inv_cancel₀ ha
  have h1 : g 0 0 = 1 * g 0 0 + g 0 1 * g 0 0 * 0 := by ring
  have h2 : g 0 1 = 1 * 0 + g 0 1 * g 0 0 * (g 0 0)⁻¹ := by linear_combination (-g 0 1) * hi
  have h3 : g 1 0 = 0 * g 0 0 + 1 * 0 := by rw [hg]; ring
  have h4 : g 1 1 = 0 * 0 + 1 * (g 0 0)⁻¹ := by rw [hd]; ring
  have hR : ((SpecialLinearGroup.transvection fin_zero_ne_one (g 0 1 * g 0 0) :
      SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * !![g 0 0, 0; 0, (g 0 0)⁻¹] =
      !![1 * g 0 0 + g 0 1 * g 0 0 * 0, 1 * 0 + g 0 1 * g 0 0 * (g 0 0)⁻¹;
        0 * g 0 0 + 1 * 0, 0 * 0 + 1 * (g 0 0)⁻¹] := by
    rw [upper_transvection_coe, Matrix.mul_fin_two]
  rw [hR, ← h1, ← h2, ← h3, ← h4]
  exact Matrix.eta_fin_two _

/-- **Two full tori sharing a point generate the upper Borel.** If a subgroup of `SL₂(K)` over an
algebraically closed field contains the diagonal torus and its conjugate by a nontrivial upper
translation, then it contains every upper triangular element. -/
private theorem upper_mem_of_two_tori {K : Type*} [Field K] [IsAlgClosed K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) {b : K} (hb : b ≠ 0)
    (hD : ∀ r : Kˣ, slDiag r ∈ Γ)
    (hUD : ∀ r : Kˣ, SpecialLinearGroup.transvection fin_zero_ne_one b * slDiag r *
      SpecialLinearGroup.transvection fin_zero_ne_one (-b) ∈ Γ) :
    ∀ g : SpecialLinearGroup (Fin 2) K, g 1 0 = 0 → g ∈ Γ := by
  classical
  -- A nonzero translation.
  obtain ⟨r₀, hr₀⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr₀
  obtain ⟨h0, h1, hm1⟩ := hr₀
  let r : Kˣ := Units.mk0 r₀ h0
  have hc : b * ((r : K)⁻¹ ^ 2 - 1) ≠ 0 := by
    refine mul_ne_zero hb fun h ↦ ?_
    have hsq : (r₀ ^ 2)⁻¹ = 1 := by
      rw [← inv_pow]
      exact sub_eq_zero.1 h
    have : r₀ ^ 2 = 1 := inv_eq_one.1 hsq
    have hfac : (r₀ - 1) * (r₀ + 1) = 0 := by linear_combination this
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact h1 (sub_eq_zero.1 h')
    · exact hm1 (eq_neg_of_add_eq_zero_left h')
  have hU₀ : SpecialLinearGroup.transvection fin_zero_ne_one (b * ((r : K)⁻¹ ^ 2 - 1)) ∈ Γ := by
    rw [← slDiag_inv_mul_conj]
    exact Γ.mul_mem (hD r⁻¹) (hUD r)
  -- Every translation.
  have hU : ∀ x : K, SpecialLinearGroup.transvection fin_zero_ne_one x ∈ Γ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, SpecialLinearGroup.transvection_coeff_zero]
      exact Γ.one_mem
    obtain ⟨a₀, ha₀⟩ := IsAlgClosed.exists_pow_nat_eq (x / (b * ((r : K)⁻¹ ^ 2 - 1)))
      (n := 2) two_pos
    have ha₀0 : a₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at ha₀
      exact div_ne_zero hx hc ha₀.symm
    let a : Kˣ := Units.mk0 a₀ ha₀0
    have hx' : x = (a : K) ^ 2 * (b * ((r : K)⁻¹ ^ 2 - 1)) := by
      change x = a₀ ^ 2 * _
      rw [ha₀, div_mul_cancel₀ _ hc]
    rw [hx', ← slDiag_conj_transvection]
    exact Γ.mul_mem (Γ.mul_mem (hD a) hU₀) (hD a⁻¹)
  -- Every upper triangular element.
  intro g hg
  obtain ⟨a, hga, -⟩ := eq_transvection_mul_slDiag g hg
  rw [hga]
  exact Γ.mul_mem (hU _) (hD a)

/-- An element algebraic over an algebraically closed subfield lies in it. -/
theorem mem_range_of_isAlgebraic_of_isAlgClosed {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] {x : K} (hx : IsAlgebraic k x) : x ∈ range (algebraMap k K) := by
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k ({x} : Set K)) :=
    IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
  have h := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
    (IntermediateField.adjoin k ({x} : Set K))
  have hx' : x ∈ IntermediateField.adjoin k ({x} : Set K) :=
    IntermediateField.subset_adjoin k _ (mem_singleton x)
  rw [h] at hx'
  exact IntermediateField.mem_bot.1 hx'

/-- A unit whose sum with its inverse lies outside an algebraically closed subfield is
transcendental over it. -/
private theorem transcendental_of_add_inv_notMem {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] {l : K} (hl : l + l⁻¹ ∉ range (algebraMap k K)) :
    Transcendental k l := by
  intro halg
  obtain ⟨x, hx⟩ := mem_range_of_isAlgebraic_of_isAlgClosed halg
  exact hl ⟨x + x⁻¹, by rw [map_add, map_inv₀, hx]⟩

/-- A transcendental element does not square to one. -/
theorem sq_ne_one_of_transcendental {k K : Type*} [Field k] [Field K] [Algebra k K]
    {l : K} (hl : Transcendental k l) : l ^ 2 ≠ 1 := by
  intro h
  refine hl ⟨Polynomial.X ^ 2 - 1, fun h0 ↦ ?_, by simp [h]⟩
  have hc := congrArg (Polynomial.coeff · 2) h0
  simp [Polynomial.coeff_one] at hc

/-- A matrix commuting with a diagonal normalization: an eigenvector matrix `P` of `γ`, scaled
by `diag(D⁻¹, 1)` with `D = det P ≠ 0`, gives `γ = R diag(l, l⁻¹) R⁻¹` with `R ∈ SL₂`. -/
private theorem exists_slDiag_conj_of_eigen {K : Type*} [Field K]
    (γ : SpecialLinearGroup (Fin 2) K) (l : Kˣ) (P : Matrix (Fin 2) (Fin 2) K)
    (hD : P.det ≠ 0)
    (hP : (γ : Matrix (Fin 2) (Fin 2) K) * P = P * !![(l : K), 0; 0, (l : K)⁻¹]) :
    ∃ R : SpecialLinearGroup (Fin 2) K, γ = R * slDiag l * R⁻¹ := by
  let S : Matrix (Fin 2) (Fin 2) K := !![P.det⁻¹, 0; 0, 1]
  have hdet : (P * S).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, mul_inv_cancel₀ hD]
  let R : SpecialLinearGroup (Fin 2) K := ⟨P * S, hdet⟩
  refine ⟨R, eq_mul_inv_of_mul_eq ?_⟩
  apply Subtype.ext
  change (γ : Matrix (Fin 2) (Fin 2) K) * (P * S) = P * S * !![(l : K), 0; 0, (l : K)⁻¹]
  have hcomm : S * !![(l : K), 0; 0, (l : K)⁻¹] = !![(l : K), 0; 0, (l : K)⁻¹] * S := by
    simp only [S, Matrix.mul_fin_two]
    congr 1
    simp [mul_comm]
  rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc]

/-- **Diagonalizing an element with trace outside the base.** An element of `SL₂(K)` whose
trace lies outside an algebraically closed subfield `k` is conjugate to `diag(l, l⁻¹)` for a
unit `l` transcendental over `k`. -/
private theorem exists_slDiag_conj_of_trace_notMem {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] (γ : SpecialLinearGroup (Fin 2) K)
    (hγ : γ 0 0 + γ 1 1 ∉ range (algebraMap k K)) :
    ∃ (R : SpecialLinearGroup (Fin 2) K) (l : Kˣ), Transcendental k (l : K) ∧
      γ = R * slDiag l * R⁻¹ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.prop
  by_cases hb : γ 0 1 = 0
  · -- Lower triangular: the eigenvalue `γ₀₀`.
    rw [hb, zero_mul, sub_zero] at hdet
    have ha : γ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    let l : Kˣ := Units.mk0 _ ha
    have hd : γ 1 1 = (γ 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    have hl : Transcendental k (l : K) := by
      refine transcendental_of_add_inv_notMem ?_
      change γ 0 0 + (γ 0 0)⁻¹ ∉ _
      rwa [← hd]
    have hsq := sq_ne_one_of_transcendental hl
    have hD : γ 0 0 - (γ 0 0)⁻¹ ≠ 0 := by
      intro h
      apply hsq
      change γ 0 0 ^ 2 = 1
      have h' : γ 0 0 = (γ 0 0)⁻¹ := sub_eq_zero.1 h
      calc γ 0 0 ^ 2 = γ 0 0 * γ 0 0 := sq _
        _ = γ 0 0 * (γ 0 0)⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel₀ ha
    have key : !![γ 0 0, γ 0 1; γ 1 0, γ 1 1] * !![γ 0 0 - (γ 0 0)⁻¹, 0; γ 1 0, 1] =
        !![γ 0 0 - (γ 0 0)⁻¹, 0; γ 1 0, 1] * !![(l : K), 0; 0, (l : K)⁻¹] := by
      change _ = _ * !![γ 0 0, 0; 0, (γ 0 0)⁻¹]
      rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hb, hd]
      have h1 : γ 0 0 * (γ 0 0 - (γ 0 0)⁻¹) + 0 * γ 1 0 =
          (γ 0 0 - (γ 0 0)⁻¹) * γ 0 0 + 0 * 0 := by ring
      have h2 : γ 0 0 * 0 + 0 * 1 = (γ 0 0 - (γ 0 0)⁻¹) * 0 + 0 * (γ 0 0)⁻¹ := by ring
      have h3 : γ 1 0 * (γ 0 0 - (γ 0 0)⁻¹) + (γ 0 0)⁻¹ * γ 1 0 =
          γ 1 0 * γ 0 0 + 1 * 0 := by ring
      have h4 : γ 1 0 * 0 + (γ 0 0)⁻¹ * 1 = γ 1 0 * 0 + 1 * (γ 0 0)⁻¹ := by ring
      rw [h1, h2, h3, h4]
    obtain ⟨R, hR⟩ := exists_slDiag_conj_of_eigen γ l !![γ 0 0 - (γ 0 0)⁻¹, 0; γ 1 0, 1]
      (by simpa only [Matrix.det_fin_two_of, mul_one, zero_mul, sub_zero] using hD)
      ((congrArg (· * !![γ 0 0 - (γ 0 0)⁻¹, 0; γ 1 0, 1])
        (Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) K))).trans key)
    exact ⟨R, l, hl, hR⟩
  · -- General position: a root of the characteristic polynomial.
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root
      (Polynomial.X ^ 2 - Polynomial.C (γ 0 0 + γ 1 1) * Polynomial.X + 1) (by
        rw [show (Polynomial.X ^ 2 - Polynomial.C (γ 0 0 + γ 1 1) * Polynomial.X + 1 :
          Polynomial K).degree = 2 by compute_degree!]
        decide)
    have hroot : μ * μ - (γ 0 0 + γ 1 1) * μ + 1 = 0 := by
      simpa [Polynomial.IsRoot, sq] using hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hroot
    let l : Kˣ := Units.mk0 μ hμ0
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have htr : γ 0 0 + γ 1 1 = μ + μ⁻¹ := by
      field_simp
      linear_combination -hroot
    have hl : Transcendental k (l : K) := by
      refine transcendental_of_add_inv_notMem ?_
      change μ + μ⁻¹ ∉ _
      rwa [← htr]
    have hsq := sq_ne_one_of_transcendental hl
    have hD : γ 0 1 * (μ⁻¹ - γ 0 0) - γ 0 1 * (μ - γ 0 0) ≠ 0 := by
      have he : γ 0 1 * (μ⁻¹ - γ 0 0) - γ 0 1 * (μ - γ 0 0) = γ 0 1 * (μ⁻¹ - μ) := by ring
      rw [he]
      refine mul_ne_zero hb fun h ↦ hsq ?_
      change μ ^ 2 = 1
      have h' : μ⁻¹ = μ := sub_eq_zero.1 h
      calc μ ^ 2 = μ * μ := sq _
        _ = μ * μ⁻¹ := by rw [h']
        _ = 1 := hinv
    have key : !![γ 0 0, γ 0 1; γ 1 0, γ 1 1] * !![γ 0 1, γ 0 1; μ - γ 0 0, μ⁻¹ - γ 0 0] =
        !![γ 0 1, γ 0 1; μ - γ 0 0, μ⁻¹ - γ 0 0] * !![(l : K), 0; 0, (l : K)⁻¹] := by
      change _ = _ * !![μ, 0; 0, μ⁻¹]
      rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
      have h1 : γ 0 0 * γ 0 1 + γ 0 1 * (μ - γ 0 0) = γ 0 1 * μ + γ 0 1 * 0 := by ring
      have h2 : γ 0 0 * γ 0 1 + γ 0 1 * (μ⁻¹ - γ 0 0) = γ 0 1 * 0 + γ 0 1 * μ⁻¹ := by ring
      have h3 : γ 1 0 * γ 0 1 + γ 1 1 * (μ - γ 0 0) =
          (μ - γ 0 0) * μ + (μ⁻¹ - γ 0 0) * 0 := by
        linear_combination -hroot - hdet
      have h4 : γ 1 0 * γ 0 1 + γ 1 1 * (μ⁻¹ - γ 0 0) =
          (μ - γ 0 0) * 0 + (μ⁻¹ - γ 0 0) * μ⁻¹ := by
        linear_combination (-(μ⁻¹ ^ 2)) * hroot +
          (μ * μ⁻¹ + 1 - (γ 0 0 + γ 1 1) * μ⁻¹) * hinv - hdet
      rw [h1, h2, h3, h4]
    obtain ⟨R, hR⟩ := exists_slDiag_conj_of_eigen γ l
      !![γ 0 1, γ 0 1; μ - γ 0 0, μ⁻¹ - γ 0 0]
      (by rw [Matrix.det_fin_two_of]; exact hD)
      ((congrArg (· * !![γ 0 1, γ 0 1; μ - γ 0 0, μ⁻¹ - γ 0 0])
        (Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) K))).trans key)
    exact ⟨R, l, hl, hR⟩

/-- **The torus seed.** An element of a subgroup of `SL₂(K)` with trace outside an algebraically
closed subfield is conjugate to `diag(l, l⁻¹)` with `l` transcendental, and the subgroup contains
infinitely many elements of the conjugate torus. -/
private theorem infinite_torus_params_of_trace_notMem {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) {γ : SpecialLinearGroup (Fin 2) K}
    (hγΓ : γ ∈ Γ) (hγ : γ 0 0 + γ 1 1 ∉ range (algebraMap k K)) :
    ∃ (R : SpecialLinearGroup (Fin 2) K) (l : Kˣ), Transcendental k (l : K) ∧
      γ = R * slDiag l * R⁻¹ ∧ {r : Kˣ | R * slDiag r * R⁻¹ ∈ Γ}.Infinite := by
  obtain ⟨R, l, hl, hγR⟩ := exists_slDiag_conj_of_trace_notMem γ hγ
  refine ⟨R, l, hl, hγR, ?_⟩
  have hpow : ∀ n : ℕ, l ^ n ∈ {r : Kˣ | R * slDiag r * R⁻¹ ∈ Γ} := by
    intro n
    change R * slDiag (l ^ n) * R⁻¹ ∈ Γ
    rw [map_pow, ← conj_pow, ← hγR]
    exact Γ.pow_mem hγΓ n
  have hinj : Function.Injective fun n : ℕ ↦ l ^ n := by
    refine injective_pow_iff_not_isOfFinOrder.2 fun hfin ↦ hl ?_
    obtain ⟨n, hn, hln⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · simpa using Polynomial.X_pow_sub_C_ne_zero hn (1 : k)
    · have : (l : K) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hln, Units.val_one]
      simp [this]
  exact Set.infinite_of_injective_forall_mem hinj hpow

/-- Entries of a product lie in any intermediate field containing the entries of the factors. -/
theorem sl_mul_entries_mem {k K : Type*} [Field k] [Field K] [Algebra k K]
    (S : IntermediateField k K) {A B : SpecialLinearGroup (Fin 2) K}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin 2) : (A * B) i j ∈ S := by
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact S.add_mem (S.mul_mem (hA i 0) (hB 0 j)) (S.mul_mem (hA i 1) (hB 1 j))

/-- Entries of an inverse lie in any intermediate field containing the entries. -/
theorem sl_inv_entries_mem {k K : Type*} [Field k] [Field K] [Algebra k K]
    (S : IntermediateField k K) {A : SpecialLinearGroup (Fin 2) K} (hA : ∀ i j, A i j ∈ S)
    (i j : Fin 2) : A⁻¹ i j ∈ S := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j
  · exact hA 1 1
  · exact S.neg_mem (hA 0 1)
  · exact S.neg_mem (hA 1 0)
  · exact hA 0 0

/-- Conjugating by a matrix with entries in `N` stays algebraic over `N` and the entries. -/
private theorem slEntries_conj_subset {k K : Type*} [Field k] [Field K] [Algebra k K]
    (N : IntermediateField k K) {R : SpecialLinearGroup (Fin 2) K} (hR : ∀ i j, R i j ∈ N)
    (g : SpecialLinearGroup (Fin 2) K) :
    slEntries (R⁻¹ * g * R) ⊆ racl k ((N : Set K) ∪ slEntries g) := by
  let S := racl k ((N : Set K) ∪ slEntries g)
  have hRS : ∀ i j, R i j ∈ S := fun i j ↦ subset_racl k _ (Or.inl (hR i j))
  have hgS : ∀ i j, g i j ∈ S := fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact sl_mul_entries_mem S (sl_mul_entries_mem S (sl_inv_entries_mem S hRS) hgS) hRS i j

/-- Conjugation by a matrix with entries in `N` preserves the rank of the entries over `N`. -/
private theorem erk_slEntries_conj {k K : Type*} [Field k] [Field K] [Algebra k K]
    (N : IntermediateField k K) {R : SpecialLinearGroup (Fin 2) K} (hR : ∀ i j, R i j ∈ N)
    (g : SpecialLinearGroup (Fin 2) K) :
    erk k (N : Set K) (slEntries (R⁻¹ * g * R)) = erk k (N : Set K) (slEntries g) := by
  have hRinv : ∀ i j, R⁻¹ i j ∈ N := sl_inv_entries_mem N hR
  have hback : R⁻¹⁻¹ * (R⁻¹ * g * R) * R⁻¹ = g := by group
  refine le_antisymm ((erk_mono k _ (slEntries_conj_subset N hR g)).trans_eq (erk_racl k _ _))
    ?_
  have h := slEntries_conj_subset N hRinv (R⁻¹ * g * R)
  rw [hback] at h
  exact (erk_mono k _ h).trans_eq (erk_racl k _ _)

/-- **Ranks over a conjugating base.** Let `Γ ≤ SL₂(K)` be constructible over `k`, with all
entry-ranks at most two and some entry-rank two. For a small field `N` containing the entries
of `R`, the conjugate `R⁻¹ Γ R` has all entry-ranks over `N` at most two and some entry-rank over
`N` equal to two; the rank-two member is chosen fresh from `N` internally. -/
private theorem conj_rank_of_constructible_rank_two {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) (hΓ : IsConstructibleOver k (slCarrier Γ))
    (hle : ∀ m ∈ Γ, erk k ∅ (slEntries m) ≤ 2) (hr : ∃ m ∈ Γ, erk k ∅ (slEntries m) = 2)
    (N : IntermediateField k K) (hN : IsSmall k (N : Set K))
    (R : SpecialLinearGroup (Fin 2) K) (hR : ∀ i j, R i j ∈ N) :
    (∀ h ∈ Γ.map (MulAut.conj R⁻¹).toMonoidHom, erk k (N : Set K) (slEntries h) ≤ 2) ∧
      ∃ h ∈ Γ.map (MulAut.conj R⁻¹).toMonoidHom, erk k (N : Set K) (slEntries h) = 2 := by
  have hconj : ∀ g : SpecialLinearGroup (Fin 2) K,
      (MulAut.conj R⁻¹).toMonoidHom g = R⁻¹ * g * R := fun g ↦ by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [hconj, erk_slEntries_conj N hR]
    exact (erk_base_mono k (empty_subset _) _).trans (hle g hg)
  · obtain ⟨m, hm, hmr⟩ := hr
    -- A conjugate of `m` over `k` fresh from `N`.
    let a : Fin 2 × Fin 2 → K := fun ij ↦ m ij.1 ij.2
    have hN₁ : IsSmall k ((racl k ((N : Set K) ∪ range a) : IntermediateField k K) : Set K) :=
      (hN.union (IsSmall.of_finite (finite_range a))).racl
    obtain ⟨u, hu⟩ := exists_isGenericOver hN₁ a
    obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := k) hu.idealOf_eq.symm
    let n := SpecialLinearGroup.map σ.toRingHom m
    have hncoeff (i j : Fin 2) : n i j = u (i, j) := hσ (i, j)
    have hna : slEntries n = range u := by
      change range (fun ij : Fin 2 × Fin 2 ↦ n ij.1 ij.2) = _
      congr 1
      funext ij
      exact hncoeff ij.1 ij.2
    have hn : n ∈ Γ := by
      have hm' : a ∈ slCarrier Γ := ⟨m, hm, fun _ _ ↦ rfl⟩
      obtain ⟨n', hn', heq⟩ := (hΓ.mem_comp_algEquiv_iff σ a).2 hm'
      have he : n' = n := SpecialLinearGroup.ext _ _ fun i j ↦ heq i j
      exact he ▸ hn'
    have hnr : erk k (N : Set K) (slEntries n) = 2 := by
      have hind : IndepOver k ∅ (range u) (N : Set K) :=
        hu.indepOver.mono_right ((subset_union_left).trans (subset_racl k _))
      have h := hind (subset_refl _) (finite_range u)
      rw [empty_union] at h
      rw [hna, h, hu.erk_empty_eq]
      exact hmr
    refine ⟨R⁻¹ * n * R, ⟨n, hn, hconj n⟩, ?_⟩
    rw [erk_slEntries_conj N hR]
    exact hnr


open MvPolynomial

private theorem matrix_diag_middle_apply {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (r z : K) (i j : Fin 2) :
    (A * !![r, 0; 0, z] * B) i j = A i 0 * r * B 0 j + A i 1 * z * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl_torus_entry {K : Type*} [Field K]
    (R : SpecialLinearGroup (Fin 2) K) (r : Kˣ) (i j : Fin 2) :
    (R * slDiag r * R⁻¹) i j =
      R i 0 * (r : K) * R⁻¹ 0 j + R i 1 * (r : K)⁻¹ * R⁻¹ 1 j := by
  change ((R : Matrix (Fin 2) (Fin 2) K) * !![(r : K), 0; 0, (r : K)⁻¹] *
    ((R⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j = _
  exact matrix_diag_middle_apply _ _ _ _ i j

private theorem isConstructibleOver_torus_parameters {k K : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) (hΓ : IsConstructibleOver k (slCarrier Γ))
    (R : SpecialLinearGroup (Fin 2) K) :
    IsConstructibleOver K {x : Fin 1 → K |
      ∃ r : Kˣ, R * slDiag r * R⁻¹ ∈ Γ ∧ (r : K) = x 0} := by
  let q : (Fin 2 × Fin 2) → MvPolynomial (Fin 1 ⊕ Fin 1) K := fun ij ↦
    C (R ij.1 0) * X (Sum.inl 0) * C (R⁻¹ 0 ij.2) +
      C (R ij.1 1) * X (Sum.inr 0) * C (R⁻¹ 1 ij.2)
  have hq (x z : Fin 1 → K) (ij : Fin 2 × Fin 2) :
      aeval (Sum.elim x z) (q ij) =
        R ij.1 0 * x 0 * R⁻¹ 0 ij.2 + R ij.1 1 * z 0 * R⁻¹ 1 ij.2 := by
    simp [q]
  let φ (x z : Fin 1 → K) : Prop :=
    (fun ij : Fin 2 × Fin 2 ↦ aeval (Sum.elim x z) (q ij)) ∈ slCarrier Γ ∧ x 0 * z 0 = 1
  have hc : IsConstructibleOver K {u : (Fin 1 ⊕ Fin 1) → K | φ (u ∘ Sum.inl) (u ∘ Sum.inr)} := by
    have hp := (hΓ.extend_base (L := K)).preimage_polynomial q
    have hzero := IsConstructibleOver.polynomial_zero (k := K) (K := K)
      (X (Sum.inl 0) * X (Sum.inr 0) - 1 : MvPolynomial (Fin 1 ⊕ Fin 1) K)
    convert hp.inter hzero using 1
    ext u
    simp [φ, sub_eq_zero]
  have hset : {x : Fin 1 → K | ∃ r : Kˣ, R * slDiag r * R⁻¹ ∈ Γ ∧ (r : K) = x 0} =
      {x : Fin 1 → K | ∃ z : Fin 1 → K, φ x z} := by
    ext x
    change (∃ r : Kˣ, R * slDiag r * R⁻¹ ∈ Γ ∧ (r : K) = x 0) ↔ ∃ z : Fin 1 → K, φ x z
    constructor
    · rintro ⟨r, hr, hx⟩
      refine ⟨fun _ ↦ (r : K)⁻¹, ?_, ?_⟩
      · refine ⟨R * slDiag r * R⁻¹, hr, fun i j ↦ ?_⟩
        have hv := hq x (fun _ ↦ (r : K)⁻¹) (i, j)
        rw [← hx] at hv
        exact (sl_torus_entry R r i j).trans hv.symm
      · change x 0 * (r : K)⁻¹ = 1
        rw [← hx]
        exact mul_inv_cancel₀ r.ne_zero
    · rintro ⟨z, ⟨m, hm, hmx⟩, hxz⟩
      let r : Kˣ := Units.mk0 (x 0) (left_ne_zero_of_mul_eq_one hxz)
      have hz : z 0 = (r : K)⁻¹ := eq_inv_of_mul_eq_one_right hxz
      have he : m = R * slDiag r * R⁻¹ := by
        apply SpecialLinearGroup.ext
        intro i j
        calc m i j = aeval (Sum.elim x z) (q (i, j)) := hmx i j
          _ = R i 0 * x 0 * R⁻¹ 0 j + R i 1 * z 0 * R⁻¹ 1 j := hq x z (i, j)
          _ = (R * slDiag r * R⁻¹) i j := by
            rw [hz]
            exact (sl_torus_entry R r i j).symm
      exact ⟨r, he ▸ hm, rfl⟩
  rw [hset]
  exact hc.exists

private theorem full_torus_of_infinite_parameters {k K : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) K)) (hΓ : IsConstructibleOver k (slCarrier Γ))
    (R : SpecialLinearGroup (Fin 2) K)
    (hInf : {r : Kˣ | R * slDiag r * R⁻¹ ∈ Γ}.Infinite) :
    ∀ r : Kˣ, R * slDiag r * R⁻¹ ∈ Γ := by
  let S : Subgroup Kˣ := Γ.comap ((MulAut.conj R).toMonoidHom.comp slDiag)
  have hSInf : (S : Set Kˣ).Infinite := hInf
  have : Infinite Kˣ := infinite_univ_iff.1 (hSInf.mono (subset_univ _))
  have hS : S = ⊤ := constructible_units_subgroup_eq_top S hSInf
    (isConstructibleOver_torus_parameters Γ hΓ R)
  intro r
  have hr : r ∈ S := by rw [hS]; trivial
  exact hr



/-! ### The pure case analysis -/

/-- Entries of a product of `SL₂` matrices. -/
theorem sl_mul_apply {K : Type*} [Field K] (A B : SpecialLinearGroup (Fin 2) K)
    (i j : Fin 2) : (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- A property of all four entries. -/
private theorem sl_entries_forall {K : Type*} [Field K] {P : K → Prop}
    (m : SpecialLinearGroup (Fin 2) K) (h00 : P (m 0 0)) (h01 : P (m 0 1)) (h10 : P (m 1 0))
    (h11 : P (m 1 1)) : ∀ i j, P (m i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Matrices with the same four entries are equal. -/
private theorem sl_ext_entries {K : Type*} [Field K] {A B : SpecialLinearGroup (Fin 2) K}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) :
    A = B := by
  refine SpecialLinearGroup.ext _ _ fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> assumption

/-- The entries of a matrix lie in a set containing each of them. -/
private theorem slEntries_subset_of {K : Type*} [Field K] {S : Set K}
    (m : SpecialLinearGroup (Fin 2) K) (h : ∀ i j, m i j ∈ S) : slEntries m ⊆ S := by
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact h i j

/-- A diagonal matrix of `SL₂` has entry-rank at most one. -/
private theorem erk_slEntries_le_one_of_offdiag {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m : SpecialLinearGroup (Fin 2) K) (h01 : m 0 1 = 0) (h10 : m 1 0 = 0) :
    erk k ∅ (slEntries m) ≤ 1 := by
  have hdet : m 0 0 * m 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, zero_mul, sub_zero] using m.prop
  let F := racl k ({m 0 0} : Set K)
  have ha : m 0 0 ∈ F := subset_racl k _ (mem_singleton _)
  have hd : m 1 1 ∈ F := by
    rw [eq_inv_of_mul_eq_one_right hdet]
    exact F.inv_mem ha
  have hsub : slEntries m ⊆ F := slEntries_subset_of m (sl_entries_forall (P := (· ∈ F)) m ha
    (show m 0 1 ∈ F by rw [h01]; exact F.zero_mem) (show m 1 0 ∈ F by rw [h10]; exact F.zero_mem)
    hd)
  have hr := (erk_mono k ∅ hsub).trans_eq (by
    simpa only [empty_union] using erk_racl k (∅ : Set K) ({m 0 0} : Set K))
  exact hr.trans ((erk_le_encard k ∅ _).trans (by simp))

/-- An antidiagonal matrix of `SL₂` has entry-rank at most one. -/
private theorem erk_slEntries_le_one_of_diag {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m : SpecialLinearGroup (Fin 2) K) (h00 : m 0 0 = 0) (h11 : m 1 1 = 0) :
    erk k ∅ (slEntries m) ≤ 1 := by
  have hdet : m 0 1 * -m 1 0 = 1 := by
    have h := m.prop
    rw [Matrix.det_fin_two, h00, zero_mul, zero_sub] at h
    linear_combination h
  let F := racl k ({m 0 1} : Set K)
  have hb : m 0 1 ∈ F := subset_racl k _ (mem_singleton _)
  have hc : m 1 0 ∈ F := by
    rw [← neg_neg (m 1 0), eq_inv_of_mul_eq_one_right hdet]
    exact F.neg_mem (F.inv_mem hb)
  have hsub : slEntries m ⊆ F := slEntries_subset_of m (sl_entries_forall (P := (· ∈ F)) m
    (show m 0 0 ∈ F by rw [h00]; exact F.zero_mem) hb hc
    (show m 1 1 ∈ F by rw [h11]; exact F.zero_mem))
  have hr := (erk_mono k ∅ hsub).trans_eq (by
    simpa only [empty_union] using erk_racl k (∅ : Set K) ({m 0 1} : Set K))
  exact hr.trans ((erk_le_encard k ∅ _).trans (by simp))

/-- A torus witness with all entries nonzero contradicts the rank bound. -/
private theorem not_witness_of_entries_ne_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (H : Subgroup (SpecialLinearGroup (Fin 2) K)) (hD : ∀ r : Kˣ, slDiag r ∈ H)
    (hle : ∀ h ∈ H, erk k ∅ (slEntries h) ≤ 2) (R : SpecialLinearGroup (Fin 2) K)
    (hR : ∀ i j, R i j ≠ 0) (hRT : ∀ r : Kˣ, R * slDiag r * R⁻¹ ∈ H) : False := by
  obtain ⟨m, hm, h3⟩ := exists_rank_three_of_two_tori (k := k) H R hR hD hRT
  have := h3.trans (hle m hm)
  norm_num at this

/-- The entries of the upper transvection. -/
private theorem upper_transvection_apply {K : Type*} [Field K] (z : K) :
    (SpecialLinearGroup.transvection fin_zero_ne_one z : SpecialLinearGroup (Fin 2) K) 0 0 = 1 ∧
      (SpecialLinearGroup.transvection fin_zero_ne_one z : SpecialLinearGroup (Fin 2) K) 0 1 = z ∧
      (SpecialLinearGroup.transvection fin_zero_ne_one z : SpecialLinearGroup (Fin 2) K) 1 0 = 0 ∧
      (SpecialLinearGroup.transvection fin_zero_ne_one z : SpecialLinearGroup (Fin 2) K) 1 1 =
        1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [upper_transvection_coe] <;> rfl

/-- **An upper torus witness forces the upper Borel.** -/
private theorem mem_iff_upper_of_witness {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (H : Subgroup (SpecialLinearGroup (Fin 2) K)) (hD : ∀ r : Kˣ, slDiag r ∈ H)
    (hle : ∀ h ∈ H, erk k ∅ (slEntries h) ≤ 2) (R : SpecialLinearGroup (Fin 2) K)
    (hR10 : R 1 0 = 0) (hR01 : R 0 1 ≠ 0) (hRT : ∀ r : Kˣ, R * slDiag r * R⁻¹ ∈ H) :
    ∀ g : SpecialLinearGroup (Fin 2) K, g ∈ H ↔ g 1 0 = 0 := by
  classical
  obtain ⟨a, hRa, -⟩ := eq_transvection_mul_slDiag R hR10
  have hdet : R 0 0 * R 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hR10, mul_zero, sub_zero] using R.prop
  have hR00 : R 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hb : R 0 1 * R 0 0 ≠ 0 := mul_ne_zero hR01 hR00
  -- The witness torus is the conjugate torus by a translation.
  have hUD : ∀ r : Kˣ, SpecialLinearGroup.transvection fin_zero_ne_one (R 0 1 * R 0 0) *
      slDiag r * SpecialLinearGroup.transvection fin_zero_ne_one (-(R 0 1 * R 0 0)) ∈ H := by
    intro r
    have hcomm : slDiag a * slDiag r * (slDiag a)⁻¹ = slDiag r := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm a r, mul_inv_cancel_right]
    have h := hRT r
    rw [hRa, _root_.mul_inv_rev, SpecialLinearGroup.transvection_inv,
      show ∀ x y z w : SpecialLinearGroup (Fin 2) K, x * y * z * (y⁻¹ * w) =
        x * (y * z * y⁻¹) * w from fun _ _ _ _ ↦ by group, hcomm] at h
    exact h
  have hupper := upper_mem_of_two_tori H hb hD hUD
  have hU : ∀ z : K, SpecialLinearGroup.transvection fin_zero_ne_one z ∈ H := fun z ↦
    hupper _ (upper_transvection_apply z).2.2.1
  intro g
  refine ⟨fun hg ↦ ?_, hupper g⟩
  by_contra hc
  -- A conjugate of `g` by translations with all entries nonzero.
  obtain ⟨x, hx⟩ : ∃ x : K, g 0 0 + x * g 1 0 ≠ 0 := by
    by_cases h0 : g 0 0 = 0
    · exact ⟨1, by rw [h0, zero_add, one_mul]; exact hc⟩
    · exact ⟨0, by rw [zero_mul, add_zero]; exact h0⟩
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    ({-(g 0 1 + x * g 1 1) / (g 0 0 + x * g 1 0), -g 1 1 / g 1 0} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨R', hR'def⟩ : ∃ R', R' = SpecialLinearGroup.transvection fin_zero_ne_one x * g *
      SpecialLinearGroup.transvection fin_zero_ne_one y := ⟨_, rfl⟩
  obtain ⟨u00, u01, u10, u11⟩ := upper_transvection_apply (K := K) x
  obtain ⟨v00, v01, v10, v11⟩ := upper_transvection_apply (K := K) y
  have e00 : R' 0 0 = g 0 0 + x * g 1 0 := by
    rw [hR'def]
    simp only [sl_mul_apply, u00, u01, v00, v10]
    ring
  have e01 : R' 0 1 = (g 0 0 + x * g 1 0) * y + (g 0 1 + x * g 1 1) := by
    rw [hR'def]
    simp only [sl_mul_apply, u00, u01, v01, v11]
    ring
  have e10 : R' 1 0 = g 1 0 := by
    rw [hR'def]
    simp only [sl_mul_apply, u10, u11, v00, v10]
    ring
  have e11 : R' 1 1 = g 1 0 * y + g 1 1 := by
    rw [hR'def]
    simp only [sl_mul_apply, u10, u11, v01, v11]
    ring
  have hR' : R' ∈ H := by
    rw [hR'def]
    exact H.mul_mem (H.mul_mem (hU x) hg) (hU y)
  refine not_witness_of_entries_ne_zero H hD hle R' (sl_entries_forall (P := (· ≠ 0)) R'
    (show R' 0 0 ≠ 0 by rw [e00]; exact hx) (show R' 0 1 ≠ 0 by
      rw [e01]
      intro h
      apply hy1
      rw [eq_div_iff hx]
      linear_combination h)
    (show R' 1 0 ≠ 0 by rw [e10]; exact hc) (show R' 1 1 ≠ 0 by
      rw [e11]
      intro h
      apply hy2
      rw [eq_div_iff hc]
      linear_combination h))
    (fun r ↦ H.mul_mem (H.mul_mem hR' (hD r)) (H.inv_mem hR'))

/-- The coordinate swap. -/
private def slSwap (K : Type*) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The entries of the swap and of its inverse. -/
private theorem slSwap_apply (K : Type*) [Field K] :
    (slSwap K 0 0 = 0 ∧ slSwap K 0 1 = 1 ∧ slSwap K 1 0 = -1 ∧ slSwap K 1 1 = 0) ∧
      ((slSwap K)⁻¹ 0 0 = 0 ∧ (slSwap K)⁻¹ 0 1 = -1 ∧ (slSwap K)⁻¹ 1 0 = 1 ∧
        (slSwap K)⁻¹ 1 1 = 0) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [SpecialLinearGroup.SL2_inv_expl]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [slSwap]

/-- Entries of the conjugate by the swap. -/
private theorem slSwap_conj_apply {K : Type*} [Field K] (g : SpecialLinearGroup (Fin 2) K) :
    (slSwap K * g * (slSwap K)⁻¹) 0 0 = g 1 1 ∧ (slSwap K * g * (slSwap K)⁻¹) 0 1 = -g 1 0 ∧
      (slSwap K * g * (slSwap K)⁻¹) 1 0 = -g 0 1 ∧ (slSwap K * g * (slSwap K)⁻¹) 1 1 = g 0 0 := by
  obtain ⟨⟨w00, w01, w10, w11⟩, ⟨i00, i01, i10, i11⟩⟩ := slSwap_apply K
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [sl_mul_apply, w00, w01, w10, w11, i00, i01, i10, i11] <;> ring

/-- Entries of a matrix and of its swap conjugate have the same rank. -/
private theorem erk_slEntries_swap_conj {k K : Type*} [Field k] [Field K] [Algebra k K]
    (g : SpecialLinearGroup (Fin 2) K) :
    erk k ∅ (slEntries (slSwap K * g * (slSwap K)⁻¹)) = erk k ∅ (slEntries g) := by
  obtain ⟨e00, e01, e10, e11⟩ := slSwap_conj_apply g
  obtain ⟨W, hWdef⟩ : ∃ W, W = slSwap K * g * (slSwap K)⁻¹ := ⟨_, rfl⟩
  rw [← hWdef] at e00 e01 e10 e11 ⊢
  have hg : ∀ i j, g i j ∈ racl k (∅ ∪ slEntries g) :=
    fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)
  have hW : ∀ i j, W i j ∈ racl k (∅ ∪ slEntries W) :=
    fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)
  have h1 : slEntries W ⊆ racl k (∅ ∪ slEntries g) :=
    slEntries_subset_of W (sl_entries_forall (P := (· ∈ racl k (∅ ∪ slEntries g))) W
      (show W 0 0 ∈ _ by rw [e00]; exact hg 1 1)
      (show W 0 1 ∈ _ by rw [e01]; exact (racl k _).neg_mem (hg 1 0))
      (show W 1 0 ∈ _ by rw [e10]; exact (racl k _).neg_mem (hg 0 1))
      (show W 1 1 ∈ _ by rw [e11]; exact hg 0 0))
  have h2 : slEntries g ⊆ racl k (∅ ∪ slEntries W) :=
    slEntries_subset_of g (sl_entries_forall (P := (· ∈ racl k (∅ ∪ slEntries W))) g
      (show g 0 0 ∈ _ by rw [← e11]; exact hW 1 1)
      (show g 0 1 ∈ _ by rw [← neg_neg (g 0 1), ← e10]; exact (racl k _).neg_mem (hW 1 0))
      (show g 1 0 ∈ _ by rw [← neg_neg (g 1 0), ← e01]; exact (racl k _).neg_mem (hW 0 1))
      (show g 1 1 ∈ _ by rw [← e00]; exact hW 0 0))
  exact le_antisymm ((erk_mono k ∅ h1).trans_eq (erk_racl k _ _))
    ((erk_mono k ∅ h2).trans_eq (erk_racl k _ _))

/-- The swap conjugates the diagonal torus to itself. -/
private theorem slSwap_conj_slDiag {K : Type*} [Field K] (r : Kˣ) :
    slSwap K * slDiag r * (slSwap K)⁻¹ = slDiag r⁻¹ := by
  obtain ⟨e00, e01, e10, e11⟩ := slSwap_conj_apply (slDiag r)
  refine sl_ext_entries ?_ ?_ ?_ ?_
  · rw [e00, slDiag_coe, slDiag_coe, Units.val_inv_eq_inv_val]
    rfl
  · rw [e01, slDiag_coe, slDiag_coe]
    exact neg_zero
  · rw [e10, slDiag_coe, slDiag_coe]
    exact neg_zero
  · rw [e11, slDiag_coe, slDiag_coe, Units.val_inv_eq_inv_val, inv_inv]
    rfl

/-- **The pure case analysis.** A subgroup of `SL₂(K)` containing the diagonal torus, with all
entry-ranks at most two and some entry-rank two, is the upper Borel subgroup up to conjugation
by the identity or the coordinate swap. -/
private theorem exists_borel_conj_of_rank_two {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (H : Subgroup (SpecialLinearGroup (Fin 2) K)) (hD : ∀ r : Kˣ, slDiag r ∈ H)
    (hle : ∀ h ∈ H, erk k ∅ (slEntries h) ≤ 2) (hr : ∃ h ∈ H, erk k ∅ (slEntries h) = 2) :
    ∃ A : SpecialLinearGroup (Fin 2) K, ∀ g, g ∈ H ↔ (A * g * A⁻¹) 1 0 = 0 := by
  obtain ⟨δ, hδ, hδr⟩ := hr
  -- The lower case: conjugate the whole subgroup by the swap.
  have hlower : ∀ R : SpecialLinearGroup (Fin 2) K, R 0 1 = 0 → R 1 0 ≠ 0 →
      (∀ r : Kˣ, R * slDiag r * R⁻¹ ∈ H) →
      ∃ A : SpecialLinearGroup (Fin 2) K, ∀ g, g ∈ H ↔ (A * g * A⁻¹) 1 0 = 0 := by
    intro R hR01 hR10 hRT
    let H' := H.map (MulAut.conj (slSwap K)).toMonoidHom
    have hmem : ∀ g : SpecialLinearGroup (Fin 2) K,
        g ∈ H' ↔ (slSwap K)⁻¹ * g * slSwap K ∈ H := by
      intro g
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hinv : ∀ r : Kˣ, (slSwap K)⁻¹ * slDiag r * slSwap K = slDiag r⁻¹ := fun r ↦ by
      have h := slSwap_conj_slDiag (K := K) r⁻¹
      rw [inv_inv] at h
      rw [← h]
      group
    have hconj : ∀ g : SpecialLinearGroup (Fin 2) K,
        (slSwap K)⁻¹ * (slSwap K * g * (slSwap K)⁻¹) * slSwap K = g := fun g ↦ by group
    have hD' : ∀ r : Kˣ, slDiag r ∈ H' := by
      intro r
      rw [hmem, ← inv_inv r, ← slSwap_conj_slDiag r⁻¹, hconj]
      exact hD r⁻¹
    have hle' : ∀ h ∈ H', erk k ∅ (slEntries h) ≤ 2 := by
      intro h hh
      rw [hmem] at hh
      have := hle _ hh
      rwa [← erk_slEntries_swap_conj,
        show slSwap K * ((slSwap K)⁻¹ * h * slSwap K) * (slSwap K)⁻¹ = h by group] at this
    obtain ⟨e00, e01, e10, e11⟩ := slSwap_conj_apply R
    have hW := mem_iff_upper_of_witness H' hD' hle' (slSwap K * R * (slSwap K)⁻¹)
      (by rw [e10, hR01, neg_zero]) (by rw [e01]; exact neg_ne_zero.2 hR10) (fun r ↦ by
        rw [hmem, show (slSwap K)⁻¹ * (slSwap K * R * (slSwap K)⁻¹ * slDiag r *
            (slSwap K * R * (slSwap K)⁻¹)⁻¹) * slSwap K =
            R * ((slSwap K)⁻¹ * slDiag r * slSwap K) * R⁻¹ by group, hinv]
        exact hRT r⁻¹)
    refine ⟨slSwap K, fun g ↦ ?_⟩
    rw [← hW, hmem, hconj]
  -- The cases on the zero entries of `δ`.
  have hnd : ¬ (δ 0 1 = 0 ∧ δ 1 0 = 0) := fun h ↦ by
    have := erk_slEntries_le_one_of_offdiag (k := k) δ h.1 h.2
    rw [hδr] at this
    norm_num at this
  have hna : ¬ (δ 0 0 = 0 ∧ δ 1 1 = 0) := fun h ↦ by
    have := erk_slEntries_le_one_of_diag (k := k) δ h.1 h.2
    rw [hδr] at this
    norm_num at this
  have hδT : ∀ r : Kˣ, δ * slDiag r * δ⁻¹ ∈ H := fun r ↦
    H.mul_mem (H.mul_mem hδ (hD r)) (H.inv_mem hδ)
  have hδWT : ∀ r : Kˣ, (δ * slSwap K) * slDiag r * (δ * slSwap K)⁻¹ ∈ H := by
    intro r
    have h := hδT r⁻¹
    convert h using 1
    rw [← slSwap_conj_slDiag r]
    group
  obtain ⟨⟨w00, w01, w10, w11⟩, -⟩ := slSwap_apply K
  have d01 : (δ * slSwap K) 0 1 = δ 0 0 := by
    simp only [sl_mul_apply, w01, w11]
    ring
  have d10 : (δ * slSwap K) 1 0 = -δ 1 1 := by
    simp only [sl_mul_apply, w00, w10]
    ring
  have hupperA : ∀ R : SpecialLinearGroup (Fin 2) K, R 1 0 = 0 → R 0 1 ≠ 0 →
      (∀ r : Kˣ, R * slDiag r * R⁻¹ ∈ H) →
      ∃ A : SpecialLinearGroup (Fin 2) K, ∀ g, g ∈ H ↔ (A * g * A⁻¹) 1 0 = 0 := by
    intro R hR10 hR01 hRT
    refine ⟨1, fun g ↦ ?_⟩
    rw [mem_iff_upper_of_witness H hD hle R hR10 hR01 hRT g, one_mul, inv_one, mul_one]
  by_cases h10 : δ 1 0 = 0
  · exact hupperA δ h10 (fun h ↦ hnd ⟨h, h10⟩) hδT
  by_cases h01 : δ 0 1 = 0
  · exact hlower δ h01 h10 hδT
  by_cases h00 : δ 0 0 = 0
  · exact hlower (δ * slSwap K) (by rw [d01, h00])
      (by rw [d10]; exact neg_ne_zero.2 fun h ↦ hna ⟨h00, h⟩) hδWT
  by_cases h11 : δ 1 1 = 0
  · exact hupperA (δ * slSwap K) (by rw [d10, h11, neg_zero]) (by rw [d01]; exact h00) hδWT
  exact (not_witness_of_entries_ne_zero H hD hle δ
    (sl_entries_forall (P := (· ≠ 0)) δ h00 h01 h10 h11) hδT).elim

/-- A subgroup of `SL₂(K)` whose entries form a set constructible over `k`, with all entry-ranks
at most two and some equal to two, is conjugate to the full upper Borel. The torus, conjugating
field and fresh rank-two element are chosen internally. -/
theorem exists_borel_conj_of_constructible_rank_two {k K : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] (Γ : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hΓ : IsConstructibleOver k {x : Fin 2 × Fin 2 → K |
      ∃ m ∈ Γ, ∀ i j, m i j = x (i, j)})
    (hle : ∀ m ∈ Γ, erk k ∅ (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ≤ 2)
    (hr : ∃ m ∈ Γ, erk k ∅ (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) = 2) :
    ∃ A : SpecialLinearGroup (Fin 2) K, ∀ m, m ∈ Γ ↔ (A * m * A⁻¹) 1 0 = 0 := by
  obtain ⟨γ, hγ, htrace⟩ := exists_nonbase_trace_of_constructible_rank_two Γ hΓ hr
  obtain ⟨R, _, _, _, hInf⟩ := infinite_torus_params_of_trace_notMem Γ hγ htrace
  have hfull := full_torus_of_infinite_parameters Γ hΓ R hInf
  -- The conjugating coefficients enter the base before ranks are compared.
  let N := racl k (slEntries R)
  have hN : IsSmall k (N : Set K) := (IsSmall.of_finite (finite_range _)).racl
  let : IsAlgClosed ↥N := isAlgClosed_racl _
  let : UniversalDomain ↥N K := universalDomain_of_isSmall N hN
  have hR (i j : Fin 2) : R i j ∈ N := subset_racl k _ ⟨(i, j), rfl⟩
  let H := Γ.map (MulAut.conj R⁻¹).toMonoidHom
  obtain ⟨hHle, hHr⟩ := conj_rank_of_constructible_rank_two Γ hΓ hle hr N hN R hR
  have hD (r : Kˣ) : slDiag r ∈ H := by
    refine ⟨R * slDiag r * R⁻¹, hfull r, ?_⟩
    change R⁻¹ * (R * slDiag r * R⁻¹) * R⁻¹⁻¹ = slDiag r
    group
  have hleN : ∀ m ∈ H, erk ↥N ∅ (slEntries m) ≤ 2 := by
    intro m hm
    rw [erk_base_empty N]
    exact hHle m hm
  have hrN : ∃ m ∈ H, erk ↥N ∅ (slEntries m) = 2 := by
    obtain ⟨m, hm, hmr⟩ := hHr
    exact ⟨m, hm, (erk_base_empty N _).trans hmr⟩
  obtain ⟨A₀, hA₀⟩ := exists_borel_conj_of_rank_two (k := ↥N) H hD hleN hrN
  refine ⟨A₀ * R⁻¹, fun m ↦ ?_⟩
  have hm : R⁻¹ * m * R ∈ H ↔ m ∈ Γ := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    rw [show R * (R⁻¹ * m * R) * R⁻¹ = m by group]
  rw [← hm, hA₀]
  group


end

end GroupConfig
