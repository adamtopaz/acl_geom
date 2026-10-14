/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.InvertibleAdmissible
import Mathlib.Data.Fintype.Pi

/-!
# Fresh generic samples for admissibility

The sampling-existence part of supplemental `lem:adm-constructible` for the
actual admissible and invertibly admissible parameter sets. Binary rank
induction chooses any finite number of jointly generic samples over any
prescribed small field. Thus the required majority samples are obtained
internally, independently from that field.

**Status:** fresh samples and the resulting common constructibility of Adm
and Adm× are proved. A single fresh sampling field also serving germ equality
and arbitrary finite word relations is a later assembly step. The constructible
group is not asserted here.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι]

/-- An arbitrary finite number of jointly generic samples can be chosen over any
prescribed small field. Both relative and absolute joint ranks are the sum of
the original locus dimensions. -/
theorem exists_genericSamples (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
    (a : ι → K) (n : ℕ) :
    ∃ t : Fin n → ι → K,
      (∀ i, IsGenericOver M a (t i)) ∧
      erk k (M : Set K) (⋃ i, range (t i)) = ∑ _i : Fin n, erk k ∅ (range a) ∧
      erk k ∅ (⋃ i, range (t i)) = ∑ _i : Fin n, erk k ∅ (range a) := by
  classical
  induction n with
  | zero =>
    refine ⟨Fin.elim0, fun i ↦ Fin.elim0 i, ?_, ?_⟩ <;> simp [erk_empty]
  | succ n ih =>
    obtain ⟨t, ht, hr, hr₀⟩ := ih
    let T : Set K := ⋃ i, range (t i)
    have hT : T.Finite := finite_iUnion fun i ↦ finite_range (t i)
    have hN : IsSmall k ((racl k ((M : Set K) ∪ T) : IntermediateField k K) : Set K) :=
      (hM.union (IsSmall.of_finite hT)).racl
    obtain ⟨y, hy⟩ := exists_isGenericOver hN a
    have hyM : IsGenericOver M a y :=
      hy.of_le (subset_union_left.trans (subset_racl k _))
    have hry : erk k ((M : Set K) ∪ T) (range y) = erk k ∅ (range a) := by
      rw [← erk_racl_base, hy.erk_coe_eq, hy.erk_empty_eq]
    have hsum : erk k (M : Set K) (range y ∪ T) =
        ∑ _i : Fin (n + 1), erk k ∅ (range a) := by
      rw [union_comm, erk_union_eq, hr, hry, Fin.sum_univ_succ, add_comm]
    refine ⟨Fin.cons y t, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact hyM
      | succ j => exact ht j
    · simpa only [Fin.cons_zero, Fin.cons_succ, iUnion_fin_add_one_eq_iUnion_succ,
        Function.comp_def] using hsum
    · have hupper : erk k ∅ (range y ∪ T) ≤
          ∑ _i : Fin (n + 1), erk k ∅ (range a) := by
        calc
          erk k ∅ (range y ∪ T) ≤ erk k ∅ (range y) + erk k ∅ T :=
            erk_union_le k ∅ _ _
          _ = ∑ _i : Fin (n + 1), erk k ∅ (range a) := by
            rw [hy.erk_empty_eq, hr₀, Fin.sum_univ_succ]
      have hlower : (∑ _i : Fin (n + 1), erk k ∅ (range a)) ≤
          erk k ∅ (range y ∪ T) := by
        rw [← hsum]
        exact erk_base_mono k (empty_subset _) _
      simpa only [Fin.cons_zero, Fin.cons_succ, iUnion_fin_add_one_eq_iUnion_succ,
        Function.comp_def] using le_antisymm hupper hlower

/-- The samples used by admissibility may be chosen jointly independent from
any prescribed small field, rather than supplied as an open hypothesis. -/
theorem exists_fresh_genericSamples (M : IntermediateField k K)
    (hM : IsSmall k (M : Set K)) (a : ι → K) (n : ℕ) :
    ∃ t : Fin n → ι → K,
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) a (t i)) ∧
      erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
        ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)) ∧
      IndepOver k ∅ (⋃ i, range (t i)) (M : Set K) := by
  obtain ⟨t, ht, hr, hr₀⟩ := exists_genericSamples M hM a n
  have hbot (i : Fin n) : IsGenericOver (⊥ : IntermediateField k K) a (t i) :=
    (ht i).of_le bot_le
  have hrbot : erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
      ∑ _i : Fin n, erk k ∅ (range a) := by
    refine le_antisymm ((erk_base_mono k (empty_subset _) _).trans hr₀.le) ?_
    rw [← hr]
    exact erk_base_mono k (show (⊥ : IntermediateField k K) ≤ M from bot_le) _
  refine ⟨t, hbot, ?_, indepOver_of_erk_eq (finite_iUnion fun i ↦ finite_range (t i)) ?_⟩
  · rw [hrbot]
    exact Finset.sum_congr rfl fun i _ ↦ ((hbot i).erk_coe_eq.trans (ht i).erk_empty_eq).symm
  · rw [empty_union, hr, hr₀]

/-- The source's arbitrary-small-field form of admissibility constructibility:
a finite sampling tuple independent from that field makes both the admissible
and invertibly admissible parameter sets constructible. -/
theorem QuasiRational.exists_fresh_constructible_admissible_samples
    {μ κ : Type*} [Fintype μ] [Finite κ] (F : QuasiRational k (μ ⊕ ι) κ)
    (a : ι → K) (a' : κ → K) (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    (M : IntermediateField k K) (hM : IsSmall k (M : Set K)) :
    ∃ t : Fin (2 * Fintype.card μ + 1) → κ → K,
      IndepOver k ∅ (⋃ i, range (t i)) (M : Set K) ∧
      IsConstructibleOver (↥(adjoin k (⋃ i, range (t i))))
        {u : μ → K | F.IsAdmissible a a' u} ∧
      IsConstructibleOver (↥(adjoin k (⋃ i, range (t i))))
        {u : μ → K | ∃ hu : F.IsAdmissible a a' u,
          Germ.IsInvertible (F.parameterGerm hu)} := by
  obtain ⟨t, ht, hind, hindM⟩ := exists_fresh_genericSamples M hM a' (2 * Fintype.card μ + 1)
  exact ⟨t, hindM, F.isConstructibleOver_admissible a a' hdim t ht hind (by simp),
    F.isConstructibleOver_invertibleAdmissible a a' hdim t ht hind (by simp)⟩

end

end GroupConfig
