/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.CommonSamples

/-!
# Fresh fields for word parameter relations

Supplemental `lem:adm-constructible`, the relation for a typed word of actual
quasi-rational families. The samples for each letter are chosen over the
closure of the prescribed small field and all preceding samples. Source and
target samples for the final generic quantifiers are then chosen jointly over
the same enlarged field. One finite set, fresh from the prescribed field,
therefore serves the entire word relation.

**Status:** every finite typed word has a fresh sampling field, and the literal
word-to-parameter-germ relation is constructible over such a field. Every factor,
including a forward factor, must be invertibly admissible; the target expression
must be admissible. `FamilySamples` supplies one fresh field for finitely many distinct
relations, including every declared expression family. `CanonicalPresentation` constructs
the actual group and homogeneous-space presentations.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u₁ u₂ u₃ v

variable {k : Type u₁} {K : Type u₂} [Field k] [Field K] [Algebra k K]

/-- Enlarging the field preserves its generic samples. Consumer: word sampling. -/
theorem HasGenericSamples.mono {L L' : IntermediateField k K} (h : L ≤ L')
    {ι : Type*} {a : ι → K} {N : ℕ} (ha : HasGenericSamples L a N) :
    HasGenericSamples L' a N := by
  obtain ⟨n, t, ht, hr, hn, htL⟩ := ha
  exact ⟨n, t, ht, hr, hn, fun i ↦ (htL i).trans h⟩

variable {P : Type u₃} {ι : Type v} {a : ι → K}

/-- Enlarging the field preserves the samples of every letter. -/
theorem Word.HasSamples.mono {L L' : IntermediateField k K} (h : L ≤ L')
    {κ : Type v} {b : κ → K} {w : Word k P a b} (hw : w.HasSamples L) :
    w.HasSamples L' := by
  induction w with
  | nil => trivial
  | fwd w c F ρ hdim ih => exact ⟨ih hw.1, hw.2.mono h⟩
  | inv w c F ρ hdim ih => exact ⟨ih hw.1, hw.2.mono h⟩

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]

/-- The samples needed by every letter of a finite typed word can be chosen
jointly fresh from any prescribed small field. -/
theorem Word.exists_fresh_samples {κ : Type v} {b : κ → K} (w : Word k P a b)
    (M : IntermediateField k K) (hM : IsSmall k (M : Set K)) :
    ∃ S : Set K, S.Finite ∧ IndepOver k ∅ S (M : Set K) ∧
      w.HasSamples (adjoin k S) := by
  classical
  -- Both kinds of letter use the same fresh-extension step; only the locus differs.
  have extend {τ : Type v} [Finite τ] (c : τ → K) (N : ℕ) (S : Set K)
      (hS : S.Finite) (hfresh : IndepOver k ∅ S (M : Set K)) :
      ∃ S' : Set K, S'.Finite ∧ S ⊆ S' ∧ IndepOver k ∅ S' (M : Set K) ∧
        HasGenericSamples (adjoin k S') c N := by
    have hN : IsSmall k ((racl k ((M : Set K) ∪ S) : IntermediateField k K) : Set K) :=
      (hM.union (IsSmall.of_finite hS)).racl
    obtain ⟨t, ht, hr, htfresh⟩ := exists_fresh_genericSamples _ hN c (2 * N + 1)
    let T : Set K := ⋃ i, range (t i)
    have hT : T.Finite := finite_iUnion fun i ↦ finite_range (t i)
    have htSM : IndepOver k ∅ T (S ∪ (M : Set K)) := by
      rw [union_comm]
      exact htfresh.mono_right (subset_racl k _)
    refine ⟨S ∪ T, hS.union hT, subset_union_left, ?_, ?_⟩
    · simpa only [union_comm] using hfresh.union_left htSM
    · exact ⟨_, t, ht, hr, le_rfl, fun i ↦
        (subset_iUnion (fun j ↦ range (t j)) i).trans
          (subset_union_right.trans (subset_adjoin k _))⟩
  induction w with
  | nil =>
    refine ⟨∅, finite_empty, ?_, trivial⟩
    intro s hs _
    obtain rfl : s = ∅ := subset_empty_iff.1 hs
    simp only [erk_empty]
  | @fwd κ τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨S, hS, hfresh, hw⟩ := ih
    obtain ⟨S', hS', hSS', hfresh', hc⟩ := extend c (Fintype.card μ) S hS hfresh
    exact ⟨S', hS', hfresh', hw.mono (adjoin.mono k _ _ hSS'), hc⟩
  | @inv κ τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨S, hS, hfresh, hw⟩ := ih
    obtain ⟨S', hS', hSS', hfresh', hb⟩ := extend b (Fintype.card μ) S hS hfresh
    exact ⟨S', hS', hfresh', hw.mono (adjoin.mono k _ _ hSS'), hb⟩

variable [Finite ι]

/-- One fresh field supplies all samples for a word and the further
source and target quantifiers in its parameter-germ equality relation. -/
theorem Word.exists_fresh_samples_with {κ : Type v} [Finite κ] {b : κ → K}
    (w : Word k P a b) (N N' : ℕ) (M : IntermediateField k K)
    (hM : IsSmall k (M : Set K)) :
    ∃ S : Set K, S.Finite ∧ IndepOver k ∅ S (M : Set K) ∧
      w.HasSamples (adjoin k S) ∧ HasGenericSamples (adjoin k S) a N ∧
      HasGenericSamples (adjoin k S) b N' := by
  obtain ⟨S, hS, hfresh, hw⟩ := w.exists_fresh_samples M hM
  have hN : IsSmall k ((racl k ((M : Set K) ∪ S) : IntermediateField k K) : Set K) :=
    (hM.union (IsSmall.of_finite hS)).racl
  obtain ⟨t, s, ht, hrt, hs, hrs, -, htsfresh⟩ := exists_joint_fresh_genericSamples
    _ hN a b (2 * N + 1) (2 * N' + 1)
  let T : Set K := (⋃ i, range (t i)) ∪ ⋃ i, range (s i)
  have hT : T.Finite :=
    (finite_iUnion fun i ↦ finite_range (t i)).union
      (finite_iUnion fun i ↦ finite_range (s i))
  have htSM : IndepOver k ∅ T (S ∪ (M : Set K)) := by
    rw [union_comm]
    exact htsfresh.mono_right (subset_racl k _)
  refine ⟨S ∪ T, hS.union hT, ?_, hw.mono (adjoin.mono k _ _ subset_union_left), ?_, ?_⟩
  · simpa only [union_comm] using hfresh.union_left htSM
  · refine ⟨_, t, ht, hrt, le_rfl, fun i ↦ ?_⟩
    exact (subset_iUnion (fun j ↦ range (t j)) i).trans
      (subset_union_left.trans (subset_union_right.trans (subset_adjoin k _)))
  · refine ⟨_, s, hs, hrs, le_rfl, fun i ↦ ?_⟩
    exact (subset_iUnion (fun j ↦ range (s j)) i).trans
      (subset_union_right.trans (subset_union_right.trans (subset_adjoin k _)))

/-- The literal typed-word parameter relation is constructible over a finite
field of samples chosen independently from any prescribed small field. All
letters are required to be invertibly admissible, including forward letters. -/
theorem Word.exists_fresh_constructible_eq_parameterGerm [Finite P]
    {κ : Type v} [Finite κ] {b : κ → K} (w : Word k P a b)
    {μ' : Type v} [Finite μ'] (F' : QuasiRational k (μ' ⊕ ι) κ) (ρ' : μ' → P)
    (hdim' : erk k ∅ (range a) = erk k ∅ (range b))
    (M : IntermediateField k K) (hM : IsSmall k (M : Set K)) :
    ∃ S : Set K, S.Finite ∧ IndepOver k ∅ S (M : Set K) ∧
      IsConstructibleOver (↥(adjoin k S)) {u : P → K | w.IsInvertiblyAdmissible u ∧
        ∃ hu' : F'.IsAdmissible a b (u ∘ ρ'), w.IsGerm u (F'.parameterGerm hu')} := by
  classical
  let _ := Fintype.ofFinite P
  let _ := Fintype.ofFinite μ'
  obtain ⟨S, hS, hfresh, hw, ha, hb⟩ :=
    w.exists_fresh_samples_with (Fintype.card P) (Fintype.card μ') M hM
  exact ⟨S, hS, hfresh, w.isConstructibleOver_eq_parameterGerm F' ρ' hdim' hw hb ha⟩

end

end GroupConfig
