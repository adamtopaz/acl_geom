/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.FreshSamples

/-!
# Joint fresh samples of two loci

The first sentence of supplemental `lem:adm-constructible` needs generic
samples from both the source and target loci, jointly independent from an
arbitrary prescribed small field. Choose the second family over the closure
of that field and the first family. The rank independence calculus gives
both cross-independence and freshness of the combined tuple.

**Status:** joint fresh sampling is proved. Its named consumer is the common
field for admissibility, invertibility and germ equality in
`GroupConfig.Constructible.CommonSamples`.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K ι κ : Type*} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] [Finite κ]

/-- Joint fresh sampling for the two source loci of admissibility and germ
equality. Named consumer: one field of samples for all three parameter relations. -/
theorem exists_joint_fresh_genericSamples (M : IntermediateField k K)
    (hM : IsSmall k (M : Set K)) (a : ι → K) (b : κ → K) (n m : ℕ) :
    ∃ (t : Fin n → ι → K) (s : Fin m → κ → K),
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) a (t i)) ∧
      erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
        ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)) ∧
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) b (s i)) ∧
      erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (s i)) =
        ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (s i)) ∧
      IndepOver k (M : Set K) (⋃ i, range (t i)) (⋃ i, range (s i)) ∧
      IndepOver k ∅ ((⋃ i, range (t i)) ∪ ⋃ i, range (s i)) (M : Set K) := by
  obtain ⟨t, ht, hrt, htM⟩ := exists_fresh_genericSamples M hM a n
  let T : Set K := ⋃ i, range (t i)
  have hT : T.Finite := finite_iUnion fun i ↦ finite_range (t i)
  have hMT : IsSmall k ((racl k ((M : Set K) ∪ T) : IntermediateField k K) : Set K) :=
    (hM.union (IsSmall.of_finite hT)).racl
  obtain ⟨s, hs, hrs, hsMT⟩ := exists_fresh_genericSamples _ hMT b m
  have hsMT' : IndepOver k ∅ (⋃ i, range (s i)) ((M : Set K) ∪ T) :=
    hsMT.mono_right (subset_racl k _)
  have hsTM : IndepOver k ∅ (⋃ i, range (s i)) (T ∪ (M : Set K)) := by
    rwa [union_comm] at hsMT'
  have hcross : IndepOver k (M : Set K) T (⋃ i, range (s i)) := by
    have h := (indepOver_union_right_iff.1 hsMT').2
    rw [empty_union] at h
    exact h.symm
  have hfresh : IndepOver k ∅ (M : Set K) (T ∪ ⋃ i, range (s i)) := by
    refine indepOver_union_right_iff.2 ⟨htM.symm, ?_⟩
    rw [empty_union]
    have h := (indepOver_union_right_iff.1 hsTM).2
    rw [empty_union] at h
    exact h.symm
  exact ⟨t, s, ht, hrt, hs, hrs, hcross, hfresh.symm⟩

end

end GroupConfig
