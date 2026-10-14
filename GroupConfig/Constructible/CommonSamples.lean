/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.JointSamples
import GroupConfig.Constructible.AdmissibleWords

/-!
# One fresh sampling field for parameter relations

For an actual quasi-rational family between loci of equal dimension, one
finite tuple of generic samples, independent from any prescribed small
field, makes Adm, Adm× and equality of parameter germs constructible over
the field it generates. Source-locus samples serve the generic quantifier
for equality; target-locus samples serve admissibility and invertibility.

**Status:** the first sentence of supplemental `lem:adm-constructible` is
proved. A common fresh field for arbitrary finite word relations and the
constructible group remain obligations.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {μ ι κ : Type w}
  [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] [Fintype μ] [Finite ι] [Finite κ]

/-- One jointly fresh sampling field serves admissibility, invertible
admissibility and equality of the actual parameter germs. This is the first
sentence of supplemental `lem:adm-constructible`. -/
theorem QuasiRational.exists_fresh_constructible_parameterRelations
    (F : QuasiRational k (μ ⊕ ι) κ) (a : ι → K) (b : κ → K)
    (hdim : erk k ∅ (range a) = erk k ∅ (range b))
    (M : IntermediateField k K) (hM : IsSmall k (M : Set K)) :
    ∃ (t : Fin (2 * Fintype.card (μ ⊕ μ) + 1) → ι → K)
      (s : Fin (2 * Fintype.card (μ ⊕ μ) + 1) → κ → K),
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) a (t i)) ∧
      erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
        ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)) ∧
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) b (s i)) ∧
      erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (s i)) =
        ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (s i)) ∧
      IndepOver k (M : Set K) (⋃ i, range (t i)) (⋃ i, range (s i)) ∧
      IndepOver k ∅ ((⋃ i, range (t i)) ∪ ⋃ i, range (s i)) (M : Set K) ∧
      IsConstructibleOver (↥(adjoin k ((⋃ i, range (t i)) ∪ ⋃ i, range (s i))))
        {u : μ → K | F.IsAdmissible a b u} ∧
      IsConstructibleOver (↥(adjoin k ((⋃ i, range (t i)) ∪ ⋃ i, range (s i))))
        {u : μ → K | ∃ hu : F.IsAdmissible a b u,
        Germ.IsInvertible (F.parameterGerm hu)} ∧
      IsConstructibleOver (↥(adjoin k ((⋃ i, range (t i)) ∪ ⋃ i, range (s i))))
        {v : (μ ⊕ μ) → K |
        ∃ (hu : F.IsAdmissible a b (v ∘ Sum.inl))
          (hu' : F.IsAdmissible a b (v ∘ Sum.inr)),
          F.parameterGerm hu = F.parameterGerm hu'} := by
  classical
  let n := 2 * Fintype.card (μ ⊕ μ) + 1
  obtain ⟨t, s, ht, hrt, hs, hrs, hcross, hfresh⟩ :=
    exists_joint_fresh_genericSamples M hM a b n n
  let L := adjoin k ((⋃ i, range (t i)) ∪ ⋃ i, range (s i))
  have htL : HasGenericSamples L a (Fintype.card (μ ⊕ μ)) :=
    ⟨n, t, ht, hrt, le_rfl, fun i ↦ (subset_iUnion (fun j ↦ range (t j)) i).trans
      (subset_union_left.trans (subset_adjoin k _))⟩
  have hn : 2 * Fintype.card μ + 1 ≤ n := by
    simp only [n, Fintype.card_sum]
    omega
  have hsL : HasGenericSamples L b (Fintype.card μ) :=
    ⟨n, s, hs, hrs, hn, fun i ↦ (subset_iUnion (fun j ↦ range (s j)) i).trans
      (subset_union_right.trans (subset_adjoin k _))⟩
  have hfield : adjoin k (⋃ i, range (s i)) ≤ L :=
    adjoin_le_iff.2 (subset_union_right.trans (subset_adjoin k _))
  have hA := IsConstructibleOver.of_le_intermediateField hfield
    (F.isConstructibleOver_admissible a b hdim s hs hrs
      (by simpa only [Fintype.card_fin] using hn))
  have hI := IsConstructibleOver.of_le_intermediateField hfield
    (F.isConstructibleOver_invertibleAdmissible a b hdim s hs hrs
      (by simpa only [Fintype.card_fin] using hn))
  let w₁ : Word k (μ ⊕ μ) a b := .fwd .nil b F Sum.inl hdim
  let w₂ : Word k (μ ⊕ μ) a b := .fwd .nil b F Sum.inr hdim
  have hw₁ : w₁.HasSamples L := ⟨trivial, hsL⟩
  have hw₂ : w₂.HasSamples L := ⟨trivial, hsL⟩
  have hE := Word.isConstructibleOver_germ_eq w₁ w₂ hw₁ hw₂ htL
  refine ⟨t, s, ht, hrt, hs, hrs, hcross, hfresh, hA, hI, ?_⟩
  convert hE using 1
  ext v
  simp only [Set.mem_ofPred_eq, w₁, w₂, Word.IsGerm]
  constructor
  · rintro ⟨hu, hu', heq⟩
    refine ⟨F.parameterGerm hu, ⟨Germ.id a, hu, rfl, (Germ.comp_id _).symm⟩,
      ⟨Germ.id a, hu', rfl, ?_⟩⟩
    rw [Germ.comp_id]
    exact heq
  · rintro ⟨g, ⟨g₁, hu, rfl, h₁⟩, ⟨g₂, hu', rfl, h₂⟩⟩
    rw [Germ.comp_id] at h₁ h₂
    exact ⟨hu, hu', h₁.symm.trans h₂⟩

end

end GroupConfig
