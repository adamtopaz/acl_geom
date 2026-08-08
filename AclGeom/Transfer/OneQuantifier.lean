/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Transfer.FiniteUnion
import AclGeom.Transfer.Intersections

/-!
# The specialized one-quantifier transfer

Gismatullin's transfer (blueprint Thm one-quantifier-transfer, main case):
a Boolean combination of closure-membership conditions with finite
parameters from `K₁` — in disjunctive normal form, a conjunction of
memberships `z ∈ racl k (Aᵢ)` and non-memberships `z ∉ racl k (Bⱼ)` —
has a witness in `K₁` iff it has one in `K₂ ≥ K₁`.

The proof is Boolean assembly of the three transfer bricks: the
intersection of the `racl k (Aᵢ)` is a single finitely generated closure
`racl k C` (iterating `exists_finite_inter_generator`), each excluded
closure traces on it as `racl k (Cⱼ)`, a witness exists in `K` exactly
when the subfield `racl k C ⊓ K` is not covered by the finitely many
subfields `racl k (Cⱼ) ⊓ K` (relative no-field-cover), and each
covering equality transfers between `K₁` and `K₂` by the
strict-inclusion transfer.

As long as at least one membership conjunct is present, *no
transcendence-degree hypothesis is needed* — blueprint hypothesis (9.4)
enters only the degenerate case with no `Aᵢ`, deferred to the descent
milestone where its trdeg interface lives.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M5, checklist T3): main case complete; the
no-membership-conjunct case (9.4) pending.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Iterated finite-intersection generator (blueprint Lemma
finite-intersection-generator, applied along a nonempty finite family):
the intersection of the closures of finitely many finite subsets of `K₁`
is the closure of a single finite subset of `K₁`, in membership form. -/
theorem exists_finite_iInter_generator [IsAlgClosed Ω]
    {K₁ : IntermediateField k Ω} {m : ℕ} {A : Fin (m + 1) → Set Ω}
    (hAfin : ∀ i, (A i).Finite) (hA : ∀ i, A i ⊆ (K₁ : Set Ω)) :
    ∃ C : Set Ω, C.Finite ∧ C ⊆ (K₁ : Set Ω) ∧
      ∀ z : Ω, z ∈ racl k C ↔ ∀ i, z ∈ racl k (A i) := by
  induction m with
  | zero =>
    exact ⟨A 0, hAfin 0, hA 0, fun z ↦
      ⟨fun h i ↦ Fin.fin_one_eq_zero i ▸ h, fun h ↦ h 0⟩⟩
  | succ m ih =>
    obtain ⟨C, hCfin, hCK, hC⟩ := ih (A := fun i ↦ A i.succ)
      (fun i ↦ hAfin i.succ) (fun i ↦ hA i.succ)
    obtain ⟨D, hDfin, hDK, hD⟩ :=
      exists_finite_inter_generator (hAfin 0) (hA 0) hCK
    refine ⟨D, hDfin, hDK, fun z ↦ ?_⟩
    rw [Fin.forall_fin_succ, ← hD]
    rw [show (∀ i : Fin (m + 1), z ∈ racl k (A i.succ)) ↔ z ∈ racl k C
      from (hC z).symm]
    exact mem_inf

/-- **Specialized one-quantifier transfer** (blueprint Theorem
one-quantifier-transfer, main case — at least one membership conjunct):
for finite `Aᵢ ⊆ K₁` and arbitrary `Bⱼ ⊆ K₁`, the conjunction
`⋀ᵢ z ∈ racl k (Aᵢ) ∧ ⋀ⱼ z ∉ racl k (Bⱼ)` has a witness `z ∈ K₁` iff it
has a witness `z ∈ K₂`. No transcendence-degree hypothesis is required in
this case. -/
theorem one_quantifier_transfer [IsAlgClosed Ω]
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    {m n : ℕ} {A : Fin (m + 1) → Set Ω} {B : Fin n → Set Ω}
    (hAfin : ∀ i, (A i).Finite) (hA : ∀ i, A i ⊆ (K₁ : Set Ω))
    (hB : ∀ j, B j ⊆ (K₁ : Set Ω)) :
    (∃ z, z ∈ K₁ ∧ (∀ i, z ∈ racl k (A i)) ∧ ∀ j, z ∉ racl k (B j)) ↔
      (∃ z, z ∈ K₂ ∧ (∀ i, z ∈ racl k (A i)) ∧ ∀ j, z ∉ racl k (B j)) := by
  classical
  obtain ⟨C, hCfin, hCK, hC⟩ := exists_finite_iInter_generator hAfin hA
  -- Trace each excluded closure on `racl k C`.
  choose Cj hCjfin hCjK hCjeq using fun j ↦
    exists_finite_inter_generator (B := B j) hCfin hCK (hB j)
  have hCjle : ∀ j, racl k (Cj j) ≤ racl k C := fun j ↦ by
    rw [← hCjeq j]
    exact inf_le_left
  -- Witnesses in `K` are exactly failures of the finite subfield cover.
  have hq : ∀ K : IntermediateField k Ω,
      (∃ z, z ∈ K ∧ (∀ i, z ∈ racl k (A i)) ∧ ∀ j, z ∉ racl k (B j)) ↔
        ¬ ((racl k C ⊓ K : IntermediateField k Ω) : Set Ω) ⊆
          ⋃ j, ((racl k (Cj j) ⊓ K : IntermediateField k Ω) : Set Ω) := by
    intro K
    constructor
    · rintro ⟨z, hzK, hzA, hzB⟩ hcov
      have hzC : z ∈ racl k C := (hC z).2 hzA
      have hzCK : z ∈ ((racl k C ⊓ K : IntermediateField k Ω) : Set Ω) :=
        mem_inf.2 ⟨hzC, hzK⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hzCK)
      have h1 : z ∈ racl k (Cj j) := (mem_inf.1 hj).1
      rw [← hCjeq j] at h1
      exact hzB j (mem_inf.1 h1).2
    · intro hncov
      obtain ⟨z, hzCK, hznot⟩ := Set.not_subset.1 hncov
      have hzC : z ∈ racl k C := (mem_inf.1 hzCK).1
      have hzK : z ∈ K := (mem_inf.1 hzCK).2
      refine ⟨z, hzK, (hC z).1 hzC, fun j hzB ↦ ?_⟩
      refine hznot (Set.mem_iUnion.2 ⟨j, ?_⟩)
      have h1 : z ∈ racl k C ⊓ racl k (B j) := mem_inf.2 ⟨hzC, hzB⟩
      rw [hCjeq j] at h1
      exact mem_inf.2 ⟨h1, hzK⟩
  -- The cover happens exactly when some traced inclusion is an equality.
  have hcover_iff : ∀ K : IntermediateField k Ω,
      (((racl k C ⊓ K : IntermediateField k Ω) : Set Ω) ⊆
          ⋃ j, ((racl k (Cj j) ⊓ K : IntermediateField k Ω) : Set Ω)) ↔
        ∃ j, racl k (Cj j) ⊓ K = racl k C ⊓ K := by
    intro K
    constructor
    · intro hcov
      exact exists_intermediateField_eq_of_subset_iUnion
        (fun j ↦ inf_le_inf_right K (hCjle j)) hcov
    · rintro ⟨j, hj⟩ x hx
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      rw [hj]
      exact hx
  -- Assemble: each equality transfers by the strict-inclusion transfer.
  rw [hq K₁, hq K₂, hcover_iff K₁, hcover_iff K₂]
  refine not_congr (exists_congr fun j ↦ ?_)
  have h₁ : racl k (Cj j) ⊓ K₁ = racl k C ⊓ K₁ ↔
      ¬ racl k (Cj j) ⊓ K₁ < racl k C ⊓ K₁ := by
    rw [(inf_le_inf_right K₁ (hCjle j)).lt_iff_ne, not_ne_iff]
  have h₂ : racl k (Cj j) ⊓ K₂ = racl k C ⊓ K₂ ↔
      ¬ racl k (Cj j) ⊓ K₂ < racl k C ⊓ K₂ := by
    rw [(inf_le_inf_right K₂ (hCjle j)).lt_iff_ne, not_ne_iff]
  rw [h₁, h₂, inf_lt_inf_iff_of_le hK hCK (hCjle j)]

end

end AclGeom
