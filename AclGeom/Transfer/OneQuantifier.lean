/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Transfer.FiniteUnion
import AclGeom.Transfer.Intersections
import AclGeom.Transfer.Transcendence

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

**Status:** complete (M5, checklist T3): both the main case and the two
branches of the no-membership case in blueprint hypothesis (9.4) are proved.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Equal finite transcendence degree for nested subfields produces one
finite parameter set in the smaller field whose relative algebraic closure
contains both fields.  This is the finite branch of blueprint hypothesis
(9.4), packaged in the exact form needed by the no-membership transfer. -/
theorem exists_finite_racl_envelope_of_trdeg_eq
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    (htr : Algebra.trdeg k (↥K₁) = Algebra.trdeg k (↥K₂))
    (hfin : Algebra.trdeg k (↥K₁) < Cardinal.aleph0) :
    ∃ C : Set Ω, C.Finite ∧ C ⊆ (K₁ : Set Ω) ∧
      (∀ z : Ω, z ∈ K₁ → z ∈ racl k C) ∧
      ∀ z : Ω, z ∈ K₂ → z ∈ racl k C := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (↥K₁)
  have hsfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.1 <| by
    rw [hs.cardinalMk_eq_trdeg]
    exact hfin
  let incl : (↥K₁) →ₐ[k] (↥K₂) := IntermediateField.inclusion hK
  let f : s → (↥K₂) := incl ∘ ((↑) : s → (↥K₁))
  have hf : AlgebraicIndependent k f := by
    exact hs.1.map' incl.injective
  have hfin₂ : Algebra.trdeg k (↥K₂) < Cardinal.aleph0 := by
    rwa [← htr]
  have hcard : Algebra.trdeg k (↥K₂) ≤ Cardinal.mk s := by
    rw [hs.cardinalMk_eq_trdeg, htr]
  have hs₂ : IsTranscendenceBasis k f :=
    hf.isTranscendenceBasis_of_trdeg_le hfin₂ hcard
  let C : Set Ω := (K₁.val : (↥K₁) → Ω) '' s
  refine ⟨C, hsfin.image _, ?_, ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    exact x.2
  · intro z hz
    let z₁ : ↥K₁ := ⟨z, hz⟩
    have hz₁ : z₁ ∈ racl k (Set.range ((↑) : s → (↥K₁))) :=
      (mem_racl_iff_isAlgebraic_adjoin
        (k := k) (S := Set.range ((↑) : s → (↥K₁))) (x := z₁)).2
        (hs.isAlgebraic.isAlgebraic z₁)
    have hzΩ := (algHom_mem_racl_image_iff K₁.val).2 hz₁
    simpa [C, Set.range_comp] using hzΩ
  · intro z hz
    let z₂ : ↥K₂ := ⟨z, hz⟩
    have hz₂ : z₂ ∈ racl k (Set.range f) :=
      (mem_racl_iff_isAlgebraic_adjoin
        (k := k) (S := Set.range f) (x := z₂)).2
        (hs₂.isAlgebraic.isAlgebraic z₂)
    have hzΩ := (algHom_mem_racl_image_iff K₂.val).2 hz₂
    have hset : (K₂.val : (↥K₂) → Ω) '' Set.range f = C := by
      ext y
      constructor
      · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.1, i.2, rfl⟩
      · rintro ⟨x, hxs, rfl⟩
        exact ⟨⟨x, hK x.2⟩, ⟨⟨x, hxs⟩, rfl⟩, rfl⟩
    rwa [hset] at hzΩ

/-- The no-membership transfer when both nested fields lie in the relative
algebraic closure of one parameter set from the smaller field.  The proof is
the same finite-subfield-cover argument as the main case, now with the
envelope standing in for the absent positive membership conjunct. -/
theorem one_quantifier_transfer_no_membership_of_envelope [IsAlgClosed Ω]
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    {n : ℕ} {B : Fin n → Set Ω} (hB : ∀ j, B j ⊆ (K₁ : Set Ω))
    {C : Set Ω} (hC : C ⊆ (K₁ : Set Ω))
    (hspan₁ : ∀ z : Ω, z ∈ K₁ → z ∈ racl k C)
    (hspan₂ : ∀ z : Ω, z ∈ K₂ → z ∈ racl k C) :
    (∃ z, z ∈ K₁ ∧ ∀ j, z ∉ racl k (B j)) ↔
      ∃ z, z ∈ K₂ ∧ ∀ j, z ∉ racl k (B j) := by
  classical
  have hBC : ∀ j, racl k (B j) ≤ racl k C := fun j ↦
    racl_le_of_subset_racl fun b hb ↦ hspan₁ b (hB j hb)
  have hCK₁ : racl k C ⊓ K₁ = K₁ :=
    le_antisymm inf_le_right fun z hz ↦ ⟨hspan₁ z hz, hz⟩
  have hCK₂ : racl k C ⊓ K₂ = K₂ :=
    le_antisymm inf_le_right fun z hz ↦ ⟨hspan₂ z hz, hz⟩
  have hq : ∀ K : IntermediateField k Ω,
      (∃ z, z ∈ K ∧ ∀ j, z ∉ racl k (B j)) ↔
        ¬ ((K : IntermediateField k Ω) : Set Ω) ⊆
          ⋃ j, ((racl k (B j) ⊓ K : IntermediateField k Ω) : Set Ω) := by
    intro K
    constructor
    · rintro ⟨z, hzK, hzB⟩ hcov
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hzK)
      exact hzB j (mem_inf.1 hj).1
    · intro hncov
      obtain ⟨z, hzK, hznot⟩ := Set.not_subset.1 hncov
      refine ⟨z, hzK, fun j hzB ↦ hznot ?_⟩
      exact Set.mem_iUnion.2 ⟨j, mem_inf.2 ⟨hzB, hzK⟩⟩
  have hcover₁ :
      (((K₁ : IntermediateField k Ω) : Set Ω) ⊆
          ⋃ j, ((racl k (B j) ⊓ K₁ : IntermediateField k Ω) : Set Ω)) ↔
        ∃ j, racl k (B j) ⊓ K₁ = racl k C ⊓ K₁ := by
    rw [hCK₁]
    constructor
    · exact exists_intermediateField_eq_of_subset_iUnion
        (fun j ↦ inf_le_right)
    · rintro ⟨j, hj⟩ x hx
      exact Set.mem_iUnion.2 ⟨j, hj.symm ▸ hx⟩
  have hcover₂ :
      (((K₂ : IntermediateField k Ω) : Set Ω) ⊆
          ⋃ j, ((racl k (B j) ⊓ K₂ : IntermediateField k Ω) : Set Ω)) ↔
        ∃ j, racl k (B j) ⊓ K₂ = racl k C ⊓ K₂ := by
    rw [hCK₂]
    constructor
    · exact exists_intermediateField_eq_of_subset_iUnion
        (fun j ↦ inf_le_right)
    · rintro ⟨j, hj⟩ x hx
      exact Set.mem_iUnion.2 ⟨j, hj.symm ▸ hx⟩
  rw [hq K₁, hq K₂, hcover₁, hcover₂]
  refine not_congr (exists_congr fun j ↦ ?_)
  have h₁ : racl k (B j) ⊓ K₁ = racl k C ⊓ K₁ ↔
      ¬ racl k (B j) ⊓ K₁ < racl k C ⊓ K₁ := by
    rw [(inf_le_inf_right K₁ (hBC j)).lt_iff_ne, not_ne_iff]
  have h₂ : racl k (B j) ⊓ K₂ = racl k C ⊓ K₂ ↔
      ¬ racl k (B j) ⊓ K₂ < racl k C ⊓ K₂ := by
    rw [(inf_le_inf_right K₂ (hBC j)).lt_iff_ne, not_ne_iff]
  rw [h₁, h₂, inf_lt_inf_iff_of_le hK hC (hBC j)]

/-- The finite-transcendence-degree branch of the no-membership case of
blueprint Theorem 9.4. -/
theorem one_quantifier_transfer_no_membership_finite [IsAlgClosed Ω]
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    (htr : Algebra.trdeg k (↥K₁) = Algebra.trdeg k (↥K₂))
    (hfin : Algebra.trdeg k (↥K₁) < Cardinal.aleph0)
    {n : ℕ} {B : Fin n → Set Ω} (hB : ∀ j, B j ⊆ (K₁ : Set Ω)) :
    (∃ z, z ∈ K₁ ∧ ∀ j, z ∉ racl k (B j)) ↔
      ∃ z, z ∈ K₂ ∧ ∀ j, z ∉ racl k (B j) := by
  obtain ⟨C, -, hC, hspan₁, hspan₂⟩ :=
    exists_finite_racl_envelope_of_trdeg_eq hK htr hfin
  exact one_quantifier_transfer_no_membership_of_envelope
    hK hB hC hspan₁ hspan₂

/-- In a field of infinite transcendence degree, finitely many relative
algebraic closures of finite parameter sets miss a common element. -/
theorem exists_avoid_finite_racl_of_aleph0_le_trdeg
    {K : Type*} [Field K] [Algebra k K]
    (htr : Cardinal.aleph0 ≤ Algebra.trdeg k K)
    {n : ℕ} {B : Fin n → Set K} (hBfin : ∀ j, (B j).Finite) :
    ∃ z : K, ∀ j, z ∉ racl k (B j) := by
  classical
  let E : Fin n → Subfield K := fun j ↦ (racl k (B j)).toSubfield
  have hE : ∀ j, E j ≠ ⊤ := by
    intro j htop
    obtain ⟨z, hz⟩ := exists_notMem_racl_of_mk_lt_trdeg (B j)
      ((hBfin j).lt_aleph0.trans_le htr)
    apply hz
    have hzE : z ∈ E j := by rw [htop]; exact Set.mem_univ z
    exact hzE
  obtain ⟨z, hz⟩ := exists_notMem_of_ne_top E hE
  exact ⟨z, fun j hj ↦ hz j hj⟩

/-- Ambient form of infinite-transcendence avoidance for a subfield of the
fixed algebraically closed overfield. -/
theorem exists_avoid_finite_racl_in_intermediateField
    {K : IntermediateField k Ω}
    (htr : Cardinal.aleph0 ≤ Algebra.trdeg k (↥K))
    {n : ℕ} {B : Fin n → Set Ω} (hBfin : ∀ j, (B j).Finite)
    (hB : ∀ j, B j ⊆ (K : Set Ω)) :
    ∃ z : Ω, z ∈ K ∧ ∀ j, z ∉ racl k (B j) := by
  classical
  let BK : Fin n → Set (↥K) := fun j ↦ K.val ⁻¹' B j
  have hBKfin : ∀ j, (BK j).Finite := fun j ↦
    (hBfin j).preimage K.val.injective.injOn
  obtain ⟨z, hz⟩ :=
    exists_avoid_finite_racl_of_aleph0_le_trdeg htr hBKfin
  refine ⟨z, z.2, fun j hj ↦ hz j ?_⟩
  have himage : (K.val : (↥K) → Ω) '' BK j = B j := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hB j hy⟩, hy, rfl⟩
  have hj' := (algHom_mem_racl_image_iff K.val).1
    (show K.val z ∈ racl k (K.val '' BK j) by rwa [himage])
  exact hj'

/-- The infinite-transcendence-degree branch of the no-membership case of
blueprint Theorem 9.4. -/
theorem one_quantifier_transfer_no_membership_infinite [IsAlgClosed Ω]
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    (htr₁ : Cardinal.aleph0 ≤ Algebra.trdeg k (↥K₁))
    (htr₂ : Cardinal.aleph0 ≤ Algebra.trdeg k (↥K₂))
    {n : ℕ} {B : Fin n → Set Ω} (hBfin : ∀ j, (B j).Finite)
    (hB : ∀ j, B j ⊆ (K₁ : Set Ω)) :
    (∃ z, z ∈ K₁ ∧ ∀ j, z ∉ racl k (B j)) ↔
      ∃ z, z ∈ K₂ ∧ ∀ j, z ∉ racl k (B j) := by
  have hB₂ : ∀ j, B j ⊆ (K₂ : Set Ω) := fun j ↦ (hB j).trans hK
  exact iff_of_true
    (exists_avoid_finite_racl_in_intermediateField htr₁ hBfin hB)
    (exists_avoid_finite_racl_in_intermediateField htr₂ hBfin hB₂)

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

/-- **Full specialized one-quantifier transfer** (blueprint Theorem 9.4).
The positive-membership case needs no transcendence-degree assumption; if
there is no positive conjunct, the stated profile is exactly the blueprint's
alternative: equal finite transcendence degrees or two infinite ones. -/
theorem one_quantifier_transfer_full [IsAlgClosed Ω]
    {K₁ K₂ : IntermediateField k Ω} (hK : K₁ ≤ K₂)
    {m n : ℕ} {A : Fin m → Set Ω} {B : Fin n → Set Ω}
    (hAfin : ∀ i, (A i).Finite) (hA : ∀ i, A i ⊆ (K₁ : Set Ω))
    (hBfin : ∀ j, (B j).Finite) (hB : ∀ j, B j ⊆ (K₁ : Set Ω))
    (hprofile :
      (Algebra.trdeg k (↥K₁) = Algebra.trdeg k (↥K₂) ∧
        Algebra.trdeg k (↥K₁) < Cardinal.aleph0) ∨
      (Cardinal.aleph0 ≤ Algebra.trdeg k (↥K₁) ∧
        Cardinal.aleph0 ≤ Algebra.trdeg k (↥K₂))) :
    (∃ z, z ∈ K₁ ∧ (∀ i, z ∈ racl k (A i)) ∧
        ∀ j, z ∉ racl k (B j)) ↔
      ∃ z, z ∈ K₂ ∧ (∀ i, z ∈ racl k (A i)) ∧
        ∀ j, z ∉ racl k (B j) := by
  cases m with
  | zero =>
      have hnone :
          (∃ z, z ∈ K₁ ∧ ∀ j, z ∉ racl k (B j)) ↔
            ∃ z, z ∈ K₂ ∧ ∀ j, z ∉ racl k (B j) := by
        rcases hprofile with ⟨htr, hfin⟩ | ⟨htr₁, htr₂⟩
        · exact one_quantifier_transfer_no_membership_finite hK htr hfin hB
        · exact one_quantifier_transfer_no_membership_infinite
            hK htr₁ htr₂ hBfin hB
      simpa using hnone
  | succ m =>
      exact one_quantifier_transfer hK hAfin hA hB

end

end AclGeom
