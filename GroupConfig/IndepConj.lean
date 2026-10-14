/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.GenericSet
import Mathlib.Data.ENat.BigOperators

/-!
# Independent generic tuples are conjugate

Blueprint `sources/group_configuration/05-hrushovski-weil.tex`, `lem:indep-conj`.

Let `V₁, …, V_r` be irreducible `k`-varieties, represented by tuples `a i`. If `(y i)ᵢ` and
`(y' i)ᵢ` are two families with `y i, y' i` generic points of `V_i` over `k`, each independent
in the sense that the rank of the union is `∑ i, dim V_i`, then some automorphism of `K` over
`k` maps `y i` to `y' i` for every `i` (`exists_algEquiv_of_erk_iUnion_eq`). The same holds
over a small algebraically closed `M` for families generic and independent over `M`
(`exists_algEquiv_of_erk_iUnion_eq_of_isGenericOver`).

The proof is by induction on the set of indices, as in the blueprint. Its rank input is that a
family whose rank is additive is independent blockwise: each member is independent from the
union of finitely many others (`indepOver_biUnion_of_erk_iUnion_eq_sum`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:indep-conj` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Additive rank of a finite family -/

section Rank

variable (k) {α : Type*}

/-- The rank of a finite union is at most the sum of the ranks. -/
theorem erk_biUnion_le (C : Set K) (X : α → Set K) (s : Finset α) :
    erk k C (⋃ i ∈ s, X i) ≤ ∑ i ∈ s, erk k C (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [erk_empty]
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (erk_union_le k C _ _).trans (add_le_add le_rfl ih)

/-- If the rank of a finite family of finite sets is the sum of their ranks, so is the rank of
every subfamily. -/
theorem erk_biUnion_eq_sum [Fintype α] (C : Set K) {X : α → Set K} (hX : ∀ i, (X i).Finite)
    (h : erk k C (⋃ i, X i) = ∑ i, erk k C (X i)) (s : Finset α) :
    erk k C (⋃ i ∈ s, X i) = ∑ i ∈ s, erk k C (X i) := by
  classical
  refine le_antisymm (erk_biUnion_le k C X s) ?_
  have hsplit : (⋃ i, X i) = (⋃ i ∈ s, X i) ∪ ⋃ i ∈ sᶜ, X i := by
    rw [← Finset.set_biUnion_union, Finset.union_compl]
    simp only [Finset.mem_univ, iUnion_true]
  have hle : ∑ i ∈ s, erk k C (X i) + ∑ i ∈ sᶜ, erk k C (X i) ≤
      erk k C (⋃ i ∈ s, X i) + ∑ i ∈ sᶜ, erk k C (X i) := by
    rw [Finset.sum_add_sum_compl, ← h, hsplit]
    exact (erk_union_le k C _ _).trans (add_le_add le_rfl (erk_biUnion_le k C X sᶜ))
  exact (ENat.add_le_add_iff_right (ENat.sum_ne_top.2 fun i _ ↦ erk_ne_top k (hX i) C)).1 hle

variable {k}

/-- A finite family of finite sets with additive rank is independent blockwise: each member is
independent from the union of finitely many others. -/
theorem indepOver_biUnion_of_erk_iUnion_eq_sum [Fintype α] {C : Set K} {X : α → Set K}
    (hX : ∀ i, (X i).Finite) (h : erk k C (⋃ i, X i) = ∑ i, erk k C (X i)) {s : Finset α}
    {i₀ : α} (hi₀ : i₀ ∉ s) : IndepOver k C (X i₀) (⋃ i ∈ s, X i) := by
  classical
  have hs : (⋃ i ∈ s, X i).Finite :=
    (finite_iUnion hX).subset (iUnion₂_subset fun i _ ↦ subset_iUnion X i)
  have hadd := erk_biUnion_eq_sum k C hX h (insert i₀ s)
  rw [Finset.set_biUnion_insert, Finset.sum_insert hi₀, ← erk_biUnion_eq_sum k C hX h s,
    union_comm, add_comm] at hadd
  exact indepOver_of_erk_eq (hX i₀) (erk_base_union_eq_of_erk_union_eq k hs hadd)

end Rank

/-! ### Conjugacy of independent generic families -/

variable [IsAlgClosed K] {α : Type*} [Fintype α] {ι : α → Type*} [∀ i, Finite (ι i)]

/-- `lem:indep-conj`: two families of generic points over `k` of the same varieties, each
independent, are conjugate under an automorphism of `K` over `k`. Independence of a family
is additivity of rank: the rank of the union is the sum of the dimensions. -/
theorem exists_algEquiv_of_erk_iUnion_eq [IsAlgClosed k] [UniversalDomain k K]
    {a y y' : (i : α) → ι i → K} (hy : ∀ i, IsGen k (a i) (y i))
    (hy' : ∀ i, IsGen k (a i) (y' i))
    (hind : erk k ∅ (⋃ i, range (y i)) = ∑ i, erk k ∅ (range (a i)))
    (hind' : erk k ∅ (⋃ i, range (y' i)) = ∑ i, erk k ∅ (range (a i))) :
    ∃ σ : K ≃ₐ[k] K, ∀ i j, σ (y i j) = y' i j := by
  classical
  have hblock (z : (i : α) → ι i → K) (hz : ∀ i, IsGen k (a i) (z i))
      (hzind : erk k ∅ (⋃ i, range (z i)) = ∑ i, erk k ∅ (range (a i))) {s : Finset α}
      {i₀ : α} (hi₀ : i₀ ∉ s) : IndepOver k ∅ (range (z i₀)) (⋃ i ∈ s, range (z i)) := by
    refine indepOver_biUnion_of_erk_iUnion_eq_sum (fun i ↦ finite_range (z i)) ?_ hi₀
    rw [hzind]
    exact Finset.sum_congr rfl fun i _ ↦ (erk_empty_range_eq_of_idealOf_eq (hz i)).symm
  suffices h : ∀ s : Finset α, ∃ σ : K ≃ₐ[k] K, ∀ i ∈ s, ∀ j, σ (y i j) = y' i j by
    obtain ⟨σ, hσ⟩ := h Finset.univ
    exact ⟨σ, fun i ↦ hσ i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨AlgEquiv.refl, fun i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert i₀ s hi₀ ih =>
    obtain ⟨σ₁, hσ₁⟩ := ih
    have hB : IsSmall k (⋃ i ∈ s, range (y' i)) :=
      IsSmall.of_finite ((finite_iUnion fun i ↦ finite_range (y' i)).subset
        (iUnion₂_subset fun i _ ↦ subset_iUnion (fun i ↦ range (y' i)) i))
    have hσB : (⋃ i ∈ s, ⇑σ₁ '' range (y i)) = ⋃ i ∈ s, range (y' i) :=
      iUnion₂_congr fun i hi ↦ by
        rw [← range_comp]
        exact congrArg range (funext (hσ₁ i hi))
    -- `σ₁ (y i₀)` and `y' i₀` are generic over the closure of the points already matched.
    have h₁ : IndepOver k ∅ (range (⇑σ₁ ∘ y i₀)) (⋃ i ∈ s, range (y' i)) := by
      have h := (hblock y hy hind hi₀).image σ₁
      rwa [image_empty, ← range_comp, image_iUnion₂, hσB] at h
    obtain ⟨τ, hτ⟩ := (((hy i₀).map σ₁).isGenericOver_racl hB h₁).exists_algEquiv
      ((hy' i₀).isGenericOver_racl hB (hblock y' hy' hind' hi₀))
    refine ⟨σ₁.trans (τ.restrictScalars k), fun i hi j ↦ ?_⟩
    change τ (σ₁ (y i j)) = y' i j
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hτ j
    · rw [hσ₁ i hi j]
      exact τ.commutes ⟨y' i j, subset_racl k _ (mem_iUnion₂.2 ⟨i, hi, mem_range_self j⟩)⟩

/-- `lem:indep-conj` over a small algebraically closed field `M`: two families of generic
points over `M` of the same `k`-varieties, each independent over `M`, are conjugate under an
automorphism of `K` over `M`. -/
theorem exists_algEquiv_of_erk_iUnion_eq_of_isGenericOver [UniversalDomain k K]
    {M : IntermediateField k K} [IsAlgClosed ↥M] (hM : IsSmall k (M : Set K))
    {a y y' : (i : α) → ι i → K} (hy : ∀ i, IsGenericOver M (a i) (y i))
    (hy' : ∀ i, IsGenericOver M (a i) (y' i))
    (hind : erk k (M : Set K) (⋃ i, range (y i)) = ∑ i, erk k ∅ (range (a i)))
    (hind' : erk k (M : Set K) (⋃ i, range (y' i)) = ∑ i, erk k ∅ (range (a i))) :
    ∃ σ : K ≃ₐ[↥M] K, ∀ i j, σ (y i j) = y' i j := by
  have := universalDomain_of_isSmall M hM
  -- Work over the base `M`, with the points `y i` themselves representing the varieties.
  have hbase (X : Set K) : erk (↥M) ∅ X = erk k (M : Set K) X := by
    rw [erk_empty_eq (↥M), ← erk_coe_eq k M]
  have hrk (i : α) : erk (↥M) ∅ (range (y i)) = erk k ∅ (range (a i)) := by
    rw [hbase, (hy i).erk_coe_eq, (hy i).erk_empty_eq]
  refine exists_algEquiv_of_erk_iUnion_eq (k := ↥M) (a := y) (fun i ↦ rfl)
    (fun i ↦ (hy' i).trans (hy i).symm) ?_ ?_
  · rw [hbase, hind]
    exact Finset.sum_congr rfl fun i _ ↦ (hrk i).symm
  · rw [hbase, hind']
    exact Finset.sum_congr rfl fun i _ ↦ (hrk i).symm

end

end GroupConfig
