/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConfigurationBaseChange
import GroupConfig.DefinableClosure

/-!
# Nested base changes

Blueprint `sources/group_configuration/08-proof.tex`, the convention "over `k₁`" at the start
of the section.

The proof of the main theorem changes the base field several times, each time to the algebraic
closure of the previous base together with a finite tuple.  A base changed twice, first to
`K₀ ⊇ k` and then to `acl_{K₀}(S)`, has the same elements as `acl_k(K₀ ∪ S)`, and relative
algebraic closures, ranks, canonical bases and definable closures only depend on a base field
through its elements.  This module records these facts (`GroupConfig.mem_racl_nested`,
`GroupConfig.erk_nested`, `GroupConfig.racl_canonicalBase_nested`,
`GroupConfig.mem_dclAdjoin_congr`) and uses them to flatten a group configuration over a nested
base to one over an intermediate field of `K` over the original base
(`GroupConfiguration.ofNested`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** complete. The module holds supporting lemmas for nested bases and states no
blueprint result of its own.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

-- Keep the universe parameter order of the two closure lemmas moved from `Main`.
universe u

section ClosureEnlargement

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]
  (K₀ : IntermediateField k K)

/-- Equal closures over `K₀` after adjoining `T` give equal closures over `acl(K₀, T)`. -/
theorem racl_eq_of_racl_union_eq {A B T : Set K}
    (h : racl (↥K₀) (A ∪ T) = racl (↥K₀) (B ∪ T)) :
    racl (↥(racl k ((K₀ : Set K) ∪ T))) A = racl (↥(racl k ((K₀ : Set K) ∪ T))) B := by
  have h' := congrArg (fun F : IntermediateField (↥K₀) K ↦ (F : Set K)) h
  simp only [racl_base_coe] at h'
  refine SetLike.coe_injective ?_
  rw [racl_base_coe, racl_base_coe, racl_union_left, racl_union_left, union_assoc, union_assoc,
    union_comm T A, union_comm T B]
  exact h'

/-- Equal closures over `K₀` remain equal over `acl(K₀, T)`. -/
theorem racl_eq_of_racl_eq (T : Set K) {A B : Set K} (h : racl (↥K₀) A = racl (↥K₀) B) :
    racl (↥(racl k ((K₀ : Set K) ∪ T))) A = racl (↥(racl k ((K₀ : Set K) ∪ T))) B :=
  racl_eq_of_racl_union_eq K₀ (racl_union_congr h rfl)

end ClosureEnlargement

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Closures and independence -/

/-- Transport an equality of closures along an enlargement of the common part. -/
theorem racl_union_congr_of_subset {C C' A B : Set K} (h : racl k (C ∪ A) = racl k (C ∪ B))
    (hC : C ⊆ racl k C') : racl k (C' ∪ A) = racl k (C' ∪ B) := by
  have key : ∀ X : Set K, racl k (C' ∪ X) = racl k (C' ∪ (C ∪ X)) := fun X ↦ by
    refine le_antisymm (racl_mono (k := k) (union_subset_union_right _ subset_union_right))
      (racl_le_of_subset_racl (union_subset ?_ (union_subset ?_ ?_)))
    · exact subset_union_left.trans (subset_racl k _)
    · exact hC.trans (racl_mono (k := k) subset_union_left)
    · exact subset_union_right.trans (subset_racl k _)
  rw [key A, key B, union_comm C' (C ∪ A), union_comm C' (C ∪ B), ← racl_union_left (C ∪ A) C',
    ← racl_union_left (C ∪ B) C', h]

/-- Equalities of closures relative to `C` may be combined over unions. -/
theorem racl_union_union_congr {C A A' B B' : Set K} (hA : racl k (C ∪ A) = racl k (C ∪ A'))
    (hB : racl k (C ∪ B) = racl k (C ∪ B')) :
    racl k (C ∪ (A ∪ B)) = racl k (C ∪ (A' ∪ B')) := by
  rw [union_union_distrib_left C A B, union_union_distrib_left C A' B', ← racl_union_left (C ∪ A),
    ← racl_union_right _ (C ∪ B), hA, hB, racl_union_left, racl_union_right]

/-- Independence only depends on the closure of the base. -/
theorem indepOver_congr_base {C C' A B : Set K} (h : racl k C = racl k C') :
    IndepOver k C A B ↔ IndepOver k C' A B := by
  have key : ∀ {C C' : Set K}, racl k C = racl k C' → IndepOver k C A B → IndepOver k C' A B :=
    fun h hi a ha hfin ↦ by
      rw [← erk_congr_base k (racl_union_congr h rfl) a, ← erk_congr_base k h a]
      exact hi ha hfin
  exact ⟨key h, key h.symm⟩

/-! ### Independence up to closure -/

theorem indepOver_congr {C A A' B B' : Set K} (hA : racl k (C ∪ A) = racl k (C ∪ A'))
    (hB : racl k (C ∪ B) = racl k (C ∪ B')) : IndepOver k C A B ↔ IndepOver k C A' B' := by
  rw [indepOver_congr_left hA.symm, indepOver_comm, indepOver_congr_left hB.symm, indepOver_comm]

theorem indepOver_congr₀ {A A' B B' : Set K} (hA : racl k A = racl k A')
    (hB : racl k B = racl k B') : IndepOver k ∅ A B ↔ IndepOver k ∅ A' B' :=
  indepOver_congr (by rwa [empty_union, empty_union]) (by rwa [empty_union, empty_union])

theorem indepOver_of_subset_racl {A A' B B' : Set K} (hA : A' ⊆ racl k A) (hB : B' ⊆ racl k B)
    (h : IndepOver k ∅ A B) : IndepOver k ∅ A' B' := by
  have h1 : IndepOver k ∅ (racl k (∅ ∪ A) : Set K) (racl k (∅ ∪ B) : Set K) :=
    indepOver_racl_right_iff.2 (indepOver_racl_left_iff.2 h)
  rw [empty_union, empty_union] at h1
  exact (h1.mono_left hA).mono_right hB

theorem racl_union_eq_of_subset_racl_of_subset {C A B : Set K} (hA : A ⊆ racl k (C ∪ B))
    (hB : B ⊆ A) : racl k (C ∪ A) = racl k (C ∪ B) :=
  le_antisymm (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hA))
    (racl_mono (k := k) (union_subset_union_right _ hB))

/-! ### Nested bases -/

section Nested

variable (K₀ : IntermediateField k K) (S : Set K)

theorem coe_subset_racl_union_left : (K₀ : Set K) ⊆ racl k ((K₀ : Set K) ∪ S) :=
  subset_union_left.trans (subset_racl k _)

/-- The carrier of `K₀` lies in every field adjoined to it. -/
theorem coe_subset_adjoin (T : Set K) : (K₀ : Set K) ⊆ adjoin (↥K₀) T := fun w hw ↦
  IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : ↥K₀)

/-- Adjoining to `K₀` is adjoining to `k` together with the carrier of `K₀`. -/
theorem coe_adjoin_base (T : Set K) :
    ((adjoin (↥K₀) T : IntermediateField (↥K₀) K) : Set K) =
      ((adjoin k ((K₀ : Set K) ∪ T) : IntermediateField k K) : Set K) := by
  rw [← restrictScalars_adjoin, coe_restrictScalars]

/-- Closure over the nested base `acl_{K₀}(S)` is closure over `acl_k(K₀ ∪ S)`. -/
theorem mem_racl_nested (T : Set K) (x : K) :
    x ∈ racl (↥(racl (↥K₀) S)) T ↔ x ∈ racl (↥(racl k ((K₀ : Set K) ∪ S))) T := by
  rw [mem_racl_base_iff (racl (↥K₀) S) T x, mem_racl_base_iff K₀,
    mem_racl_base_iff (racl k ((K₀ : Set K) ∪ S)) T x, racl_base_coe K₀ S, ← union_assoc,
    union_eq_right.2 (coe_subset_racl_union_left K₀ S)]

theorem racl_nested_coe (T : Set K) :
    ((racl (↥(racl (↥K₀) S)) T : IntermediateField (↥(racl (↥K₀) S)) K) : Set K) =
      ((racl (↥(racl k ((K₀ : Set K) ∪ S))) T :
        IntermediateField (↥(racl k ((K₀ : Set K) ∪ S))) K) : Set K) :=
  Set.ext fun x ↦ mem_racl_nested K₀ S T x

/-- Rank over the nested base `acl_{K₀}(S)` is rank over `acl_k(K₀ ∪ S)`. -/
theorem erk_nested (X : Set K) :
    erk (↥(racl (↥K₀) S)) ∅ X = erk (↥(racl k ((K₀ : Set K) ∪ S))) ∅ X := by
  rw [erk_base_empty (racl (↥K₀) S), erk_base_empty (racl k ((K₀ : Set K) ∪ S)),
    ← erk_coe_union K₀, racl_base_coe K₀ S, union_eq_right.2 (coe_subset_racl_union_left K₀ S)]

theorem indepOver_nested (A B : Set K) :
    IndepOver (↥(racl (↥K₀) S)) ∅ A B ↔ IndepOver (↥(racl k ((K₀ : Set K) ∪ S))) ∅ A B := by
  rw [indepOver_base_iff (racl (↥K₀) S), indepOver_base_iff (racl k ((K₀ : Set K) ∪ S)),
    ← indepOver_coe_union_iff K₀, racl_base_coe K₀ S,
    union_eq_right.2 (coe_subset_racl_union_left K₀ S)]

variable {ι : Type*}

/-- The closure of a canonical base over the nested base `acl_{K₀}(S)`, as a closure over
`acl_k(K₀ ∪ S)`. -/
theorem racl_canonicalBase_nested [Finite ι] (P : Set K) (t : ι → K) :
    ((racl (↥(racl (↥K₀) S)) (canonicalBase (racl (↥(racl (↥K₀) S)) P) t : Set K) :
        IntermediateField (↥(racl (↥K₀) S)) K) : Set K) =
      ((racl (↥(racl k ((K₀ : Set K) ∪ S)))
          (canonicalBase (racl (↥(racl k ((K₀ : Set K) ∪ S))) P) t : Set K) :
        IntermediateField (↥(racl k ((K₀ : Set K) ∪ S))) K) : Set K) := by
  have hK₀ := coe_subset_racl_union_left K₀ S
  have hI : locusIdeal (↥(racl (↥K₀)
      (((racl (↥K₀) S : IntermediateField (↥K₀) K) : Set K) ∪ P))) t =
      locusIdeal (↥(racl k ((K₀ : Set K) ∪ S ∪ P))) t := by
    rw [locusIdeal_racl_base K₀, racl_base_coe K₀ S, ← union_assoc, union_eq_right.2 hK₀,
      racl_union_left]
  have hI' : locusIdeal (↥(racl k
      (((racl k ((K₀ : Set K) ∪ S) : IntermediateField k K) : Set K) ∪ P))) t =
      locusIdeal (↥(racl k ((K₀ : Set K) ∪ S ∪ P))) t := by
    rw [racl_union_left]
  rw [racl_canonicalBase_base (racl (↥K₀) S) P t,
    racl_canonicalBase_base (racl k ((K₀ : Set K) ∪ S)) P t]
  unfold canonicalBase
  rw [hI, hI', racl_base_coe K₀, racl_base_coe K₀ S, coe_adjoin_base K₀, ← union_assoc,
    union_eq_right.2 hK₀, racl_union_adjoin, racl_union_adjoin, ← union_assoc,
    union_eq_left.2 hK₀]

end Nested

/-! ### Definable closure over different bases -/

section Dcl

variable {k' : Type*} [Field k'] [Algebra k' K] {ι ι' : Type*}

/-- Membership in `dclAdjoin L u` only depends on the set `L ∪ range u`, whatever the base
field of `L`. -/
theorem mem_dclAdjoin_mono' {L : IntermediateField k K} {L' : IntermediateField k' K}
    {u : ι → K} {u' : ι' → K} (h : (L : Set K) ∪ range u ⊆ (L' : Set K) ∪ range u') {x : K}
    (hx : x ∈ dclAdjoin L u) : x ∈ dclAdjoin L' u' := by
  have hx' : x ∈ dcl ((adjoin (↥L) (range u)).restrictScalars k) := hx
  obtain ⟨n, hn⟩ := mem_dcl_iff.1 hx'
  change x ∈ dcl ((adjoin (↥L') (range u')).restrictScalars k')
  refine mem_dcl_iff.2 ⟨n, (mem_restrictScalars k').2 ?_⟩
  have hn' : x ^ ringExpChar K ^ n ∈ adjoin (↥L) (range u) := (mem_restrictScalars k).1 hn
  rw [← mem_toSubfield, adjoin_toSubfield, range_algebraMap_coe] at hn' ⊢
  exact Subfield.closure_mono h hn'

theorem mem_dclAdjoin_congr {L : IntermediateField k K} {L' : IntermediateField k' K}
    (h : (L : Set K) = (L' : Set K)) (u : ι → K) (x : K) :
    x ∈ dclAdjoin L u ↔ x ∈ dclAdjoin L' u :=
  ⟨mem_dclAdjoin_mono' (by rw [h]), mem_dclAdjoin_mono' (by rw [h])⟩

end Dcl

/-! ### Configurations over nested bases -/

namespace GroupConfiguration

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅]
  [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- A configuration over the nested base `acl_{K₀}(S)` is one over `acl_k(K₀ ∪ S)`. -/
theorem ofNested (K₀ : IntermediateField k K) (S : Set K)
    (hc : GroupConfiguration (↥(racl (↥K₀) S)) a b c x y z) :
    GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ S))) a b c x y z := by
  have hracl : ∀ A B : Set K, racl (↥(racl (↥K₀) S)) A = racl (↥(racl (↥K₀) S)) B →
      racl (↥(racl k ((K₀ : Set K) ∪ S))) A = racl (↥(racl k ((K₀ : Set K) ∪ S))) B :=
    fun A B h ↦ SetLike.coe_injective (by rw [← racl_nested_coe, ← racl_nested_coe, h])
  refine
    { racl_ab_ac := hracl _ _ hc.racl_ab_ac
      racl_ab_bc := hracl _ _ hc.racl_ab_bc
      racl_ax_ay := hracl _ _ hc.racl_ax_ay
      racl_by_bz := hracl _ _ hc.racl_by_bz
      racl_cx_cz := hracl _ _ hc.racl_cx_cz
      indep := fun i j l hij hil hjl hcol ↦ ?_
      cb_a := ?_
      cb_b := ?_
      cb_c := ?_
      one_le_erk := ?_ }
  · have h := hc.indep i j l hij hil hjl hcol
    unfold IndepTriple at h ⊢
    simp only [erk_nested K₀ S] at h
    exact h
  · have h := hc.cb_a
    rwa [racl_canonicalBase_nested K₀ S] at h
  · have h := hc.cb_b
    rwa [racl_canonicalBase_nested K₀ S] at h
  · have h := hc.cb_c
    rwa [racl_canonicalBase_nested K₀ S] at h
  · have h := hc.one_le_erk
    rwa [erk_nested K₀ S] at h

end GroupConfiguration

end

end GroupConfig
