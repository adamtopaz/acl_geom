/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.CanonicalBase

/-!
# Irreducible varieties represented by tuples

Blueprint `sources/group_configuration/04-germs.tex`, `def:variety` and `lem:generic-char`.

An irreducible `k`-variety is represented by a tuple `a`: its ideal is `locusIdeal k a`,
its `K`-points are the tuples at which this ideal vanishes (`InLocus a y`), its
dimension is `erk k ∅ (range a)`, and its generic points over a small subfield `M` are
the tuples `y` with `IsGenericOver M a y` (`GroupConfig.Locus`).  This module proves
`lem:generic-char`: a `K`-point has rank over `M` at most the dimension, with equality
iff it is generic (`erk_le_of_inLocus`, `isGenericOver_iff_erk_eq`); a generic point
over an algebraically closed `M` is generic over a larger `M'` iff it is independent
from `M'` over `M` (`IsGenericOver.isGenericOver_iff_indepOver`); and adjoining
elements algebraic over `M` and a generic point does not change the rank
(`erk_union_eq_of_subset_racl_of_isGenericOver`).  Existence and conjugacy of generic
points are `exists_isGenericOver` and `IsGenericOver.exists_algEquiv` in
`GroupConfig.Locus`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** for loci represented by finite tuples, point rank is bounded
by locus dimension, equality characterizes generic points, genericity over a
larger field is equivalent to independence, and algebraic adjoining preserves
rank. Algebraic closedness, universal-domain and smallness assumptions are
explicit where needed. Realization of an arbitrary prime ideal remains open;
this module does not construct a group or a quasi-rational map.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*}

/-! ### Points of a locus -/

/-- `def:variety`: `y` is a `K`-point of the locus of `a` over `k`. -/
def InLocus (a y : ι → K) : Prop := locusIdeal k a ≤ idealOf K y

theorem inLocus_iff {a y : ι → K} :
    InLocus (k := k) a y ↔ ∀ f ∈ locusIdeal k a, aeval y f = 0 := by
  constructor
  · intro h f hf
    exact (mem_idealOf_iff K).1 (h hf)
  · intro h f hf
    exact (mem_idealOf_iff K).2 (h f hf)

/-- The tuple itself is a `K`-point of its locus. -/
theorem inLocus_self (a : ι → K) : InLocus (k := k) a a := fun _ hf ↦
  (mem_idealOf_iff K).2 (aeval_eq_zero_of_mem_locusIdeal k hf)

/-- A generic point is a `K`-point. -/
theorem IsGenericOver.inLocus {M : IntermediateField k K} {a y : ι → K}
    (h : IsGenericOver M a y) : InLocus (k := k) a y := by
  intro f hf
  rw [← h.locusIdeal_eq] at hf
  exact (mem_idealOf_iff K).2 (aeval_eq_zero_of_mem_locusIdeal (↥M) hf)

/-- A `K`-point of the locus of `a` satisfies the vanishing ideal of `a` extended to `M`. -/
theorem map_idealOf_le_of_inLocus (M : IntermediateField k K) {a y : ι → K}
    (h : InLocus (k := k) a y) :
    (idealOf k a).map (MvPolynomial.map (algebraMap k ↥M)) ≤ idealOf (↥M) y := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
  have hK := (mem_idealOf_iff K).1 (h (map_mem_locusIdeal k hf))
  rwa [MvPolynomial.aeval_map_algebraMap] at hK

/-! ### Rank and genericity -/

/-- `lem:dimdrop`, non-strict form: a containment of vanishing ideals does not increase the
rank. -/
theorem erk_le_of_idealOf_le (M : IntermediateField k K) [Finite ι] {a b : ι → K}
    (hle : idealOf (↥M) a ≤ idealOf (↥M) b) :
    erk k (M : Set K) (range b) ≤ erk k (M : Set K) (range a) := by
  obtain ⟨π, hπ, -⟩ := exists_surjective_adjoin_of_idealOf_le M hle
  rw [erk_coe_eq_toENat_trdeg_adjoin, erk_coe_eq_toENat_trdeg_adjoin]
  exact OrderHomClass.monotone Cardinal.toENat (trdeg_le_of_surjective π hπ)

/-- `lem:generic-char`(1): a `K`-point of the locus of `a` has rank over a small subfield `M`
at most the dimension of the locus. -/
theorem erk_le_of_inLocus [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι]
    {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) {a y : ι → K}
    (h : InLocus (k := k) a y) :
    erk k (M : Set K) (range y) ≤ erk k ∅ (range a) := by
  obtain ⟨a', ha'⟩ := exists_isGenericOver hM a
  have hgen : idealOf (↥M) a' = (idealOf k a).map (MvPolynomial.map (algebraMap k ↥M)) := ha'
  have hle : idealOf (↥M) a' ≤ idealOf (↥M) y := by
    rw [hgen]
    exact map_idealOf_le_of_inLocus M h
  calc erk k (M : Set K) (range y) ≤ erk k (M : Set K) (range a') := erk_le_of_idealOf_le M hle
    _ = erk k ∅ (range a') := ha'.erk_coe_eq
    _ = erk k ∅ (range a) := ha'.erk_empty_eq

/-- `lem:generic-char`(1): a `K`-point of the locus of `a` is generic over a small subfield `M`
iff its rank over `M` is the dimension of the locus. -/
theorem isGenericOver_iff_erk_eq [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    [Finite ι] {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) {a y : ι → K}
    (h : InLocus (k := k) a y) :
    IsGenericOver M a y ↔ erk k (M : Set K) (range y) = erk k ∅ (range a) := by
  constructor
  · intro hy
    rw [hy.erk_coe_eq, hy.erk_empty_eq]
  · intro heq
    obtain ⟨a', ha'⟩ := exists_isGenericOver hM a
    have hgen : idealOf (↥M) a' = (idealOf k a).map (MvPolynomial.map (algebraMap k ↥M)) :=
      ha'
    have hle : idealOf (↥M) a' ≤ idealOf (↥M) y := by
      rw [hgen]
      exact map_idealOf_le_of_inLocus M h
    have herk : erk k (M : Set K) (range y) = erk k (M : Set K) (range a') := by
      rw [heq, ha'.erk_coe_eq, ha'.erk_empty_eq]
    exact ha'.iff_idealOf_eq.2 (idealOf_eq_of_le_of_erk_eq M hle herk).symm

/-- `lem:generic-char`(1): a generic point over an algebraically closed small `M` is generic
over a larger small `M'` iff it is independent from `M'` over `M`. -/
theorem IsGenericOver.isGenericOver_iff_indepOver [IsAlgClosed K] [UniversalDomain k K]
    [Finite ι] {M M' : IntermediateField k K} [IsAlgClosed (↥M)] (hM : IsSmall k (M : Set K))
    (hM' : IsSmall k (M' : Set K)) (hMM' : M ≤ M') {a y : ι → K} (hy : IsGenericOver M a y) :
    IsGenericOver M' a y ↔ IndepOver k (M : Set K) (range y) (M' : Set K) := by
  constructor
  · intro hy'
    refine indepOver_of_erk_eq (finite_range y) ?_
    rw [union_eq_right.2 (SetLike.coe_subset_coe.2 hMM'), hy'.erk_coe_eq, hy.erk_coe_eq]
  · intro hind
    rw [isGenericOver_iff_locusIdeal_eq, locusIdeal_eq_of_indepOver hM hM' hMM' hind]
    exact hy.locusIdeal_eq

/-- `lem:generic-char`(3): adjoining elements algebraic over `M` and a generic point does not
change the rank. -/
theorem erk_union_eq_of_subset_racl_of_isGenericOver {M : IntermediateField k K} {a y : ι → K}
    (hy : IsGenericOver M a y) {Z : Set K} (hZ : Z ⊆ racl k ((M : Set K) ∪ range y)) :
    erk k (M : Set K) (range y ∪ Z) = erk k ∅ (range a) := by
  rw [erk_union_eq_of_subset_racl k hZ, hy.erk_coe_eq, hy.erk_empty_eq]

end

end GroupConfig
