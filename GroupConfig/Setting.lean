/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Transfer.Transcendence
import GroupConfig.Rank

/-!
# The universal domain: small sets and fresh elements

Blueprint `sources/group_configuration/01-universal-domain.tex`, `conv:ud`
and `lem:fresh`.

`UniversalDomain k K` records the standing hypothesis that the ambient field
`K` has infinite transcendence degree over the base `k`.  A set `C ⊆ K` is
*small* (`IsSmall k C`) if it has finite rank over `k`; a small set has the
same closure as one of its finite subsets (`IsSmall.exists_finite_racl_eq`),
and in a universal domain every small set has a fresh element outside its
closure (`exists_notMem_racl_of_isSmall`) and, for every `n`, a fresh
`n`-tuple of rank `n` over it (`exists_fresh_tuple`, blueprint `lem:fresh`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** finite-rank small sets have finite closure generators, and the explicit
infinite-transcendence-degree hypothesis supplies fresh tuples of every finite
rank. Algebraic closedness is not needed for these results. Generic loci are
developed in `GroupConfig.Locus` and `GroupConfig.PrimeLocus`; group-of-germs
extraction is in `GroupConfig.Main`.
-/

namespace GroupConfig

open AclGeom Matroid Set

noncomputable section

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- `conv:ud`: the ambient field `K` has infinite transcendence degree over the
base field `k`.  (The hypotheses that `k` and `K` are algebraically closed are
separate instance arguments where they are needed.) -/
class UniversalDomain : Prop where
  /-- The ambient extension has at least countably infinite transcendence degree. -/
  aleph0_le_trdeg : Cardinal.aleph0 ≤ Algebra.trdeg k K

variable {K}

/-- A set `C ⊆ K` is *small* if it has finite rank over `k`. -/
def IsSmall (C : Set K) : Prop := erk k ∅ C ≠ ⊤

variable {k}

theorem IsSmall.of_finite {C : Set K} (hC : C.Finite) : IsSmall k C :=
  erk_ne_top k hC ∅

theorem IsSmall.mono {C C' : Set K} (hC : IsSmall k C) (h : C' ⊆ C) : IsSmall k C' :=
  fun htop ↦ hC (eq_top_iff.2 (htop ▸ erk_mono k ∅ h))

theorem IsSmall.union {C D : Set K} (hC : IsSmall k C) (hD : IsSmall k D) :
    IsSmall k (C ∪ D) := by
  intro htop
  have h := erk_union_le k ∅ C D
  rw [htop] at h
  exact (ENat.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hC, lt_top_iff_ne_top.2 hD⟩).ne
    (top_le_iff.1 h)

theorem IsSmall.racl {C : Set K} (hC : IsSmall k C) : IsSmall k (racl k C : Set K) := by
  have h := erk_racl k ∅ C
  rw [empty_union] at h
  exact fun htop ↦ hC (h ▸ htop)

/-- A small set has the same closure as one of its finite subsets. -/
theorem IsSmall.exists_finite_racl_eq {C : Set K} (hC : IsSmall k C) :
    ∃ S ⊆ C, S.Finite ∧ AclGeom.racl k S = AclGeom.racl k C := by
  obtain ⟨J, hJ⟩ := (rkMatroid k ∅).exists_isBasis' C
  have hJfin : J.Finite := by
    rw [← encard_lt_top_iff, hJ.encard_eq_eRk]
    exact lt_top_iff_ne_top.2 hC
  refine ⟨J, hJ.subset, hJfin, le_antisymm (racl_mono hJ.subset) ?_⟩
  have h := subset_racl_of_isBasis' k hJ
  rw [empty_union] at h
  exact racl_le_of_subset_racl h

/-- In a universal domain, every small set has a fresh element outside its
closure. -/
theorem exists_notMem_racl_of_isSmall [UniversalDomain k K] {C : Set K} (hC : IsSmall k C) :
    ∃ z : K, z ∉ racl k C := by
  obtain ⟨S, -, hSfin, hS⟩ := hC.exists_finite_racl_eq
  rw [← hS]
  refine exists_notMem_racl_of_mk_lt_trdeg S ?_
  exact (Cardinal.lt_aleph0_iff_set_finite.2 hSfin).trans_le UniversalDomain.aleph0_le_trdeg

/-- `lem:fresh`: in a universal domain, over every small set there is an
injective `n`-tuple independent over it. -/
theorem exists_fresh_tuple [UniversalDomain k K] {C : Set K} (hC : IsSmall k C) (n : ℕ) :
    ∃ t : Fin n → K, (rkMatroid k C).Indep (range t) ∧ Function.Injective t := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_, fun i ↦ i.elim0⟩
    rw [range_eq_empty]
    exact (rkMatroid k C).empty_indep
  | succ n ih =>
    obtain ⟨t, htind, htinj⟩ := ih
    have hsmall : IsSmall k (C ∪ range t) := hC.union (IsSmall.of_finite (finite_range t))
    obtain ⟨z, hz⟩ := exists_notMem_racl_of_isSmall hsmall
    have hzrange : z ∉ range t := fun hzt ↦ hz (subset_racl k _ (mem_union_right _ hzt))
    refine ⟨Fin.cons z t, ?_, Fin.cons_injective_iff.2 ⟨hzrange, htinj⟩⟩
    rw [Fin.range_cons, htind.insert_indep_iff]
    left
    refine ⟨mem_univ z, ?_⟩
    rw [mem_rkMatroid_closure_iff]
    exact hz

/-- A fresh `n`-tuple has rank `n` over the base set. -/
theorem erk_range_eq_of_indep_of_injective {C : Set K} {n : ℕ} {t : Fin n → K}
    (hind : (rkMatroid k C).Indep (range t)) (hinj : Function.Injective t) :
    erk k C (range t) = n := by
  unfold erk
  rw [hind.eRk_eq_encard, hinj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- `lem:fresh`, rank form: over every small set there is a tuple of rank `n`. -/
theorem exists_erk_range_eq [UniversalDomain k K] {C : Set K} (hC : IsSmall k C) (n : ℕ) :
    ∃ t : Fin n → K, erk k C (range t) = n := by
  obtain ⟨t, hind, hinj⟩ := exists_fresh_tuple hC n
  exact ⟨t, erk_range_eq_of_indep_of_injective hind hinj⟩

end

end GroupConfig
