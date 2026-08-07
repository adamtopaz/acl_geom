/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.FiniteRank

/-!
# Validation: the rank bridge on a dependent triple

The rank bridge proves a witness-table-style clause: the dependent triple
`([a], [c], [ac])` at independent `a, c` has rank two. This is the proof
shape by which the configuration layer verifies every rank clause of the
`Q`-witness (blueprint witness table 7.1), so it is kept as a regression
test.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

example {a c : K} (h : AlgebraicIndependent k ![a, c]) :
    RankEq 2 (point k a ⊔ (point k c ⊔ point k (a * c))) := by
  refine rankEq_of_coe_eq_racl h ?_
  rw [coe_sup]
  simp only [coe_set_sup, coe_set_point]
  have hrange : Set.range ![a, c] = {a, c} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]
    simp only [Set.union_empty, Set.union_singleton]
    exact Set.pair_comm c a
  rw [hrange]
  have ha : a ∈ racl k ({a, c} : Set K) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hc : c ∈ racl k ({a, c} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hac : a * c ∈ racl k ({a, c} : Set K) :=
    MulMemClass.mul_mem ha hc
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z (hz | hz)
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 ha) hz
    · have hle : racl k ((racl k {c} : Set K) ∪ (racl k {a * c} : Set K)) ≤
          racl k ({a, c} : Set K) := by
        refine racl_le_of_subset_racl (Set.union_subset ?_ ?_)
        · exact fun w hw ↦
            racl_le_of_subset_racl (Set.singleton_subset_iff.2 hc) hw
        · exact fun w hw ↦
            racl_le_of_subset_racl (Set.singleton_subset_iff.2 hac) hw
      exact hle hz
  · rintro z (rfl | rfl)
    · refine subset_racl k _ ?_
      refine Set.mem_union_left _ ?_
      exact subset_racl k _ rfl
    · refine subset_racl k _ ?_
      refine Set.mem_union_right _ ?_
      refine subset_racl k _ ?_
      refine Set.mem_union_left _ ?_
      exact subset_racl k _ rfl

end AclGeom
