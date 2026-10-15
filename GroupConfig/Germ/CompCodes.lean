/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Group

/-!
# Canonical bases of composites of germs between loci

Blueprint `sources/group_configuration/04-germs.tex`, `lem:comp-codes`(1), for germs
`g : V → V'` and `g' : V' → V''` between possibly different loci.

`GroupConfig.Germ.cb_comp_le_racl` and `GroupConfig.Germ.cb_le_of_isInverse` give
`Cb(g' g) ⊆ acl(Cb g, Cb g')` and, for invertible `g`, `Cb g' ⊆ acl(Cb(g' g), Cb g)`. This
module adds the third containment `Cb g ⊆ acl(Cb(g' g), Cb g')` for invertible `g'`
(`Germ.cb_le_of_isInverse_left`), and the resulting rank equalities over the canonical base of
either factor (`Germ.erk_cb_comp_eq_of_isInverse`, `Germ.erk_cb_comp_eq_of_isInverse_left`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:comp-codes`(1) complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ μ : Type*} [Finite ι] [Finite κ] [Finite μ] {a : ι → K}
  {a' : κ → K} {a'' : μ → K}

namespace Germ

/-- `lem:comp-codes`(1): for an invertible `g'`, the canonical base of `g` lies in the closure
of the canonical bases of `g' ∘ g` and `g'`. -/
theorem cb_le_of_isInverse_left (g : Germ k a a') {g' : Germ k a' a''} {h' : Germ k a'' a'}
    (hi : IsInverse h' g') : g.cb ≤ racl k (((Germ.comp g' g).cb : Set K) ∪ g'.cb) := by
  have hg : g = Germ.comp h' (Germ.comp g' g) := by
    rw [← comp_assoc, hi.1, id_comp]
  have hle : (Germ.comp h' (Germ.comp g' g)).cb ≤
      racl k (((Germ.comp g' g).cb : Set K) ∪ h'.cb) := cb_comp_le_racl h' (Germ.comp g' g)
  rw [← hg] at hle
  have h1 : ((Germ.comp g' g).cb : Set K) ⊆ racl k (((Germ.comp g' g).cb : Set K) ∪ g'.cb) :=
    subset_union_left.trans (subset_racl k _)
  have h2 : (h'.cb : Set K) ⊆ racl k (((Germ.comp g' g).cb : Set K) ∪ g'.cb) :=
    hi.cb_le.trans (racl_mono (k := k) subset_union_right)
  exact hle.trans (racl_le_of_subset_racl (union_subset h1 h2))

/-- `lem:comp-codes`(1): over the canonical base of an invertible `g`, the composite `g' ∘ g`
and `g'` have the same rank: `rk(g' g / C g) = rk(g' / C g)`. -/
theorem erk_cb_comp_eq_of_isInverse (C : Set K) {g : Germ k a a'} {h : Germ k a' a}
    (hi : IsInverse h g) (g' : Germ k a' a'') :
    erk k (C ∪ g.cb) ((Germ.comp g' g).cb : Set K) = erk k (C ∪ g.cb) (g'.cb : Set K) := by
  refine erk_eq_of_subset_racl ?_ ?_
  · refine (cb_comp_le_racl g' g).trans (racl_mono (k := k) ?_)
    rw [union_assoc]
    exact subset_union_right
  · refine (cb_le_of_isInverse g' hi).trans (racl_mono (k := k) ?_)
    exact union_subset subset_union_right (subset_union_right.trans subset_union_left)

/-- `lem:comp-codes`(1): over the canonical base of an invertible `g'`, the composite `g' ∘ g`
and `g` have the same rank: `rk(g' g / C g') = rk(g / C g')`. -/
theorem erk_cb_comp_eq_of_isInverse_left (C : Set K) (g : Germ k a a') {g' : Germ k a' a''}
    {h' : Germ k a'' a'} (hi : IsInverse h' g') :
    erk k (C ∪ g'.cb) ((Germ.comp g' g).cb : Set K) = erk k (C ∪ g'.cb) (g.cb : Set K) := by
  refine erk_eq_of_subset_racl ?_ ?_
  · refine (cb_comp_le_racl g' g).trans (racl_mono (k := k) ?_)
    exact union_subset subset_union_right (subset_union_right.trans subset_union_left)
  · refine (cb_le_of_isInverse_left g hi).trans (racl_mono (k := k) ?_)
    exact union_subset subset_union_right (subset_union_right.trans subset_union_left)

end Germ

end

end GroupConfig
