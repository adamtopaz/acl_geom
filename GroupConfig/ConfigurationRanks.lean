/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Configuration

/-!
# Ranks in a group configuration

Blueprint `sources/group_configuration/07-configurations.tex`, `lem:gc-ranks`, the clauses not
in `GroupConfig.Configuration`.

For a group configuration with group rank `n = rk(a)` and space rank `m = rk(x)`:
`m ≤ n` (`GroupConfiguration.erk_x_le_erk_a`), `rk(abc) = 2n`
(`GroupConfiguration.erk_abc`), `rk(axy) = rk(byz) = rk(czx) = n + m`
(`GroupConfiguration.erk_axy`, `GroupConfiguration.erk_byz`, `GroupConfiguration.erk_czx`),
`rk(abcxyz) = 2n + m` (`GroupConfiguration.erk_abcxyz`), and every point is independent from
every line not through it: twelve statements, one for each such pair
(`GroupConfiguration.indepOver_x_abc` through `GroupConfiguration.indepOver_y_czx`).
Equality of ranks, pairwise independence and `1 ≤ n` are in `GroupConfig.Configuration`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:gc-ranks` is proved together with `GroupConfig.Configuration`.
The positive space-rank clauses are moved here unchanged from the later main-theorem
producer, so the full rank table has no dependency on group extraction.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A point independent from two points of a line is independent from the line, when the third
point of the line is algebraic over the two. -/
theorem IndepTriple.indepOver_line {P Q R S : Set K} (h : IndepTriple k P Q R) (hP : P.Finite)
    (hQ : Q.Finite) (hR : R.Finite) (hS : S ⊆ racl k (Q ∪ R)) :
    IndepOver k ∅ P (Q ∪ R ∪ S) := by
  refine (indepOver_racl_right_iff.2 (h.indepOver_union hP hQ hR)).mono_right ?_
  rw [empty_union]
  exact union_subset (subset_racl k _) hS

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄]
  [Finite ι₅] [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K}
  {z : ι₆ → K}

namespace GroupConfiguration

variable (hc : GroupConfiguration k a b c x y z)
include hc

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- The group point `c` is algebraic over `a, b`. -/
theorem range_c_subset_racl_ab : range c ⊆ racl k (range a ∪ range b) := by
  rw [hc.racl_ab_ac]
  exact subset_union_right.trans (subset_racl k _)

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- The space point `y` is algebraic over `a, x`. -/
theorem range_y_subset_racl_ax : range y ⊆ racl k (range a ∪ range x) := by
  rw [hc.racl_ax_ay]
  exact subset_union_right.trans (subset_racl k _)

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- The space point `z` is algebraic over `b, y`. -/
theorem range_z_subset_racl_by : range z ⊆ racl k (range b ∪ range y) := by
  rw [hc.racl_by_bz]
  exact subset_union_right.trans (subset_racl k _)

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- The space point `z` is algebraic over `c, x`. -/
theorem range_z_subset_racl_cx : range z ⊆ racl k (range c ∪ range x) := by
  rw [hc.racl_cx_cz]
  exact subset_union_right.trans (subset_racl k _)

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- The space point `x` is algebraic over `c, z`. -/
theorem range_x_subset_racl_cz : range x ⊆ racl k (range c ∪ range z) := by
  rw [← hc.racl_cx_cz]
  exact subset_union_right.trans (subset_racl k _)

/-! ### Ranks of the lines and of the configuration -/

/-- `lem:gc-ranks`: `rk(abc) = 2n`. -/
theorem erk_abc :
    erk k ∅ (range a ∪ range b ∪ range c) = erk k ∅ (range a) + erk k ∅ (range a) := by
  rw [erk_union_eq_of_subset_racl k (by rw [empty_union]; exact hc.range_c_subset_racl_ab),
    erk_union_of_indepOver (finite_range b) hc.indepOver_ab, hc.erk_b_eq]

/-- `lem:gc-ranks`: `rk(axy) = n + m`. -/
theorem erk_axy :
    erk k ∅ (range a ∪ range x ∪ range y) = erk k ∅ (range a) + erk k ∅ (range x) := by
  rw [erk_union_eq_of_subset_racl k (by rw [empty_union]; exact hc.range_y_subset_racl_ax),
    erk_union_of_indepOver (finite_range x) hc.indepOver_ax]

/-- `lem:gc-ranks`: `rk(byz) = n + m`. -/
theorem erk_byz :
    erk k ∅ (range b ∪ range y ∪ range z) = erk k ∅ (range a) + erk k ∅ (range x) := by
  rw [erk_union_eq_of_subset_racl k (by rw [empty_union]; exact hc.range_z_subset_racl_by),
    erk_union_of_indepOver (finite_range y) hc.indepOver_by, hc.erk_b_eq, hc.erk_y_eq]

/-- `lem:gc-ranks`: `rk(czx) = n + m`. -/
theorem erk_czx :
    erk k ∅ (range c ∪ range z ∪ range x) = erk k ∅ (range a) + erk k ∅ (range x) := by
  rw [erk_union_eq_of_subset_racl k (by rw [empty_union]; exact hc.range_x_subset_racl_cz),
    erk_union_of_indepOver (finite_range z) hc.indepOver_cz, hc.erk_c_eq, hc.erk_z_eq]

/-- `lem:gc-ranks`: `m ≤ n`. -/
theorem erk_x_le_erk_a : erk k ∅ (range x) ≤ erk k ∅ (range a) := by
  have h : erk k ∅ (range x ∪ range y) ≤ erk k ∅ (range a ∪ range x ∪ range y) :=
    erk_mono k ∅ (union_subset (subset_union_right.trans subset_union_left) subset_union_right)
  rw [erk_union_of_indepOver (finite_range y) hc.indepOver_xy, hc.erk_y_eq, hc.erk_axy,
    add_comm (erk k ∅ (range a))] at h
  exact (ENat.add_le_add_iff_left (erk_ne_top k (finite_range x) ∅)).1 h

/-- `lem:gc-ranks`: `rk(abcxyz) = 2n + m`. -/
theorem erk_abcxyz :
    erk k ∅ (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) =
      erk k ∅ (range a) + erk k ∅ (range a) + erk k ∅ (range x) := by
  -- Every point is algebraic over the non-collinear triple `(a, b, y)`.
  have ha : range a ⊆ racl k (range a ∪ range b ∪ range y) :=
    (subset_union_left.trans subset_union_left).trans (subset_racl k _)
  have hb : range b ⊆ racl k (range a ∪ range b ∪ range y) :=
    (subset_union_right.trans subset_union_left).trans (subset_racl k _)
  have hy : range y ⊆ racl k (range a ∪ range b ∪ range y) :=
    subset_union_right.trans (subset_racl k _)
  have hsub : range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ⊆
      racl k (range a ∪ range b ∪ range y) := by
    refine union_subset (union_subset (union_subset (union_subset (union_subset ha hb) ?_) ?_)
      hy) ?_
    · exact hc.range_c_subset_racl_ab.trans (racl_le_of_subset_racl (union_subset ha hb))
    · have hx : range x ⊆ racl k (range a ∪ range y) := by
        rw [← hc.racl_ax_ay]
        exact subset_union_right.trans (subset_racl k _)
      exact hx.trans (racl_le_of_subset_racl (union_subset ha hy))
    · exact hc.range_z_subset_racl_by.trans (racl_le_of_subset_racl (union_subset hb hy))
  have hracl : racl k (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) =
      racl k (range a ∪ range b ∪ range y) := by
    refine le_antisymm (racl_le_of_subset_racl hsub) (racl_mono (k := k) ?_)
    intro w hw
    rcases hw with (hw | hw) | hw
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hw))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hw))))
    · exact Or.inl (Or.inr hw)
  have t : erk k ∅ (range a ∪ range b ∪ range y) =
      erk k ∅ (range a) + erk k ∅ (range b) + erk k ∅ (range y) :=
    hc.indep 0 1 4 (by decide) (by decide) (by decide) (by decide)
  rw [erk_eq_of_racl_eq hracl, t, hc.erk_b_eq, hc.erk_y_eq]

/-! ### Independence of points from lines -/

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `x` is independent from the line `{a, b, c}`. -/
theorem indepOver_x_abc : IndepOver k ∅ (range x) (range a ∪ range b ∪ range c) :=
  (hc.indep 3 0 1 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range x) (finite_range a) (finite_range b) hc.range_c_subset_racl_ab

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `y` is independent from the line `{a, b, c}`. -/
theorem indepOver_y_abc : IndepOver k ∅ (range y) (range a ∪ range b ∪ range c) :=
  (hc.indep 4 0 1 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range y) (finite_range a) (finite_range b) hc.range_c_subset_racl_ab

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `z` is independent from the line `{a, b, c}`. -/
theorem indepOver_z_abc : IndepOver k ∅ (range z) (range a ∪ range b ∪ range c) :=
  (hc.indep 5 0 1 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range z) (finite_range a) (finite_range b) hc.range_c_subset_racl_ab

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the group point `b` is independent from the line `{a, x, y}`. -/
theorem indepOver_b_axy : IndepOver k ∅ (range b) (range a ∪ range x ∪ range y) :=
  (hc.indep 1 0 3 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range b) (finite_range a) (finite_range x) hc.range_y_subset_racl_ax

omit [Finite ι₂] in
/-- `lem:gc-ranks`: the group point `c` is independent from the line `{a, x, y}`. -/
theorem indepOver_c_axy : IndepOver k ∅ (range c) (range a ∪ range x ∪ range y) :=
  (hc.indep 2 0 3 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range c) (finite_range a) (finite_range x) hc.range_y_subset_racl_ax

omit [Finite ι₂] [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `z` is independent from the line `{a, x, y}`. -/
theorem indepOver_z_axy : IndepOver k ∅ (range z) (range a ∪ range x ∪ range y) :=
  (hc.indep 5 0 3 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range z) (finite_range a) (finite_range x) hc.range_y_subset_racl_ax

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the group point `a` is independent from the line `{b, y, z}`. -/
theorem indepOver_a_byz : IndepOver k ∅ (range a) (range b ∪ range y ∪ range z) :=
  (hc.indep 0 1 4 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range a) (finite_range b) (finite_range y) hc.range_z_subset_racl_by

omit [Finite ι₁] in
/-- `lem:gc-ranks`: the group point `c` is independent from the line `{b, y, z}`. -/
theorem indepOver_c_byz : IndepOver k ∅ (range c) (range b ∪ range y ∪ range z) :=
  (hc.indep 2 1 4 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range c) (finite_range b) (finite_range y) hc.range_z_subset_racl_by

omit [Finite ι₁] [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `x` is independent from the line `{b, y, z}`. -/
theorem indepOver_x_byz : IndepOver k ∅ (range x) (range b ∪ range y ∪ range z) :=
  (hc.indep 3 1 4 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range x) (finite_range b) (finite_range y) hc.range_z_subset_racl_by

omit [Finite ι₂] in
/-- `lem:gc-ranks`: the group point `a` is independent from the line `{c, z, x}`. -/
theorem indepOver_a_czx : IndepOver k ∅ (range a) (range c ∪ range z ∪ range x) :=
  (hc.indep 0 2 5 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range a) (finite_range c) (finite_range z) hc.range_x_subset_racl_cz

omit [Finite ι₁] in
/-- `lem:gc-ranks`: the group point `b` is independent from the line `{c, z, x}`. -/
theorem indepOver_b_czx : IndepOver k ∅ (range b) (range c ∪ range z ∪ range x) :=
  (hc.indep 1 2 5 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range b) (finite_range c) (finite_range z) hc.range_x_subset_racl_cz

omit [Finite ι₁] [Finite ι₂] in
/-- `lem:gc-ranks`: the space point `y` is independent from the line `{c, z, x}`. -/
theorem indepOver_y_czx : IndepOver k ∅ (range y) (range c ∪ range z ∪ range x) :=
  (hc.indep 4 2 5 (by decide) (by decide) (by decide) (by decide)).indepOver_line
    (finite_range y) (finite_range c) (finite_range z) hc.range_x_subset_racl_cz

variable [IsAlgClosed K] [UniversalDomain k K]

/-- `lem:gc-ranks`: the space points have positive rank. -/
theorem one_le_erk_x : 1 ≤ erk k ∅ (range x) := by
  by_contra hx
  have hx0 : erk k ∅ (range x) = 0 := Order.lt_one_iff.1 (not_le.1 hx)
  have hxs : range x ⊆ racl k (∅ : Set K) := (erk_eq_zero_iff k).1 hx0
  have hys : range y ⊆ racl k (∅ : Set K) := (erk_eq_zero_iff k).1 (hc.erk_y_eq.trans hx0)
  have _ : IsAlgClosed ↥(racl k (∅ : Set K)) := isAlgClosed_racl _
  have hxy : range (Sum.elim x y) ⊆ racl k (∅ : Set K) := by
    rw [Sum.elim_range]
    exact union_subset hxs hys
  have hL : range (Sum.elim x y) ⊆ racl k (racl k (∅ : Set K) : Set K) :=
    hxy.trans (subset_racl k _)
  have hLM : range (Sum.elim x y) ⊆
      racl k ((racl k (∅ : Set K) : Set K) ∪ (racl k (range a) : Set K)) :=
    hxy.trans (subset_union_left.trans (subset_racl k _))
  have hind : IndepOver k (racl k (∅ : Set K) : Set K) (range (Sum.elim x y))
      (racl k (range a) : Set K) := by
    refine indepOver_of_erk_eq (finite_range _) ?_
    rw [(erk_eq_zero_iff k).2 hLM, (erk_eq_zero_iff k).2 hL]
  have hcb := canonicalBase_eq_of_indepOver (IsSmall.of_finite (k := k) finite_empty).racl
    (IsSmall.of_finite (k := k) (finite_range a)).racl (racl_mono (empty_subset _)) hind
  have ha : range a ⊆ racl k (∅ : Set K) := by
    have h := hc.cb_a
    rw [hcb] at h
    exact h.trans (SetLike.coe_subset_coe.2
      (racl_le_of_isAlgClosed (SetLike.coe_subset_coe.2 (canonicalBase_le _ _))))
  have h1 := hc.one_le_erk
  rw [(erk_eq_zero_iff k).2 ha] at h1
  exact not_le.2 zero_lt_one h1

/-- `lem:gc-ranks`: the space points have positive rank. -/
theorem one_le_erk_y : 1 ≤ erk k ∅ (range y) := by
  rw [hc.erk_y_eq]
  exact hc.one_le_erk_x


end GroupConfiguration

end

end GroupConfig
