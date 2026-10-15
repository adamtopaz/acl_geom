/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConfigurationRanks
import GroupConfig.ConjugateSet

/-!
# Conjugate sets of space points of a configuration

Blueprint `sources/group_configuration/07-configurations.tex`, `lem:conjset-gc`.

For a space point `r` of a group configuration with lines `{p₁, q₁, r}` and `{p₂, q₂, r}`,
and `L = k(p₁ q₁ p₂ q₂)`, the point `r` is algebraic over `L`
(`GroupConfiguration.isIntegral_z`), every conjugate of `r` over `L` is algebraic over `r`
(`GroupConfiguration.conj_z_mem_racl`), and the code of the conjugate set lies in `dcl(L)`
and is interalgebraic with `r` (`GroupConfiguration.conjCode_z_subset_dcl`,
`GroupConfiguration.racl_conjCode_z`).  The statements are given for `r = z`; the other
space points are obtained by relabeling.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:conjset-gc` complete for every space point: `r = z`, and `r = x`, `r = y`
through the relabelings `swapAB` and `swapBC.swapAB.swapBC` (the `_x` and `_y` statements).
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem image_eq_self_of_forall_fixed {S : Set K} (σ : K ≃ₐ[k] K) (h : ∀ s ∈ S, σ s = s) :
    ⇑σ '' S = S := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [h s hs]
    exact hs
  · intro hw
    exact ⟨w, hw, h w hw⟩

/-- An automorphism fixing `S` pointwise maps `acl(S)` to itself. -/
theorem apply_mem_racl_of_forall_fixed (σ : K ≃ₐ[k] K) {S : Set K} (hS : ∀ s ∈ S, σ s = s)
    {w : K} (hw : w ∈ racl k S) : σ w ∈ racl k S := by
  have h1 : σ w ∈ ⇑σ '' (racl k S : Set K) := mem_image_of_mem σ hw
  rwa [← AlgEquiv.coe_toAlgHom, ← coe_map, racl_map, AlgEquiv.coe_toAlgHom,
    image_eq_self_of_forall_fixed σ hS] at h1

theorem isIntegral_of_mem_racl_coe {L : IntermediateField k K} {w : K}
    (hw : w ∈ racl k (L : Set K)) : IsIntegral (↥L) w := by
  rw [mem_racl_iff k, adjoin_self] at hw
  exact hw.isIntegral

/-- `racl` absorbs a set algebraic over the other part of a union. -/
theorem racl_union_eq_of_subset_racl {A B : Set K} (h : A ⊆ racl k B) :
    racl k (A ∪ B) = racl k B :=
  le_antisymm (racl_le_of_subset_racl (union_subset h (subset_racl k B)))
    (racl_mono (k := k) subset_union_right)

theorem racl_union_eq_of_subset_racl' {A B : Set K} (h : A ⊆ racl k B) :
    racl k (B ∪ A) = racl k B := by
  rw [union_comm]
  exact racl_union_eq_of_subset_racl h

namespace GroupConfiguration

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K}
  {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}
  (hc : GroupConfiguration k a b c x y z)
include hc

theorem range_y_subset_racl_zb : range y ⊆ racl k (range z ∪ range b) := by
  rw [union_comm, ← hc.racl_by_bz]
  exact subset_union_right.trans (subset_racl k _)

theorem range_x_subset_racl_zc : range x ⊆ racl k (range z ∪ range c) := by
  rw [union_comm, ← hc.racl_cx_cz]
  exact subset_union_right.trans (subset_racl k _)

/-- `lem:conjset-gc`: the two lines through `z` are independent over `z`. -/
theorem indepOver_lines_z [Finite ι₂] [Finite ι₃] :
    IndepOver k (range z) (range b ∪ range y) (range c ∪ range x) := by
  have h := hc.indep 1 5 2 (by decide) (by decide) (by decide) (by decide)
  have h1 : IndepOver k ∅ (range b) (range z ∪ range c) :=
    h.indepOver_union (finite_range b) (finite_range z) (finite_range c)
  have h2 : IndepOver k (∅ ∪ range z) (range b) (range c) :=
    (indepOver_union_right_iff.1 h1).2
  rw [empty_union] at h2
  have e1 : racl k (range z ∪ (range b ∪ range y)) = racl k (range z ∪ range b) := by
    rw [← union_assoc]
    exact racl_union_eq_of_subset_racl' hc.range_y_subset_racl_zb
  have e2 : racl k (range z ∪ (range c ∪ range x)) = racl k (range z ∪ range c) := by
    rw [← union_assoc]
    exact racl_union_eq_of_subset_racl' hc.range_x_subset_racl_zc
  have h3 : IndepOver k (range z) (range b ∪ range y) (range c) :=
    (indepOver_congr_left e1).1 h2
  exact ((indepOver_congr_left e2).1 h3.symm).symm

/-- `lem:conjset-gc`: `z` is algebraic over `L = k(b, y, c, x)`. -/
theorem isIntegral_z (i : ι₆) :
    IsIntegral (↥(adjoin k (range b ∪ range y ∪ range c ∪ range x))) (z i) := by
  refine isIntegral_of_mem_racl_coe (racl_mono (k := k) ?_ (hc.range_z_subset_racl_by
    (mem_range_self i)))
  exact (subset_union_left.trans subset_union_left).trans (subset_adjoin k _)

/-- `lem:conjset-gc`: every conjugate of `z` over `L = k(b, y, c, x)` is algebraic over `z`. -/
theorem conj_z_mem_racl [Finite ι₂] [Finite ι₃]
    (σ : K ≃ₐ[↥(adjoin k (range b ∪ range y ∪ range c ∪ range x))] K)
    (i : ι₆) : σ (z i) ∈ racl k (range z) := by
  have hfix : ∀ s ∈ range b ∪ range y ∪ range c ∪ range x, (σ.restrictScalars k) s = s :=
    fun s hs ↦ by
      change σ s = s
      exact σ.commutes ⟨s, subset_adjoin k _ hs⟩
  have h1 : σ (z i) ∈ racl k (range b ∪ range y) :=
    apply_mem_racl_of_forall_fixed (σ.restrictScalars k)
      (fun s hs ↦ hfix s ((subset_union_left.trans subset_union_left) hs))
      (hc.range_z_subset_racl_by (mem_range_self i))
  have h2 : σ (z i) ∈ racl k (range c ∪ range x) :=
    apply_mem_racl_of_forall_fixed (σ.restrictScalars k)
      (fun s hs ↦ hfix s ((union_subset (subset_union_right.trans subset_union_left)
        subset_union_right) hs))
      (hc.range_z_subset_racl_cx (mem_range_self i))
  have hmeet := hc.indepOver_lines_z.racl_inter_eq
  rw [racl_union_eq_of_subset_racl hc.range_z_subset_racl_by,
    racl_union_eq_of_subset_racl hc.range_z_subset_racl_cx] at hmeet
  rw [← SetLike.mem_coe, ← hmeet]
  exact ⟨h1, h2⟩

/-- `lem:conjset-gc`: the code of the conjugate set of `z` over `L = k(b, y, c, x)` lies in
`dcl(L)`. -/
theorem conjCode_z_subset_dcl [IsAlgClosed K] :
    conjCode (adjoin k (range b ∪ range y ∪ range c ∪ range x)) z ⊆
      dcl (adjoin k (range b ∪ range y ∪ range c ∪ range x)) :=
  conjCode_subset_dcl hc.isIntegral_z

/-- `lem:conjset-gc`: the code of the conjugate set of `z` is interalgebraic with `z`. -/
theorem racl_conjCode_z [Finite ι₂] [Finite ι₃] :
    racl k (conjCode (adjoin k (range b ∪ range y ∪ range c ∪ range x)) z) =
      racl k (range z) :=
  racl_conjCode_eq hc.isIntegral_z hc.conj_z_mem_racl

/-! ### The other space points -/

/-- `lem:conjset-gc` for the space point `x`, by the relabeling `swapAB`: the two lines through `x`
are independent over `x`. -/
theorem indepOver_lines_x [Finite ι₁] [Finite ι₂] [Finite ι₃] :
    IndepOver k (range x) (range a ∪ range y) (range c ∪ range z) :=
  hc.swapAB.indepOver_lines_z

/-- `lem:conjset-gc` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC`: the two
lines through `y` are independent over `y`. -/
theorem indepOver_lines_y [Finite ι₁] [Finite ι₂] [Finite ι₃] :
    IndepOver k (range y) (range b ∪ range z) (range a ∪ range x) :=
  hc.swapBC.swapAB.swapBC.indepOver_lines_z

/-- `lem:conjset-gc` for the space point `x`, by the relabeling `swapAB`: `x` is algebraic over the
field of the other points of its lines. -/
theorem isIntegral_x [Finite ι₁] [Finite ι₂] [Finite ι₃] (i : ι₄) :
    IsIntegral (↥(adjoin k (range a ∪ range y ∪ range c ∪ range z))) (x i) :=
  hc.swapAB.isIntegral_z i

/-- `lem:conjset-gc` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC`: `y` is
algebraic over the field of the other points of its lines. -/
theorem isIntegral_y [Finite ι₁] [Finite ι₂] [Finite ι₃] (i : ι₅) :
    IsIntegral (↥(adjoin k (range b ∪ range z ∪ range a ∪ range x))) (y i) :=
  hc.swapBC.swapAB.swapBC.isIntegral_z i

/-- `lem:conjset-gc` for the space point `x`, by the relabeling `swapAB`: every conjugate of `x`
over that field is algebraic over `x`. -/
theorem conj_x_mem_racl [Finite ι₁] [Finite ι₂] [Finite ι₃]
    (σ : K ≃ₐ[↥(adjoin k (range a ∪ range y ∪ range c ∪ range z))] K)
    (i : ι₄) : σ (x i) ∈ racl k (range x) :=
  hc.swapAB.conj_z_mem_racl σ i

/-- `lem:conjset-gc` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC`: every
conjugate of `y` over that field is algebraic over `y`. -/
theorem conj_y_mem_racl [Finite ι₁] [Finite ι₂] [Finite ι₃]
    (σ : K ≃ₐ[↥(adjoin k (range b ∪ range z ∪ range a ∪ range x))] K)
    (i : ι₅) : σ (y i) ∈ racl k (range y) :=
  hc.swapBC.swapAB.swapBC.conj_z_mem_racl σ i

/-- `lem:conjset-gc` for the space point `x`, by the relabeling `swapAB`: the code of the conjugate
set of `x` lies in the definable closure of that field. -/
theorem conjCode_x_subset_dcl [Finite ι₁] [Finite ι₂] [Finite ι₃] [IsAlgClosed K] :
    conjCode (adjoin k (range a ∪ range y ∪ range c ∪ range z)) x ⊆
      dcl (adjoin k (range a ∪ range y ∪ range c ∪ range z)) :=
  hc.swapAB.conjCode_z_subset_dcl

/-- `lem:conjset-gc` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC`: the code of
the conjugate set of `y` lies in the definable closure of that field. -/
theorem conjCode_y_subset_dcl [Finite ι₁] [Finite ι₂] [Finite ι₃] [IsAlgClosed K] :
    conjCode (adjoin k (range b ∪ range z ∪ range a ∪ range x)) y ⊆
      dcl (adjoin k (range b ∪ range z ∪ range a ∪ range x)) :=
  hc.swapBC.swapAB.swapBC.conjCode_z_subset_dcl

/-- `lem:conjset-gc` for the space point `x`, by the relabeling `swapAB`: the code of the conjugate
set of `x` is interalgebraic with `x`. -/
theorem racl_conjCode_x [Finite ι₁] [Finite ι₂] [Finite ι₃] :
    racl k (conjCode (adjoin k (range a ∪ range y ∪ range c ∪ range z)) x) =
      racl k (range x) :=
  hc.swapAB.racl_conjCode_z

/-- `lem:conjset-gc` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC`: the code of
the conjugate set of `y` is interalgebraic with `y`. -/
theorem racl_conjCode_y [Finite ι₁] [Finite ι₂] [Finite ι₃] :
    racl k (conjCode (adjoin k (range b ∪ range z ∪ range a ∪ range x)) y) =
      racl k (range y) :=
  hc.swapBC.swapAB.swapBC.racl_conjCode_z

end GroupConfiguration

end

end GroupConfig
