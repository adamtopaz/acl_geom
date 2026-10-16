/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Configuration

/-!
# Base change of group configurations

Blueprint `sources/group_configuration/07-configurations.tex`, `lem:gc-invariance`(2).

A group configuration over `k` is a group configuration over any small subfield `K₀ ⊇ k`
independent from it (`GroupConfig.GroupConfiguration.baseChange`); in the blueprint
`K₀ = acl(k, e)` for a tuple `e` independent from the configuration.  The bridging lemmas
express closures, ranks, independence and canonical bases over the base `K₀` through the
corresponding notions over `k` (`GroupConfig.mem_racl_base_iff`, `GroupConfig.erk_base_empty`,
`GroupConfig.indepOver_base_iff`, `GroupConfig.racl_canonicalBase_base`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:gc-invariance`(2) complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Bridges between the bases `k` and `K₀` -/

section Bridges

variable (K₀ : IntermediateField k K)

/-- The relative algebraic closure over the base `K₀`, as a closure over `k`. -/
theorem mem_racl_base_iff (S : Set K) (x : K) :
    x ∈ racl (↥K₀) S ↔ x ∈ racl k ((K₀ : Set K) ∪ S) := by
  rw [mem_racl_iff (↥K₀), mem_racl_iff k, ← restrictScalars_adjoin]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

theorem racl_base_coe (S : Set K) :
    ((racl (↥K₀) S : IntermediateField (↥K₀) K) : Set K) =
      ((racl k ((K₀ : Set K) ∪ S) : IntermediateField k K) : Set K) :=
  Set.ext fun x ↦ mem_racl_base_iff K₀ S x

/-- Equal closures over `k` remain equal over the larger base `K₀`. -/
theorem racl_base_congr {S T : Set K} (h : racl k S = racl k T) : racl (↥K₀) S = racl (↥K₀) T := by
  apply SetLike.coe_injective
  rw [racl_base_coe, racl_base_coe, ← racl_union_right, h, racl_union_right]

/-- Ranks over the base `K₀` are ranks over `k` relative to `K₀`. -/
theorem erk_base_empty (X : Set K) : erk (↥K₀) ∅ X = erk k (K₀ : Set K) X := by
  rw [erk_empty_eq (↥K₀), ← erk_coe_eq k K₀]

theorem indepOver_base_iff (A B : Set K) :
    IndepOver (↥K₀) ∅ A B ↔ IndepOver k (K₀ : Set K) A B := by
  rw [← indepOver_coe_union_iff K₀ ∅ A B, union_empty]

theorem racl_union_adjoin (A B : Set K) :
    racl k (A ∪ (adjoin k B : IntermediateField k K)) = racl k (A ∪ B) := by
  refine le_antisymm (racl_le_of_subset_racl (union_subset ?_ ?_)) ?_
  · exact subset_union_left.trans (subset_racl k _)
  · exact (adjoin_le_racl k B).trans (racl_mono (k := k) subset_union_right)
  · exact racl_mono (k := k) (union_subset_union_right _ (subset_adjoin k B))

variable {ι : Type*}

/-- Locus ideals over closures over the base `K₀`, as locus ideals over closures over `k`. -/
theorem locusIdeal_racl_base (S : Set K) (t : ι → K) :
    locusIdeal (↥(racl (↥K₀) S)) t = locusIdeal (↥(racl k ((K₀ : Set K) ∪ S))) t :=
  locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe, racl_base_coe]) t

/-- The closure of a canonical base over `K₀`, as a closure over `k`. -/
theorem racl_canonicalBase_base [Finite ι] (S : Set K) (t : ι → K) :
    ((racl (↥K₀) (canonicalBase (racl (↥K₀) S) t : Set K) : IntermediateField (↥K₀) K) :
        Set K) =
      ((racl k ((K₀ : Set K) ∪ (canonicalBase (racl k ((K₀ : Set K) ∪ S)) t : Set K)) :
        IntermediateField k K) : Set K) := by
  unfold canonicalBase
  have e1 : ((adjoin (↥K₀) (idealFod (locusIdeal (↥(racl (↥K₀) S)) t) : Set K) :
      IntermediateField (↥K₀) K) : Set K) =
      ((adjoin k ((K₀ : Set K) ∪ (idealFod (locusIdeal (↥(racl k ((K₀ : Set K) ∪ S))) t) :
        Set K)) : IntermediateField k K) : Set K) := by
    rw [locusIdeal_racl_base, ← restrictScalars_adjoin, coe_restrictScalars]
  rw [racl_base_coe, e1, racl_union_adjoin, ← union_assoc, union_self, racl_union_adjoin]

end Bridges

/-! ### Base change of a configuration -/

namespace GroupConfiguration

variable [IsAlgClosed K] [UniversalDomain k K] {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁]
  [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K}
  {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

omit [Field K] [IsAlgClosed K] [UniversalDomain k K] [Finite ι₁] [Finite ι₂] [Finite ι₃]
  [Finite ι₄] [Finite ι₅] [Finite ι₆] in
theorem gcPoints_subset (i : Fin 6) :
    gcPoints a b c x y z i ⊆
      range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z := by
  fin_cases i
  · exact subset_union_left.trans (subset_union_left.trans (subset_union_left.trans
      (subset_union_left.trans subset_union_left)))
  · exact subset_union_right.trans (subset_union_left.trans (subset_union_left.trans
      (subset_union_left.trans subset_union_left)))
  · exact subset_union_right.trans (subset_union_left.trans (subset_union_left.trans
      subset_union_left))
  · exact subset_union_right.trans (subset_union_left.trans subset_union_left)
  · exact subset_union_right.trans subset_union_left
  · exact subset_union_right

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] in
/-- (GC4) is preserved by base change to a small subfield independent from the points
(`prop:cb` (Cb6)). -/
theorem cb_baseChange (K₀ : IntermediateField k K) (hs : IsSmall k (K₀ : Set K)) {W : Set K}
    (hW : IndepOver k ∅ (K₀ : Set K) W) {ι ι' : Type*} [Finite ι] [Finite ι'] {p : ι → K}
    {t : ι' → K} (hp : range p ⊆ W) (ht : range t ⊆ W)
    (h : range p ⊆ racl k (canonicalBase (racl k (range p)) t : Set K)) :
    range p ⊆ racl (↥K₀) (canonicalBase (racl (↥K₀) (range p)) t : Set K) := by
  have _ : IsAlgClosed ↥(racl k (range p)) := isAlgClosed_racl _
  rw [racl_canonicalBase_base, union_comm (K₀ : Set K) (range p),
    ← racl_union_left (range p) (K₀ : Set K),
    canonicalBase_racl_union_eq (IsSmall.of_finite (finite_range p)).racl hs]
  · exact h.trans (racl_mono (k := k) subset_union_right)
  · refine (indepOver_racl_right_iff.2 hW).mono_right ?_
    rw [empty_union]
    exact union_subset (ht.trans (subset_racl k _)) (racl_mono (k := k) hp)

variable (hc : GroupConfiguration k a b c x y z)
include hc

/-- `lem:gc-invariance`(2): a configuration over `k` is a configuration over every small
subfield `K₀ ⊇ k` independent from it (in the blueprint, `K₀ = acl(k, e)`). -/
theorem baseChange (K₀ : IntermediateField k K) (hs : IsSmall k (K₀ : Set K))
    (he : IndepOver k ∅ (K₀ : Set K)
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z)) :
    GroupConfiguration (↥K₀) a b c x y z := by
  have key : ∀ X ⊆ range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z,
      X.Finite → erk (↥K₀) ∅ X = erk k ∅ X := fun X hX hfin ↦ by
    rw [erk_base_empty]
    have := (he.symm.mono_left hX).erk_eq (subset_refl _) hfin
    rwa [empty_union] at this
  have hall : (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z).Finite :=
    (((((finite_range a).union (finite_range b)).union (finite_range c)).union
      (finite_range x)).union (finite_range y)).union (finite_range z)
  have hracl : ∀ A B : Set K, racl k A = racl k B →
      racl (↥K₀) A = racl (↥K₀) B := fun A B h ↦
    SetLike.coe_injective (by rw [racl_base_coe, racl_base_coe, racl_union_congr rfl h])
  exact
    { racl_ab_ac := hracl _ _ hc.racl_ab_ac
      racl_ab_bc := hracl _ _ hc.racl_ab_bc
      racl_ax_ay := hracl _ _ hc.racl_ax_ay
      racl_by_bz := hracl _ _ hc.racl_by_bz
      racl_cx_cz := hracl _ _ hc.racl_cx_cz
      indep i j l hij hil hjl hcol := by
        have h := hc.indep i j l hij hil hjl hcol
        unfold IndepTriple at h ⊢
        rw [key _ (union_subset (union_subset (gcPoints_subset i) (gcPoints_subset j))
            (gcPoints_subset l)) (((gcPoints_finite a b c x y z i).union
            (gcPoints_finite a b c x y z j)).union (gcPoints_finite a b c x y z l)),
          key _ (gcPoints_subset i) (gcPoints_finite a b c x y z i),
          key _ (gcPoints_subset j) (gcPoints_finite a b c x y z j),
          key _ (gcPoints_subset l) (gcPoints_finite a b c x y z l)]
        exact h
      cb_a := cb_baseChange K₀ hs he (gcPoints_subset (a := a) (b := b) (c := c) (x := x)
        (y := y) (z := z) 0) (by
          rw [Sum.elim_range]
          exact union_subset (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 3) (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 4)) hc.cb_a
      cb_b := cb_baseChange K₀ hs he (gcPoints_subset (a := a) (b := b) (c := c) (x := x)
        (y := y) (z := z) 1) (by
          rw [Sum.elim_range]
          exact union_subset (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 4) (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 5)) hc.cb_b
      cb_c := cb_baseChange K₀ hs he (gcPoints_subset (a := a) (b := b) (c := c) (x := x)
        (y := y) (z := z) 2) (by
          rw [Sum.elim_range]
          exact union_subset (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 3) (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
            (z := z) 5)) hc.cb_c
      one_le_erk := by
        rw [key (range a) (gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
          (z := z) 0) (finite_range a)]
        exact hc.one_le_erk }

end GroupConfiguration

end

end GroupConfig
