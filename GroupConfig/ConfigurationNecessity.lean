/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Main

/-!
# Necessity of the group configuration hypotheses

Blueprint `sources/group_configuration/08-proof.tex`, `rem:main-props`: the conclusion of
`thm:main` forces the hypotheses of a group configuration, in particular clause (GC4) for `a`.

* `GroupConfig.GroupConfiguration.descend` is the converse of `lem:gc-invariance`(2)
  (`GroupConfig.GroupConfiguration.baseChange`): a configuration over a small subfield `K₀`
  independent from the points is a configuration over `k`.
* `GroupConfig.GroupConfiguration.of_isMainConclusion`: if the conclusion of `thm:main`
  (`GroupConfig.IsMainConclusion`) holds over `k' = acl(k, E)` for a finite set `E` independent
  from the points, then the points form a group configuration over `k`. The configuration of codes
  and values in the conclusion transfers to the interalgebraic original points over `k'`
  (`lem:gc-invariance`(3), `GroupConfig.GroupConfiguration.ofRaclEq`) and then descends to `k`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the necessity claim of `rem:main-props` is complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Algebraicity descends along a base extension independent from the points: a finite set
`Y ⊆ W` algebraic over `K₀ ∪ X`, with `X ⊆ W` and `K₀` independent from `W`, is algebraic over `X`.
Named consumer: `GroupConfig.GroupConfiguration.descend`. -/
private theorem subset_racl_of_indepOver {K₀ W X Y : Set K} (he : IndepOver k ∅ K₀ W)
    (hX : X ⊆ W) (hY : Y ⊆ W) (hYfin : Y.Finite) (h : Y ⊆ racl k (K₀ ∪ X)) :
    Y ⊆ racl k X := by
  have h₁ := (indepOver_union_right_iff.1 (he.mono_right (union_subset hX hY))).2
  rw [empty_union] at h₁
  have h₀ : erk k (X ∪ K₀) Y = 0 := (erk_eq_zero_iff k).2 (by rwa [union_comm])
  rw [h₁.symm.erk_eq (subset_refl _) hYfin] at h₀
  exact (erk_eq_zero_iff k).1 h₀

variable [IsAlgClosed K] [UniversalDomain k K]

/-- (GC4) descends from a small subfield independent from the points (`prop:cb` (Cb6)). Named
consumer: `GroupConfig.GroupConfiguration.descend`. -/
private theorem cb_descend (K₀ : IntermediateField k K) (hs : IsSmall k (K₀ : Set K))
    {W : Set K} (hW : IndepOver k ∅ (K₀ : Set K) W) {ι ι' : Type*} [Finite ι] [Finite ι']
    {p : ι → K} {t : ι' → K} (hp : range p ⊆ W) (ht : range t ⊆ W)
    (h : range p ⊆ racl (↥K₀) (canonicalBase (racl (↥K₀) (range p)) t : Set K)) :
    range p ⊆ racl k (canonicalBase (racl k (range p)) t : Set K) := by
  have _ : IsAlgClosed ↥(racl k (range p)) := isAlgClosed_racl _
  have hW' : IndepOver k ∅ (K₀ : Set K) (racl k W : Set K) := by
    have := indepOver_racl_right_iff.2 hW
    rwa [empty_union] at this
  rw [racl_canonicalBase_base, union_comm (K₀ : Set K) (range p),
    ← racl_union_left (range p) (K₀ : Set K),
    canonicalBase_racl_union_eq (IsSmall.of_finite (finite_range p)).racl hs] at h
  · exact subset_racl_of_indepOver hW'
      ((SetLike.coe_subset_coe.2 (canonicalBase_le _ _)).trans (racl_mono (k := k) hp))
      (hp.trans (subset_racl k W)) (finite_range p) h
  · exact hW'.mono_right (union_subset (ht.trans (subset_racl k W)) (racl_mono (k := k) hp))

namespace GroupConfiguration

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅]
  [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

/-- `lem:gc-invariance`(2), converse: a configuration over a small subfield `K₀` independent from
the points is a configuration over `k`. Named consumer:
`GroupConfig.GroupConfiguration.of_isMainConclusion`. -/
theorem descend (K₀ : IntermediateField k K) (hs : IsSmall k (K₀ : Set K))
    (he : IndepOver k ∅ (K₀ : Set K)
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z))
    (h : GroupConfiguration (↥K₀) a b c x y z) : GroupConfiguration k a b c x y z := by
  have hP : ∀ i, gcPoints a b c x y z i ⊆
      range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z := gcPoints_subset
  have hall : (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z).Finite :=
    (((((finite_range a).union (finite_range b)).union (finite_range c)).union
      (finite_range x)).union (finite_range y)).union (finite_range z)
  -- Ranks of the points over `K₀` are their ranks over `k`.
  have key : ∀ X ⊆ range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z,
      X.Finite → erk (↥K₀) ∅ X = erk k ∅ X := fun X hX hfin ↦ by
    rw [erk_base_empty]
    have := (he.symm.mono_left hX).erk_eq (subset_refl _) hfin
    rwa [empty_union] at this
  -- Closures over `K₀` of sets of points descend to `k`.
  have hracl : ∀ A B : Set K, A ⊆ range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z →
      B ⊆ range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z →
      racl (↥K₀) A = racl (↥K₀) B → racl k A = racl k B := by
    intro A B hA hB hAB
    have h' : (racl k ((K₀ : Set K) ∪ A) : Set K) = racl k ((K₀ : Set K) ∪ B) := by
      rw [← racl_base_coe K₀ A, ← racl_base_coe K₀ B, hAB]
    have hBA : B ⊆ racl k A := subset_racl_of_indepOver he hA hB (hall.subset hB) (by
      rw [h']
      exact subset_union_right.trans (subset_racl k _))
    have hAB' : A ⊆ racl k B := subset_racl_of_indepOver he hB hA (hall.subset hA) (by
      rw [← h']
      exact subset_union_right.trans (subset_racl k _))
    exact le_antisymm (racl_le_of_subset_racl hAB') (racl_le_of_subset_racl hBA)
  exact
    { racl_ab_ac := hracl _ _ (union_subset (hP 0) (hP 1)) (union_subset (hP 0) (hP 2))
        h.racl_ab_ac
      racl_ab_bc := hracl _ _ (union_subset (hP 0) (hP 1)) (union_subset (hP 1) (hP 2))
        h.racl_ab_bc
      racl_ax_ay := hracl _ _ (union_subset (hP 0) (hP 3)) (union_subset (hP 0) (hP 4))
        h.racl_ax_ay
      racl_by_bz := hracl _ _ (union_subset (hP 1) (hP 4)) (union_subset (hP 1) (hP 5))
        h.racl_by_bz
      racl_cx_cz := hracl _ _ (union_subset (hP 2) (hP 3)) (union_subset (hP 2) (hP 5))
        h.racl_cx_cz
      indep i j l hij hil hjl hcol := by
        have h' := h.indep i j l hij hil hjl hcol
        unfold IndepTriple at h' ⊢
        rwa [key _ (union_subset (union_subset (hP i) (hP j)) (hP l))
            (((gcPoints_finite a b c x y z i).union (gcPoints_finite a b c x y z j)).union
              (gcPoints_finite a b c x y z l)),
          key _ (hP i) (gcPoints_finite a b c x y z i),
          key _ (hP j) (gcPoints_finite a b c x y z j),
          key _ (hP l) (gcPoints_finite a b c x y z l)] at h'
      cb_a := cb_descend K₀ hs he (hP 0)
        (by rw [Sum.elim_range]; exact union_subset (hP 3) (hP 4)) h.cb_a
      cb_b := cb_descend K₀ hs he (hP 1)
        (by rw [Sum.elim_range]; exact union_subset (hP 4) (hP 5)) h.cb_b
      cb_c := cb_descend K₀ hs he (hP 2)
        (by rw [Sum.elim_range]; exact union_subset (hP 3) (hP 5)) h.cb_c
      one_le_erk := by
        rw [← key (range a) (hP 0) (finite_range a)]
        exact h.one_le_erk }

/-- `rem:main-props`: the conclusion of `thm:main` (`GroupConfig.IsMainConclusion`) over
`k' = acl(k, E)`, for a finite set `E` independent from the points, forces the points to form a
group configuration over `k`. Its clause (GC4) for `a`, `(of_isMainConclusion hE hind h).cb_a`,
is the remark's claim that this clause is a consequence of the conclusion. -/
theorem of_isMainConclusion {E : Set K} (hE : E.Finite)
    (hind : IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z))
    (h : IsMainConclusion k (racl k E) a b c x y z) : GroupConfiguration k a b c x y z := by
  unfold IsMainConclusion at h
  obtain ⟨_, _, ν, ν', _, _, v, v', f₀, ga, gb, gc, y', _, _, _, _, _, _, _, _, hconf, r₁, r₂, r₃,
    r₄, r₅, r₆, _⟩ := h
  -- The original points are interalgebraic with the configuration of the conclusion over `k'`.
  have hconf' : GroupConfiguration (↥(racl k E)) a b c x y z :=
    hconf.ofRaclEq r₁ r₂ r₃ r₄ r₅ r₆
  have hind' : IndepOver k ∅ (racl k E : Set K)
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) := by
    have := indepOver_racl_left_iff.2 hind
    rwa [empty_union] at this
  exact hconf'.descend (racl k E) (IsSmall.of_finite hE).racl hind'

end GroupConfiguration

end GroupConfig
