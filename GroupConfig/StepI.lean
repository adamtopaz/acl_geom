/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.DefinabilityStep

/-!
# Step I: making the lines definable

Blueprint `sources/group_configuration/08-proof.tex`, `prop:stepI`.

Applying the definability step (`lem:defstep`) three times, to the space points `z`, `x` and
`y` in turn, replaces a group configuration `(a, b, c, x, y, z)` over `k` by one over
`k' = acl(k, e)`, for a finite tuple `e` independent from the configuration, which is
pointwise interalgebraic over `k'` with the original one and in which `z'` is definable over
`k', b', y'` and `y'` is definable over `k', b', z'` (`GroupConfiguration.exists_stepI`).
The consequences drawn in the blueprint (the germ `g_{b'}` and the generic set `𝓕`) are
derived in the next step.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the first part of `prop:stepI` (the configuration `𝔠'`) complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

namespace GroupConfiguration

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*}
  [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K}
  {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}
  (hc : GroupConfiguration k a b c x y z)
include hc

/-- `prop:stepI` retaining the total rank of its three actual generic copies.
Named consumer: `GroupConfiguration.exists_main_with_parameterRank`. -/
theorem exists_stepI_with_parameterRank :
    ∃ E : Set K, E.Finite ∧ erk k ∅ E = 3 * erk k ∅ (range a) ∧
      IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      ∃ (κ₁ κ₂ κ₃ κ₄ κ₅ κ₆ : Type u) (_ : Finite κ₁) (_ : Finite κ₂) (_ : Finite κ₃)
        (_ : Finite κ₄) (_ : Finite κ₅) (_ : Finite κ₆) (a' : κ₁ → K) (b' : κ₂ → K)
        (c' : κ₃ → K) (x' : κ₄ → K) (y' : κ₅ → K) (z' : κ₆ → K),
        GroupConfiguration (↥(racl k E)) a' b' c' x' y' z' ∧
        racl k (E ∪ range a') = racl k (E ∪ range a) ∧
        racl k (E ∪ range b') = racl k (E ∪ range b) ∧
        racl k (E ∪ range c') = racl k (E ∪ range c) ∧
        racl k (E ∪ range x') = racl k (E ∪ range x) ∧
        racl k (E ∪ range y') = racl k (E ∪ range y) ∧
        racl k (E ∪ range z') = racl k (E ∪ range z) ∧
        (∀ j, z' j ∈ dclAdjoin (adjoin (↥(racl k E)) (range b')) y') ∧
        (∀ j, y' j ∈ dclAdjoin (adjoin (↥(racl k E)) (range b')) z') := by
  /- Step 1: the space point `z`, lines `{b, y, z}` and `{c, z, x}`. -/
  obtain ⟨e₁, c', x', he₁rank, he₁, -, -, -, hZ₁, hb₁, hy₁, hc₁, hzt, -⟩ :=
    hc.exists_defStep_with_parameterRank
  obtain ⟨Z₁, _, hZ₁, hc₁, hzt⟩ : ∃ (Z : Set K) (_ : Finite ↥Z), racl k Z = racl k (range z) ∧
      GroupConfiguration (↥(racl k (range e₁))) a (Sum.elim b c') c x (Sum.elim y x')
        (tupleOf Z) ∧
      ∀ s ∈ Z, s ∈ dclAdjoin (racl k (range e₁)) (Sum.elim (Sum.elim b c') (Sum.elim y x')) :=
    ⟨_, inferInstance, hZ₁, hc₁, fun s hs ↦ hzt ⟨s, hs⟩⟩
  /- Step 2: over `K₁ = acl(k, e₁)`, the space point `x`, lines `{a, x, y₁}` and `{c, z̃, x}`;
  the relabeling `swapAB` moves `x` to the position of `z`. -/
  have _ : IsAlgClosed ↥(racl k (range e₁)) := isAlgClosed_racl _
  have _ : UniversalDomain ↥(racl k (range e₁)) K :=
    universalDomain_of_isSmall _ (IsSmall.of_finite (finite_range e₁)).racl
  obtain ⟨e₂, c'', z'', Z₂, _, he₂rank, he₂, -, -, hZ₂, ha₂, hy₂, hc₂, hxt, -⟩ :=
    hc₁.swapAB.exists_defStep_base_with_parameterRank (racl k (range e₁))
  replace hc₂ := hc₂.swapAB
  /- Step 3: over `K₂ = acl(K₁, e₂)`, the space point `y₂`, lines `{b₁, y₂, z̃}` and
  `{a₂, x̃, y₂}`; the relabeling `swapBC ∘ swapAB ∘ swapBC` moves `y` to the position of `z`. -/
  have _ : IsAlgClosed ↥(racl k ((racl k (range e₁) : Set K) ∪ range e₂)) := isAlgClosed_racl _
  have _ : UniversalDomain ↥(racl k ((racl k (range e₁) : Set K) ∪ range e₂)) K :=
    universalDomain_of_isSmall _
      ((IsSmall.of_finite (finite_range e₁)).racl.union (IsSmall.of_finite (finite_range e₂))).racl
  obtain ⟨e₃, a', x''', Z₃, _, he₃rank, he₃, -, -, hZ₃, hb₃, hz₃, hc₃, hyt, himp₃⟩ :=
    hc₂.swapBC.swapAB.swapBC.exists_defStep_base_with_parameterRank
      (racl k ((racl k (range e₁) : Set K) ∪ range e₂))
  replace hc₃ := hc₃.swapBC.swapAB.swapBC
  -- The three actual generic copies each contribute the original group rank.
  have hA₁ : erk k (range e₁) (range a) = erk k ∅ (range a) := by
    simpa only [empty_union] using he₁.symm.erk_eq
      (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))) (finite_range a)
  have hB₁ : erk k (racl k (range e₁) : Set K) (range (Sum.elim b c')) =
      erk k ∅ (range a) := by
    rw [← erk_base_empty (racl k (range e₁)), hc₁.erk_b_eq, erk_base_empty, erk_racl_base]
    exact hA₁
  have he₂rank' : erk k (range e₁) (range e₂) = erk k ∅ (range a) :=
    (erk_racl_base k _ _).symm.trans (he₂rank.trans hB₁)
  have hB₂ : erk k ((racl k (range e₁) : Set K) ∪ range e₂) (range (Sum.elim b c')) =
      erk k (racl k (range e₁) : Set K) (range (Sum.elim b c')) :=
    he₂.symm.erk_eq (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
      (finite_range (Sum.elim b c'))
  have hC₂ : erk k (racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) (range c) =
      erk k ∅ (range a) := by
    rw [← erk_base_empty (racl k ((racl k (range e₁) : Set K) ∪ range e₂)),
      hc₂.erk_c_eq, ← hc₂.erk_b_eq, erk_base_empty, erk_racl_base, hB₂, hB₁]
  have he₃rank' : erk k (range e₁ ∪ range e₂) (range e₃) = erk k ∅ (range a) := by
    have h := he₃rank.trans hC₂
    rwa [racl_union_left, erk_racl_base] at h
  have hErank : erk k ∅ (range e₁ ∪ range e₂ ∪ range e₃) = 3 * erk k ∅ (range a) := by
    rw [erk_union_eq, erk_union_eq]
    simp only [empty_union, he₁rank, he₂rank', he₃rank']
    ring
  /- The final base `k' = acl(k, e₁ e₂ e₃)`. -/
  have hK₃ : racl k ((racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) ∪ range e₃) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃) := by
    rw [racl_union_left, union_assoc, racl_union_left, ← union_assoc]
  rw [hK₃] at hc₃ hyt himp₃
  have hEfin : (range e₁ ∪ range e₂ ∪ range e₃).Finite :=
    ((finite_range e₁).union (finite_range e₂)).union (finite_range e₃)
  have _ : UniversalDomain ↥(racl k (range e₁ ∪ range e₂ ∪ range e₃)) K :=
    universalDomain_of_isSmall _ (IsSmall.of_finite hEfin).racl
  -- Inclusions of the intermediate bases into the final one.
  have hE₁ : range e₁ ⊆ racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    (subset_union_left.trans subset_union_left).trans (subset_racl k _)
  have hE₁₂ : range e₁ ∪ range e₂ ⊆ racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    subset_union_left.trans (subset_racl k _)
  have hK₁ : (racl k (range e₁) : Set K) ⊆ racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    racl_mono (k := k) (subset_union_left.trans subset_union_left)
  have hK₁e₂ : (racl k (range e₁) : Set K) ∪ range e₂ ⊆
      racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    union_subset hK₁ ((subset_union_right.trans subset_union_left).trans (subset_racl k _))
  have hK₂ : (racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) ⊆
      racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    racl_le_of_subset_racl hK₁e₂
  have hK₂e₃ : (racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) ∪ range e₃ ⊆
      racl k (range e₁ ∪ range e₂ ∪ range e₃) :=
    union_subset hK₂ (subset_union_right.trans (subset_racl k _))
  have hK₁K₂ : (racl k (range e₁) : Set K) ⊆
      racl k ((racl k (range e₁) : Set K) ∪ range e₂) :=
    subset_union_left.trans (subset_racl k _)
  -- Interalgebraicity over `k'`, point by point.
  simp only [Sum.elim_range, range_tupleOf] at hb₁ hy₁ ha₂ hy₂ hZ₃ hb₃ hz₃ he₂ he₃
  have ia : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (range a ∪ range c'')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range a) :=
    racl_union_congr_of_subset ha₂ hK₁e₂
  have ib₁ : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (range b ∪ range c')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range b) :=
    racl_union_congr_of_subset hb₁ hE₁
  have ib : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (range b ∪ range c' ∪ range a')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range b) :=
    (racl_union_congr_of_subset hb₃ hK₂e₃).trans ib₁
  have ix : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ Z₂) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range x) :=
    racl_union_congr_of_subset hZ₂ hK₁
  have iy₁ : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (range y ∪ range x')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range y) :=
    racl_union_congr_of_subset hy₁ hE₁
  have iy₂ : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (range y ∪ range x' ∪ range z'')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range y) :=
    (racl_union_congr_of_subset hy₂ hK₁e₂).trans iy₁
  have iy : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ Z₃) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range y) :=
    (racl_union_congr_of_subset hZ₃ hK₂).trans iy₂
  have iz₁ : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ Z₁) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range z) :=
    racl_union_congr rfl hZ₁
  have iz : racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ (Z₁ ∪ range x''')) =
      racl k (range e₁ ∪ range e₂ ∪ range e₃ ∪ range z) :=
    (racl_union_congr_of_subset hz₃ hK₂e₃).trans iz₁
  -- Independence of `e₁ e₂ e₃` from the configuration (`R:trans`).
  have hind : IndepOver k ∅ (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z)
      (range e₁ ∪ range e₂ ∪ range e₃) := by
    refine indepOver_union_right_iff.2 ⟨indepOver_union_right_iff.2 ⟨he₁.symm, ?_⟩, ?_⟩
    · rw [empty_union]
      refine (indepOver_congr_left ?_).1 ((indepOver_racl_base_iff _ _ _).1 he₂.symm)
      have hperm : range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z =
          range b ∪ range a ∪ range c ∪ range z ∪ range y ∪ range x := by ac_rfl
      rw [hperm]
      exact racl_union_union_congr (racl_union_union_congr (racl_union_union_congr
        (racl_union_union_congr (racl_union_union_congr hb₁.symm rfl) rfl)
        (racl_union_congr rfl hZ₁.symm)) hy₁.symm) rfl
    · rw [empty_union]
      have h := (indepOver_congr_base (racl_union_left (k := k) (range e₁) (range e₂))).1
        ((indepOver_racl_base_iff _ _ _).1 he₃.symm)
      refine (indepOver_congr_left ?_).1 h
      have hperm : range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z =
          range c ∪ range b ∪ range a ∪ range x ∪ range z ∪ range y := by ac_rfl
      rw [hperm]
      have hE₁' : range e₁ ⊆ racl k (range e₁ ∪ range e₂) :=
        subset_union_left.trans (subset_racl k _)
      have hK₁' : (racl k (range e₁) : Set K) ⊆ racl k (range e₁ ∪ range e₂) :=
        racl_mono (k := k) subset_union_left
      have hK₁e₂' : (racl k (range e₁) : Set K) ∪ range e₂ ⊆ racl k (range e₁ ∪ range e₂) :=
        union_subset hK₁' (subset_union_right.trans (subset_racl k _))
      exact racl_union_union_congr (racl_union_union_congr (racl_union_union_congr
        (racl_union_union_congr (racl_union_union_congr rfl
          (racl_union_congr_of_subset hb₁ hE₁').symm)
          (racl_union_congr_of_subset ha₂ hK₁e₂').symm)
          (racl_union_congr_of_subset hZ₂ hK₁').symm)
          (racl_union_congr rfl hZ₁.symm))
        ((racl_union_congr_of_subset hy₁ hE₁').symm.trans
          (racl_union_congr_of_subset hy₂ hK₁e₂').symm)
  -- The definability clauses.
  have hyp1 : ∀ i, tupleOf Z₁ i ∈ dclAdjoin (adjoin k
      ((racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) ∪ range (Sum.elim b c')))
      (Sum.elim (Sum.elim y x') z'') := fun i ↦
    mem_dclAdjoin_mono' (by
      rw [Sum.elim_range (Sum.elim b c') (Sum.elim y x'), Sum.elim_range (Sum.elim y x') z'']
      exact union_subset
        ((hK₁K₂.trans (subset_union_left.trans (subset_adjoin k _))).trans subset_union_left)
        (union_subset ((subset_union_right.trans (subset_adjoin k _)).trans subset_union_left)
          (subset_union_left.trans subset_union_right))) (hzt i i.2)
  have hyp2 : ∀ i, tupleOf Z₂ i ∈ dclAdjoin (adjoin k
      ((racl k ((racl k (range e₁) : Set K) ∪ range e₂) : Set K) ∪ range (Sum.elim a c'')))
      (Sum.elim (Sum.elim y x') z'') := fun i ↦
    mem_dclAdjoin_mono' (by
      rw [Sum.elim_range (Sum.elim a c'') (Sum.elim (Sum.elim y x') z'')]
      exact union_subset ((subset_union_left.trans (subset_adjoin k _)).trans subset_union_left)
        (union_subset ((subset_union_right.trans (subset_adjoin k _)).trans subset_union_left)
          subset_union_right)) (hxt i i.2)
  have hzdcl := himp₃ hyp1 hyp2
  -- Assemble, re-indexing the group points by their ranges.
  refine ⟨range e₁ ∪ range e₂ ∪ range e₃, hEfin, hErank, hind.symm, ↥(range (Sum.elim a c'')),
    ↥(range (Sum.elim (Sum.elim b c') a')), ↥(range c), ↥Z₂, ↥Z₃, ↥Z₁ ⊕ ↥Z₂, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    tupleOf (range (Sum.elim a c'')), tupleOf (range (Sum.elim (Sum.elim b c') a')),
    tupleOf (range c), tupleOf Z₂, tupleOf Z₃, Sum.elim (tupleOf Z₁) x''',
    hc₃.ofRaclEq (by rw [range_tupleOf]) (by rw [range_tupleOf]) (by rw [range_tupleOf]) rfl rfl
      rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [range_tupleOf, Sum.elim_range]
  · rwa [range_tupleOf, Sum.elim_range, Sum.elim_range]
  · rw [range_tupleOf]
  · rwa [range_tupleOf]
  · rwa [range_tupleOf]
  · rwa [Sum.elim_range, range_tupleOf]
  · intro j
    refine (mem_dclAdjoin_congr ?_ _ _).1 (hzdcl j)
    simp only [range_tupleOf, Sum.elim_range, coe_adjoin_base]
  · intro j
    refine mem_dclAdjoin_mono' ?_ (hyt j j.2)
    rw [range_tupleOf, Sum.elim_range (Sum.elim (Sum.elim b c') a') (Sum.elim (tupleOf Z₁) x''')]
    exact union_subset ((coe_subset_adjoin _ _).trans subset_union_left)
      (union_subset ((subset_adjoin _ _).trans subset_union_left) subset_union_right)

/-- `prop:stepI`: there is a finite set `E` independent from the configuration such that, over
`k' = acl(k, E)`, there is a group configuration pointwise interalgebraic over `k'` with the
given one in which `z'` is definable over `k', b', y'` and `y'` over `k', b', z'`. -/
theorem exists_stepI :
    ∃ E : Set K, E.Finite ∧
      IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      ∃ (κ₁ κ₂ κ₃ κ₄ κ₅ κ₆ : Type u) (_ : Finite κ₁) (_ : Finite κ₂) (_ : Finite κ₃)
        (_ : Finite κ₄) (_ : Finite κ₅) (_ : Finite κ₆) (a' : κ₁ → K) (b' : κ₂ → K)
        (c' : κ₃ → K) (x' : κ₄ → K) (y' : κ₅ → K) (z' : κ₆ → K),
        GroupConfiguration (↥(racl k E)) a' b' c' x' y' z' ∧
        racl k (E ∪ range a') = racl k (E ∪ range a) ∧
        racl k (E ∪ range b') = racl k (E ∪ range b) ∧
        racl k (E ∪ range c') = racl k (E ∪ range c) ∧
        racl k (E ∪ range x') = racl k (E ∪ range x) ∧
        racl k (E ∪ range y') = racl k (E ∪ range y) ∧
        racl k (E ∪ range z') = racl k (E ∪ range z) ∧
        (∀ j, z' j ∈ dclAdjoin (adjoin (↥(racl k E)) (range b')) y') ∧
        (∀ j, y' j ∈ dclAdjoin (adjoin (↥(racl k E)) (range b')) z') := by
  obtain ⟨E, hEfin, -, h⟩ := hc.exists_stepI_with_parameterRank
  exact ⟨E, hEfin, h⟩

end GroupConfiguration

end

end GroupConfig
