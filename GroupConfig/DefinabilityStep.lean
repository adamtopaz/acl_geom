/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.BaseNesting
import GroupConfig.ConfigurationGerm
import GroupConfig.Germ.Triple

/-!
# The definability step

Blueprint `sources/group_configuration/08-proof.tex`, `lem:defstep`.

For a group configuration `(a, b, c, x, y, z)` and the space point `z` with its lines
`{b, y, z}` and `{c, z, x}`, there is a generic copy `e` of `a` independent from the
configuration and conjugates `p₂', q₂'` of `c, x` over `acl(b, y, z)` such that, with
`K₁ = acl(k, e)`, the tuple obtained by enlarging `b` to `(b, p₂')`, `y` to `(y, q₂')` and
replacing `z` by the code `z̃` of its conjugate set over `L = k(b, y, p₂', q₂')` is a group
configuration over `K₁`, pointwise interalgebraic over `K₁` with the original one, in which
`z̃` is definable over `K₁` and the enlarged `b`, `y`; moreover `(y, q₂')` is definable over
`K₁`, the enlarged `b` and `z̃` as soon as `y` is definable over `b, z` and `x` over `c, z`
(`GroupConfiguration.exists_defStep`).  The other space points are handled by relabeling.
The version `GroupConfiguration.exists_defStep_base` applies the step to a configuration over
an intermediate field `K₀ ⊇ k` and states every conclusion over `k`, so that the step can be
iterated without nesting base fields.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:defstep` complete for every space point: `r = z` (`exists_defStep`, with the
relative version `exists_defStep_base`), and `r = x`, `r = y` through the relabelings `swapAB` and
`swapBC.swapAB.swapBC` (`exists_defStep_x`, `exists_defStep_y`).
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem racl_union_union_eq_of_subset {A B C : Set K} (h : C ⊆ racl k (A ∪ B)) :
    racl k (A ∪ (B ∪ C)) = racl k (A ∪ B) := by
  refine le_antisymm (racl_le_of_subset_racl (union_subset ?_ (union_subset ?_ h)))
    (racl_mono (k := k) (union_subset_union_right _ subset_union_left))
  · exact subset_union_left.trans (subset_racl k _)
  · exact subset_union_right.trans (subset_racl k _)

namespace GroupConfiguration

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*}
  [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K}
  {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}
  (hc : GroupConfiguration k a b c x y z)
include hc

/-- `lem:defstep` retaining the rank of its actual generic copy. Named consumer:
`GroupConfiguration.exists_stepI_with_parameterRank`. -/
theorem exists_defStep_with_parameterRank :
    ∃ (e : ι₁ → K) (p₂' : ι₃ → K) (q₂' : ι₄ → K),
      erk k ∅ (range e) = erk k ∅ (range a) ∧
      IndepOver k ∅ (range e) (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      range p₂' ⊆ racl k (range e ∪ range b) ∧ range q₂' ⊆ racl k (range e ∪ range y) ∧
      conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z ⊆
        dcl (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) ∧
      racl k (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z) =
        racl k (range z) ∧
      racl k (range e ∪ (range b ∪ range p₂')) = racl k (range e ∪ range b) ∧
      racl k (range e ∪ (range y ∪ range q₂')) = racl k (range e ∪ range y) ∧
      GroupConfiguration (↥(racl k (range e))) a (Sum.elim b p₂') c x (Sum.elim y q₂')
        (tupleOf (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z)) ∧
      (∀ s : conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z,
        (s : K) ∈ dclAdjoin (racl k (range e))
          (Sum.elim (Sum.elim b p₂') (Sum.elim y q₂'))) ∧
      ((∀ i, y i ∈ dclAdjoin (adjoin k (range b)) z) →
        (∀ i, x i ∈ dclAdjoin (adjoin k (range c)) z) →
        ∀ j, Sum.elim y q₂' j ∈
          dclAdjoin (adjoin k ((racl k (range e) : Set K) ∪ (range b ∪ range p₂')))
            (tupleOf (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z))) := by
  -- A generic copy `e` of `a` over the closure of the configuration.
  have hall : (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z).Finite :=
    (((((finite_range a).union (finite_range b)).union (finite_range c)).union
      (finite_range x)).union (finite_range y)).union (finite_range z)
  obtain ⟨e, he⟩ := exists_isGenericOver (IsSmall.of_finite (k := k) hall).racl a
  have he_ind :
      IndepOver k ∅ (range e) (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) :=
    he.indepOver.mono_right (subset_racl k _)
  -- `a` and `e` are generic points of the locus of `a` over `acl(b, y, z)`.
  have hbyz : (range b ∪ range y ∪ range z).Finite :=
    ((finite_range b).union (finite_range y)).union (finite_range z)
  have hbyz_sub : range b ∪ range y ∪ range z ⊆
      range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z :=
    union_subset (union_subset
      (subset_union_right.trans (subset_union_left.trans (subset_union_left.trans
        (subset_union_left.trans subset_union_left))))
      (subset_union_right.trans subset_union_left)) subset_union_right
  have haN : IsGenericOver (racl k (range b ∪ range y ∪ range z)) a a := by
    refine isGenericOver_self_of_indepOver (IsSmall.of_finite (k := k) hbyz).racl ?_
    have := indepOver_racl_right_iff.2 hc.indepOver_a_byz
    rwa [empty_union] at this
  have heN : IsGenericOver (racl k (range b ∪ range y ∪ range z)) a e :=
    he.of_le (racl_mono (k := k) hbyz_sub)
  obtain ⟨σ, hσ⟩ := haN.exists_algEquiv heN
  have hfix : ∀ s ∈ range b ∪ range y ∪ range z, (σ.restrictScalars k) s = s := fun s hs ↦ by
    change σ s = s
    exact σ.commutes ⟨s, subset_racl k _ hs⟩
  have hσa : ⇑(σ.restrictScalars k) ∘ a = e := funext fun i ↦ hσ i
  have hσb : ⇑(σ.restrictScalars k) ∘ b = b := funext fun i ↦
    hfix _ (subset_union_left (subset_union_left (mem_range_self i)))
  have hσy : ⇑(σ.restrictScalars k) ∘ y = y := funext fun i ↦
    hfix _ (subset_union_left (subset_union_right (mem_range_self i)))
  have hσz : ⇑(σ.restrictScalars k) ∘ z = z := funext fun i ↦
    hfix _ (subset_union_right (mem_range_self i))
  -- The conjugate configuration `(e, b, p₂', q₂', y, z)`.
  obtain ⟨p₂', hp⟩ : ∃ p : ι₃ → K, p = ⇑(σ.restrictScalars k) ∘ c := ⟨_, rfl⟩
  obtain ⟨q₂', hq⟩ : ∃ q : ι₄ → K, q = ⇑(σ.restrictScalars k) ∘ x := ⟨_, rfl⟩
  have hσc := hc.map (σ.restrictScalars k)
  rw [hσa, hσb, hσy, hσz, ← hp, ← hq] at hσc
  have hp₂' : range p₂' ⊆ racl k (range e ∪ range b) := by
    rw [hσc.racl_ab_ac]
    exact subset_union_right.trans (subset_racl k _)
  have hq₂' : range q₂' ⊆ racl k (range e ∪ range y) := by
    rw [← hσc.racl_ax_ay]
    exact subset_union_right.trans (subset_racl k _)
  have hzdcl := hσc.conjCode_z_subset_dcl
  have hzracl := hσc.racl_conjCode_z
  -- Base change to `K₁ = acl(k, e)`.
  have hK₁s : IsSmall k ((racl k (range e) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range e)).racl
  have hK₁ind : IndepOver k ∅ ((racl k (range e) : IntermediateField k K) : Set K)
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) := by
    have := indepOver_racl_left_iff.2 he_ind
    rwa [empty_union] at this
  have hc₁ := hc.baseChange _ hK₁s hK₁ind
  have _ : IsAlgClosed ↥(racl k (range e)) := isAlgClosed_racl _
  have _ : UniversalDomain ↥(racl k (range e)) K := universalDomain_of_isSmall _ hK₁s
  have he_sub : range e ⊆ ((racl k (range e) : IntermediateField k K) : Set K) :=
    subset_racl k _
  have hb₁ : racl k (((racl k (range e) : IntermediateField k K) : Set K) ∪
      (range b ∪ range p₂')) = racl k (((racl k (range e) : IntermediateField k K) : Set K) ∪
      range b) :=
    racl_union_union_eq_of_subset
      (hp₂'.trans (racl_mono (k := k) (union_subset_union_left _ he_sub)))
  have hy₁ : racl k (((racl k (range e) : IntermediateField k K) : Set K) ∪
      (range y ∪ range q₂')) = racl k (((racl k (range e) : IntermediateField k K) : Set K) ∪
      range y) :=
    racl_union_union_eq_of_subset
      (hq₂'.trans (racl_mono (k := k) (union_subset_union_left _ he_sub)))
  refine ⟨e, p₂', q₂', he.erk_empty_eq, he_ind, hp₂', hq₂', hzdcl, hzracl,
    racl_union_union_eq_of_subset hp₂', racl_union_union_eq_of_subset hq₂', ?_, ?_, ?_⟩
  · -- The modified configuration over `K₁`.
    refine hc₁.ofRaclEq rfl ?_ rfl rfl ?_ ?_
    · refine SetLike.coe_injective ?_
      rw [racl_base_coe, racl_base_coe, Sum.elim_range, hb₁]
    · refine SetLike.coe_injective ?_
      rw [racl_base_coe, racl_base_coe, Sum.elim_range, hy₁]
    · refine SetLike.coe_injective ?_
      rw [racl_base_coe, racl_base_coe, range_tupleOf, racl_union_congr rfl hzracl]
  · -- `z̃` is definable over `K₁` and the enlarged points.
    intro s
    unfold dclAdjoin
    rw [restrictScalars_adjoin]
    refine dcl_mono ?_ (hzdcl s.2)
    refine adjoin_le_iff.2 (subset_trans ?_ (subset_adjoin k _))
    rw [Sum.elim_range, Sum.elim_range, Sum.elim_range]
    refine (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_).trans subset_union_right
    · exact subset_union_left.trans subset_union_left
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_left
    · exact subset_union_right.trans subset_union_right
  · -- The clause (4).
    intro hq₁ hq₂ j
    have hL₀L : adjoin k (range b ∪ range p₂') ≤
        adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂') :=
      adjoin.mono k _ _ (union_subset
        (subset_union_left.trans (subset_union_left.trans subset_union_left))
        (subset_union_right.trans subset_union_left))
    have hw : ∀ j, Sum.elim y q₂' j ∈ dclAdjoin (adjoin k (range b ∪ range p₂')) z := by
      intro j
      cases j with
      | inl i =>
        exact dclAdjoin_mono (adjoin.mono k _ _ subset_union_left) z (hq₁ i)
      | inr i =>
        have := mem_dclAdjoin_map (σ.restrictScalars k) (hq₂ i)
        rw [adjoin_map, AlgEquiv.coe_toAlgHom, ← range_comp, hσz, ← hp] at this
        change q₂' i ∈ _
        rw [hq]
        exact dclAdjoin_mono (adjoin.mono k _ _ subset_union_right) z this
    have hwL : ∀ j, Sum.elim y q₂' j ∈ adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂') := by
      intro j
      cases j with
      | inl i =>
        exact subset_adjoin k _
          (subset_union_left (subset_union_left (subset_union_right (mem_range_self i))))
      | inr i => exact subset_adjoin k _ (subset_union_right (mem_range_self i))
    have key := mem_dclAdjoin_conjCode hσc.isIntegral_z hL₀L hw hwL j
    exact dclAdjoin_mono (adjoin.mono k _ _ subset_union_right) _ key

/-- `lem:defstep` for the space point `z` with lines `{b, y, z}` (`p₁ = b`, `q₁ = y`) and
`{c, z, x}` (`p₂ = c`, `q₂ = x`), third line `{a, x, y}`, `p₃ = a`. -/
theorem exists_defStep :
    ∃ (e : ι₁ → K) (p₂' : ι₃ → K) (q₂' : ι₄ → K),
      IndepOver k ∅ (range e) (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      range p₂' ⊆ racl k (range e ∪ range b) ∧ range q₂' ⊆ racl k (range e ∪ range y) ∧
      conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z ⊆
        dcl (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) ∧
      racl k (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z) =
        racl k (range z) ∧
      racl k (range e ∪ (range b ∪ range p₂')) = racl k (range e ∪ range b) ∧
      racl k (range e ∪ (range y ∪ range q₂')) = racl k (range e ∪ range y) ∧
      GroupConfiguration (↥(racl k (range e))) a (Sum.elim b p₂') c x (Sum.elim y q₂')
        (tupleOf (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z)) ∧
      (∀ s : conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z,
        (s : K) ∈ dclAdjoin (racl k (range e))
          (Sum.elim (Sum.elim b p₂') (Sum.elim y q₂'))) ∧
      ((∀ i, y i ∈ dclAdjoin (adjoin k (range b)) z) →
        (∀ i, x i ∈ dclAdjoin (adjoin k (range c)) z) →
        ∀ j, Sum.elim y q₂' j ∈
          dclAdjoin (adjoin k ((racl k (range e) : Set K) ∪ (range b ∪ range p₂')))
            (tupleOf (conjCode (adjoin k (range b ∪ range y ∪ range p₂' ∪ range q₂')) z))) := by
  obtain ⟨e, p₂', q₂', -, h⟩ := hc.exists_defStep_with_parameterRank
  exact ⟨e, p₂', q₂', h⟩

/-- `lem:defstep` for the space point `x`, by the relabeling `swapAB` of the configuration. -/
theorem exists_defStep_x :
    ∃ (e : ι₂ → K) (p₂' : ι₃ → K) (q₂' : ι₆ → K),
      IndepOver k ∅ (range e) (range b ∪ range a ∪ range c ∪ range z ∪ range y ∪ range x) ∧
      range p₂' ⊆ racl k (range e ∪ range a) ∧ range q₂' ⊆ racl k (range e ∪ range y) ∧
      conjCode (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) x ⊆
        dcl (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) ∧
      racl k (conjCode (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) x) =
        racl k (range x) ∧
      racl k (range e ∪ (range a ∪ range p₂')) = racl k (range e ∪ range a) ∧
      racl k (range e ∪ (range y ∪ range q₂')) = racl k (range e ∪ range y) ∧
      GroupConfiguration (↥(racl k (range e))) b (Sum.elim a p₂') c z (Sum.elim y q₂')
        (tupleOf (conjCode (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) x)) ∧
      (∀ s : conjCode (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) x,
        (s : K) ∈ dclAdjoin (racl k (range e))
          (Sum.elim (Sum.elim a p₂') (Sum.elim y q₂'))) ∧
      ((∀ i, y i ∈ dclAdjoin (adjoin k (range a)) x) →
        (∀ i, z i ∈ dclAdjoin (adjoin k (range c)) x) →
        ∀ j, Sum.elim y q₂' j ∈
          dclAdjoin (adjoin k ((racl k (range e) : Set K) ∪ (range a ∪ range p₂')))
            (tupleOf (conjCode (adjoin k (range a ∪ range y ∪ range p₂' ∪ range q₂')) x))) :=
  hc.swapAB.exists_defStep

/-- `lem:defstep` for the space point `y`, by the relabeling `swapBC.swapAB.swapBC` of the
configuration. -/
theorem exists_defStep_y :
    ∃ (e : ι₃ → K) (p₂' : ι₁ → K) (q₂' : ι₄ → K),
      IndepOver k ∅ (range e) (range c ∪ range b ∪ range a ∪ range x ∪ range z ∪ range y) ∧
      range p₂' ⊆ racl k (range e ∪ range b) ∧ range q₂' ⊆ racl k (range e ∪ range z) ∧
      conjCode (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) y ⊆
        dcl (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) ∧
      racl k (conjCode (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) y) =
        racl k (range y) ∧
      racl k (range e ∪ (range b ∪ range p₂')) = racl k (range e ∪ range b) ∧
      racl k (range e ∪ (range z ∪ range q₂')) = racl k (range e ∪ range z) ∧
      GroupConfiguration (↥(racl k (range e))) c (Sum.elim b p₂') a x (Sum.elim z q₂')
        (tupleOf (conjCode (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) y)) ∧
      (∀ s : conjCode (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) y,
        (s : K) ∈ dclAdjoin (racl k (range e))
          (Sum.elim (Sum.elim b p₂') (Sum.elim z q₂'))) ∧
      ((∀ i, z i ∈ dclAdjoin (adjoin k (range b)) y) →
        (∀ i, x i ∈ dclAdjoin (adjoin k (range a)) y) →
        ∀ j, Sum.elim z q₂' j ∈
          dclAdjoin (adjoin k ((racl k (range e) : Set K) ∪ (range b ∪ range p₂')))
            (tupleOf (conjCode (adjoin k (range b ∪ range z ∪ range p₂' ∪ range q₂')) y))) :=
  hc.swapBC.swapAB.swapBC.exists_defStep

end GroupConfiguration

/-! ### The definability step over an intermediate base -/

namespace GroupConfiguration

variable [IsAlgClosed K] {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃]
  [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K}
  {y : ι₅ → K} {z : ι₆ → K}

/-- `lem:defstep` over an intermediate base, retaining the rank of its actual generic copy.
Named consumer: `GroupConfiguration.exists_stepI_with_parameterRank`. -/
theorem exists_defStep_base_with_parameterRank (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hc : GroupConfiguration (↥K₀) a b c x y z) :
    ∃ (e : ι₁ → K) (p₂' : ι₃ → K) (q₂' : ι₄ → K) (Z : Set K) (_ : Finite ↥Z),
      erk k (K₀ : Set K) (range e) = erk k (K₀ : Set K) (range a) ∧
      IndepOver k (K₀ : Set K) (range e)
        (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      range p₂' ⊆ racl k ((K₀ : Set K) ∪ range e ∪ range b) ∧
      range q₂' ⊆ racl k ((K₀ : Set K) ∪ range e ∪ range y) ∧
      racl k ((K₀ : Set K) ∪ Z) = racl k ((K₀ : Set K) ∪ range z) ∧
      racl k ((K₀ : Set K) ∪ range e ∪ (range b ∪ range p₂')) =
        racl k ((K₀ : Set K) ∪ range e ∪ range b) ∧
      racl k ((K₀ : Set K) ∪ range e ∪ (range y ∪ range q₂')) =
        racl k ((K₀ : Set K) ∪ range e ∪ range y) ∧
      GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range e))) a (Sum.elim b p₂') c x
        (Sum.elim y q₂') (tupleOf Z) ∧
      (∀ s ∈ Z, s ∈ dclAdjoin (racl k ((K₀ : Set K) ∪ range e))
        (Sum.elim (Sum.elim b p₂') (Sum.elim y q₂'))) ∧
      ((∀ i, y i ∈ dclAdjoin (adjoin k ((K₀ : Set K) ∪ range b)) z) →
        (∀ i, x i ∈ dclAdjoin (adjoin k ((K₀ : Set K) ∪ range c)) z) →
        ∀ j, Sum.elim y q₂' j ∈
          dclAdjoin
            (adjoin k ((racl k ((K₀ : Set K) ∪ range e) : Set K) ∪ (range b ∪ range p₂')))
            (tupleOf Z)) := by
  obtain ⟨e, p₂', q₂', hrank, he, hp, hq, -, hZ, hbp, hyq, hc', hdcl, himp⟩ :=
    hc.exists_defStep_with_parameterRank
  have hK₀ : (K₀ : Set K) ⊆ racl k ((K₀ : Set K) ∪ range e) :=
    subset_union_left.trans (subset_racl k _)
  refine ⟨e, p₂', q₂', conjCode (adjoin (↥K₀) (range b ∪ range y ∪ range p₂' ∪ range q₂')) z,
    inferInstance, (by simpa only [erk_base_empty] using hrank),
    (indepOver_base_iff K₀ _ _).1 he, ?_, ?_, ?_, ?_, ?_,
    ofNested K₀ (range e) hc', ?_, ?_⟩
  · rw [union_assoc, ← racl_base_coe K₀ (range e ∪ range b)]
    exact hp
  · rw [union_assoc, ← racl_base_coe K₀ (range e ∪ range y)]
    exact hq
  · exact SetLike.coe_injective (by rw [← racl_base_coe K₀, ← racl_base_coe K₀, hZ])
  · exact SetLike.coe_injective (by
      rw [union_assoc, union_assoc, ← racl_base_coe K₀ (range e ∪ (range b ∪ range p₂')),
        ← racl_base_coe K₀ (range e ∪ range b), hbp])
  · exact SetLike.coe_injective (by
      rw [union_assoc, union_assoc, ← racl_base_coe K₀ (range e ∪ (range y ∪ range q₂')),
        ← racl_base_coe K₀ (range e ∪ range y), hyq])
  · exact fun s hs ↦ (mem_dclAdjoin_congr (racl_base_coe K₀ (range e)) _ s).1 (hdcl ⟨s, hs⟩)
  · intro hy hx j
    have hy' : ∀ i, y i ∈ dclAdjoin (adjoin (↥K₀) (range b)) z := fun i ↦
      (mem_dclAdjoin_congr (coe_adjoin_base K₀ (range b)) z _).2 (hy i)
    have hx' : ∀ i, x i ∈ dclAdjoin (adjoin (↥K₀) (range c)) z := fun i ↦
      (mem_dclAdjoin_congr (coe_adjoin_base K₀ (range c)) z _).2 (hx i)
    refine (mem_dclAdjoin_congr ?_ _ _).1 (himp hy' hx' j)
    rw [coe_adjoin_base K₀, racl_base_coe K₀ (range e), ← union_assoc, union_eq_right.2 hK₀]

/-- `lem:defstep` for a configuration over an intermediate field `K₀ ⊇ k`, with every
conclusion stated over `k`: the new base is `acl_k(K₀ ∪ e)` and the code `z̃` of the conjugate
set of `z` is only kept as a finite set `Z` with `tupleOf Z = z̃`. -/
theorem exists_defStep_base (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hc : GroupConfiguration (↥K₀) a b c x y z) :
    ∃ (e : ι₁ → K) (p₂' : ι₃ → K) (q₂' : ι₄ → K) (Z : Set K) (_ : Finite ↥Z),
      IndepOver k (K₀ : Set K) (range e)
        (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      range p₂' ⊆ racl k ((K₀ : Set K) ∪ range e ∪ range b) ∧
      range q₂' ⊆ racl k ((K₀ : Set K) ∪ range e ∪ range y) ∧
      racl k ((K₀ : Set K) ∪ Z) = racl k ((K₀ : Set K) ∪ range z) ∧
      racl k ((K₀ : Set K) ∪ range e ∪ (range b ∪ range p₂')) =
        racl k ((K₀ : Set K) ∪ range e ∪ range b) ∧
      racl k ((K₀ : Set K) ∪ range e ∪ (range y ∪ range q₂')) =
        racl k ((K₀ : Set K) ∪ range e ∪ range y) ∧
      GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range e))) a (Sum.elim b p₂') c x
        (Sum.elim y q₂') (tupleOf Z) ∧
      (∀ s ∈ Z, s ∈ dclAdjoin (racl k ((K₀ : Set K) ∪ range e))
        (Sum.elim (Sum.elim b p₂') (Sum.elim y q₂'))) ∧
      ((∀ i, y i ∈ dclAdjoin (adjoin k ((K₀ : Set K) ∪ range b)) z) →
        (∀ i, x i ∈ dclAdjoin (adjoin k ((K₀ : Set K) ∪ range c)) z) →
        ∀ j, Sum.elim y q₂' j ∈
          dclAdjoin
            (adjoin k ((racl k ((K₀ : Set K) ∪ range e) : Set K) ∪ (range b ∪ range p₂')))
            (tupleOf Z)) := by
  obtain ⟨e, p₂', q₂', Z, hZ, -, h⟩ := exists_defStep_base_with_parameterRank K₀ hc
  exact ⟨e, p₂', q₂', Z, hZ, h⟩

end GroupConfiguration

end

end GroupConfig
