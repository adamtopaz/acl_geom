/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Translation
import GroupConfig.Germ.HomogeneousSpace

/-!
# The homogeneous space of the translations of the affine line

Blueprint `sources/group_configuration/05-hrushovski-weil.tex`, `rem:connected`: for the group of
translations of the affine line, the homogeneous space `S` of `thm:hw` is `K`, through
`(γ, y) ↦ γ + y`.

* `GroupConfig.Germ.Translation.spaceEquiv` is the actual equivalence `S ≃ K`, with
  `(τ_a, y) ↦ a + y` (`GroupConfig.Germ.Translation.spaceEquiv_ofPair`). Two pairs are
  identified iff their sums agree (`GroupConfig.Germ.Translation.ofPair_eq_ofPair_iff_add`), and
  the group acts by translation (`GroupConfig.Germ.Translation.spaceEquiv_smul`).
* The image of the generic points is the set of transcendental elements
  (`GroupConfig.Germ.Translation.spaceEquiv_iota`,
  `GroupConfig.Germ.Translation.range_spaceEquiv_iota`).
* The class `[-t, t]` is `0` (`GroupConfig.Germ.Translation.spaceEquiv_zeroClass`) and has no
  presentation `γ · ι(y)` with `y` independent from `γ`
  (`GroupConfig.Germ.Translation.zeroClass_ne_smul_iota`): such a presentation equals `ι(γ(y))`,
  a transcendental element.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the translation example of `rem:connected` is complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {x₀ c₀ : K}

namespace Germ

namespace Translation

/-- The translations are the members of the group. -/
theorem translation_mem_prodSet (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) (a : K) :
    translation hx₀ a ∈ IsHW.prodSet (translation hx₀ c₀) :=
  (Set.ext_iff.1 (prodSet_translation hx₀ hc₀) _).2 ⟨a, rfl⟩

/-- The translation parameter of a member of the group of translations. -/
def translationParam (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    {γ : Germ k ![x₀] ![x₀]} (hγ : γ ∈ IsHW.prodSet (translation hx₀ c₀)) : K :=
  ((Set.ext_iff.1 (prodSet_translation hx₀ hc₀) γ).1 hγ).choose

/-- The translation by the parameter of a member of the group is that member. -/
theorem translation_translationParam (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) {γ : Germ k ![x₀] ![x₀]}
    (hγ : γ ∈ IsHW.prodSet (translation hx₀ c₀)) :
    translation hx₀ (translationParam hx₀ hc₀ hγ) = γ :=
  ((Set.ext_iff.1 (prodSet_translation hx₀ hc₀) γ).1 hγ).choose_spec

/-- The parameter of the translation by `a` is `a`. -/
theorem translationParam_eq (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    {γ : Germ k ![x₀] ![x₀]} (hγ : γ ∈ IsHW.prodSet (translation hx₀ c₀)) {a : K}
    (h : γ = translation hx₀ a) : translationParam hx₀ hc₀ hγ = a :=
  translation_injective hx₀ ((translation_translationParam hx₀ hc₀ hγ).trans h)

/-- A composite of translations at a generic point, for a parameter outside `acl(a, y)`. Named
consumer: `rel_iff_pairValue_eq`. -/
private theorem evalGen_mul_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) {a c : K}
    {y : Fin 1 → K} (hy : IsGen k ![x₀] y) (hc : c ∉ racl k (({a} : Set K) ∪ range y)) :
    (translation hx₀ c * translation hx₀ a).evalGen y = fun _ ↦ y 0 + (c + a) := by
  rw [translation_mul]
  refine evalGen_translation hx₀ (c + a) hy ?_
  have hca : c + a ∉ racl k (range y) := fun h ↦ hc (by
    have h' := sub_mem (racl_mono (k := k) subset_union_right h)
      (subset_racl k _ (Or.inl (mem_singleton a) : a ∈ ({a} : Set K) ∪ range y))
    simpa using h')
  refine IndepOver.symm (indepOver_of_erk_eq (finite_singleton _) ?_)
  rw [empty_union, erk_singleton_eq_one hca,
    erk_singleton_eq_one fun h ↦ hca (racl_mono (k := k) (empty_subset _) h)]

/-- The value `a + y` of a pair `(τ_a, y)`. -/
def pairValue (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    (p : Pair (translation hx₀ c₀)) : K :=
  translationParam hx₀ hc₀ p.mem + p.pt 0

/-- `rem:connected`: two pairs are related iff their values agree. -/
theorem rel_iff_pairValue_eq (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    (p q : Pair (translation hx₀ c₀)) :
    p.Rel q ↔ pairValue hx₀ hc₀ p = pairValue hx₀ hc₀ q := by
  have hpa := (translation_translationParam hx₀ hc₀ p.mem).symm
  have hqb := (translation_translationParam hx₀ hc₀ q.mem).symm
  have hmem {r : Pair (translation hx₀ c₀)} {d : K} (hd : r.γ = translation hx₀ d) :
      ({d} : Set K) ∪ range r.pt ⊆ r.base := by
    refine union_subset (singleton_subset_iff.2 (r.cb_subset_base ?_)) r.range_subset_base
    rw [hd, cb_translation]
    exact subset_adjoin k _ rfl
  have key : ∀ h ∈ orbit (translation hx₀ c₀),
      IndepOver k ∅ (h.cb : Set K) (p.base ∪ q.base) →
        ((h * p.γ).evalGen p.pt = (h * q.γ).evalGen q.pt ↔
          pairValue hx₀ hc₀ p = pairValue hx₀ hc₀ q) := by
    intro h hh hind
    rw [orbit_translation hx₀ hc₀] at hh
    obtain ⟨c, hc, rfl⟩ := hh
    rw [cb_translation] at hind
    have hcB : c ∉ racl k (p.base ∪ q.base) :=
      not_mem_racl_of_indepOver hc (hind.mono_left (subset_adjoin k _))
    conv_lhs => rw [hpa, hqb]
    rw [evalGen_mul_translation hx₀ p.isGen
        fun h ↦ hcB (racl_mono (k := k) ((hmem hpa).trans subset_union_left) h),
      evalGen_mul_translation hx₀ q.isGen
        fun h ↦ hcB (racl_mono (k := k) ((hmem hqb).trans subset_union_right) h)]
    unfold pairValue
    constructor
    · intro he
      linear_combination congrFun he 0
    · intro he
      funext j
      linear_combination he
  constructor
  · intro hr
    obtain ⟨h, hh, hind⟩ := exists_mem_orbit_indepOver (translation hx₀ c₀)
      (p.isSmall_base.union q.isSmall_base)
    exact (key h hh hind).1 (hr h hh hind)
  · intro hv h hh hind
    exact (key h hh hind).2 hv

/-- `rem:connected`: the homogeneous space of the translations is `K`. -/
def spaceEquiv (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K)) :
    (isHW_translation hx₀ hc₀).Space ≃ K where
  toFun := Quotient.lift (pairValue hx₀ hc₀) fun p q h ↦
    (rel_iff_pairValue_eq hx₀ hc₀ p q).1 h
  invFun x := (isHW_translation hx₀ hc₀).ofPair
    ⟨translation hx₀ (x - x₀), translation_mem_prodSet hx₀ hc₀ _, ![x₀], rfl⟩
  left_inv s := by
    refine (isHW_translation hx₀ hc₀).ind (fun p ↦ ?_) s
    refine (isHW_translation hx₀ hc₀).ofPair_eq_ofPair.2
      ((rel_iff_pairValue_eq hx₀ hc₀ _ p).2 ?_)
    change translationParam hx₀ hc₀ _ + x₀ = _
    rw [translationParam_eq hx₀ hc₀ _ rfl]
    change pairValue hx₀ hc₀ p - x₀ + x₀ = pairValue hx₀ hc₀ p
    ring
  right_inv x := by
    change translationParam hx₀ hc₀ _ + x₀ = x
    rw [translationParam_eq hx₀ hc₀ _ rfl]
    ring

/-- `rem:connected`: the pair `(τ_a, y)` is the element `a + y` of `K`. -/
theorem spaceEquiv_ofPair (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    (p : Pair (translation hx₀ c₀)) {a : K} (ha : p.γ = translation hx₀ a) :
    spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).ofPair p) = a + p.pt 0 := by
  change translationParam hx₀ hc₀ p.mem + p.pt 0 = _
  rw [translationParam_eq hx₀ hc₀ p.mem ha]

/-- `rem:connected`: `(γ, y)` and `(γ', y')` are identified iff `γ + y = γ' + y'`. -/
theorem ofPair_eq_ofPair_iff_add (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) (p q : Pair (translation hx₀ c₀)) {a b : K}
    (ha : p.γ = translation hx₀ a) (hb : q.γ = translation hx₀ b) :
    (isHW_translation hx₀ hc₀).ofPair p = (isHW_translation hx₀ hc₀).ofPair q ↔
      a + p.pt 0 = b + q.pt 0 := by
  rw [(isHW_translation hx₀ hc₀).ofPair_eq_ofPair, rel_iff_pairValue_eq hx₀ hc₀]
  unfold pairValue
  rw [translationParam_eq hx₀ hc₀ p.mem ha, translationParam_eq hx₀ hc₀ q.mem hb]

/-- `rem:connected`: a generic point `y` of the affine line is the element `y` of `K`. -/
theorem spaceEquiv_iota (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    {y : Fin 1 → K} (hy : IsGen k ![x₀] y) :
    spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).iota hy) = y 0 := by
  rw [IsHW.iota, spaceEquiv_ofPair hx₀ hc₀ ((isHW_translation hx₀ hc₀).onePair hy)
    (translation_zero hx₀).symm, zero_add]
  rfl

/-- `rem:connected`: the image of the generic points is the set of transcendental elements. -/
theorem range_spaceEquiv_iota (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) :
    (range fun y : {y : Fin 1 → K // IsGen k ![x₀] y} ↦
      spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).iota y.2)) =
        {x | x ∉ racl k (∅ : Set K)} := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    change spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).iota hy) ∉ racl k (∅ : Set K)
    rw [spaceEquiv_iota]
    exact (isGen_translation_iff hx₀ y).1 hy
  · intro hx
    refine ⟨⟨![x], (isGen_translation_iff hx₀ _).2 (show ![x] 0 ∉ racl k (∅ : Set K) from hx)⟩, ?_⟩
    change spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).iota _) = x
    rw [spaceEquiv_iota]
    rfl

/-- `rem:connected`: the group acts on `K` by translation. -/
theorem spaceEquiv_smul (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    (a : K) (s : (isHW_translation hx₀ hc₀).Space) :
    spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).ofMem (translation_mem_prodSet hx₀ hc₀ a) • s) =
      a + spaceEquiv hx₀ hc₀ s := by
  refine (isHW_translation hx₀ hc₀).ind (fun p ↦ ?_) s
  have hpb := (translation_translationParam hx₀ hc₀ p.mem).symm
  have hγ : ((isHW_translation hx₀ hc₀).smulPair
      ((isHW_translation hx₀ hc₀).ofMem (translation_mem_prodSet hx₀ hc₀ a)) p).γ =
        translation hx₀ (a + translationParam hx₀ hc₀ p.mem) := by
    change (isHW_translation hx₀ hc₀).val _ * p.γ = _
    conv_lhs => rw [IsHW.val_ofMem, hpb]
    rw [translation_mul]
  rw [IsHW.smul_ofPair, spaceEquiv_ofPair hx₀ hc₀ _ hγ, spaceEquiv_ofPair hx₀ hc₀ p hpb,
    add_assoc]
  rfl

/-- `rem:connected`: the class `[-t, t]` is `0`. -/
theorem spaceEquiv_zeroClass (hx₀ : x₀ ∉ racl k (∅ : Set K)) (hc₀ : c₀ ∉ racl k (∅ : Set K))
    {t : K} (ht : IsGen k ![x₀] ![t]) :
    spaceEquiv hx₀ hc₀ ((isHW_translation hx₀ hc₀).ofPair
      ⟨translation hx₀ (-t), translation_mem_prodSet hx₀ hc₀ _, ![t], ht⟩) = 0 := by
  rw [spaceEquiv_ofPair hx₀ hc₀ _ rfl]
  change -t + t = 0
  exact neg_add_cancel t

/-- `rem:connected`: the class `[-t, t]` has no presentation `γ · ι(y)` with `y` independent
from `γ`: such a presentation is `ι(γ(y))`, a transcendental element. -/
theorem zeroClass_ne_smul_iota (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) {t : K} (ht : IsGen k ![x₀] ![t])
    (γ : ↥(isHW_translation hx₀ hc₀).prodSubgroup) {y : Fin 1 → K} (hy : IsGen k ![x₀] y)
    (hind : IndepOver k ∅ (range y) (((isHW_translation hx₀ hc₀).val γ).cb : Set K)) :
    (isHW_translation hx₀ hc₀).ofPair
        ⟨translation hx₀ (-t), translation_mem_prodSet hx₀ hc₀ _, ![t], ht⟩ ≠
      γ • (isHW_translation hx₀ hc₀).iota hy := by
  intro h
  have hγ : γ = (isHW_translation hx₀ hc₀).ofMem ((isHW_translation hx₀ hc₀).val_mem γ) :=
    (isHW_translation hx₀ hc₀).val_injective
      ((IsHW.val_ofMem _ ((isHW_translation hx₀ hc₀).val_mem γ)).symm)
  rw [hγ, IsHW.smul_iota _ _ hy hind] at h
  have h0 := congrArg (spaceEquiv hx₀ hc₀) h
  rw [spaceEquiv_zeroClass, spaceEquiv_iota] at h0
  have hgen := (isGen_translation_iff hx₀ _).1 (Germ.isGen_evalGen _ hy hind)
  exact hgen (by rw [← h0]; exact zero_mem _)

end Translation

end Germ

end

end GroupConfig
