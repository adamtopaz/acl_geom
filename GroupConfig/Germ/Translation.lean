/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Definable
import GroupConfig.Germ.HW
import GroupConfig.CanonicalBaseCounterexample
import GroupConfig.Configuration

/-!
# The germs of translations of the affine line

Blueprint `sources/group_configuration/05-hrushovski-weil.tex`, `rem:connected`: the group of
translations of the affine line. For a transcendental `x₀`, the locus of `![x₀]` is the affine line
`V = A¹`, and its generic points are the transcendental elements
(`GroupConfig.Germ.isGen_translation_iff`).

For `c : K` the actual germ `GroupConfig.Germ.translation hx₀ c` is represented by `y ↦ y + c` over
`acl(c)`. Translations compose additively and are permuted by automorphisms. The canonical base
of the translation by `c` is `k(c)`. A translation by a transcendental element is a
Hrushovski–Weil germ (`GroupConfig.Germ.isHW_translation`), whose generic set consists of the
translations by transcendental elements and whose group is the group of all translations
(`GroupConfig.Germ.prodSet_translation`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the translation germs and their Hrushovski–Weil structure are complete.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Transcendence over subfields -/

/-- An element is transcendental over a subfield `M` iff it lies outside `acl(M)`. Named
consumers: the generic points and translations below. -/
theorem transcendental_iff_not_mem_racl (M : IntermediateField k K) (x : K) :
    Transcendental (↥M) x ↔ x ∉ racl k (M : Set K) := by
  rw [mem_racl_iff k, adjoin_self]
  exact Iff.rfl

/-- A singleton outside `acl(C)` has rank one over `C`. Named consumers: `isHW_translation` and
the translation space. -/
theorem erk_singleton_eq_one {C : Set K} {x : K} (h : x ∉ racl k C) :
    erk k C ({x} : Set K) = 1 :=
  le_antisymm ((erk_le_encard k C _).trans (by simp))
    (Order.one_le_iff_ne_zero.2 fun h0 ↦ h ((erk_eq_zero_iff k).1 h0 (mem_singleton x)))

/-- A transcendental element independent from a set lies outside its closure. Named consumers:
`isHW_translation`, `prodSet_translation` and the translation space. -/
theorem not_mem_racl_of_indepOver {x : K} {B : Set K} (hx : x ∉ racl k (∅ : Set K))
    (h : IndepOver k ∅ ({x} : Set K) B) : x ∉ racl k B := by
  intro hxB
  have h1 := h.erk_eq (subset_refl _) (finite_singleton x)
  rw [empty_union, erk_eq_zero_of_subset_racl k (singleton_subset_iff.2 hxB)] at h1
  exact hx ((erk_eq_zero_iff k).1 h1.symm (mem_singleton x))

/-- The range of a one-point tuple. -/
private theorem range_fin_one {α : Type*} (y : Fin 1 → α) : range y = {y 0} := range_unique

variable {x₀ : K}

namespace Germ

/-! ### Generic points of the affine line -/

/-- A tuple has the zero ideal over `M` iff it is algebraically independent over `M`. -/
private theorem idealOf_eq_bot_iff (M : Type*) [Field M] [Algebra M K] (y : Fin 1 → K) :
    idealOf M y = ⊥ ↔ Transcendental M (y 0) :=
  (RingHom.injective_iff_ker_eq_bot _).symm.trans algebraicIndependent_unique_type_iff

/-- A transcendental element has the zero ideal. -/
private theorem idealOf_eq_bot (hx₀ : x₀ ∉ racl k (∅ : Set K)) : idealOf k ![x₀] = ⊥ :=
  (idealOf_eq_bot_iff k ![x₀]).2 fun h ↦ hx₀ (mem_racl_empty_of_isAlgebraic h)

/-- `rem:connected`: a point is generic over `M` on the affine line iff its coordinate is
transcendental over `M`. -/
theorem isGenericOver_translation_iff (hx₀ : x₀ ∉ racl k (∅ : Set K))
    (M : IntermediateField k K) (y : Fin 1 → K) :
    IsGenericOver M ![x₀] y ↔ Transcendental (↥M) (y 0) := by
  unfold IsGenericOver
  rw [idealOf_eq_bot hx₀, Ideal.map_bot]
  exact idealOf_eq_bot_iff (↥M) y

/-- `rem:connected`: the generic points of the affine line are the transcendental elements. -/
theorem isGen_translation_iff (hx₀ : x₀ ∉ racl k (∅ : Set K)) (y : Fin 1 → K) :
    IsGen k ![x₀] y ↔ y 0 ∉ racl k (∅ : Set K) := by
  unfold IsGen
  rw [idealOf_eq_bot hx₀, idealOf_eq_bot_iff k y]
  exact not_congr ⟨mem_racl_empty_of_isAlgebraic, isAlgebraic_of_mem_racl_empty⟩

/-! ### Translation germs -/

variable [IsAlgClosed K]

/-- The expression `y ↦ y + c` over `acl(c)`. -/
private def translationExpr (c : K) :
    QuasiRational (↥(racl k ({c} : Set K))) (Fin 1) (Fin 1) :=
  ⟨0, fun _ ↦ X 0 + C ⟨c, subset_racl k ({c} : Set K) (mem_singleton c)⟩, fun _ ↦ 1⟩

private theorem translationExpr_eval (c : K) (y : Fin 1 → K) :
    (translationExpr (k := k) c).eval y = fun _ ↦ y 0 + c := by
  funext j
  simp [translationExpr, QuasiRational.eval_apply, pRoot_zero]

/-- `rem:connected`: the representative `y ↦ y + c` over `acl(c)` of a germ of the affine line. -/
def translationRep (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c : K) :
    Representative k K ![x₀] ![x₀] where
  M := racl k ({c} : Set K)
  isAlgClosed := isAlgClosed_racl _
  isSmall := (IsSmall.of_finite (finite_singleton c)).racl
  f := translationExpr c
  isDefinedAt _ _ _ := by simp [translationExpr]
  isGenericOver y hy := by
    rw [isGenericOver_translation_iff hx₀] at hy ⊢
    rw [translationExpr_eval, transcendental_iff_not_mem_racl]
    rw [transcendental_iff_not_mem_racl] at hy
    intro h
    refine hy ?_
    have hc : c ∈ racl k ((racl k ({c} : Set K) : IntermediateField k K) : Set K) :=
      subset_racl k _ (subset_racl k ({c} : Set K) (mem_singleton c))
    simpa using sub_mem h hc

variable [IsAlgClosed k] [UniversalDomain k K]

/-- `rem:connected`: the germ of the translation `y ↦ y + c` of the affine line. -/
def translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c : K) : Germ k ![x₀] ![x₀] :=
  ⟦translationRep hx₀ c⟧

/-- A representative taking the values of the translation by `c` at generic points represents
the translation by `c`. Named consumers: `translation_mul`, `translation_zero` and
`map_translation`. -/
private theorem mk_eq_translation (hx₀ : x₀ ∉ racl k (∅ : Set K))
    {r : Representative k K ![x₀] ![x₀]} {c : K}
    (h : ∀ y, IsGenericOver (racl k ((r.M : Set K) ∪ (racl k ({c} : Set K) : Set K))) ![x₀] y →
      r.f.eval y = fun _ ↦ y 0 + c) :
    (⟦r⟧ : Germ k ![x₀] ![x₀]) = translation hx₀ c :=
  Quotient.sound fun y hy ↦ (h y hy).trans (translationExpr_eval c y).symm

/-- `rem:connected`: distinct parameters give distinct translations. -/
theorem translation_injective (hx₀ : x₀ ∉ racl k (∅ : Set K)) :
    Function.Injective (translation (k := k) hx₀) := by
  intro a b h
  have he : (translationRep hx₀ a).Equivalent (translationRep hx₀ b) := Quotient.exact h
  obtain ⟨y, hy⟩ := exists_isGenericOver (k := k)
    (((IsSmall.of_finite (finite_singleton a)).racl.union
      (IsSmall.of_finite (finite_singleton b)).racl).racl) ![x₀]
  have h2 : (translationExpr (k := k) a).eval y = (translationExpr b).eval y := he y hy
  rw [translationExpr_eval, translationExpr_eval] at h2
  exact add_left_cancel (congrFun h2 0)

/-- `rem:connected`: translations compose additively. -/
theorem translation_mul (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c d : K) :
    translation hx₀ c * translation hx₀ d = translation hx₀ (c + d) := by
  change Germ.comp (⟦translationRep hx₀ c⟧ : Germ k ![x₀] ![x₀]) ⟦translationRep hx₀ d⟧ = _
  rw [comp_mk]
  refine mk_eq_translation hx₀ fun y hy ↦ ?_
  rw [Representative.comp_eval _ _ (hy.of_le fun x hx ↦ subset_racl k _ (Or.inl hx))]
  change (translationExpr c).eval ((translationExpr d).eval y) = _
  rw [translationExpr_eval, translationExpr_eval]
  funext j
  ring

/-- `rem:connected`: the translation by zero is the identity germ. -/
theorem translation_zero (hx₀ : x₀ ∉ racl k (∅ : Set K)) : translation hx₀ (0 : K) = 1 := by
  change translation hx₀ (0 : K) = (⟦Representative.id ![x₀]⟧ : Germ k ![x₀] ![x₀])
  refine (mk_eq_translation hx₀ fun y _ ↦ ?_).symm
  change (QuasiRational.id _ (Fin 1)).eval y = _
  rw [QuasiRational.id_eval]
  funext j
  fin_cases j
  simp

/-- `rem:connected`: automorphisms permute translations. -/
theorem map_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) (σ : K ≃ₐ[k] K) (c : K) :
    (translation hx₀ c).map σ = translation hx₀ (σ c) := by
  change Germ.map σ (⟦translationRep hx₀ c⟧ : Germ k ![x₀] ![x₀]) = _
  rw [map_mk]
  refine mk_eq_translation hx₀ fun y _ ↦ ?_
  funext j
  simp [Representative.map, translationRep, translationExpr, QuasiRational.eval_apply,
    QuasiRational.map, pRoot_zero, intermediateFieldMap_apply_coe]

/-! ### Canonical bases and generic values -/

/-- `rem:connected`: the canonical base of the translation by `c` is `k(c)`. -/
theorem cb_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c : K) :
    (translation hx₀ c).cb = adjoin k ({c} : Set K) := by
  obtain ⟨y, hy⟩ := exists_isGenericOver (k := k)
    (IsSmall.of_finite (finite_singleton c)).racl ![x₀]
  have hy' : IsGenericOver (translationRep hx₀ c).M ![x₀] y := hy
  have hgp : (translationRep hx₀ c).graphPoint y =
      ![y 0, 1 * y 0 + c] ∘ (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) := by
    have h1 : (translationRep hx₀ c).graphPoint y = Sum.elim y fun _ ↦ y 0 + c :=
      congrArg (Sum.elim y) (translationExpr_eval c y)
    rw [h1]
    funext i
    rcases i with i | i <;> fin_cases i
    · rfl
    · change y 0 + c = 1 * y 0 + c
      rw [one_mul]
  change Germ.cb (⟦translationRep hx₀ c⟧ : Germ k ![x₀] ![x₀]) = _
  rw [cb_mk_eq_canonicalBase _ hy']
  have hc : c ∈ (translationRep hx₀ c).M := subset_racl k ({c} : Set K) (mem_singleton c)
  rw [hgp, canonicalBase_comp_equiv, canonicalBase_affineLine (translationRep hx₀ c).M
    (one_mem _) hc ((isGenericOver_translation_iff hx₀ _ y).1 hy')]
  refine le_antisymm (adjoin_le_iff.2 ?_) (adjoin_le_iff.2 ?_)
  · rintro x (rfl | rfl)
    · exact one_mem _
    · exact subset_adjoin k _ rfl
  · rintro x rfl
    exact subset_adjoin k _ (Or.inr rfl)

/-- `rem:connected`: the translation by `c` sends a generic point `y` independent from `c` to
`y + c`. -/
theorem evalGen_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c : K) {y : Fin 1 → K}
    (hy : IsGen k ![x₀] y) (hind : IndepOver k ∅ (range y) ({c} : Set K)) :
    (translation hx₀ c).evalGen y = fun _ ↦ y 0 + c :=
  (evalGen_mk_eq (translationRep hx₀ c)
    (hy.isGenericOver_racl (IsSmall.of_finite (finite_singleton c)) hind)).trans
      (translationExpr_eval c y)

/-! ### The Hrushovski–Weil structure -/

/-- The translations by transcendental elements are the orbit of one of them. -/
theorem orbit_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) {c₀ : K}
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) :
    orbit (translation hx₀ c₀) = translation hx₀ '' {c | c ∉ racl k (∅ : Set K)} := by
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨σ c₀, fun h ↦ hc₀ ?_, (map_translation hx₀ σ c₀).symm⟩
    exact mem_racl_empty_of_isAlgebraic ((isAlgebraic_algHom_iff σ.toAlgHom σ.injective).1
      (isAlgebraic_of_mem_racl_empty h))
  · rintro ⟨c, hc, rfl⟩
    have hgen (d : K) (hd : d ∉ racl k (∅ : Set K)) :
        IsGenericOver (racl k (∅ : Set K)) ![x₀] ![d] := by
      rw [isGenericOver_translation_iff hx₀, transcendental_iff_not_mem_racl, racl_racl]
      exact hd
    obtain ⟨σ, hσ⟩ := (hgen c₀ hc₀).exists_algEquiv (hgen c hc)
    refine ⟨σ.restrictScalars k, ?_⟩
    change (translation hx₀ c₀).map (σ.restrictScalars k) = _
    rw [map_translation]
    exact congrArg _ (by simpa using hσ 0)

/-- Membership of a translation in the generic set. -/
theorem translation_mem_orbit (hx₀ : x₀ ∉ racl k (∅ : Set K)) {c₀ : K}
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) {c : K} (hc : c ∉ racl k (∅ : Set K)) :
    translation hx₀ c ∈ orbit (translation hx₀ c₀) := by
  rw [orbit_translation hx₀ hc₀]
  exact ⟨c, hc, rfl⟩

/-- The translation by `-c` is the inverse of the translation by `c`. -/
theorem isInverse_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) (c : K) :
    IsInverse (translation hx₀ (-c)) (translation hx₀ c) := by
  constructor
  · change translation hx₀ (-c) * translation hx₀ c = 1
    rw [translation_mul, neg_add_cancel, translation_zero]
  · change translation hx₀ c * translation hx₀ (-c) = 1
    rw [translation_mul, add_neg_cancel, translation_zero]

/-- `rem:connected`: a translation by a transcendental element is a Hrushovski–Weil germ. -/
theorem isHW_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) {c₀ : K}
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) : IsHW (translation hx₀ c₀) where
  isUnit := isUnit_iff.2 ⟨_, isInverse_translation hx₀ c₀⟩
  trans g hg y hy hind := by
    rw [orbit_translation hx₀ hc₀] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    rw [cb_translation] at hind
    have hyc : IndepOver k ∅ (range y) ({c} : Set K) :=
      hind.mono_right (subset_adjoin k _)
    rw [evalGen_translation hx₀ c hy hyc, range_const, range_fin_one]
    have hy0 : y 0 ∉ racl k (∅ : Set K) := (isGen_translation_iff hx₀ y).1 hy
    have hcy : c ∉ racl k ({y 0} : Set K) := by
      refine not_mem_racl_of_indepOver hc ?_
      rw [range_fin_one] at hyc
      exact hyc.symm
    have hsum : y 0 + c ∉ racl k ({y 0} : Set K) := fun h ↦
      hcy (by simpa using sub_mem h (subset_racl k ({y 0} : Set K) (mem_singleton (y 0))))
    refine indepOver_of_erk_eq (finite_singleton _) ?_
    rw [empty_union, erk_singleton_eq_one hsum,
      erk_singleton_eq_one fun h ↦ hsum (racl_mono (k := k) (empty_subset _) h)]
  inv g hg h hi := by
    rw [orbit_translation hx₀ hc₀] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    rw [hi.unique (isInverse_translation hx₀ c)]
    exact translation_mem_orbit hx₀ hc₀ fun h ↦ hc (by simpa using neg_mem h)
  comp g₁ hg₁ g₂ hg₂ hind := by
    rw [orbit_translation hx₀ hc₀] at hg₁ hg₂
    obtain ⟨c₁, hc₁, rfl⟩ := hg₁
    obtain ⟨c₂, hc₂, rfl⟩ := hg₂
    rw [cb_translation, cb_translation] at hind
    have h12 : c₁ ∉ racl k ({c₂} : Set K) := not_mem_racl_of_indepOver hc₁
      ((hind.mono_left (subset_adjoin k _)).mono_right (subset_adjoin k _))
    rw [translation_mul]
    refine translation_mem_orbit hx₀ hc₀ fun h ↦ h12 ?_
    have h' := sub_mem (racl_mono (k := k) (empty_subset ({c₂} : Set K)) h)
      (subset_racl k ({c₂} : Set K) (mem_singleton c₂))
    simpa using h'

/-- `rem:connected`: the group generated by the generic set is the group of all translations. -/
theorem prodSet_translation (hx₀ : x₀ ∉ racl k (∅ : Set K)) {c₀ : K}
    (hc₀ : c₀ ∉ racl k (∅ : Set K)) :
    IsHW.prodSet (translation hx₀ c₀) = range (translation hx₀) := by
  ext γ
  constructor
  · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    rw [orbit_translation hx₀ hc₀] at hg₁ hg₂
    obtain ⟨c₁, -, rfl⟩ := hg₁
    obtain ⟨c₂, -, rfl⟩ := hg₂
    exact ⟨c₁ + c₂, (translation_mul hx₀ c₁ c₂).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := exists_isGenericOver (k := k)
      (IsSmall.of_finite (finite_singleton a)).racl ![x₀]
    have hya : y 0 ∉ racl k ({a} : Set K) := by
      have h := (isGenericOver_translation_iff hx₀ _ y).1 hy
      rwa [transcendental_iff_not_mem_racl, racl_racl] at h
    have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ (mem_singleton a)
    refine ⟨translation hx₀ (a + y 0), translation_mem_orbit hx₀ hc₀ fun h ↦ hya ?_,
      translation hx₀ (-y 0), translation_mem_orbit hx₀ hc₀ fun h ↦ hya ?_, ?_⟩
    · simpa using sub_mem (racl_mono (k := k) (empty_subset ({a} : Set K)) h) ha
    · simpa using neg_mem (racl_mono (k := k) (empty_subset ({a} : Set K)) h)
    · rw [translation_mul, add_neg_cancel_right]

end Germ

end

end GroupConfig
