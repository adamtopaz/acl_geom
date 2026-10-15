/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.BaseChange
import GroupConfig.Germ.Bijections
import GroupConfig.ConfigurationConverse

/-!
# Base change of generic sets of germs

Blueprint `sources/group_configuration/08-proof.tex`, `lem:hw-basechange`, the statements about
`𝓕` and `𝓖(𝓕)`.

For a Hrushovski–Weil datum of bijections `f₀` over `K₀` (`thm:hw-bij`) whose canonical base
is independent from a small algebraically closed intermediate field `K₁ ⊇ K₀`, the orbit of
the base change of `f₀` over `K₁` consists of the base changes of the elements of the orbit of
`f₀` independent from `K₁` (`Germ.baseChange_mem_orbit`,
`Germ.exists_of_mem_orbit_baseChange`), the difference set of the base change contains the
base changes of the difference germs independent from `K₁` (`Germ.baseChange_mem_diffSet`,
via the representation `Germ.exists_diff_rep_indepOver`) and consists of them
(`Germ.exists_of_mem_diffSet_baseChange`),
and the base change is again a Hrushovski–Weil datum of bijections (`Germ.IsHWBij.baseChange`).
The same holds for a Hrushovski–Weil datum of germs on `V` (`Germ.IsHW.baseChange`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the `𝓕`-part of `lem:hw-basechange` and hypotheses `H:trans`–`H:comp` of `𝓖''`
are complete when the tuples `a`, `a'` representing `V`, `V'` are independent from `K₁` over
`K₀` (hypotheses `ha`, `ha'`) and the chosen member `f₀` is independent from `K₁`. This covers
the finite independent base extension used in `thm:main`. For an arbitrary small `K₁`, as in
the source, `V` and `V'` are first represented by tuples independent from `K₁`; that case is
`GroupConfig.Germ.BaseChangeArbitrary`. The claims about `G`, `E` and `S` are in
`GroupConfig.Germ.BaseChangeGroup`.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}
  [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K} (K₀ K₁ : IntermediateField k K)
  [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K]
  (h₀₁ : K₀ ≤ K₁) (hK₁ : IsSmall (↥K₀) (K₁ : Set K))
  (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a') (K₁ : Set K))

namespace Germ

section Generic

variable {k' : Type*} [Field k'] [Algebra k' K] [IsAlgClosed k'] [UniversalDomain k' K]
  {b : ι → K} {b' : κ → K}

/-- The canonical base of a germ is algebraic over its code. -/
theorem cb_subset_racl_codeTuple (g : Germ k' b b') :
    (g.cb : Set K) ⊆ racl k' (range g.codeTuple) := by
  rw [racl_codeTuple]
  exact subset_racl k' _

/-- The code of a conjugate germ is interalgebraic with the conjugate of the code. -/
theorem racl_codeTuple_map (σ : K ≃ₐ[k'] K) (g : Germ k' b b') :
    racl k' (range (g.map σ).codeTuple) = racl k' (range (⇑σ ∘ g.codeTuple)) := by
  rw [racl_codeTuple, cb_map, range_comp, range_codeTuple, coe_map, AlgEquiv.coe_toAlgHom,
    ← racl_map σ, ← racl_map σ, racl_codeSet]

/-- `lem:hw-basechange`: a difference germ `δ` independent from a small set `w` has a
representation `δ = f₁⁻¹ f₂` by a pair independent from `w` over `δ`. The pair is obtained by
conjugating over `acl(Cb δ)` (`lem:fresh-conj`). -/
theorem exists_diff_rep_indepOver {f₀ : Germ k' b b'} {δ : Germ k' b b} (hδ : δ ∈ diffSet f₀)
    {w : Set K} (hw : IsSmall k' w) (h : IndepOver k' ∅ (δ.cb : Set K) w) :
    ∃ f₁ ∈ orbit f₀, ∃ f₂ ∈ orbit f₀, ∃ g₁ : Germ k' b' b, IsInverse g₁ f₁ ∧
      δ = Germ.comp g₁ f₂ ∧ IndepOver k' ∅ (f₁.cb : Set K) w ∧
      IndepOver k' ∅ (f₂.cb : Set K) w ∧ IndepOver k' w (f₁.cb : Set K) f₂.cb := by
  obtain ⟨f₁, hf₁, f₂, hf₂, g₁, hg₁, hind, rfl⟩ := hδ
  have _ : IsAlgClosed ↥(racl k' ((Germ.comp g₁ f₂).cb : Set K)) := isAlgClosed_racl _
  obtain ⟨ρ₀, hρ⟩ := exists_algEquiv_indepOver (Germ.comp g₁ f₂).isSmall_cb.racl
    (Sum.elim f₁.codeTuple f₂.codeTuple) hw
  obtain ⟨ρ, hρdef⟩ : ∃ τ : K ≃ₐ[k'] K, τ = ρ₀.restrictScalars k' := ⟨_, rfl⟩
  /- The conjugation fixes `δ`. -/
  have hδfix : (Germ.comp g₁ f₂).map ρ = Germ.comp g₁ f₂ := by
    refine (Germ.map_eq_self_iff _ _).2 fun x hx ↦ ?_
    rw [hρdef]
    change ρ₀ x = x
    exact ρ₀.commutes ⟨x, subset_racl k' _ hx⟩
  have hfun : (fun i ↦ ρ₀ (Sum.elim f₁.codeTuple f₂.codeTuple i)) =
      Sum.elim (⇑ρ ∘ f₁.codeTuple) (⇑ρ ∘ f₂.codeTuple) := by
    rw [hρdef]
    funext i
    cases i <;> rfl
  have hrange : racl k' (range fun i ↦ ρ₀ (Sum.elim f₁.codeTuple f₂.codeTuple i)) =
      racl k' (((f₁.map ρ).cb : Set K) ∪ (f₂.map ρ).cb) := by
    rw [hfun, Sum.elim_range]
    exact (racl_union_congr (racl_codeTuple_map ρ f₁).symm (racl_codeTuple_map ρ f₂).symm).trans
      (racl_union_congr (racl_codeTuple _) (racl_codeTuple _))
  have hpair : IndepOver k' ((Germ.comp g₁ f₂).cb : Set K)
      (((f₁.map ρ).cb : Set K) ∪ (f₂.map ρ).cb) w :=
    (indepOver_congr_left (racl_union_congr rfl hrange).symm).1
      ((indepOver_racl_base_iff _ _ _).1 hρ)
  /- The conjugated pair represents `δ` and is independent from `w`. -/
  have hδ' : Germ.comp g₁ f₂ = Germ.comp (g₁.map ρ) (f₂.map ρ) := by
    rw [← Germ.comp_map, hδfix]
  have hind' : IndepOver k' ∅ ((f₁.map ρ).cb : Set K) (f₂.map ρ).cb := by
    have h' := hind.image ρ
    rwa [image_empty, ← AlgEquiv.coe_toAlgHom, ← coe_map, ← coe_map, ← cb_map, ← cb_map] at h'
  have hE : IndepOver k' ∅ w
      (((Germ.comp g₁ f₂).cb : Set K) ∪ (((f₁.map ρ).cb : Set K) ∪ (f₂.map ρ).cb)) :=
    indepOver_union_right_iff.2 ⟨h.symm, by rw [empty_union]; exact hpair.symm⟩
  have hC : IndepOver k' ∅ (((f₁.map ρ).cb : Set K) ∪ (f₂.map ρ).cb) w :=
    (hE.mono_right subset_union_right).symm
  have hC₁₂ : IndepOver k' w ((f₁.map ρ).cb : Set K) (f₂.map ρ).cb := by
    have h1 := IndepOver.of_union_right hC.symm
    rw [empty_union] at h1
    have h2 : IndepOver k' ∅ ((f₁.map ρ).cb : Set K) (((f₂.map ρ).cb : Set K) ∪ w) :=
      indepOver_union_right_iff.2 ⟨hind', by rw [empty_union]; exact h1.symm⟩
    rw [union_comm] at h2
    have h3 := (indepOver_union_right_iff.1 h2).2
    rwa [empty_union] at h3
  exact ⟨f₁.map ρ, map_mem_orbit hf₁ ρ, f₂.map ρ, map_mem_orbit hf₂ ρ, g₁.map ρ, hg₁.map ρ, hδ',
    hC.mono_left subset_union_left, hC.mono_left subset_union_right, hC₁₂⟩

end Generic

include h₀₁ in
omit [IsAlgClosed K] [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K]
  [UniversalDomain (↥K₁) K] [Finite ι] [Finite κ] in
/-- An automorphism over `K₁` maps `K₁` onto itself. -/
theorem image_coe_restrictBase (σ : K ≃ₐ[↥K₁] K) :
    ⇑(restrictBase K₀ K₁ h₀₁ σ) '' (K₁ : Set K) = K₁ := by
  have hfix : ∀ x ∈ (K₁ : Set K), restrictBase K₀ K₁ h₀₁ σ x = x := fun x hx ↦ by
    rw [coe_restrictBase]
    exact σ.commutes ⟨x, hx⟩
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hfix x hx]
    exact hx
  · intro hw
    exact ⟨w, hw, hfix w hw⟩

include h₀₁ in
omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
/-- Conjugating by an automorphism over `K₁` preserves independence from `K₁`. -/
theorem indepOver_cb_map_restrictBase {g : Germ (↥K₀) a a'}
    (h : IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K)) (σ : K ≃ₐ[↥K₁] K) :
    IndepOver (↥K₀) ∅ ((g.map (restrictBase K₀ K₁ h₀₁ σ)).cb : Set K) (K₁ : Set K) := by
  have h' := h.image (restrictBase K₀ K₁ h₀₁ σ)
  rwa [image_empty, image_coe_restrictBase, ← AlgEquiv.coe_toAlgHom, ← coe_map, ← cb_map] at h'

include h₀₁ hK₁ ha ha'

theorem baseChange_injective : Function.Injective (baseChange K₀ K₁ h₀₁ hK₁ ha ha') :=
  fun g g' h ↦ graphIdeal_injective
    (by rw [← graphIdeal_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g, h, graphIdeal_baseChange])

/-! ### Orbits -/

omit ha ha' [UniversalDomain (↥K₁) K] in
/-- Two conjugates over `K₀` with canonical bases independent from `K₁` are conjugate over
`K₁`. -/
theorem exists_restrictBase_map_eq {g₀ : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (g₀.cb : Set K) (K₁ : Set K)) (σ : K ≃ₐ[↥K₀] K)
    (h : IndepOver (↥K₀) ∅ ((g₀.map σ).cb : Set K) (K₁ : Set K)) :
    ∃ τ : K ≃ₐ[↥K₁] K, g₀.map σ = g₀.map (restrictBase K₀ K₁ h₀₁ τ) := by
  -- The code tuple and its conjugate are both generic over `K₁`.
  have hc₀ : IndepOver (↥K₀) ∅ (range g₀.codeTuple) (K₁ : Set K) := by
    rw [range_codeTuple]
    exact indepOver_of_subset_racl (codeSet_subset_racl_cb g₀) (subset_racl (↥K₀) _) h₀
  have hσc₀ : IndepOver (↥K₀) ∅ (range (⇑σ ∘ g₀.codeTuple)) (K₁ : Set K) := by
    refine indepOver_of_subset_racl ?_ (subset_racl (↥K₀) _) h
    rw [range_comp, range_codeTuple, cb_map, coe_map, AlgEquiv.coe_toAlgHom]
    have e : ⇑σ '' (racl (↥K₀) (g₀.cb : Set K) : Set K) = racl (↥K₀) (⇑σ '' (g₀.cb : Set K)) := by
      rw [← racl_map σ, coe_map, AlgEquiv.coe_toAlgHom]
    exact (image_mono (codeSet_subset_racl_cb g₀)).trans e.subset
  have hgen₁ : IsGenericOver (racl (↥K₀) (K₁ : Set K)) g₀.codeTuple g₀.codeTuple :=
    IsGen.isGenericOver_racl (rfl : IsGen (↥K₀) g₀.codeTuple g₀.codeTuple) hK₁ hc₀
  have hgen₂ : IsGenericOver (racl (↥K₀) (K₁ : Set K)) g₀.codeTuple (⇑σ ∘ g₀.codeTuple) :=
    (IsGen.map (rfl : IsGen (↥K₀) g₀.codeTuple g₀.codeTuple) σ).isGenericOver_racl hK₁ hσc₀
  obtain ⟨τ₀, hτ⟩ := hgen₁.exists_algEquiv hgen₂
  have hsub : range (algebraMap (↥K₁) K) ⊆
      range (algebraMap (↥(racl (↥K₀) (K₁ : Set K))) K) := by
    rw [range_algebraMap_coe, range_algebraMap_coe, coe_racl_base_self K₀ K₁ h₀₁]
  refine ⟨algEquivRestrict hsub τ₀, ?_⟩
  have hfix : g₀.map (σ.trans (restrictBase K₀ K₁ h₀₁ (algEquivRestrict hsub τ₀)).symm) = g₀ := by
    refine map_eq_self_of_fixes_codeSet _ fun x hx ↦ ?_
    change (restrictBase K₀ K₁ h₀₁ (algEquivRestrict hsub τ₀)).symm (σ x) = x
    have hx' := hτ ⟨x, hx⟩
    change τ₀ x = σ x at hx'
    rw [← hx']
    exact (restrictBase K₀ K₁ h₀₁ (algEquivRestrict hsub τ₀)).symm_apply_apply x
  have hcomp : (σ.trans (restrictBase K₀ K₁ h₀₁ (algEquivRestrict hsub τ₀)).symm).trans
      (restrictBase K₀ K₁ h₀₁ (algEquivRestrict hsub τ₀)) = σ :=
    AlgEquiv.ext fun x ↦ by simp
  rw [← hcomp, ← map_map, hfix]

/-- `lem:hw-basechange`: base changes of orbit elements independent from `K₁` lie in the
orbit of the base change. -/
theorem baseChange_mem_orbit {g₀ g : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (g₀.cb : Set K) (K₁ : Set K)) (hg : g ∈ orbit g₀)
    (h : IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K)) :
    g.baseChange K₀ K₁ h₀₁ hK₁ ha ha' ∈ orbit (g₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  obtain ⟨σ, rfl⟩ := hg
  dsimp only at h ⊢
  obtain ⟨τ, hτ⟩ := exists_restrictBase_map_eq K₀ K₁ h₀₁ hK₁ h₀ σ h
  rw [hτ, map_baseChange]
  exact map_mem_orbit (self_mem_orbit _) τ

/-- `lem:hw-basechange`: every element of the orbit of the base change is the base change of
an orbit element independent from `K₁`. -/
theorem exists_of_mem_orbit_baseChange {g₀ : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (g₀.cb : Set K) (K₁ : Set K)) {f : Germ (↥K₁) a a'}
    (hf : f ∈ orbit (g₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha')) :
    ∃ g ∈ orbit g₀, IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K) ∧
      g.baseChange K₀ K₁ h₀₁ hK₁ ha ha' = f := by
  obtain ⟨τ, rfl⟩ := hf
  exact ⟨g₀.map (restrictBase K₀ K₁ h₀₁ τ), map_mem_orbit (self_mem_orbit _) _,
    indepOver_cb_map_restrictBase K₀ K₁ h₀₁ h₀ τ, map_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g₀ τ⟩

/-! ### Difference sets -/

/-- `lem:hw-basechange`: a difference germ `δ` independent from `K₁` is a base change of a
difference germ of the base change, using a representation `δ = f₁⁻¹ f₂` by a pair independent
from `K₁` (`exists_diff_rep_indepOver`). -/
theorem baseChange_mem_diffSet {f₀ : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) {δ : Germ (↥K₀) a a}
    (hδ : δ ∈ diffSet f₀) (h : IndepOver (↥K₀) ∅ (δ.cb : Set K) (K₁ : Set K)) :
    δ.baseChange K₀ K₁ h₀₁ hK₁ ha ha ∈ diffSet (f₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  obtain ⟨f₁, hf₁, f₂, hf₂, g₁, hg₁, rfl, hC₁, hC₂, hC₁₂⟩ := exists_diff_rep_indepOver hδ hK₁ h
  have hind : IndepOver (↥K₁) ∅ ((f₁.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)
      ((f₂.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) :=
    (indepOver_congr₀ (racl_cb_baseChange K₀ K₁ h₀₁ hK₁ ha ha' f₁).symm rfl).1
      ((indepOver_cb_baseChange_iff K₀ K₁ h₀₁ hK₁ ha ha' f₂ _).2 hC₁₂)
  rw [comp_baseChange K₀ K₁ h₀₁ hK₁ ha ha' ha g₁ f₂]
  exact ⟨_, baseChange_mem_orbit K₀ K₁ h₀₁ hK₁ ha ha' h₀ hf₁ hC₁, _,
    baseChange_mem_orbit K₀ K₁ h₀₁ hK₁ ha ha' h₀ hf₂ hC₂, _,
    hg₁.baseChange K₀ K₁ h₀₁ hK₁ ha ha', hind, rfl⟩

/-- `lem:hw-basechange`: every difference germ of the base change is the base change of a
difference germ independent from `K₁`. With `baseChange_mem_diffSet`, the difference set of the
base change is exactly the set of base changes of the difference germs independent from `K₁`. -/
theorem exists_of_mem_diffSet_baseChange {f₀ : Germ (↥K₀) a a'} (hf₀ : IsInvertible f₀)
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) {δ : Germ (↥K₁) a a}
    (hδ : δ ∈ diffSet (f₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha')) :
    ∃ δ₀ ∈ diffSet f₀, IndepOver (↥K₀) ∅ (δ₀.cb : Set K) (K₁ : Set K) ∧
      δ₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha = δ := by
  obtain ⟨δ₂, hδ₂⟩ := diffSet_nonempty hf₀
  obtain ⟨δ₁, hδ₁, hδ₁K⟩ := exists_mem_orbit_indepOver δ₂ hK₁
  rw [← diffSet_eq_orbit hδ₂] at hδ₁
  have hδ₁' := baseChange_mem_diffSet K₀ K₁ h₀₁ hK₁ ha ha' h₀ hδ₁ hδ₁K
  rw [diffSet_eq_orbit hδ₁'] at hδ
  obtain ⟨δ₀, hδ₀, hδ₀K, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha hδ₁K hδ
  exact ⟨δ₀, by rwa [diffSet_eq_orbit hδ₁], hδ₀K, rfl⟩

/-! ### Hrushovski–Weil data of bijections -/

omit hK₁ ha ha' [IsAlgClosed K] [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)]
  [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K] in
/-- Ranks over `K₁` are ranks over `K₀` relative to `K₁`. -/
theorem erk_base_le (X : Set K) : erk (↥K₁) ∅ X = erk (↥K₀) (K₁ : Set K) X := by
  rw [erk_base_empty K₁, ← erk_coe_union K₀, union_eq_right.2 (SetLike.coe_subset_coe.2 h₀₁)]

/-- The canonical base of a base change independent from `K₁` keeps its rank. -/
theorem erk_cb_baseChange {g : Germ (↥K₀) a a'}
    (hg : IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K)) :
    erk (↥K₁) ∅ ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) = erk (↥K₀) ∅ (g.cb : Set K) := by
  rw [erk_base_le K₀ K₁ h₀₁, coe_cb_baseChange, erk_adjoin_eq (k := ↥K₀), union_comm,
    erk_union_eq_of_subset_racl (↥K₀) (fun w hw ↦ subset_racl (↥K₀) _ (Or.inl hw))]
  have := erk_cb_eq_of_indepOver hg
  rwa [empty_union] at this

/-- `lem:hw-basechange`, `H:trans`: generic transitivity of an orbit is inherited by the
orbit of the base change. -/
theorem trans_baseChange {f₀ : Germ (↥K₀) a a'}
    (htrans : ∀ g ∈ orbit f₀, ∀ y : ι → K, IsGen (↥K₀) a y →
      IndepOver (↥K₀) ∅ (range y) (g.cb : Set K) →
        IndepOver (↥K₀) ∅ (range (g.evalGen y)) (range y))
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K))
    {f : Germ (↥K₁) a a'} (hf : f ∈ orbit (f₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha')) {y : ι → K}
    (hy : IsGen (↥K₁) a y) (hind : IndepOver (↥K₁) ∅ (range y) (f.cb : Set K)) :
    IndepOver (↥K₁) ∅ (range (f.evalGen y)) (range y) := by
  obtain ⟨g, hg, hgK, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha' h₀ hf
  have hyk := (isGen_base_iff K₀ K₁ h₀₁ hK₁ ha).1 hy
  have hyg : IndepOver (↥K₀) (K₁ : Set K) (range y) (g.cb : Set K) :=
    (indepOver_cb_baseChange_iff K₀ K₁ h₀₁ hK₁ ha ha' g _).1 hind
  have hyKg : IndepOver (↥K₀) ∅ (range y) ((K₁ : Set K) ∪ g.cb) :=
    indepOver_union_right_iff.2 ⟨hyk.2, by rw [empty_union]; exact hyg⟩
  have hyg₀ : IndepOver (↥K₀) ∅ (range y) (g.cb : Set K) := hyKg.mono_right subset_union_right
  have htrans := htrans g hg y hyk.1 hyg₀
  rw [evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g hy hind, indepOver_base_le_iff K₀ K₁ h₀₁]
  /- `K₁` is independent from `g`, `y` and `g(y)`. -/
  have hK : IndepOver (↥K₀) ∅ (K₁ : Set K) ((g.cb : Set K) ∪ range y) := by
    refine indepOver_union_right_iff.2 ⟨hgK.symm, ?_⟩
    rw [empty_union]
    have h1 := IndepOver.of_union_right hyKg
    rw [empty_union] at h1
    exact h1.symm
  have hsub : range (g.evalGen y) ∪ range y ⊆
      racl (↥K₀) (∅ ∪ ((g.cb : Set K) ∪ range y)) := by
    rw [empty_union]
    refine union_subset ?_ (fun w hw ↦ subset_racl (↥K₀) _ (Or.inr hw))
    rintro _ ⟨j, rfl⟩
    exact g.evalGen_mem_racl hyk.1 hyg₀ j
  have hK' : IndepOver (↥K₀) ∅ (K₁ : Set K) (∅ ∪ (range (g.evalGen y) ∪ range y)) := by
    rw [empty_union]
    exact (indepOver_racl_right_iff.2 hK).mono_right hsub
  have := (indepOver_base_union_iff hK').1 htrans
  rwa [empty_union] at this

/-- `lem:hw-basechange`: the base change of a Hrushovski–Weil datum of bijections independent
from `K₁` is a Hrushovski–Weil datum of bijections over `K₁`. -/
theorem IsHWBij.baseChange {f₀ : Germ (↥K₀) a a'} (hb : IsHWBij f₀)
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) :
    IsHWBij (f₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  refine ⟨hb.isInvertible.baseChange K₀ K₁ h₀₁ hK₁ ha ha',
    fun f hf y hy hind ↦ trans_baseChange K₀ K₁ h₀₁ hK₁ ha ha' hb.trans h₀ hf hy hind, ?_⟩
  /- A difference germ independent from `K₁`, by conjugation. -/
  obtain ⟨δ₁, hδ₁⟩ := diffSet_nonempty hb.isInvertible
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := exists_mem_orbit_indepOver δ₁ hK₁
  rw [← diffSet_eq_orbit hδ₁] at hδ₀
  refine IsHWBij.rank_of_exists (baseChange_mem_diffSet K₀ K₁ h₀₁ hK₁ ha ha' h₀ hδ₀ hδ₀K) ?_
  rw [erk_cb_baseChange K₀ K₁ h₀₁ hK₁ ha ha hδ₀K, erk_cb_baseChange K₀ K₁ h₀₁ hK₁ ha ha' h₀]
  exact hb.rank δ₀ hδ₀

omit ha' in
/-- `lem:hw-basechange` for a generic set of germs on `V`: the base change of a Hrushovski–Weil
datum independent from `K₁` is a Hrushovski–Weil datum over `K₁`. -/
theorem IsHW.baseChange {g₀ : Germ (↥K₀) a a} (hw : IsHW g₀)
    (h₀ : IndepOver (↥K₀) ∅ (g₀.cb : Set K) (K₁ : Set K)) :
    IsHW (g₀.baseChange K₀ K₁ h₀₁ hK₁ ha ha) := by
  refine ⟨?_, fun f hf y hy hind ↦ trans_baseChange K₀ K₁ h₀₁ hK₁ ha ha hw.trans h₀ hf hy hind,
    ?_, ?_⟩
  · obtain ⟨g₀', hg₀'⟩ := isUnit_iff.1 hw.isUnit
    exact isUnit_iff.2 ⟨_, hg₀'.baseChange K₀ K₁ h₀₁ hK₁ ha ha⟩
  · intro f hf h hh
    obtain ⟨g, hg, hgK, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha h₀ hf
    obtain ⟨g', hg'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hg)
    rw [hh.unique (hg'.baseChange K₀ K₁ h₀₁ hK₁ ha ha)]
    exact baseChange_mem_orbit K₀ K₁ h₀₁ hK₁ ha ha h₀ (hw.inv g hg g' hg')
      (indepOver_of_cb_le hg'.cb_le hgK)
  · intro f₁ hf₁ f₂ hf₂ hind
    obtain ⟨g₁, hg₁, hg₁K, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha h₀ hf₁
    obtain ⟨g₂, hg₂, -, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha h₀ hf₂
    have h12 : IndepOver (↥K₀) (K₁ : Set K) (g₁.cb : Set K) g₂.cb :=
      (indepOver_cb_baseChange_iff K₀ K₁ h₀₁ hK₁ ha ha g₂ _).1
        ((indepOver_congr₀ (racl_cb_baseChange K₀ K₁ h₀₁ hK₁ ha ha g₁) rfl).1 hind)
    have h1 : IndepOver (↥K₀) ∅ (g₁.cb : Set K) ((K₁ : Set K) ∪ g₂.cb) :=
      indepOver_union_right_iff.2 ⟨hg₁K, by rwa [empty_union]⟩
    obtain ⟨hmem, hK⟩ := hw.keyrank (hw.mem_prodSet_of_mem hg₂) hg₁ (by rwa [union_comm] at h1)
    rw [mul_def, ← comp_baseChange K₀ K₁ h₀₁ hK₁ ha ha ha g₁ g₂, ← mul_def]
    exact baseChange_mem_orbit K₀ K₁ h₀₁ hK₁ ha ha h₀ hmem hK

end Germ

end

end GroupConfig
