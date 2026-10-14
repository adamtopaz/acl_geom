/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.HW

/-!
# Difference germs of a generic set of invertible germs

Blueprint `sources/group_configuration/06-bijections.tex`, `def:diff` and `lem:diff-basic`.

For a generic set `𝓕` of invertible germs `V → V'` (the orbit of an invertible germ
`f₀ : Germ k a a'`), the *difference set* `Germ.diffSet f₀` consists of the germs
`f₁⁻¹ f₂` for independent `f₁, f₂ ∈ 𝓕`.  It is a single orbit (`Germ.diffSet_eq_orbit`),
and `δ = f₁⁻¹ f₂` is interalgebraic with `f₂` over `f₁` and with `f₁` over `f₂`
(`Germ.cb_diff_le`, `Germ.cb_right_le_diff`, `Germ.cb_left_le_diff`), so that `δ` has rank
at least that of `𝓕` (`Germ.erk_cb_le_erk_diff`), with equality iff `δ` is independent
from `f₁` iff `δ` is independent from `f₂` (`Germ.indepOver_diff_left_iff`,
`Germ.indepOver_diff_right_iff`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `def:diff` and `lem:diff-basic` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ : Type*} [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

namespace Germ

/-! ### Invertible germs -/

/-- A germ is invertible if it has a two-sided inverse. -/
def IsInvertible (g : Germ k a a') : Prop := ∃ h, IsInverse h g

theorem IsInvertible.map {g : Germ k a a'} (hg : IsInvertible g) (σ : K ≃ₐ[k] K) :
    IsInvertible (g.map σ) :=
  let ⟨h, hi⟩ := hg
  ⟨h.map σ, hi.map σ⟩

theorem isInvertible_of_mem_orbit {g₀ g : Germ k a a'} (h₀ : IsInvertible g₀)
    (hg : g ∈ orbit g₀) : IsInvertible g := by
  obtain ⟨σ, rfl⟩ := hg
  exact h₀.map σ

/-- The composite of two invertible germs is invertible, with inverse the composite of
the inverses in the opposite order. -/
theorem IsInverse.comp {μ : Type*} [Finite μ] {a'' : μ → K} {h : Germ k a' a}
    {g : Germ k a a'} {h' : Germ k a'' a'} {g' : Germ k a' a''} (hi : IsInverse h g)
    (hi' : IsInverse h' g') : IsInverse (Germ.comp h h') (Germ.comp g' g) := by
  constructor
  · rw [comp_assoc, ← comp_assoc h' g' g, hi'.1, id_comp, hi.1]
  · rw [comp_assoc, ← comp_assoc g h h', hi.2, id_comp, hi'.2]

/-! ### Interalgebraicity in an independent pair -/

section Pair

variable {f₁ f₂ : Germ k a a'} {g₁ : Germ k a' a} (hg₁ : IsInverse g₁ f₁)
include hg₁

/-- `f₁ δ = f₂` for the difference germ `δ = f₁⁻¹ f₂`. -/
theorem comp_diff : Germ.comp f₁ (Germ.comp g₁ f₂) = f₂ := by
  rw [← comp_assoc, hg₁.2, id_comp]

/-- `lem:diff-basic`(2): `Cb(δ) ⊆ acl(f₁, f₂)`. -/
theorem cb_diff_le : (Germ.comp g₁ f₂).cb ≤ racl k ((f₁.cb : Set K) ∪ f₂.cb) := by
  refine (cb_comp_le_racl g₁ f₂).trans (racl_le_of_subset_racl (union_subset ?_ ?_))
  · exact subset_union_right.trans (subset_racl k _)
  · exact hg₁.cb_le.trans (racl_mono (k := k) subset_union_left)

/-- `lem:diff-basic`(2): `Cb(f₂) ⊆ acl(f₁, δ)`. -/
theorem cb_right_le_diff : f₂.cb ≤ racl k ((f₁.cb : Set K) ∪ (Germ.comp g₁ f₂).cb) := by
  have := cb_comp_le_racl f₁ (Germ.comp g₁ f₂)
  rw [comp_diff hg₁] at this
  exact this.trans (racl_mono (k := k) (union_comm _ _).le)

/-- `lem:diff-basic`(2): `Cb(f₁) ⊆ acl(f₂, δ)`. -/
theorem cb_left_le_diff (hf₂ : IsInvertible f₂) :
    f₁.cb ≤ racl k ((f₂.cb : Set K) ∪ (Germ.comp g₁ f₂).cb) := by
  obtain ⟨g₂, hg₂⟩ := hf₂
  have h1 : g₁.cb ≤ racl k (((Germ.comp g₁ f₂).cb : Set K) ∪ f₂.cb) :=
    cb_le_of_isInverse g₁ hg₂
  exact hg₁.symm.cb_le.trans
    (racl_le_of_subset_racl (h1.trans (racl_mono (k := k) (union_comm _ _).le)))

variable (hind : IndepOver k ∅ (f₁.cb : Set K) f₂.cb)
include hind

/-- `lem:diff-basic`(2): `rk(δ/f₁) = rk(f₂/f₁) = rk(f₂)`. -/
theorem erk_diff_eq :
    erk k (f₁.cb : Set K) ((Germ.comp g₁ f₂).cb : Set K) = erk k ∅ (f₂.cb : Set K) := by
  rw [erk_eq_of_subset_racl (cb_diff_le hg₁) (cb_right_le_diff hg₁)]
  have := erk_cb_eq_of_indepOver hind.symm
  rwa [empty_union] at this

/-- `lem:diff-basic`(2): `rk(δ/f₂) = rk(f₁/f₂) = rk(f₁)`. -/
theorem erk_diff_eq' (hf₂ : IsInvertible f₂) :
    erk k (f₂.cb : Set K) ((Germ.comp g₁ f₂).cb : Set K) = erk k ∅ (f₁.cb : Set K) := by
  rw [erk_eq_of_subset_racl ((cb_diff_le hg₁).trans (racl_mono (k := k) (union_comm _ _).le))
    (cb_left_le_diff hg₁ hf₂)]
  have := erk_cb_eq_of_indepOver hind
  rwa [empty_union] at this

/-- `lem:diff-basic`(2): `rk(δ) ≥ rk(f₂)`. -/
theorem erk_cb_le_erk_diff :
    erk k ∅ (f₂.cb : Set K) ≤ erk k ∅ ((Germ.comp g₁ f₂).cb : Set K) := by
  rw [← erk_diff_eq hg₁ hind]
  exact erk_base_mono k (empty_subset _) _

/-- `lem:diff-basic`(2): `δ` is independent from `f₁` iff `rk(δ) = rk(f₂)`. -/
theorem indepOver_diff_left_iff :
    IndepOver k ∅ ((Germ.comp g₁ f₂).cb : Set K) f₁.cb ↔
      erk k ∅ ((Germ.comp g₁ f₂).cb : Set K) = erk k ∅ (f₂.cb : Set K) := by
  constructor
  · intro h
    rw [← erk_cb_eq_of_indepOver h, empty_union, erk_diff_eq hg₁ hind]
  · intro h
    refine indepOver_cb_of_erk_eq _ ?_
    rw [empty_union, erk_diff_eq hg₁ hind, h]

/-- `lem:diff-basic`(2): `δ` is independent from `f₂` iff `rk(δ) = rk(f₁)`. -/
theorem indepOver_diff_right_iff (hf₂ : IsInvertible f₂) :
    IndepOver k ∅ ((Germ.comp g₁ f₂).cb : Set K) f₂.cb ↔
      erk k ∅ ((Germ.comp g₁ f₂).cb : Set K) = erk k ∅ (f₁.cb : Set K) := by
  constructor
  · intro h
    rw [← erk_cb_eq_of_indepOver h, empty_union, erk_diff_eq' hg₁ hind hf₂]
  · intro h
    refine indepOver_cb_of_erk_eq _ ?_
    rw [empty_union, erk_diff_eq' hg₁ hind hf₂, h]

end Pair

/-! ### The difference set -/

/-- `def:diff`: the difference germs `f₁⁻¹ f₂` of independent pairs of members of the orbit
of `f₀`. -/
def diffSet (f₀ : Germ k a a') : Set (Germ k a a) :=
  {δ | ∃ f₁ ∈ orbit f₀, ∃ f₂ ∈ orbit f₀, ∃ g₁ : Germ k a' a, IsInverse g₁ f₁ ∧
    IndepOver k ∅ (f₁.cb : Set K) f₂.cb ∧ δ = Germ.comp g₁ f₂}

variable {f₀ : Germ k a a'}

theorem diffSet_nonempty (hf₀ : IsInvertible f₀) : (diffSet f₀).Nonempty := by
  obtain ⟨f₂, hf₂, hind⟩ := exists_mem_orbit_indepOver f₀ f₀.isSmall_cb
  obtain ⟨g₀, hg₀⟩ := hf₀
  exact ⟨_, f₀, self_mem_orbit f₀, f₂, hf₂, g₀, hg₀, hind.symm, rfl⟩

theorem isInvertible_of_mem_diffSet (hf₀ : IsInvertible f₀) {δ : Germ k a a}
    (hδ : δ ∈ diffSet f₀) : IsInvertible δ := by
  obtain ⟨f₁, h₁, f₂, h₂, g₁, hg₁, -, rfl⟩ := hδ
  obtain ⟨g₂, hg₂⟩ := isInvertible_of_mem_orbit hf₀ h₂
  exact ⟨Germ.comp g₂ f₁, hg₂.comp hg₁.symm⟩

/-- `lem:diff-basic`(1): the inverse of a difference germ is a difference germ. -/
theorem inv_mem_diffSet (hf₀ : IsInvertible f₀) {δ δ' : Germ k a a} (hδ : δ ∈ diffSet f₀)
    (hi : IsInverse δ' δ) : δ' ∈ diffSet f₀ := by
  obtain ⟨f₁, h₁, f₂, h₂, g₁, hg₁, hind, rfl⟩ := hδ
  obtain ⟨g₂, hg₂⟩ := isInvertible_of_mem_orbit hf₀ h₂
  rw [← (hg₂.comp hg₁.symm).unique hi]
  exact ⟨f₂, h₂, f₁, h₁, g₂, hg₂, hind.symm, rfl⟩

theorem map_mem_diffSet {δ : Germ k a a} (hδ : δ ∈ diffSet f₀) (σ : K ≃ₐ[k] K) :
    δ.map σ ∈ diffSet f₀ := by
  obtain ⟨f₁, h₁, f₂, h₂, g₁, hg₁, hind, rfl⟩ := hδ
  refine ⟨f₁.map σ, map_mem_orbit h₁ σ, f₂.map σ, map_mem_orbit h₂ σ, g₁.map σ, hg₁.map σ,
    ?_, comp_map σ g₁ f₂⟩
  have := hind.image σ
  rwa [image_empty, ← AlgEquiv.coe_toAlgHom, ← coe_map, ← coe_map, ← cb_map, ← cb_map]
    at this

/-- `lem:diff-basic`(1): the difference set is a single orbit. -/
theorem diffSet_eq_orbit {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ diffSet f₀) :
    diffSet f₀ = orbit δ₀ := by
  ext δ
  constructor
  · rintro ⟨f₁', h₁', f₂', h₂', g₁', hg₁', hind', rfl⟩
    obtain ⟨f₁, h₁, f₂, h₂, g₁, hg₁, hind, rfl⟩ := hδ₀
    obtain ⟨σ, hσ⟩ : ∃ σ : K ≃ₐ[k] K, f₁.map σ = f₁' := by
      rw [← orbit_eq_of_mem h₁] at h₁'
      exact h₁'
    have hind₂ : IndepOver k ∅ ((f₂.map σ).cb : Set K) f₁'.cb := by
      have := hind.symm.image σ
      rwa [image_empty, ← AlgEquiv.coe_toAlgHom, ← coe_map, ← coe_map, ← cb_map, ← cb_map,
        hσ] at this
    obtain ⟨τ, hτ⟩ :=
      exists_algEquiv_of_mem_orbit (map_mem_orbit h₂ σ) h₂' f₁'.isSmall_cb hind₂ hind'.symm
    have hfix : f₁'.map (τ.restrictScalars k) = f₁' := by
      refine (map_eq_self_iff _ _).2 fun x hx ↦ ?_
      change τ x = x
      exact τ.commutes ⟨x, subset_racl k _ hx⟩
    have hinv : IsInverse ((g₁.map σ).map (τ.restrictScalars k)) f₁' := by
      have := (hg₁.map σ).map (τ.restrictScalars k)
      rwa [hσ, hfix] at this
    refine ⟨σ.trans (τ.restrictScalars k), ?_⟩
    change (Germ.comp g₁ f₂).map (σ.trans (τ.restrictScalars k)) = Germ.comp g₁' f₂'
    rw [← map_map, comp_map, comp_map, hτ, hinv.unique hg₁']
  · rintro ⟨σ, rfl⟩
    exact map_mem_diffSet hδ₀ σ

theorem erk_cb_eq_of_mem_diffSet {δ δ' : Germ k a a} (hδ : δ ∈ diffSet f₀)
    (hδ' : δ' ∈ diffSet f₀) : erk k ∅ (δ.cb : Set K) = erk k ∅ (δ'.cb : Set K) := by
  rw [diffSet_eq_orbit hδ'] at hδ
  exact erk_cb_eq_of_mem_orbit hδ

/-- `lem:diff-basic`(2): every difference germ has rank at least the rank of the generic
set. -/
theorem erk_cb_le_of_mem_diffSet {δ : Germ k a a} (hδ : δ ∈ diffSet f₀) :
    erk k ∅ (f₀.cb : Set K) ≤ erk k ∅ (δ.cb : Set K) := by
  obtain ⟨f₁, h₁, f₂, h₂, g₁, hg₁, hind, rfl⟩ := hδ
  rw [← erk_cb_eq_of_mem_orbit h₂]
  exact erk_cb_le_erk_diff hg₁ hind

end Germ

end

end GroupConfig
