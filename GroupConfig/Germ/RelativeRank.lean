/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.CompCodes
import GroupConfig.Germ.HW

/-!
# Generic elements of the group over a larger base

Blueprint `sources/group_configuration/09-constructibility.tex`, `rem:constr-connected`: over the
final base, the generic elements of the group `G` of a Hrushovski–Weil datum `g₀` are its
elements of maximal rank `n = rk Cb(g₀)`; they form one orbit, and every element of `G` is a
product of two of them.

For a small subfield `M` (the final base `acl(k'')` of the source, or `k''` itself; no algebraic
closedness is needed):

* every element of `G` has rank at most `n` over `M` (`GroupConfig.Germ.IsHW.erk_base_cb_le`), and
  it has rank exactly `n` over `M` iff it lies in the generic set and is independent from `M`
  (`GroupConfig.Germ.IsHW.erk_base_cb_eq_iff`);
* every element of `G` is a product of two elements of `G` of rank `n` over `M`
  (`GroupConfig.Germ.IsHW.exists_mul_eq_of_mem_prodSet`);
* automorphisms over `M` preserve ranks over `M` (`GroupConfig.Germ.erk_cb_map_restrictScalars`),
  and any two elements of `G` of rank `n` over `M` are conjugate by an automorphism over `M`
  (`GroupConfig.Germ.IsHW.exists_algEquiv_of_erk_base_eq`).

All ranks are over the final base `M`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `rem:constr-connected` is complete over every small base.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {a : ι → K}

namespace Germ

/-- An automorphism over a subfield `M` preserves ranks of canonical bases over `M`. Named
consumer: the invariance part of the one-orbit statement of `rem:constr-connected`. -/
theorem erk_cb_map_restrictScalars {κ : Type*} [Finite κ] {a' : κ → K}
    {M : IntermediateField k K} (σ : K ≃ₐ[↥M] K) (g : Germ k a a') :
    erk k (M : Set K) ((g.map (σ.restrictScalars k)).cb : Set K) =
      erk k (M : Set K) (g.cb : Set K) := by
  have hM : (σ.restrictScalars k) '' (M : Set K) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change σ y ∈ M
      rw [show σ y = y from σ.commutes ⟨y, hy⟩]
      exact hy
    · intro hx
      exact ⟨x, hx, σ.commutes ⟨x, hx⟩⟩
  rw [cb_map, coe_map, AlgEquiv.coe_toAlgHom,
    ← erk_image (σ.restrictScalars k) (M : Set K) (g.cb : Set K), hM]

namespace IsHW

variable {g₀ : Germ k a a} (hw : IsHW g₀)
include hw

/-- `rem:constr-connected`: every element of the group has rank at most `rk Cb(g₀)` over any
base. -/
theorem erk_base_cb_le (C : Set K) {γ : Germ k a a} (hγ : γ ∈ prodSet g₀) :
    erk k C (γ.cb : Set K) ≤ erk k ∅ (g₀.cb : Set K) :=
  (erk_base_mono k (empty_subset C) _).trans (hw.erk_cb_le_of_mem_prodSet hγ)

/-- `rem:constr-connected`: an element of the group has maximal rank over `M` iff it lies in
the generic set and is independent from `M`. -/
theorem erk_base_cb_eq_iff {M : Set K} {γ : Germ k a a} (hγ : γ ∈ prodSet g₀) :
    erk k M (γ.cb : Set K) = erk k ∅ (g₀.cb : Set K) ↔
      γ ∈ orbit g₀ ∧ IndepOver k ∅ (γ.cb : Set K) M := by
  constructor
  · intro h
    have h0 : erk k ∅ (γ.cb : Set K) = erk k ∅ (g₀.cb : Set K) :=
      le_antisymm (hw.erk_cb_le_of_mem_prodSet hγ)
        (h.symm.le.trans (erk_base_mono k (empty_subset M) _))
    refine ⟨(hw.mem_orbit_iff_erk_eq hγ).2 h0, indepOver_cb_of_erk_eq γ ?_⟩
    rw [empty_union, h, h0]
  · rintro ⟨hmem, hind⟩
    have h := erk_cb_eq_of_indepOver hind
    rw [empty_union] at h
    rw [h, erk_cb_of_mem hmem]

/-- `rem:constr-connected`: every element of the group is a product of two elements of the
group of maximal rank over a small base `M`. -/
theorem exists_mul_eq_of_mem_prodSet {M : Set K} (hM : IsSmall k M) {γ : Germ k a a}
    (hγ : γ ∈ prodSet g₀) :
    ∃ γ₁ ∈ prodSet g₀, ∃ γ₂ ∈ prodSet g₀, γ = γ₁ * γ₂ ∧
      erk k M (γ₁.cb : Set K) = erk k ∅ (g₀.cb : Set K) ∧
      erk k M (γ₂.cb : Set K) = erk k ∅ (g₀.cb : Set K) := by
  -- A member of the generic set independent from `M` and from `γ`.
  obtain ⟨f, hf, hfind⟩ := exists_mem_orbit_indepOver g₀ (hM.union γ.isSmall_cb)
  obtain ⟨hγf, -⟩ := hw.mul_mem_of_indepOver hγ hf (hfind.mono_right subset_union_right)
  obtain ⟨γ', hγ'⟩ := isUnit_iff.1 (hw.isUnit_of_mem_prodSet hγ)
  obtain ⟨f', hf'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hf)
  have hfM : erk k M (f.cb : Set K) = erk k ∅ (g₀.cb : Set K) := by
    have h := erk_cb_eq_of_indepOver (hfind.mono_right subset_union_left)
    rw [empty_union] at h
    rw [h, erk_cb_of_mem hf]
  -- `γ f` and `f` are interalgebraic over `Cb(γ)`, so `γ f` keeps the rank of `f` over `M`.
  have h₁ : erk k M ((γ * f).cb : Set K) = erk k ∅ (g₀.cb : Set K) := by
    refine le_antisymm (hw.erk_base_cb_le M (hw.mem_prodSet_of_mem hγf)) ?_
    have h := erk_cb_eq_of_indepOver hfind
    rw [empty_union, erk_cb_of_mem hf] at h
    calc erk k ∅ (g₀.cb : Set K) = erk k (M ∪ γ.cb) (f.cb : Set K) := h.symm
      _ = erk k (M ∪ γ.cb) ((γ * f).cb : Set K) := by
          rw [mul_def, erk_cb_comp_eq_of_isInverse_left M f hγ']
      _ ≤ erk k M ((γ * f).cb : Set K) := erk_base_mono k subset_union_left _
  -- The inverse of `f` has the same algebraic closure of its canonical base.
  have hsub {A B : Set K} (h : racl k A = racl k B) : A ⊆ racl k (M ∪ B) :=
    (subset_racl k A).trans (h ▸ racl_mono (k := k) subset_union_right)
  have h₂ : erk k M (f'.cb : Set K) = erk k ∅ (g₀.cb : Set K) :=
    (erk_eq_of_subset_racl (hsub hf'.racl_cb_eq) (hsub hf'.racl_cb_eq.symm)).trans hfM
  refine ⟨γ * f, hw.mem_prodSet_of_mem hγf, f', hw.inv_mem_prodSet (hw.mem_prodSet_of_mem hf) hf',
    ?_, h₁, h₂⟩
  have hff : f * f' = 1 := hf'.2
  rw [mul_assoc, hff, mul_one]

/-- `rem:constr-connected`: any two elements of the group of maximal rank over a small base `M`
are conjugate by an automorphism over `M`. -/
theorem exists_algEquiv_of_erk_base_eq {M : IntermediateField k K} (hM : IsSmall k (M : Set K))
    {γ γ' : Germ k a a} (hγ : γ ∈ prodSet g₀) (hγ' : γ' ∈ prodSet g₀)
    (hr : erk k (M : Set K) (γ.cb : Set K) = erk k ∅ (g₀.cb : Set K))
    (hr' : erk k (M : Set K) (γ'.cb : Set K) = erk k ∅ (g₀.cb : Set K)) :
    ∃ σ : K ≃ₐ[↥M] K, γ.map (σ.restrictScalars k) = γ' := by
  obtain ⟨hmem, hind⟩ := (hw.erk_base_cb_eq_iff hγ).1 hr
  obtain ⟨hmem', hind'⟩ := (hw.erk_base_cb_eq_iff hγ').1 hr'
  obtain ⟨τ, hτ⟩ := exists_algEquiv_of_mem_orbit hmem hmem' hM hind hind'
  -- The conjugating automorphism fixes `acl(M) ⊇ M`.
  let σ : K ≃ₐ[↥M] K :=
    { τ.toRingEquiv with commutes' := fun x ↦ τ.commutes ⟨x, subset_racl k _ x.2⟩ }
  have hστ : σ.restrictScalars k = τ.restrictScalars k := AlgEquiv.ext fun _ ↦ rfl
  exact ⟨σ, hστ ▸ hτ⟩

end IsHW

end Germ

end

end GroupConfig
