/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Inverse

/-!
# The monoid of germs of a locus to itself

Blueprint `sources/group_configuration/04-germs.tex`, `lem:comp`, `lem:inverse` and
`conv:germ-tuple`, in the form used by the Hrushovski–Weil theorem.

Germs from a locus to itself form a monoid under composition (`Germ.instMonoid`), whose
units are the invertible germs (`Germ.isUnit_iff`); automorphisms over `k` act by monoid
endomorphisms (`Germ.mapHom`), compatibly with composition of automorphisms
(`Germ.map_map`).  Ranks of germs are ranks of their canonical bases; the canonical base
of a product and of a factor are interalgebraic over the other factor
(`Germ.erk_cb_mul_eq`, `lem:comp-codes`(1)).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the monoid of germs of `V` and its group of units `Germ^×(V)` (`lem:inverse`, last
sentence) are complete. So are the compatibility of the action with composition of
automorphisms (`lem:germ-aut`) and the rank statement of `lem:comp-codes`(1).
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Sets algebraic over each other have the same rank. -/
theorem erk_eq_of_subset_racl {C X Y : Set K} (hX : X ⊆ racl k (C ∪ Y))
    (hY : Y ⊆ racl k (C ∪ X)) : erk k C X = erk k C Y := by
  rw [← erk_union_eq_of_subset_racl k hY, ← erk_union_eq_of_subset_racl k hX, union_comm]

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι κ : Type*} [Finite ι]
  [Finite κ] {a : ι → K} {a' : κ → K}

namespace Germ

/-! ### Composition of automorphisms -/

/-- `lem:germ-aut`: the action of germs is compatible with composition of automorphisms. -/
theorem map_map (σ τ : K ≃ₐ[k] K) (g : Germ k a a') : (g.map σ).map τ = g.map (σ.trans τ) := by
  obtain ⟨F, hF_def⟩ : ∃ F : IntermediateField k K, F = racl k (g.cb : Set K) := ⟨_, rfl⟩
  have hF : IsSmall k (F : Set K) := hF_def ▸ g.isSmall_cb.racl
  have _ : IsAlgClosed ↥F := hF_def ▸ isAlgClosed_racl _
  have hcb : g.cb ≤ F := hF_def ▸ subset_racl k _
  have hcomp : (σ.trans τ).toAlgHom = τ.toAlgHom.comp σ.toAlgHom := AlgHom.ext fun _ ↦ rfl
  have hF' : F.map (σ.trans τ).toAlgHom = (F.map σ.toAlgHom).map τ.toAlgHom := by
    rw [hcomp, IntermediateField.map_map]
  have _ := isAlgClosed_map σ F
  have _ := isAlgClosed_map τ (F.map σ.toAlgHom)
  have hF2 := isSmall_map τ (isSmall_map σ hF)
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  have hy1 : IsGenericOver (F.map σ.toAlgHom) a (⇑σ ∘ y) := (isGenericOver_map_iff σ _ a y).2 hy
  have hy2 : IsGenericOver ((F.map σ.toAlgHom).map τ.toAlgHom) a (⇑τ ∘ (⇑σ ∘ y)) :=
    (isGenericOver_map_iff τ _ a _).2 hy1
  have hcb2 : (g.map (σ.trans τ)).cb ≤ (F.map σ.toAlgHom).map τ.toAlgHom := by
    rw [← hF']
    exact cb_map_le _ hcb
  refine eq_of_eval_eq hF2 (cb_map_le τ (cb_map_le σ hcb)) hcb2 hy2 ?_
  have h1 := eval_map g (σ.trans τ) hF hcb hy
  rw [hF', AlgEquiv.coe_trans, Function.comp_assoc] at h1
  rw [h1, eval_map _ τ (isSmall_map σ hF) (cb_map_le σ hcb) hy1, eval_map g σ hF hcb hy]
  exact (Function.comp_assoc _ _ _).symm

/-! ### The monoid of germs of a locus to itself -/

instance : Mul (Germ k a a) := ⟨Germ.comp⟩

instance : One (Germ k a a) := ⟨Germ.id a⟩

theorem mul_def (g g' : Germ k a a) : g * g' = Germ.comp g g' := rfl

theorem one_def : (1 : Germ k a a) = Germ.id a := rfl

/-- `lem:comp`: germs of a locus to itself form a monoid under composition. -/
instance : Monoid (Germ k a a) where
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

/-- `lem:inverse`: the units of the monoid of germs are the invertible germs. -/
theorem isUnit_iff {g : Germ k a a} : IsUnit g ↔ ∃ h, IsInverse h g := by
  rw [isUnit_iff_exists]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, h2, h1⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, h2, h1⟩

/-- `lem:germ-aut`, `lem:comp`: an automorphism over `k` acts on germs by a monoid
endomorphism. -/
def mapHom (σ : K ≃ₐ[k] K) : Germ k a a →* Germ k a a where
  toFun := Germ.map σ
  map_one' := map_id σ a
  map_mul' := comp_map σ

theorem mapHom_apply (σ : K ≃ₐ[k] K) (g : Germ k a a) : mapHom σ g = g.map σ := rfl

/-! ### Ranks of germs -/

/-- The rank of a germ is invariant under automorphisms over `k`. -/
theorem erk_cb_map (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    erk k ∅ ((g.map σ).cb : Set K) = erk k ∅ (g.cb : Set K) := by
  rw [cb_map, coe_map, AlgEquiv.coe_toAlgHom, ← image_empty ⇑σ, erk_image, image_empty]

/-- `lem:comp-codes`(1): a product and its left factor are interalgebraic over the right
factor, when the right factor is invertible. -/
theorem erk_cb_mul_eq {γ δ : Germ k a a} (hγ : IsUnit γ) (C : Set K) :
    erk k (C ∪ γ.cb) ((δ * γ).cb : Set K) = erk k (C ∪ γ.cb) (δ.cb : Set K) := by
  obtain ⟨γ', hγ'⟩ := isUnit_iff.1 hγ
  refine erk_eq_of_subset_racl ?_ ?_
  · refine (cb_comp_le_racl δ γ).trans (racl_mono (k := k) ?_)
    rw [union_assoc]
    exact subset_union_right
  · refine (cb_le_of_isInverse δ hγ').trans (racl_mono (k := k) ?_)
    exact union_subset subset_union_right (subset_union_right.trans subset_union_left)

end Germ

end

end GroupConfig
