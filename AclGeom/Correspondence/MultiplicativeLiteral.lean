/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Multiplicative
import AclGeom.Closure.Ambient
import AclGeom.Closure.FreshExtension
import AclGeom.Geometry.Points
import AclGeom.Transfer.Transcendence

/-!
# The multiplicative correspondence theorem

Blueprint Theorem `mulcorr`: let `(x₁, y₁)` and `(x₂, y₂)` be independent generic points of
finite correspondences in `Gₘ²` over an algebraically closed `k ⊆ Ω`.  If `[x₁x₂] = [y₁y₂]`,
there are nonzero integers `m, n` and `c₁, c₂ ∈ kˣ` with `yᵢ^n = cᵢ xᵢ^m` (`mulcorr`).

The finite correspondences give `[xᵢ] = [yᵢ]`, and independence of the two points gives that
of `x₁, x₂`.  The hypotheses `y₁, y₂ ≠ 0` are the `Gₘ` conditions on the second coordinates;
`x₁, x₂ ≠ 0` follow from independence.  The two-pair core
`MulCorrSetup.exists_coset_equations` proves `xᵢ^a yᵢ^b = cᵢ` given an element fresh over
`x₁, x₂`.  The blueprint has no such hypothesis: the theorem passes to `FreshAmbient Ω`
(`Closure.FreshExtension`), pulls the equations back along the injective embedding and takes
`n = b`, `m = -a`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5).
-/

namespace AclGeom

open ClosedIF

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **The multiplicative correspondence theorem** (blueprint Theorem `mulcorr`): for
algebraically independent `x₁, x₂` over an algebraically closed `k ⊆ Ω` and nonzero `y₁, y₂`
with `[xᵢ] = [yᵢ]` and `[x₁x₂] = [y₁y₂]`, there are nonzero integers `m, n` and nonzero
constants `c₁, c₂ ∈ k` with `yᵢ^n = cᵢ xᵢ^m` for `i = 1, 2`. -/
theorem mulcorr [IsAlgClosed k] [IsAlgClosed Ω] {x₁ x₂ y₁ y₂ : Ω}
    (hx : AlgebraicIndependent k ![x₁, x₂]) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (h₁ : point k x₁ = point k y₁) (h₂ : point k x₂ = point k y₂)
    (h₁₂ : point k (x₁ * x₂) = point k (y₁ * y₂)) :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ ∃ c₁ c₂ : k, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      y₁ ^ n = algebraMap k Ω c₁ * x₁ ^ m ∧ y₂ ^ n = algebraMap k Ω c₂ * x₂ ^ m := by
  classical
  -- Pass to an algebraically closed extension with four fresh elements.
  let ι : Ω →ₐ[k] FreshAmbient Ω := IsScalarTower.toAlgHom k Ω (FreshAmbient Ω)
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hpt : ∀ {u v : Ω}, point k u = point k v → racl k {ι u} = racl k {ι v} :=
    fun {u v} h ↦ by
      simpa [Set.image_singleton] using
        algHom_racl_image_eq_of_racl_eq ι (congrArg Subtype.val h : racl k {u} = racl k {v})
  have mem : ∀ {u v : FreshAmbient Ω}, racl k {u} = racl k {v} → v ∈ racl k {u} := fun h ↦ by
    rw [h]
    exact subset_racl k _ (Set.mem_singleton _)
  have h₁' := hpt h₁
  have h₂' := hpt h₂
  have h₁₂' : racl k {ι x₁ * ι x₂} = racl k {ι y₁ * ι y₂} := by
    simpa only [map_mul] using hpt h₁₂
  let S : MulCorrSetup k (FreshAmbient Ω) :=
    { x₁ := ι x₁, y₁ := ι y₁, x₂ := ι x₂, y₂ := ι y₂
      indep := by
        convert hx.map' hι using 1
        funext i
        fin_cases i <;> rfl
      y₁_ne := (map_ne_zero ι).2 hy₁, y₂_ne := (map_ne_zero ι).2 hy₂
      y₁_mem := mem h₁', x₁_mem := mem h₁'.symm, y₂_mem := mem h₂', x₂_mem := mem h₂'.symm
      mul_mem := mem h₁₂', mul_mem' := mem h₁₂'.symm }
  -- One element fresh over the images of `x₁, x₂`.
  obtain ⟨s, hs⟩ := exists_notMem_racl_of_card_lt_trdeg (n := 2)
    (lt_of_lt_of_le (by norm_num) (four_le_trdeg_freshAmbient k Ω)) {ι x₁, ι x₂}
    Finset.card_le_two
  have hs' : s ∉ racl k ({ι x₁, ι x₂} : Set (FreshAmbient Ω)) := by simpa using hs
  obtain ⟨a, b, c₁, c₂, ha, hb, hc₁, hc₂, he₁, he₂⟩ := S.exists_coset_equations hs'
  have he₁' : ι x₁ ^ a * ι y₁ ^ b = algebraMap k (FreshAmbient Ω) c₁ := he₁
  have he₂' : ι x₂ ^ a * ι y₂ ^ b = algebraMap k (FreshAmbient Ω) c₂ := he₂
  -- Pull the equations back to `Ω` and reorient them.
  have pull : ∀ {u v : Ω} {c : k}, u ≠ 0 →
      ι u ^ a * ι v ^ b = algebraMap k (FreshAmbient Ω) c →
      v ^ b = algebraMap k Ω c * u ^ (-a) := fun {u v c} hu h ↦ by
    have h' : u ^ a * v ^ b = algebraMap k Ω c := hι (by
      rw [map_mul, map_zpow₀, map_zpow₀, AlgHom.commutes]
      exact h)
    rw [zpow_neg, ← h', mul_comm (u ^ a), mul_assoc, mul_inv_cancel₀ (zpow_ne_zero a hu),
      mul_one]
  have hx₁ : x₁ ≠ 0 := AlgebraicIndependent.ne_zero hx 0
  have hx₂ : x₂ ≠ 0 := AlgebraicIndependent.ne_zero hx 1
  exact ⟨-a, b, neg_ne_zero.2 ha, hb, c₁, c₂, hc₁, hc₂, pull hx₁ he₁', pull hx₂ he₂'⟩

end AclGeom
