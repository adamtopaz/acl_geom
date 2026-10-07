/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Ambient
import AclGeom.Closure.RationalFunctions
import AclGeom.Test.RationalFunctionField

/-!
# The Frobenius kernel theorem needs its rank hypothesis

The displayed blueprint Thm `kernel` asks only for a perfect extension `K/k` with `k` relatively
algebraically closed, but its proof uses five independent elements, and the Lean kernel theorem
(`exists_eq_frobeniusZPow_of_point_fixed`, `eq_refl_of_point_fixed` in `Reconstruct.Kernel`)
assumes `trdeg_k K ≥ 5`.  Without a rank hypothesis the statement is false
(`not_forall_eq_refl_of_point_fixed`, issue #9).

The construction works over every field `k`; its characteristic-zero specialization
`ℚ(t)/ℚ` refutes the rank-free kernel claim. The coefficient field is relatively closed (M1,
`mem_range_algebraMap_of_isAlgebraic_fractionRing`). In the `ℚ` specialization the ambient field
has characteristic zero, so it is perfect and every integral Frobenius power is the identity.
The geometry has a single point:
for transcendental `z`, `z ∈ racl_ℚ {t} = ℚ(t)` and exchange give `t ∈ racl_ℚ {z}`, so
`[z] = ℚ(t)`.  Hence the translation `t ↦ t + 1` fixes every point, but it is not the identity.

**Status:** the rank-free characteristic-zero kernel has a concrete Lean refutation (#9).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open MvPolynomial

/-- **The rank hypothesis of the Frobenius kernel theorem cannot be dropped** (blueprint Thm
`kernel`, issue #9). For every field `k`, the translation `t ↦ t + 1` of `k(t)/k` fixes
every point but is not the identity. It is a `k`-algebra automorphism and `k` is relatively
algebraically closed. In characteristic zero the identity is the only Frobenius power. -/
theorem not_forall_eq_refl_of_point_fixed (k : Type*) [Field k] :
    IsRAC (⊥ : IntermediateField k (Test.RatFn k 1)) ∧
      ¬ ∀ σ : Test.RatFn k 1 ≃ₐ[k] Test.RatFn k 1,
        (∀ z : Test.RatFn k 1, z ∉ racl k (∅ : Set (Test.RatFn k 1)) →
          ClosedIF.point k (σ z) = ClosedIF.point k z) →
        σ.toRingEquiv = RingEquiv.refl _ := by
  -- `k` is relatively algebraically closed in `k(t)` (M1).
  have hbot : (⊥ : ClosedIF k (Test.RatFn k 1)).1 = ⊥ := by
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    have hxalg : IsAlgebraic k x :=
      ClosedIF.mem_bot_iff.1 (ClosedIF.mem_val.1 hx)
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isAlgebraic_fractionRing
      (F := k) (σ := Fin 1) hxalg
    exact IntermediateField.mem_bot.2 ⟨c, hc⟩
  refine ⟨by rw [← hbot]; exact (⊥ : ClosedIF k (Test.RatFn k 1)).2, fun hker ↦ ?_⟩
  -- The geometry has one point: every transcendental element generates everything.
  have hgen : racl k ({Test.t k 1 0} : Set (Test.RatFn k 1)) = ⊤ := by
    simpa only [Set.range_unique, Fin.default_eq_zero] using Test.racl_range_t k 1
  have htop : ∀ z : Test.RatFn k 1, z ∉ racl k (∅ : Set (Test.RatFn k 1)) →
      racl k ({z} : Set (Test.RatFn k 1)) = ⊤ := by
    intro z hz
    have hzt : z ∈ racl k (insert (Test.t k 1 0) (∅ : Set (Test.RatFn k 1))) := by
      simp [hgen]
    have htz : Test.t k 1 0 ∈ racl k ({z} : Set (Test.RatFn k 1)) := by
      simpa using racl_exchange hzt hz
    rw [eq_top_iff, ← hgen]
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 htz)
  -- The translation `t ↦ t + 1`.
  let shift : MvPolynomial (Fin 1) k ≃ₐ[k] MvPolynomial (Fin 1) k :=
    AlgEquiv.ofAlgHom (aeval fun i ↦ X i + 1) (aeval fun i ↦ X i - 1)
      (algHom_ext fun i ↦ by simp) (algHom_ext fun i ↦ by simp)
  let e : Test.RatFn k 1 ≃ₐ[k] Test.RatFn k 1 := IsFractionRing.algEquivOfAlgEquiv shift
  -- It fixes every point.
  have hfix : ∀ z : Test.RatFn k 1, z ∉ racl k (∅ : Set (Test.RatFn k 1)) →
      ClosedIF.point k (e.toRingEquiv z) = ClosedIF.point k z := by
    intro z hz
    have hez : e z ∉ racl k (∅ : Set (Test.RatFn k 1)) := fun h ↦
      hz ((algHom_mem_racl_empty_iff e.toAlgHom).1 h)
    apply Subtype.ext
    rw [ClosedIF.coe_point, ClosedIF.coe_point]
    exact (htop _ hez).trans (htop z hz).symm
  -- It moves `t`.
  have ht : e (Test.t k 1 0) = Test.t k 1 0 + 1 := by
    change IsFractionRing.algEquivOfAlgEquiv shift
      (algebraMap (MvPolynomial (Fin 1) k) (Test.RatFn k 1) (X 0)) = _
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simp [shift, Test.t]
  have h1 : e (Test.t k 1 0) = Test.t k 1 0 := DFunLike.congr_fun (hker e hfix) (Test.t k 1 0)
  rw [ht] at h1
  simp at h1

end

end AclGeom
