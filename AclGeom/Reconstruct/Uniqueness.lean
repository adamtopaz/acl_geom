/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Transport
import AclGeom.Perfection.Induces
import AclGeom.Reconstruct.Kernel

/-!
# Uniqueness of the inducing isomorphism up to Frobenius

The uniqueness clause of blueprint Thm `target`: if two isomorphisms `Φ₁, Φ₂ : K^perf ≃+* L^perf`
of chosen perfections induce the same order isomorphism `φ : 𝒢(K/k) ≃o 𝒢(L/l)` and
`trdeg(K/k) ≥ 5`, then `Φ₂ = Frob^n ∘ Φ₁` for some `n : ℤ`.  The integer is unique when `p > 1`,
and `Φ₁ = Φ₂` when `p = 1`.

* `Φ₂ ∘ Φ₁⁻¹` fixes every point of the perfected target geometry (`Induces.point_symm_trans`).
  Both isomorphisms carry `M^perf` onto `φ(M)^perf`, and every closed subextension of the
  perfected target has this form.
* Rank five transports from `K/k` to `L^perf/l^perf` along `φ` and the perfection order
  isomorphism, so the Frobenius kernel theorem applies (`Induces.exists_eq_trans_frobZPow`).
* Frobenius twists induce the same map (`Induces.trans_frobZPow`), which gives the fibre
  description `Induces.iff_exists_eq_trans_frobZPow`.
* The exponent is unique in positive characteristic (`trans_frobZPow_injective`), and the
  inducing isomorphism is unique in characteristic zero (`Induces.eq_of_p_eq_one`).

No hypothesis on the bases is needed: relative algebraic closedness of `k` and `l` enters only the
base clause `Induces.compatible`.  The existence of an inducing isomorphism is not claimed here.

**Status:** uniqueness and the Frobenius fibre for supplied inducing maps are proved (#9).
Reconstruction existence remains open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]
  {π : Perfection K} {ρ : Perfection L}

/-- Rank five transports to the perfected target along an order isomorphism of closed lattices
and the perfection order isomorphism. -/
private theorem five_le_trdeg_basePerf (ρ : Perfection L) (φ : ClosedIF k K ≃o ClosedIF l L)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    (5 : Cardinal) ≤ Algebra.trdeg (ρ.basePerf l) ρ.carrier :=
  Cardinal.ofNat_le_lift_iff.1 <| (Cardinal.ofNat_le_lift_iff.2 htr).trans
    (lift_trdeg_le_of_orderIso (φ.trans (ρ.latticeIso l)))

/-- **Uniqueness of the Frobenius exponent** (blueprint Thm `target`: if `p > 1`, the integer
is unique).  The rank hypothesis on `K/k`, transported along `φ`, supplies an element of the
perfected target that is transcendental over `l^perf`. -/
theorem trans_frobZPow_injective (φ : ClosedIF k K ≃o ClosedIF l L)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (hp : ρ.p ≠ 1) (Φ : π.carrier ≃+* ρ.carrier) :
    Function.Injective fun n : ℤ ↦ Φ.trans (ρ.frobZPow n) := by
  classical
  obtain ⟨z, hz⟩ := fresh_three_of_five_le_trdeg (five_le_trdeg_basePerf ρ φ htr) ∅ (by simp)
  intro m n hmn
  refine frobeniusZPow_injective (k := ρ.basePerf l) ρ.p hp (x := z) (by simpa using hz) ?_
  ext y
  obtain ⟨x, rfl⟩ := Φ.surjective y
  exact DFunLike.congr_fun hmn x

variable {φ : ClosedIF k K ≃o ClosedIF l L} {Φ₁ Φ₂ : π.carrier ≃+* ρ.carrier}

/-- **Two isomorphisms inducing the same map differ by a point-fixing automorphism**: if `Φ₁` and
`Φ₂` induce `φ`, then `Φ₂ ∘ Φ₁⁻¹` fixes every point `[z]` of the perfected target geometry. -/
theorem Induces.point_symm_trans (h₁ : π.Induces ρ φ Φ₁) (h₂ : π.Induces ρ φ Φ₂)
    (z : ρ.carrier) :
    ClosedIF.point (ρ.basePerf l) ((Φ₁.symm.trans Φ₂) z) = ClosedIF.point (ρ.basePerf l) z := by
  -- `Φ₂ ∘ Φ₁⁻¹` fixes every closed subextension `N = φ(M)^perf` of the perfected target.
  have hfix : ∀ N : ClosedIF (ρ.basePerf l) ρ.carrier,
      (Φ₁.symm.trans Φ₂) '' (N.1 : Set ρ.carrier) = N.1 := by
    intro N
    obtain ⟨M, hM⟩ : ∃ M, φ M = ρ.comapClosed l N := ⟨_, φ.apply_symm_apply _⟩
    have hN : ρ.perfSubfield (φ M).1.toSubfield = N.1.toSubfield := by
      rw [hM]
      exact congrArg (fun P : ClosedIF (ρ.basePerf l) ρ.carrier ↦ P.1.toSubfield)
        (ρ.perfClosed_comapClosed N)
    have hi : ∀ {Φ : π.carrier ≃+* ρ.carrier}, π.Induces ρ φ Φ →
        Φ '' (π.perfSubfield M.1.toSubfield : Set π.carrier) = (N.1 : Set ρ.carrier) := by
      intro Φ h
      have hS := congrArg (fun F : Subfield ρ.carrier ↦ (F : Set ρ.carrier)) ((h M).symm.trans hN)
      simp only [Subfield.coe_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hS
      exact hS
    have hS₁ : Φ₁.symm '' (N.1 : Set ρ.carrier) =
        (π.perfSubfield M.1.toSubfield : Set π.carrier) := by
      rw [← hi h₁]
      exact Φ₁.toEquiv.symm_image_image _
    rw [RingEquiv.coe_trans, Set.image_comp, hS₁]
    exact hi h₂
  refine ClosedIF.point_eq_point_iff.2 ⟨?_, ?_⟩
  · have hmem : (Φ₁.symm.trans Φ₂) z ∈
        (Φ₁.symm.trans Φ₂) '' ((ClosedIF.point (ρ.basePerf l) z).1 : Set ρ.carrier) :=
      Set.mem_image_of_mem _ (ClosedIF.mem_point_self z)
    rw [hfix] at hmem
    exact hmem
  · have hmem : (Φ₁.symm.trans Φ₂) z ∈
        ((ClosedIF.point (ρ.basePerf l) ((Φ₁.symm.trans Φ₂) z)).1 : Set ρ.carrier) :=
      ClosedIF.mem_point_self _
    rw [← hfix (ClosedIF.point (ρ.basePerf l) ((Φ₁.symm.trans Φ₂) z))] at hmem
    obtain ⟨w, hw, hwz⟩ := hmem
    rw [(Φ₁.symm.trans Φ₂).injective hwz] at hw
    exact hw

/-- **Uniqueness up to Frobenius** (blueprint Thm `target`): two isomorphisms of chosen
perfections inducing the same lattice isomorphism differ by an integral Frobenius power of the
target, when `trdeg(K/k) ≥ 5`.  The Frobenius kernel theorem is applied to `Φ₂ ∘ Φ₁⁻¹` over the
perfected target. -/
theorem Induces.exists_eq_trans_frobZPow (h₁ : π.Induces ρ φ Φ₁) (h₂ : π.Induces ρ φ Φ₂)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) : ∃ n : ℤ, Φ₂ = Φ₁.trans (ρ.frobZPow n) := by
  obtain ⟨n, hn⟩ := exists_eq_frobeniusZPow_of_point_fixed (k := ρ.basePerf l) ρ.p
    (five_le_trdeg_basePerf ρ φ htr) (Φ₁.symm.trans Φ₂) fun z _ ↦ h₁.point_symm_trans h₂ z
  refine ⟨n, ?_⟩
  change Φ₂ = Φ₁.trans (frobeniusZPow ρ.carrier ρ.p n)
  rw [← hn]
  ext x
  simp

/-- **The fibre of `Induces`** (blueprint Thm `target`): given one isomorphism inducing `φ`, the
isomorphisms inducing `φ` are exactly its integral Frobenius twists, when `trdeg(K/k) ≥ 5`. -/
theorem Induces.iff_exists_eq_trans_frobZPow (h₁ : π.Induces ρ φ Φ₁)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    π.Induces ρ φ Φ₂ ↔ ∃ n : ℤ, Φ₂ = Φ₁.trans (ρ.frobZPow n) := by
  refine ⟨fun h₂ ↦ h₁.exists_eq_trans_frobZPow h₂ htr, ?_⟩
  rintro ⟨n, rfl⟩
  exact h₁.trans_frobZPow n

/-- **Characteristic zero: the inducing isomorphism is unique** (blueprint Thm `target`, the case
`p = 1`; validation item TEST-1). -/
theorem Induces.eq_of_p_eq_one (h₁ : π.Induces ρ φ Φ₁) (h₂ : π.Induces ρ φ Φ₂)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (hp : ρ.p = 1) : Φ₁ = Φ₂ := by
  obtain ⟨n, rfl⟩ := h₁.exists_eq_trans_frobZPow h₂ htr
  change Φ₁ = Φ₁.trans (frobeniusZPow ρ.carrier ρ.p n)
  rw [frobeniusZPow_eq_one_of_eq_one (K := ρ.carrier) ρ.p hp n]
  ext x
  rfl

end Perfection

end

end AclGeom
