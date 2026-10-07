/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Perfection.Naturality

/-!
# Lattice isomorphisms induced by isomorphisms of chosen perfections

For chosen perfections `π` of `K` and `ρ` of `L`, an isomorphism `Φ : K^perf ≃+* L^perf`
*induces* an order isomorphism `φ : 𝒢(K/k) ≃o 𝒢(L/l)` when `(φ M)^perf = Φ(M^perf)` for every
closed `M` (`Perfection.Induces`; blueprint §type-correct statement, the definition after the
`Perfection` bundle).  This file proves:

* the intersection formula `φ(M) = Φ(M^perf) ∩ L` of blueprint Thm `target`
  (`Induces.mem_iff`) and the resulting uniqueness of `φ` (`Induces.unique`);
* the converse of Thm `target`: an isomorphism carrying `k^perf` onto `l^perf` induces the
  transported lattice map `T_Φ` of blueprint (20.6) (`inducedIso`, `induces_inducedIso`), and
  inducing is equivalent to being `T_Φ` (`induces_iff_eq_inducedIso`);
* the base clause `Φ(k^perf) = l^perf` (`Induces.compatible`).  Applying `Induces` to the bottom
  element only gives `Φ((racl_K k)^perf) = (racl_L l)^perf` (`Induces.map_bot`), because the
  bottom of `𝒢(K/k)` is the relative algebraic closure of `k`.  The base clause therefore assumes
  that both bases are relatively algebraically closed, as Thm `target` does.  Without this the
  clause fails: for `K = L = ℚ(√2)(t)`, `k = ℚ` and `l = ℚ(√2)`, the carrier identity of closed
  fields is induced by the identity, which does not carry `ℚ` onto `ℚ(√2)` (issue #24);
* Frobenius twists of an inducing isomorphism induce the same map (`Induces.trans_frobZPow`), the
  forward half of the fibre clause of Thm `target`. The converse for supplied inducing maps is
  proved in `Reconstruct.Uniqueness`; reconstruction existence remains open;
* an isomorphism `σ : K ≃+* L` compatible with the bases induces, through its unique extension to
  the chosen perfections, the direct transport of closed fields (`induces_liftEquiv`).  With `σ`
  the identity this is the blueprint's statement that the comparison `u_K` between two chosen
  perfections induces the identity of `𝒢(K/k)`.

**Status:** the inducing relation, intersection formula, compatible converse and
forward Frobenius invariance are proved (#24, #10). Reconstruction existence
remains open. The uniqueness-up-to-Frobenius fibre for supplied maps is proved in
`Reconstruct.Uniqueness`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- With a relatively algebraically closed base, the bottom of `𝒢(K/k)` is the image of `k`. -/
private theorem bot_toSubfield_of_isRAC (hk : IsRAC (⊥ : IntermediateField k K)) :
    (⊥ : ClosedIF k K).1.toSubfield = (algebraMap k K).fieldRange := by
  rw [ClosedIF.coe_bot, isRAC_iff_racl_eq.1 hk, IntermediateField.bot_toSubfield]

variable (π : Perfection K) (ρ : Perfection L)

/-- `Φ : K^perf ≃+* L^perf` *induces* `φ : 𝒢(K/k) ≃o 𝒢(L/l)` when `(φ M)^perf = Φ(M^perf)` for
every closed `M` (blueprint §type-correct statement: equality of perfected subfields). -/
def Induces (φ : ClosedIF k K ≃o ClosedIF l L) (Φ : π.carrier ≃+* ρ.carrier) : Prop :=
  ∀ M : ClosedIF k K,
    ρ.perfSubfield (φ M).1.toSubfield = (π.perfSubfield M.1.toSubfield).map Φ.toRingHom

/-- The lattice map `T_Φ` of blueprint (20.6) for an isomorphism of perfections carrying `k^perf`
onto `l^perf`: conjugate the direct transport `N ↦ Φ(N)` (20.5) by the perfection order
isomorphisms. -/
def inducedIso {Φ : π.carrier ≃+* ρ.carrier}
    (hΦ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ) :
    ClosedIF k K ≃o ClosedIF l L :=
  (π.latticeIso k).trans ((CrossBase.closedIFMap Φ hΦ).trans (ρ.latticeIso l).symm)

/-- **Field isomorphisms induce the direct transport.**  A field isomorphism `σ : K ≃+* L`
compatible with the bases induces, through its extension `π.liftEquiv ρ σ` to the chosen
perfections, the direct transport `M ↦ σ(M)` of closed fields.  For `σ` the identity this is the
blueprint's statement that the comparison `u_K` of two chosen perfections induces the identity
of `𝒢(K/k)` (`CrossBase.closedIFMap_refl`). -/
theorem induces_liftEquiv {σ : K ≃+* L} (hσ : CrossBase.Compatible (k := k) (l := l) σ) :
    π.Induces ρ (CrossBase.closedIFMap σ hσ) (π.liftEquiv ρ σ) := by
  intro M
  rw [perfSubfield_map]
  congr 1
  apply SetLike.coe_injective
  rw [Subfield.coe_map]
  exact CrossBase.coe_closedIFMap hσ M

variable {π ρ} {φ ψ : ClosedIF k K ≃o ClosedIF l L} {Φ : π.carrier ≃+* ρ.carrier}

/-- **The intersection formula** of blueprint Thm `target`: if `Φ` induces `φ`, then
`φ(M) = Φ(M^perf) ∩ L`. -/
theorem Induces.mem_iff (h : π.Induces ρ φ Φ) {M : ClosedIF k K} {y : L} :
    y ∈ φ M ↔ ρ.incl y ∈ (π.perfSubfield M.1.toSubfield).map Φ.toRingHom := by
  rw [← h M]
  exact ρ.incl_mem_perfIF_iff.symm

/-- An inducing isomorphism carries the perfection of the bottom of `𝒢(K/k)` (the relative
algebraic closure of `k`) onto that of `𝒢(L/l)`. -/
theorem Induces.map_bot (h : π.Induces ρ φ Φ) :
    (π.perfSubfield (⊥ : ClosedIF k K).1.toSubfield).map Φ.toRingHom =
      ρ.perfSubfield (⊥ : ClosedIF l L).1.toSubfield := by
  rw [← h ⊥, OrderIso.map_bot]

/-- The isomorphism of perfections determines the lattice isomorphism it induces. -/
theorem Induces.unique (h₁ : π.Induces ρ φ Φ) (h₂ : π.Induces ρ ψ Φ) : φ = ψ := by
  refine OrderIso.ext (funext fun M ↦ Subtype.ext (SetLike.ext fun y ↦ ?_))
  rw [ClosedIF.mem_val, ClosedIF.mem_val, h₁.mem_iff, h₂.mem_iff]

/-- **The base clause** of blueprint Thm `target`: an inducing isomorphism carries `k^perf` onto
`l^perf`, provided both bases are relatively algebraically closed.  The hypotheses are needed:
see the module docstring. -/
theorem Induces.compatible (h : π.Induces ρ φ Φ) (hk : IsRAC (⊥ : IntermediateField k K))
    (hl : IsRAC (⊥ : IntermediateField l L)) :
    CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ := by
  unfold CrossBase.Compatible
  change (π.basePerf k).subtype.fieldRange.map _ = (ρ.basePerf l).subtype.fieldRange
  rw [Subfield.fieldRange_subtype, Subfield.fieldRange_subtype, basePerf, basePerf,
    ← bot_toSubfield_of_isRAC hk, ← bot_toSubfield_of_isRAC hl]
  exact h.map_bot

/-- **Frobenius twists induce the same map** (blueprint Thm `target`, the easy half of the fibre
clause): integral Frobenius powers fix every closed subextension of the perfection. -/
theorem Induces.trans_frobZPow (h : π.Induces ρ φ Φ) (n : ℤ) :
    π.Induces ρ φ (Φ.trans (ρ.frobZPow n)) := by
  intro M
  apply SetLike.coe_injective
  have hM := congrArg (fun F : Subfield ρ.carrier ↦ (F : Set ρ.carrier)) (h M)
  simp only [Subfield.coe_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hM ⊢
  rw [RingEquiv.coe_trans, Set.image_comp, ← hM]
  exact (ρ.frobZPow_image_closed n (ρ.perfClosed l (φ M))).symm

/-- **The converse** of blueprint Thm `target`: an isomorphism of perfections carrying `k^perf`
onto `l^perf` induces the transported lattice map `T_Φ` (20.6).  No hypothesis on the bases is
needed. -/
theorem induces_inducedIso (hΦ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ) :
    π.Induces ρ (π.inducedIso ρ hΦ) Φ := by
  intro M
  apply SetLike.coe_injective
  have hM : ρ.latticeIso l (π.inducedIso ρ hΦ M) =
      CrossBase.closedIFMap Φ hΦ (π.latticeIso k M) := by
    rw [inducedIso, OrderIso.trans_apply, OrderIso.trans_apply, OrderIso.apply_symm_apply]
  have hc := congrArg (fun N : ClosedIF (ρ.basePerf l) ρ.carrier ↦ (N.1 : Set ρ.carrier)) hM
  simp only [CrossBase.coe_closedIFMap] at hc
  rw [Subfield.coe_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact hc

/-- Inducing is equivalent to being the transported lattice map `T_Φ` of blueprint (20.6). -/
theorem induces_iff_eq_inducedIso
    (hΦ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ) :
    π.Induces ρ φ Φ ↔ φ = π.inducedIso ρ hΦ := by
  refine ⟨fun h ↦ h.unique (induces_inducedIso hΦ), ?_⟩
  rintro rfl
  exact induces_inducedIso hΦ

end Perfection

end

end AclGeom
