/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Perfection.Induces
import AclGeom.Reconstruct.Existence

/-!
# Existence of an inducing isomorphism of chosen perfections

Blueprint Thm `target`, existence part, for the original fields.  Let `K/k` and `L/l` be
relatively algebraically closed extensions with `trdeg(K/k) ≥ 5`, and let
`φ : ClosedIF k K ≃o ClosedIF l L` be an order isomorphism.  For chosen perfections `π` of `K` and
`ρ` of `L`, some field isomorphism `Φ : K^perf ≃+* L^perf` carries `k^perf` onto `l^perf` and
induces `φ` (`Perfection.exists_induces`).

* `Perfection.isRAC_basePerf`: the perfected base `k^perf` is relatively algebraically closed in
  `K^perf` whenever `k` is relatively algebraically closed in `K`.  The bottom of `𝒢(K/k)` is `k`
  itself, its perfection is `k^perf`, and perfections of closed fields are relatively
  algebraically closed (`isRAC_perfIF`).
* `Perfection.exists_induces`: conjugate `φ` by the perfection order isomorphisms
  (`latticeIso`, blueprint Prop `perf-lattice`).  Apply the perfect-field existence theorem
  `exists_ringEquiv_closedIFMap_eq` to the perfections, and recognize the result as the
  transported lattice map of the inducing isomorphism (`induces_iff_eq_inducedIso`).

ACF J-completeness of the two perfections' algebraic-closure pairs is an explicit hypothesis.
Uniqueness up to Frobenius is the landed `Induces.iff_exists_eq_trans_frobZPow`; the converse is
`induces_inducedIso`.

**Status:** perfected-base RAC and actual inducing existence through arbitrary chosen
perfections of the original fields are proved (#9, conditional original-field existence).
Only original-base RAC on both sides, source rank five and both still-open perfected ACF
J-completeness hypotheses are supplied; perfected-base RAC, perfected source rank and the
actual conjugated lattice map are derived. The original fields need not be perfect. The
bundles supply separate exponential characteristics and two local Prop-valued PerfectField
witnesses; no global instance, local Algebra instance, supplied point/scalar/inducing oracle
or duplicate RingEquiv is added. Main assembles the public conditional target with rank,
base/intersection formulas, the exact Frobenius fibre, characteristic-zero uniqueness,
positive-characteristic exponent uniqueness and converse. Unconditional completeness and
literal/TOT/group/three-pair/tensor/frozen obligations remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The perfected base is relatively algebraically closed** (blueprint Prop `perf-lattice`,
applied to the bottom): if `k` is relatively algebraically closed in `K`, then `k^perf` is
relatively algebraically closed in the chosen perfection of `K`. -/
theorem isRAC_basePerf (π : Perfection K) (hk : IsRAC (⊥ : IntermediateField k K)) :
    IsRAC (⊥ : IntermediateField (π.basePerf k) π.carrier) := by
  -- The bottom of `𝒢(K/k)` is the image of `k`.
  have hbot : (⊥ : ClosedIF k K).1.toSubfield = (algebraMap k K).fieldRange := by
    rw [ClosedIF.coe_bot, isRAC_iff_racl_eq.1 hk, IntermediateField.bot_toSubfield]
  -- Hence its perfection is the bottom over the perfected base.
  have heq : π.perfIF k ⊥ = ⊥ := by
    apply IntermediateField.toSubfield_injective
    rw [IntermediateField.bot_toSubfield]
    change π.perfSubfield (⊥ : ClosedIF k K).1.toSubfield = (π.basePerf k).subtype.fieldRange
    rw [hbot]
    exact (Subfield.fieldRange_subtype _).symm
  rw [← heq]
  exact π.isRAC_perfIF ⊥

/-- **An isomorphism of chosen perfections induces the lattice isomorphism** (the existence part
of blueprint Thm `target`): for relatively algebraically closed extensions with
`trdeg(K/k) ≥ 5`, every order isomorphism `φ` of closed-subfield lattices is induced by a field
isomorphism of the chosen perfections carrying `k^perf` onto `l^perf`.  ACF J-completeness of the
two perfections' algebraic-closure pairs is assumed. -/
theorem exists_induces (π : Perfection K) (ρ : Perfection L)
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure (↥(π.basePerf k)) (AlgebraicClosure π.carrier)))
      (AlgebraicClosure π.carrier))
    (hcomp' : JCompletenessACF (↥(algebraicClosure (↥(ρ.basePerf l)) (AlgebraicClosure ρ.carrier)))
      (AlgebraicClosure ρ.carrier))
    (φ : ClosedIF k K ≃o ClosedIF l L) :
    ∃ Φ : π.carrier ≃+* ρ.carrier,
      CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ ∧ π.Induces ρ φ Φ := by
  have : PerfectField π.carrier := PerfectRing.toPerfectField π.carrier π.p
  have : PerfectField ρ.carrier := PerfectRing.toPerfectField ρ.carrier ρ.p
  -- The perfected source still has rank at least five.
  have htrπ : (5 : Cardinal) ≤ Algebra.trdeg (π.basePerf k) π.carrier :=
    Cardinal.ofNat_le_lift_iff.1 <| (Cardinal.ofNat_le_lift_iff.2 htr).trans
      (lift_trdeg_le_of_orderIso (π.latticeIso k))
  -- The perfect-field existence theorem for `φ` conjugated to the perfections.
  obtain ⟨σ, hσ, he⟩ := exists_ringEquiv_closedIFMap_eq π.p htrπ hcomp ρ.p hcomp'
    (π.isRAC_basePerf hk) (ρ.isRAC_basePerf hl)
    ((π.latticeIso k).symm.trans (φ.trans (ρ.latticeIso l)))
  refine ⟨σ, hσ, (induces_iff_eq_inducedIso hσ).2 ?_⟩
  rw [inducedIso, ← he]
  ext M
  simp only [OrderIso.trans_apply, OrderIso.symm_apply_apply]

end Perfection

end

end AclGeom
