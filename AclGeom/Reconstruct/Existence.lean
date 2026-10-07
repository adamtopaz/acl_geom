/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Reconstruct.Points
import AclGeom.Reconstruct.Scalar

/-!
# Existence of an inducing field isomorphism

Let `k ⊆ K` and `l ⊆ L` be relatively algebraically closed bases of perfect fields, `K` of rank at
least five, and let `e : ClosedIF k K ≃o ClosedIF l L` be an order isomorphism of closed-subfield
lattices.  Under ACF J-completeness for both algebraic-closure pairs, `e` is induced by a field
isomorphism compatible with the bases:

* `closedIFMap_interpretedRingEquiv`: for a base tuple `j(x₀, a)` carried to `j(x₀', a')`, the
  corrected interpreted reconstruction `H` induces `e`.  `H` carries the base onto the base
  (`interpretedRingEquiv_compatible`) and every point outside `acl_k(a)` to the point of its image
  (`interpretedRingEquiv_point`).  The conditional propagation `eq_closedIFMap_of_point_eq` then
  identifies `e` with the transport of closed fields along `H` (blueprint Prop `all-points` and
  the atomistic extension).
* `exists_ringEquiv_closedIFMap_eq`: hence some compatible field isomorphism induces `e`.  The base
  pair of `K` is chosen fresh, the rank of `L` is read off from `e`, and the image base exists by
  `exists_map_jTupleOf_eq`.

These results live in the perfected, relatively algebraically closed setting, under the explicit
open ACF J-completeness inputs.  The blueprint's scalar elimination is replaced by the geometric
transport of genericity (`interpretedRingEquiv_base_coord`).  The literal ratio, totalization and
scalar arguments keep their recorded status.

**Status:** actual inducing equality and inducing field-isomorphism existence are proved (#9,
corrected conditional R3/R4 in the perfect-field setting). Both relatively algebraically closed
bases, both perfections and separate exponential characteristics, source rank five and both
still-open ACF J-completeness inputs remain explicit. The existence endpoint derives the source
pair, target rank and actual image pair inline; no supplied pair, target rank or point/scalar oracle
is assumed. Target proves perfected-base RAC and original-field inducing existence through
arbitrary chosen perfections under explicit perfected ACF completeness. The assembled target
theorem with Frobenius uniqueness and unconditional ACF J-completeness remain open. Literal
RatioEq/TOT/scalar arguments, bypassed
linear-disjointness and frozen M4a obligations retain their recorded provenance.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The corrected interpreted reconstruction induces the lattice isomorphism** (the corrected
counterpart of blueprint Prop `all-points` and the atomistic extension): with relatively
algebraically closed bases, `e` is the transport of closed fields along
`interpretedRingEquiv … e …`. -/
theorem closedIFMap_interpretedRingEquiv [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L)) :
    e = CrossBase.closedIFMap (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ)
      (interpretedRingEquiv_compatible q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hk hl) :=
  eq_closedIFMap_of_point_eq e
    (interpretedRingEquiv_compatible q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hk hl) (a := a)
    fun _ hx ↦ interpretedRingEquiv_point q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hx

/-- **Existence of an inducing field isomorphism** (the corrected existence half of the
reconstruction theorem, in the perfected, relatively algebraically closed setting): every order
isomorphism of closed-subfield lattices is the transport of closed fields along some field
isomorphism compatible with the bases.  Perfection of both fields, rank five of `K`, relative
algebraic closedness of both bases and ACF J-completeness of both algebraic-closure pairs are
explicit hypotheses. -/
theorem exists_ringEquiv_closedIFMap_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (e : ClosedIF k K ≃o ClosedIF l L) :
    ∃ (σ : K ≃+* L) (hσ : CrossBase.Compatible (k := k) (l := l) σ),
      e = CrossBase.closedIFMap σ hσ := by
  -- An independent base pair `x₀, a` of `K`: `a` fresh over `∅`, then `x₀` fresh over `a`.
  obtain ⟨a, ha⟩ := fresh_three_of_five_le_trdeg htr ∅ (by simp)
  obtain ⟨x₀, hx⟩ := fresh_three_of_five_le_trdeg htr {a} (by simp)
  have ha' : a ∉ racl k (∅ : Set K) := by simpa using ha
  have hx' : x₀ ∉ racl k ({a} : Set K) := by simpa using hx
  have h₀ : AlgebraicIndependent k ![x₀, a] :=
    algebraicIndependent_pair hx' fun h ↦ hx' (racl_exchange_singleton ha' h)
  -- The rank of `L` and the image base.
  have htr' : (5 : Cardinal) ≤ Algebra.trdeg l L :=
    Cardinal.ofNat_le_lift_iff.1 <| (Cardinal.ofNat_le_lift_iff.2 htr).trans
      (lift_trdeg_le_of_orderIso e)
  obtain ⟨x₀', a', h₀', hφ⟩ := exists_map_jTupleOf_eq q' hcomp' e htr h₀
  exact ⟨_, _, closedIFMap_interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hk hl⟩

end

end AclGeom
