/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.ClassCoordinates
import AclGeom.Interpretation.FrobLinkSemantic
import AclGeom.Interpretation.JArithSem

/-!
# Corrected generic arithmetic on the fixed Frobenius class

Blueprint §genericops defines generic addition and multiplication on the fixed class
`J₁ = [j(x₀, a)]_FrobEq` by the predicates `JAdd` and `JMul`, which are refuted (#23: they are not
functional).  The coupled EH95 meet/join operations `JAddRel`, `JMulRel`, `JSubRel`, `JDivRel`
(`AclGeom.Interpretation.JArithSem`) replace them.  For two members `u, v` of the class whose
`X`-coordinates are generic over the parameter (`PointTripleIndependent (u 0) (v 0) (u 4)`, the
blueprint's independence clause), every output `w` lies in the class again, and its coordinate
`μ(w)` (`jClassEquiv`) is the sum, product, difference or quotient of `μ(u)` and `μ(v)`.

The proof reads `u = j(x, a)` and `v = j(y, a)` off the fixed-class description
(`frobEq_jTupleOf_iff`), so `K` is perfect of rank at least five and the completeness input
`hcomp` stays explicit.  The rank-three clause makes `x, y, a` independent
(`algebraicIndependent_of_rankEq_three_points`), and the generic semantics of the coupled
operations computes the output.

**Status:** corrected generic outputs remain in the fixed geometric class, and their decoded
coordinates satisfy the displayed field operations, under explicit perfection, rank-five and
ACF J-completeness inputs (#23). Non-generic totalization, ratio semantics, setoid laws and the
interpreted field remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF JArith

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Two members of the fixed class with generic `X`-coordinates are `j(x, a)` and `j(y, a)` for an
independent triple `x, y, a`. -/
private theorem exists_generic_pair [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hgen : PointTripleIndependent (u 0) (v 0) (u 4)) :
    ∃ (x y : K) (h : AlgebraicIndependent k ![x, y, a]),
      u = jTupleOf x a (AlgebraicIndependent.pair_zero_two h) ∧
        v = jTupleOf y a (AlgebraicIndependent.pair_one_two h) := by
  obtain ⟨x, hx, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hu
  obtain ⟨y, hy, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hv
  exact ⟨x, y, algebraicIndependent_of_rankEq_three_points (x := x) (y := y) (a := a) hgen,
    rfl, rfl⟩

/-- **Corrected generic addition on the fixed class** (blueprint §genericops, with the coupled
EH95 sum in place of the refuted `JAdd`): the sum of two generic class members lies in the class,
and its coordinate is the sum of their coordinates. -/
theorem JAddRel.jClassEquiv_add [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hgen : PointTripleIndependent (u 0) (v 0) (u 4)) (h : JAddRel u v w) :
    ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := exists_generic_pair q htr hcomp h₀ hu hv hgen
  obtain rfl := (jAddRel_jTupleOf_iff hxy).1 h
  refine ⟨frobEq_jTupleOf_of_common htr h₀ (pair_add_a hxy), ?_⟩
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]

/-- **Corrected generic multiplication on the fixed class** (blueprint §genericops, with the
coupled EH95 product in place of the refuted `JMul`): the product of two generic class members lies
in the class, and its coordinate is the product of their coordinates. -/
theorem JMulRel.jClassEquiv_mul [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hgen : PointTripleIndependent (u 0) (v 0) (u 4)) (h : JMulRel u v w) :
    ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) * (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := exists_generic_pair q htr hcomp h₀ hu hv hgen
  obtain rfl := (jMulRel_jTupleOf_iff hxy).1 h
  refine ⟨frobEq_jTupleOf_of_common htr h₀ (pair_mul_a hxy), ?_⟩
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]

/-- **Corrected generic subtraction on the fixed class** (EH95 Lemma 2.11, Fig. 4): the
meet/join difference of two generic class members lies in the class, and its coordinate is the
difference of their coordinates. -/
theorem JSubRel.jClassEquiv_sub [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hgen : PointTripleIndependent (u 0) (v 0) (u 4)) (h : JSubRel u v w) :
    ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) - (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := exists_generic_pair q htr hcomp h₀ hu hv hgen
  obtain rfl := (jSubRel_jTupleOf_iff hxy).1 h
  refine ⟨frobEq_jTupleOf_of_common htr h₀ (pair_sub_a hxy), ?_⟩
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]

/-- **Corrected generic division on the fixed class** (EH95 Lemma 2.11, Fig. 5): the meet/join
quotient of two generic class members lies in the class, and its coordinate is the quotient of
their coordinates. -/
theorem JDivRel.jClassEquiv_div [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hgen : PointTripleIndependent (u 0) (v 0) (u 4)) (h : JDivRel u v w) :
    ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := exists_generic_pair q htr hcomp h₀ hu hv hgen
  obtain rfl := (jDivRel_jTupleOf_iff hxy).1 h
  refine ⟨frobEq_jTupleOf_of_common htr h₀ (pair_div_a hxy), ?_⟩
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]

end

end AclGeom
