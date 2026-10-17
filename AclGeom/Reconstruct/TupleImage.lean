/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Reconstruct.Scalar

/-!
# Images of semantic `j`-tuples under the reconstruction

Blueprint Prop `scalar-one` has two conclusions for every `x ∉ acl(a)`: the tuple formula
`F(j(x, a)) = j(F̃(x), b)` and the point formula `F([x]) = [F̃(x)]`.  The point formula is
`interpretedRingEquiv_point`.  This module states the tuple formula for the actual corrected
reconstruction `H = interpretedRingEquiv … e …` (`interpretedRingEquiv_jTupleOf`): if `e`
carries the base tuple `j(x₀, a)` to `j(x₀', a')`, then `(H(x), a')` is independent and
`e(j(x, a)) = j(H(x), a')`.

The image of `j(x, a)` lies in the Frobenius class of `j(x₀', a')`, so it is `j(y, a')` for some
`y` (`frobEq_jTupleOf_iff`).  The coordinate law `y · H(x₀) = H(x) · x₀'` and scalar one
`H(x₀) = x₀'` then give `y = H(x)`.  No relative algebraic closedness is needed.  Perfection,
rank five and ACF J-completeness of both sides and the image-base equality are explicit, as in
`Reconstruct.Scalar`; in the source setting `jCompletenessACF` supplies both completeness
inputs.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the tuple formula of Prop `scalar-one` is proved for the actual reconstruction under
the explicit carrier inputs of `Reconstruct.Scalar` (#9, R2).  The original proof's literal
RatioEq/JMul argument and its choice over `acl(a, x₀, t₀)` retain their provenance.
-/

namespace AclGeom

open ClosedIF

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **Semantic `j`-tuples are carried to the tuples of their reconstructed coordinates** (the
tuple formula of blueprint Prop `scalar-one`): for `x ∉ acl_k(a)`, the pair `(H(x), a')` is
independent and `e(j(x, a)) = j(H(x), a')`. -/
theorem interpretedRingEquiv_jTupleOf [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    {x : K} (hx : x ∉ racl k ({a} : Set K)) :
    ∃ hHx : AlgebraicIndependent l
        ![interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x, a'],
      Point.map e ∘ jTupleOf x a (pair_of_notMem h₀ hx) =
        jTupleOf (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x) a' hHx := by
  have hx₀'0 : x₀' ≠ 0 := AlgebraicIndependent.ne_zero h₀' 0
  -- The image of `j(x, a)` is `j(y, a')` for some `y`.
  have h := (frobEq_map_iff e).2 (frobEq_jTupleOf_of_common htr h₀ (pair_of_notMem h₀ hx))
  rw [hφ] at h
  obtain ⟨y, hy, hxy⟩ := (frobEq_jTupleOf_iff q' htr' hcomp' h₀').1 h
  -- With scalar one, `y = H(x)`.
  have hc := interpretedRingEquiv_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
    (pair_of_notMem h₀ hx) hy hxy
  rw [interpretedRingEquiv_base_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ] at hc
  obtain rfl : y = interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x :=
    mul_right_cancel₀ hx₀'0 hc
  exact ⟨hy, hxy⟩

end AclGeom
