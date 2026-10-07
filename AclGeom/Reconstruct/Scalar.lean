/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Reconstruct.Base

/-!
# The naturality scalar is one

Let `e : ClosedIF k K ≃o ClosedIF l L` carry the base tuple `j(x₀, a)` to `j(x₀', a')`, and let
`H = interpretedRingEquiv … e …` be the corrected interpreted reconstruction `K ≃+* L`.  Write
`e(j(x, a)) = j(y, a')` for the image of a semantic `j`-tuple: by ACF J-completeness over `L` the
image tuple is again semantic with parameter `a'`.

* `interpretedRingEquiv_coord`: the coordinates are `H` up to one global scalar,
  `y · H(x₀) = H(x) · x₀'`.  The ratio class of `(j(x, a), j(x₀, a))` decodes to `x / x₀` and is
  carried to the class of `(j(y, a'), j(x₀', a'))`.
* `interpretedRingEquiv_base_coord`: the scalar is one, `H(x₀) = x₀'` (blueprint Prop
  `scalar-one`).  Take `x₁, x₂` generic over `a`.  The coupled product of `j(x₁, a)` and
  `j(x₂, a)` is `j(x₁ x₂, a)`; the lattice isomorphism preserves the coupled product and carries
  the genericity clause to the image tuples.  The semantic product in `L` then forces the scalar
  to equal its square.
* `interpretedRingEquiv_point`: hence `e([x]) = [H(x)]` for every `x` outside `acl_k(a)`.

Genericity of the image tuples is transported geometrically, so only two fresh elements over `a`
are used.  No relative algebraic closedness is needed.  Perfection, rank five and ACF
J-completeness of both sides and the image-base equality are explicit.

**Status:** corrected conditional scalar one and the outside-point formula are proved (#9,
R2a/b/c), with both perfections/rank-five bounds, separate exponential characteristics, both
still-open ACF J-completeness inputs and the actual canonical image-tuple equality explicit. No
RAC, extra target-genericity/freshness or scalar oracle is assumed. The full tuple-image
consequence follows from B1 and these laws. Public inducing/existence assembly is the named next
consumer and remains open, as do general unconditional R1/R2, chosen-perfection reconstruction,
unconditional completeness and the literal/TOT/frozen source obligations. The original scalar
proof chooses over acl(a,x₀,t₀); the corrected route transports genericity geometrically instead.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **Class coordinates are the reconstruction up to a global scalar**: if the lattice
isomorphism carries `j(x, a)` to `j(y, a')`, then `y · H(x₀) = H(x) · x₀'`. -/
theorem interpretedRingEquiv_coord [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    {x : K} (hx : AlgebraicIndependent k ![x, a]) {y : L} (hy : AlgebraicIndependent l ![y, a'])
    (hxy : Point.map e ∘ jTupleOf x a hx = jTupleOf y a' hy) :
    y * interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀ =
      interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x * x₀' := by
  have hx₀0 : x₀ ≠ 0 := AlgebraicIndependent.ne_zero h₀ 0
  have hx₀'0 : x₀' ≠ 0 := AlgebraicIndependent.ne_zero h₀' 0
  -- The class of `(j(x, a), j(x₀, a))` decodes to `x / x₀`.
  have hu : FrobEq (jTupleOf x₀ a h₀) (jTupleOf x a hx) := frobEq_jTupleOf_of_common htr h₀ hx
  have hv : FrobEq (jTupleOf x₀ a h₀) (jTupleOf x₀ a h₀) := frobEq_jTupleOf_of_common htr h₀ h₀
  have hD : ratioInterpDecode q htr hcomp h₀
      ((Quotient.mk (ratioSetoid q htr hcomp h₀)
        (⟨jTupleOf x a hx, hu⟩, ⟨jTupleOf x₀ a h₀, hv⟩) : Quotient _) :
        RatioInterp q htr hcomp h₀) = x / x₀ := by
    rw [ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]
  -- Its image is the class of `(j(y, a'), j(x₀', a'))`, which decodes to `y / x₀'`.
  have hCu : ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x a hx, hu⟩ =
      ⟨jTupleOf y a' hy, frobEq_jTupleOf_of_common htr' h₀' hy⟩ := Subtype.ext hxy
  have hCv : ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x₀ a h₀, hv⟩ =
      ⟨jTupleOf x₀' a' h₀', frobEq_jTupleOf_of_common htr' h₀' h₀'⟩ := Subtype.ext hφ
  have hval : interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ (x / x₀) = y / x₀' := by
    change ratioInterpDecode q' htr' hcomp' h₀'
      (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
        ((ratioInterpDecode q htr hcomp h₀).symm (x / x₀))) = y / x₀'
    rw [(Equiv.symm_apply_eq _).2 hD.symm]
    change ratioInterpDecode q' htr' hcomp' h₀'
      ((Quotient.mk (ratioSetoid q' htr' hcomp' h₀')
        (ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x a hx, hu⟩,
          ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x₀ a h₀, hv⟩) : Quotient _) :
        RatioInterp q' htr' hcomp' h₀') = y / x₀'
    rw [hCu, hCv, ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]
  have hH0 : interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀ ≠ 0 :=
    (map_ne_zero _).2 hx₀0
  rw [map_div₀, div_eq_div_iff hH0 hx₀'0] at hval
  exact hval.symm

/-- **The naturality scalar is one** (the corrected counterpart of blueprint Prop
`scalar-one`): the reconstruction sends the base coordinate `x₀` to the target base coordinate
`x₀'`.  A generic product `j(x₁, a) · j(x₂, a) = j(x₁ x₂, a)` is carried to a generic product in
`L`, whose coordinates are the scaled values `H(xᵢ) · s` with `s = x₀' / H(x₀)`; hence `s = s²`. -/
theorem interpretedRingEquiv_base_coord [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀') :
    interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀ = x₀' := by
  classical
  have hx₀'0 : x₀' ≠ 0 := AlgebraicIndependent.ne_zero h₀' 0
  -- Images of semantic `j`-tuples with parameter `a` are semantic with parameter `a'`.
  have himg : ∀ (z : K) (hz : AlgebraicIndependent k ![z, a]), ∃ (w : L)
      (hw : AlgebraicIndependent l ![w, a']), Point.map e ∘ jTupleOf z a hz = jTupleOf w a' hw := by
    intro z hz
    have h := (frobEq_map_iff e).2 (frobEq_jTupleOf_of_common htr h₀ hz)
    rw [hφ] at h
    exact (frobEq_jTupleOf_iff q' htr' hcomp' h₀').1 h
  -- A generic pair `x₁, x₂` over `a`: `x₁` fresh over `a`, then `x₂` fresh over `x₁, a`.
  obtain ⟨x₁, hx₁⟩ := fresh_three_of_five_le_trdeg htr {a} (by simp)
  obtain ⟨x₂, hx₂⟩ := fresh_three_of_five_le_trdeg htr {a, x₁}
    (Finset.card_le_two.trans (by norm_num))
  have hx₁' : x₁ ∉ racl k ({a} : Set K) := by simpa using hx₁
  have hx₂' : x₂ ∉ racl k ({x₁, a} : Set K) := by
    rw [Set.pair_comm]
    simpa using hx₂
  have T : AlgebraicIndependent k ![x₁, x₂, a] :=
    AlgebraicIndependent.insert_middle (pair_of_notMem h₀ hx₁') hx₂'
  -- Their images and the image of their product.
  obtain ⟨y₁, hy₁, h₁⟩ := himg x₁ (AlgebraicIndependent.pair_zero_two T)
  obtain ⟨y₂, hy₂, h₂⟩ := himg x₂ (AlgebraicIndependent.pair_one_two T)
  obtain ⟨y₁₂, hy₁₂, h₁₂⟩ := himg (x₁ * x₂) (JArith.pair_mul_a T)
  -- The images are generic: the genericity clause is carried by `e`.
  have T' : AlgebraicIndependent l ![y₁, y₂, a'] := by
    have h := (pointTripleIndependent_map_iff e).2 (pointTripleIndependent_jTupleOf T)
    have e0 : Point.map e (jTupleOf x₁ a (AlgebraicIndependent.pair_zero_two T) 0) =
        jTupleOf y₁ a' hy₁ 0 := congrFun h₁ 0
    have e1 : Point.map e (jTupleOf x₂ a (AlgebraicIndependent.pair_one_two T) 0) =
        jTupleOf y₂ a' hy₂ 0 := congrFun h₂ 0
    have e4 : Point.map e (jTupleOf x₁ a (AlgebraicIndependent.pair_zero_two T) 4) =
        jTupleOf y₁ a' hy₁ 4 := congrFun h₁ 4
    rw [e0, e1, e4] at h
    exact algebraicIndependent_of_rankEq_three_points (x := y₁) (y := y₂) (a := a') h
  -- The coupled product is carried to the coupled product, which is semantic in `L`.
  have hmul : JMulRel (jTupleOf y₁ a' hy₁) (jTupleOf y₂ a' hy₂) (jTupleOf y₁₂ a' hy₁₂) := by
    have h := (jMulRel_map_iff e).2 (jMulRel_jTupleOf T)
    rw [h₁, h₂, h₁₂] at h
    exact h
  have hy : y₁₂ = y₁ * y₂ :=
    eq_of_jTupleOf_eq htr' hy₁₂ (JArith.pair_mul_a T') ((jMulRel_jTupleOf_iff T').1 hmul)
  -- The scaled coordinates force the scalar to be one.
  have c₁ := interpretedRingEquiv_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ _ hy₁ h₁
  have c₂ := interpretedRingEquiv_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ _ hy₂ h₂
  have c₁₂ := interpretedRingEquiv_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ _ hy₁₂ h₁₂
  rw [map_mul] at c₁₂
  have hx₁0 : x₁ ≠ 0 := AlgebraicIndependent.ne_zero T 0
  have hx₂0 : x₂ ≠ 0 := AlgebraicIndependent.ne_zero T 1
  have hP : interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₁ *
      interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₂ * x₀' ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero _).2 hx₁0) ((map_ne_zero _).2 hx₂0)) hx₀'0
  apply mul_left_cancel₀ hP
  linear_combination (-interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀) * c₁₂ +
    interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀ ^ 2 * hy +
    (y₂ * interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₀) * c₁ +
    (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x₁ * x₀') * c₂

/-- **Points outside `acl_k(a)` are carried by the reconstruction** (the corrected counterpart of
the point formula of blueprint Prop `scalar-one`): `e([x]) = [H(x)]` for `x ∉ acl_k(a)`. -/
theorem interpretedRingEquiv_point [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    {x : K} (hx : x ∉ racl k ({a} : Set K)) :
    e (point k x) = point l (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x) := by
  have hx₀'0 : x₀' ≠ 0 := AlgebraicIndependent.ne_zero h₀' 0
  have hxa : AlgebraicIndependent k ![x, a] := pair_of_notMem h₀ hx
  -- The image of `j(x, a)` is `j(y, a')` for some `y`.
  have h := (frobEq_map_iff e).2 (frobEq_jTupleOf_of_common htr h₀ hxa)
  rw [hφ] at h
  obtain ⟨y, hy, hxy⟩ := (frobEq_jTupleOf_iff q' htr' hcomp' h₀').1 h
  -- With scalar one, `y = H(x)`.
  have hc := interpretedRingEquiv_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hxa hy hxy
  rw [interpretedRingEquiv_base_coord q htr hcomp q' htr' hcomp' e h₀ h₀' hφ] at hc
  have hyx : y = interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ x :=
    mul_right_cancel₀ hx₀'0 hc
  -- The first coordinate of `j(y, a')` is the point `[y]`.
  rw [← hyx]
  exact congrArg Subtype.val (congrFun hxy 0)

end

end AclGeom
