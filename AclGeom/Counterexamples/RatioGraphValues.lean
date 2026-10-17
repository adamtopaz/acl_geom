/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.BlueprintTotalGraphs
import AclGeom.Counterexamples.RatioReflexivity

/-!
# The literal operation graphs do not compute sums and products

Validation for issue #8, continuing `AclGeom.Counterexamples.BlueprintTotalGraphs`.  Blueprint
Thm `total-field-graphs` asserts that the geometric operation graphs satisfy
`AddGraph(r, s, t) ↔ decode(t) = decode(r) + decode(s)` and
`MulGraph(r, s, t) ↔ decode(t) = decode(r) decode(s)`.  For the literal recipes
`BlueprintRatioAddGraph` and `BlueprintRatioMulGraph` the forward directions fail already on
semantic representatives (`blueprintRatioAddGraph_wrong_sum`,
`blueprintRatioMulGraph_wrong_product`).

For independent `x, y, a` and `κ ∈ kˣ`, the literal graphs `BlueprintJAddTotalNZ` and
`BlueprintJMul` accept the outputs `j(κx + y, a)` and `j(κxy, a)` for the inputs
`j(x, a), j(y, a)` (`blueprintJAddTotalNZ_kappa`, `blueprintJMul_kappa`).  The reflexivity of the
literal ratio relation (`blueprintRatioEq_refl`) supplies every replacement and comparison.

* Addition: the inputs `(j(x, a), j(y, a))` and `(j(y, a), j(y, a))` have the common denominator
  `j(y, a)`, and the literal graph relates them to `(j(κx + y, a), j(y, a))`, whose ratio
  `(κx + y)/y` differs from the sum `x/y + y/y` of the input ratios.
* Multiplication: the reciprocal inputs `(j(x, a), j(y, a))` and `(j(y, a), j(x, a))` are related
  to `(j(κxy, a), j(xy, a))`, whose ratio `κ` differs from the product `1` of the input ratios.

No decoder is used: the ratios are those of the explicit generators of the semantic tuples.
The base field is infinite, so that `κ ∉ {0, 1}` exists, and the ambient field is perfect with
transcendence degree at least five, as for `blueprintRatioEq_refl`.  Totality of the literal
graphs is not addressed here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (refutation for issue #8).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The literal addition graph does not compute sums** (blueprint Thm `total-field-graphs`,
addition, forward direction).  There are semantic class pairs `r = (j(x, a), j(y, a))`,
`s = (j(y, a), j(y, a))` and `t = (j(κx + y, a), j(y, a))` in the Frobenius class of `j(x, a)`
with `BlueprintRatioAddGraph r s t`, although the ratio `(κx + y)/y` of `t` differs from the sum
of the ratios `x/y` and `y/y` of `r` and `s`. -/
theorem blueprintRatioAddGraph_wrong_sum [Infinite k] [PerfectField K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∃ (x y a : K) (κ : k) (hx : AlgebraicIndependent k ![x, a])
      (hy : AlgebraicIndependent k ![y, a])
      (hp : AlgebraicIndependent k ![algebraMap k K κ * x + y, a])
      (r s t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
        {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u}),
      (r.1.1, r.2.1) = (jTupleOf x a hx, jTupleOf y a hy) ∧
      (s.1.1, s.2.1) = (jTupleOf y a hy, jTupleOf y a hy) ∧
      (t.1.1, t.2.1) = (jTupleOf (algebraMap k K κ * x + y) a hp, jTupleOf y a hy) ∧
      BlueprintRatioAddGraph (jTupleOf x a hx) (some r) (some s) (some t) ∧
      (algebraMap k K κ * x + y) / y ≠ x / y + y / y := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have hκ0 : κ ≠ 0 := fun h ↦ hκ (by rw [h]; exact Finset.mem_insert_self _ _)
  have hκ1 : κ ≠ 1 := fun h ↦ hκ (by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hx0 : x ≠ 0 := fun h0 ↦ hind.transcendental 0 (by
    change IsAlgebraic k x
    rw [h0]
    exact isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h0 ↦ hind.transcendental 1 (by
    change IsAlgebraic k y
    rw [h0]
    exact isAlgebraic_zero)
  have hx : AlgebraicIndependent k ![x, a] := AlgebraicIndependent.pair_zero_two hind
  have hy : AlgebraicIndependent k ![y, a] := AlgebraicIndependent.pair_one_two hind
  -- The total nonzero sum `j(κx + y, a)` of the numerators over the common denominator `j(y, a)`.
  obtain ⟨p, hp, A, rfl⟩ : ∃ (p : K) (hp : AlgebraicIndependent k ![p, a]),
      BlueprintJAddTotalNZ (jTupleOf x a hx) (jTupleOf x a hx) (jTupleOf y a hy)
        (jTupleOf p a hp) ∧ p = algebraMap k K κ * x + y :=
    ⟨_, _, blueprintJAddTotalNZ_kappa htr hx hind hκ0, rfl⟩
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x a hx) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr hx hw
  let r : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ x hx⟩, ⟨_, hJ y hy⟩)
  let s : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ y hy⟩, ⟨_, hJ y hy⟩)
  let t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ _ hp⟩, ⟨_, hJ y hy⟩)
  refine ⟨x, y, a, κ, hx, hy, hp, r, s, t, rfl, rfl, rfl,
    Or.inr (Or.inr ⟨r, s, rfl, rfl, r.1, s.1, r.2, blueprintRatioEq_refl htr hx r,
      blueprintRatioEq_refl htr hx s,
      Or.inr ⟨t.1, t, rfl, A, blueprintRatioEq_refl htr hx t⟩⟩), ?_⟩
  -- The output ratio is `κ x/y + 1` and the sum of the input ratios is `x/y + 1`.
  intro h
  rw [add_div, div_self hy0] at h
  have h' : algebraMap k K κ * x = x := (div_left_inj' hy0).1 (add_right_cancel h)
  exact hκ1 ((algebraMap k K).injective ((mul_right_cancel₀ hx0
    (h'.trans (one_mul x).symm)).trans (map_one _).symm))

/-- **The literal multiplication graph does not compute products** (blueprint Thm
`total-field-graphs`, multiplication, forward direction).  There are semantic class pairs
`r = (j(x, a), j(y, a))`, `s = (j(y, a), j(x, a))` and `t = (j(κxy, a), j(xy, a))` in the
Frobenius class of `j(x, a)` with `BlueprintRatioMulGraph r s t`, although the ratio `κxy/(xy)`
of `t` differs from the product of the ratios `x/y` and `y/x` of `r` and `s`. -/
theorem blueprintRatioMulGraph_wrong_product [Infinite k] [PerfectField K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∃ (x y a : K) (κ : k) (hx : AlgebraicIndependent k ![x, a])
      (hy : AlgebraicIndependent k ![y, a])
      (hp : AlgebraicIndependent k ![algebraMap k K κ * x * y, a])
      (hq : AlgebraicIndependent k ![x * y, a])
      (r s t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
        {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u}),
      (r.1.1, r.2.1) = (jTupleOf x a hx, jTupleOf y a hy) ∧
      (s.1.1, s.2.1) = (jTupleOf y a hy, jTupleOf x a hx) ∧
      (t.1.1, t.2.1) = (jTupleOf (algebraMap k K κ * x * y) a hp, jTupleOf (x * y) a hq) ∧
      BlueprintRatioMulGraph (jTupleOf x a hx) (some r) (some s) (some t) ∧
      algebraMap k K κ * x * y / (x * y) ≠ x / y * (y / x) := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have hκ0 : κ ≠ 0 := fun h ↦ hκ (by rw [h]; exact Finset.mem_insert_self _ _)
  have hκ1 : κ ≠ 1 := fun h ↦ hκ (by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hx0 : x ≠ 0 := fun h0 ↦ hind.transcendental 0 (by
    change IsAlgebraic k x
    rw [h0]
    exact isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h0 ↦ hind.transcendental 1 (by
    change IsAlgebraic k y
    rw [h0]
    exact isAlgebraic_zero)
  have hx : AlgebraicIndependent k ![x, a] := AlgebraicIndependent.pair_zero_two hind
  have hy : AlgebraicIndependent k ![y, a] := AlgebraicIndependent.pair_one_two hind
  -- The swapped triple `y, x, a` for the denominator product.
  have hind' : AlgebraicIndependent k ![y, x, a] :=
    (by funext i; fin_cases i <;> rfl : ![x, y, a] ∘ ![1, 0, 2] = ![y, x, a]) ▸
      hind.comp ![1, 0, 2] (by decide)
  -- The numerator product `j(κxy, a)` and the denominator product `j(xy, a)`.
  obtain ⟨p, hp, M, rfl⟩ : ∃ (p : K) (hp : AlgebraicIndependent k ![p, a]),
      BlueprintJMul (jTupleOf x a hx) (jTupleOf y a hy) (jTupleOf p a hp) ∧
        p = algebraMap k K κ * x * y :=
    ⟨_, _, blueprintJMul_kappa hind htr hκ0, rfl⟩
  obtain ⟨q, hq', M', hq'eq⟩ : ∃ (q : K) (hq : AlgebraicIndependent k ![q, a]),
      BlueprintJMul (jTupleOf y a hy) (jTupleOf x a hx) (jTupleOf q a hq) ∧
        q = algebraMap k K 1 * y * x :=
    ⟨_, _, blueprintJMul_kappa hind' htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  rw [map_one, one_mul, mul_comm] at hq'eq
  subst hq'eq
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x a hx) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr hx hw
  let r : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ x hx⟩, ⟨_, hJ y hy⟩)
  let s : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ y hy⟩, ⟨_, hJ x hx⟩)
  let t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, hJ _ hp⟩, ⟨_, hJ _ hq'⟩)
  refine ⟨x, y, a, κ, hx, hy, hp, hq', r, s, t, rfl, rfl, rfl,
    Or.inr ⟨r, s, t, rfl, rfl, rfl, r.1, r.2, s.1, s.2, t.1, t.2,
      blueprintRatioEq_refl htr hx r, blueprintRatioEq_refl htr hx s, M, M',
      blueprintRatioEq_refl htr hx t⟩, ?_⟩
  -- The output ratio is `κ` and the product of the input ratios is `1`.
  have hxy : x * y ≠ 0 := mul_ne_zero hx0 hy0
  rw [mul_assoc, mul_div_assoc, div_self hxy, mul_one, div_mul_div_comm, mul_comm y x,
    div_self hxy]
  exact fun h ↦ hκ1 ((algebraMap k K).injective (h.trans (map_one _).symm))

end AclGeom
