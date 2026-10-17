/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Counterexamples.BlueprintTotalGraphs
import AclGeom.Interpretation.ClassCoordinates

/-!
# The raw zero-addition clause does not respect equality of generator ratios

The literal addition recipe's named-zero completion uses equality of representatives.
Consequently the reverse operation law on semantic representatives must restrict its
inputs: even for zero plus one, another representative of ratio one need not be an output.
This refutation records the reason for the nonzero-input domain of the corrected
representative-level reverse addition statement. No quotient decoder is assumed.

For independent `x, y, a`, the two diagonal pairs `(j(x,a),j(x,a))` and
`(j(y,a),j(y,a))` have ratio one and belong to the actual class of `j(x,a)`.
They are different raw pairs, by same-parameter tuple injectivity. The named-zero addition
clause requires the unchanged input pair as its output, so the second pair is not an
output of zero plus the first. Arbitrary fields and source rank five suffice.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the zero-input raw reverse-addition claim is refuted (#8).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The reverse raw addition law fails at a zero input.** There are two explicit semantic
pairs of ratio one in the actual class of `j(x,a)`, but the second is not an output of zero
plus the first. The literal named-zero completion uses equality of raw representatives;
this explains the nonzero-input domain of the corrected representative-level reverse law.
No perfection, infinite base or decoder is assumed. -/
theorem blueprintRatioAddGraph_zero_reverse_counterexample
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∃ (x y a : K) (hx : AlgebraicIndependent k ![x, a])
      (hy : AlgebraicIndependent k ![y, a])
      (s t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
        {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u}),
      (s.1.1, s.2.1) = (jTupleOf x a hx, jTupleOf x a hx) ∧
      (t.1.1, t.2.1) = (jTupleOf y a hy, jTupleOf y a hy) ∧
      y / y = 0 + x / x ∧
      ¬ BlueprintRatioAddGraph (jTupleOf x a hx) none (some s) (some t) := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  have hx := AlgebraicIndependent.pair_zero_two hind
  have hy := AlgebraicIndependent.pair_one_two hind
  have hxy : x ≠ y := hind.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hx0 : x ≠ 0 := fun h ↦ hind.transcendental 0 (by
    change IsAlgebraic k x
    rw [h]
    exact isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h ↦ hind.transcendental 1 (by
    change IsAlgebraic k y
    rw [h]
    exact isAlgebraic_zero)
  let s : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, frobEq_jTupleOf_of_common htr hx hx⟩, ⟨_, frobEq_jTupleOf_of_common htr hx hx⟩)
  let t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a hx) u} :=
    (⟨_, frobEq_jTupleOf_of_common htr hx hy⟩, ⟨_, frobEq_jTupleOf_of_common htr hx hy⟩)
  refine ⟨x, y, a, hx, hy, s, t, rfl, rfl, ?_, ?_⟩
  · rw [div_self hy0, div_self hx0, zero_add]
  · rintro (⟨_, hts⟩ | ⟨hzero, _⟩ | ⟨r₀, s₀, hzero, _⟩)
    · have hpair : t = s := Option.some.inj hts
      have htuple : jTupleOf y a hy = jTupleOf x a hx := congrArg (fun z ↦ z.1.1) hpair
      exact hxy (eq_of_jTupleOf_eq htr hy hx htuple).symm
    · cases hzero
    · cases hzero

end AclGeom
