/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Counterexamples.RatioAddGraphLaws

/-!
# Literal addition stays nonfunctional after identifying nonzero representatives

Blueprint Thm `total-field-graphs` asserts functionality on the interpreted ratio carrier.
The diagonal raw input `(j(x,a),j(x,a))`, added to itself, has both zero output and the
nonzero output `(j(2x,a),j(x,a))` when the base has `2 ≠ 0`. The first uses literal
self-negation; the second uses the true representative reverse sum law. All class and
replacement witnesses are retained.

Any map of the nonzero representative pairs, including the equivalence-closure quotient
map, preserves the distinction between the adjoined zero and a nonzero representative.
The projected graph therefore cannot be functional. This is independent of a decoder;
it does not assert that an unrelated field structure on a quotient carrier is impossible.

**Status:** literal addition functionality is refuted after any identification of nonzero
representatives with the named zero adjoined, when `2 ≠ 0` in the base (#8).
-/

namespace AclGeom

variable {k K A : Type*} [Field k] [Field K] [Algebra k K]

/-- **Identifying nonzero representatives cannot make literal addition functional**
(blueprint Thm `total-field-graphs`, functionality). For an actual semantic base class
over arbitrary fields at rank five with `2 ≠ 0` in the base, every map `f` of its raw
class pairs retains two distinct projected outputs of the same addition inputs: zero
and a nonzero class pair. In particular, taking the equivalence-closure quotient cannot
repair functionality. No perfection, infinite base, completeness or decoder is assumed. -/
theorem blueprintRatioAddGraph_not_functional_after_map
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {x a : K}
    (h₀ : AlgebraicIndependent k ![x, a]) (h2 : (2 : k) ≠ 0)
    (f : ({u : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) u}) → A) :
    ¬ ∀ r s t t' : Option ({u : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) u} ×
        {u : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) u}),
      BlueprintRatioAddGraph (jTupleOf x a h₀) r s t →
      BlueprintRatioAddGraph (jTupleOf x a h₀) r s t' → t.map f = t'.map f := by
  have hJ := frobEq_jTupleOf_of_common htr h₀ h₀
  let u : {w : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) w} :=
    ⟨jTupleOf x a h₀, hJ⟩
  let r := (u, u)
  have hR : BlueprintRatioEq (jTupleOf x a h₀) (u.1, u.1) (u.1, u.1) :=
    blueprintRatioEq_of_mul_eq htr h₀ h₀ h₀ h₀ h₀ rfl
  have hN := (blueprintJNeg_self htr h₀ h₀ h2).1
  have hzero : BlueprintRatioAddGraph (jTupleOf x a h₀) (some r) (some r) none :=
    Or.inr (Or.inr ⟨r, r, rfl, rfl, u, u, u, hR, hR, Or.inl ⟨hN, rfl⟩⟩)
  have hx2 : AlgebraicIndependent k ![algebraMap k K 2 * x, a] :=
    AlgebraicIndependent.smul_left h₀ h2
  let v : {w : Fin 5 → Point k K // FrobEq (jTupleOf x a h₀) w} :=
    ⟨jTupleOf (algebraMap k K 2 * x) a hx2, frobEq_jTupleOf_of_common htr h₀ hx2⟩
  let t := (v, u)
  have hnonzero : BlueprintRatioAddGraph (jTupleOf x a h₀) (some r) (some r) (some t) :=
    blueprintRatioAddGraph_of_add_ratio htr h₀ h₀ h₀ h₀ h₀ hx2 h₀ r r t rfl rfl rfl
      (by rw [map_ofNat]; ring)
  intro h
  have heq := h (some r) (some r) none (some t) hzero hnonzero
  cases heq

end AclGeom
