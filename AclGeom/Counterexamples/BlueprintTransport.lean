/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.GenericNegation
import AclGeom.Interpretation.FrobTransport

/-!
# Transport of the literal generic-arithmetic predicates

The proof of blueprint Prop `interpreted-reconstruction` asserts that the definitions of
generic arithmetic and of `RatioEq` use only the closure relation, equality, finite rank and point
quantifiers, so that a geometry isomorphism and its inverse preserve them, and that direct image is
a bijection of quotient carriers extended over the named zero. For the literal predicates of
`Counterexamples.GenericArithmetic` and `Counterexamples.GenericNegation` these invariance
assertions are proved here, for an arbitrary base tuple and arbitrary point tuples:

* `sumPoint_map_iff`: the derived sum relation `SumPoint`;
* `blueprintJAdd_map_iff`, `blueprintJMul_map_iff`: the literal addition and multiplication graphs;
* `blueprintRatioEq_map_iff`: the literal ratio relation, with all four witness tuples;
* `blueprintJNeg_map_iff`, `blueprintJAddTotalNZ_map_iff`: the literal negation and total
  nonzero addition, with all their witness tuples;
* `blueprintRatioCarrierMap`: for an arbitrary base tuple `b`, the literal class-pair carrier of
  `b` with an adjoined zero corresponds to that of its image `Point.map e ∘ b`.

Witness tuples on the target side are pulled back by the bijection
`Equiv.piCongrRight fun _ ↦ Point.map e`, as in `AclGeom.Interpretation.TotalTransport`.

This is invariance only. The literal predicates remain nonfunctional
(`Counterexamples.GenericArithmetic`, `Counterexamples.GenericNegation`), and for some base tuple
no function on class pairs both respects the literal ratio relation and sends each semantic pair to
its ratio (`blueprintRatioEq_no_decoder`). The literal ratio relation is not transitive
(`blueprintRatioEq_not_transitive`), so the carriers are quotients by `Quot`,
that is, by its equivalence closure,
and no field structure or decoding is asserted on them. The literal operation recipes
are transcribed on raw class-pair representatives in `Counterexamples.BlueprintTotalGraphs`,
where their geometric invariance is proved; no quotient operation descent is asserted.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** literal predicate invariance and the literal carrier correspondence are proved
(#8, #23). Literal ratio symmetry and fixed-class reflexivity over perfect ambient fields at
rank five are proved; transitivity is refuted over arbitrary fields at rank five. The
representative-level recipe invariance is proved in `Counterexamples.BlueprintTotalGraphs`;
the source totality and decoded-operation claims retain separate obligations.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- **The derived sum relation is invariant** under order isomorphisms of closed lattices. This is
invariance only: it does not make `SumPoint` functional. -/
theorem sumPoint_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {U V W : Point k K} :
    SumPoint (Point.map e U) (Point.map e V) (Point.map e W) ↔ SumPoint U V W := by
  constructor
  · rintro ⟨R, hR⟩
    obtain ⟨R₀, rfl⟩ := (Point.map e).surjective R
    exact ⟨R₀, (qGeom_map_iff e).1 hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨Point.map e R, (qGeom_map_iff e).2 hR⟩

/-- **The literal addition graph is invariant** under order isomorphisms of closed lattices. -/
theorem blueprintJAdd_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v w : Fin 5 → Point k K} :
    BlueprintJAdd (Point.map e ∘ u) (Point.map e ∘ v) (Point.map e ∘ w) ↔ BlueprintJAdd u v w :=
  and_congr (Point.map e).injective.eq_iff <| and_congr (Point.map e).injective.eq_iff <|
    and_congr (pointTripleIndependent_map_iff e) <| and_congr (sumPoint_map_iff e) <|
      and_congr (sumPoint_map_iff e) <| and_congr (sumPoint_map_iff e) (sumPoint_map_iff e)

/-- **The literal multiplication graph is invariant** under order isomorphisms of closed
lattices. -/
theorem blueprintJMul_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v w : Fin 5 → Point k K} :
    BlueprintJMul (Point.map e ∘ u) (Point.map e ∘ v) (Point.map e ∘ w) ↔ BlueprintJMul u v w :=
  and_congr (Point.map e).injective.eq_iff <| and_congr (Point.map e).injective.eq_iff <|
    and_congr (pointTripleIndependent_map_iff e) <| and_congr (mulPoint_map_iff e) <|
      and_congr (sumPoint_map_iff e) <| and_congr (mulPoint_map_iff e) (mulPoint_map_iff e)

/-- **The literal ratio relation is invariant** under order isomorphisms of closed lattices: the
four witness tuples, their class memberships and the four literal products transfer. -/
theorem blueprintRatioEq_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {b r₁ r₂ s₁ s₂ : Fin 5 → Point k K} :
    BlueprintRatioEq (Point.map e ∘ b) (Point.map e ∘ r₁, Point.map e ∘ r₂)
        (Point.map e ∘ s₁, Point.map e ∘ s₂) ↔
      BlueprintRatioEq b (r₁, r₂) (s₁, s₂) := by
  -- Every target-side tuple is the image of a source-side tuple.
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, m₁, m₂, m₃, m₄⟩
    obtain ⟨c₁₀, rfl⟩ := hT c₁
    obtain ⟨c₂₀, rfl⟩ := hT c₂
    obtain ⟨d₁₀, rfl⟩ := hT d₁
    obtain ⟨d₂₀, rfl⟩ := hT d₂
    exact ⟨c₁₀, c₂₀, d₁₀, d₂₀, (frobEq_map_iff e).1 hc₁, (frobEq_map_iff e).1 hc₂,
      (frobEq_map_iff e).1 hd₁, (frobEq_map_iff e).1 hd₂, (blueprintJMul_map_iff e).1 m₁,
      (blueprintJMul_map_iff e).1 m₂, (blueprintJMul_map_iff e).1 m₃,
      (blueprintJMul_map_iff e).1 m₄⟩
  · rintro ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, m₁, m₂, m₃, m₄⟩
    exact ⟨Point.map e ∘ c₁, Point.map e ∘ c₂, Point.map e ∘ d₁, Point.map e ∘ d₂,
      (frobEq_map_iff e).2 hc₁, (frobEq_map_iff e).2 hc₂, (frobEq_map_iff e).2 hd₁,
      (frobEq_map_iff e).2 hd₂, (blueprintJMul_map_iff e).2 m₁, (blueprintJMul_map_iff e).2 m₂,
      (blueprintJMul_map_iff e).2 m₃, (blueprintJMul_map_iff e).2 m₄⟩

/-- **The literal negation is invariant** under order isomorphisms of closed lattices. -/
theorem blueprintJNeg_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {b u v : Fin 5 → Point k K} :
    BlueprintJNeg (Point.map e ∘ b) (Point.map e ∘ u) (Point.map e ∘ v) ↔ BlueprintJNeg b u v := by
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨z, r, hz, hr, m₁, m₂⟩
    obtain ⟨z₀, rfl⟩ := hT z
    obtain ⟨r₀, rfl⟩ := hT r
    exact ⟨z₀, r₀, (frobEq_map_iff e).1 hz, (frobEq_map_iff e).1 hr,
      (blueprintJAdd_map_iff e).1 m₁, (blueprintJAdd_map_iff e).1 m₂⟩
  · rintro ⟨z, r, hz, hr, m₁, m₂⟩
    exact ⟨Point.map e ∘ z, Point.map e ∘ r, (frobEq_map_iff e).2 hz, (frobEq_map_iff e).2 hr,
      (blueprintJAdd_map_iff e).2 m₁, (blueprintJAdd_map_iff e).2 m₂⟩

/-- **The literal total nonzero addition is invariant** under order isomorphisms of closed
lattices. -/
theorem blueprintJAddTotalNZ_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {b u v w : Fin 5 → Point k K} :
    BlueprintJAddTotalNZ (Point.map e ∘ b) (Point.map e ∘ u) (Point.map e ∘ v)
        (Point.map e ∘ w) ↔ BlueprintJAddTotalNZ b u v w := by
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨z, nz, r, s, hz, hnz, hr, hs, hneg, m₁, m₂, m₃⟩
    obtain ⟨z₀, rfl⟩ := hT z
    obtain ⟨nz₀, rfl⟩ := hT nz
    obtain ⟨r₀, rfl⟩ := hT r
    obtain ⟨s₀, rfl⟩ := hT s
    exact ⟨z₀, nz₀, r₀, s₀, (frobEq_map_iff e).1 hz, (frobEq_map_iff e).1 hnz,
      (frobEq_map_iff e).1 hr, (frobEq_map_iff e).1 hs, (blueprintJNeg_map_iff e).1 hneg,
      (blueprintJAdd_map_iff e).1 m₁, (blueprintJAdd_map_iff e).1 m₂,
      (blueprintJAdd_map_iff e).1 m₃⟩
  · rintro ⟨z, nz, r, s, hz, hnz, hr, hs, hneg, m₁, m₂, m₃⟩
    exact ⟨Point.map e ∘ z, Point.map e ∘ nz, Point.map e ∘ r, Point.map e ∘ s,
      (frobEq_map_iff e).2 hz, (frobEq_map_iff e).2 hnz, (frobEq_map_iff e).2 hr,
      (frobEq_map_iff e).2 hs, (blueprintJNeg_map_iff e).2 hneg, (blueprintJAdd_map_iff e).2 m₁,
      (blueprintJAdd_map_iff e).2 m₂, (blueprintJAdd_map_iff e).2 m₃⟩

/-- **The literal class-pair carriers correspond** (blueprint Prop `interpreted-reconstruction`,
proof: direct image is a bijection of quotient carriers). For an arbitrary base tuple `b`, an order
isomorphism of closed lattices maps the class of `b` onto the class of its image
`Point.map e ∘ b` pointwise, maps pairs of class members componentwise, respects the literal ratio
relation in both directions and extends over the adjoined zero. The carriers are quotients by the
equivalence closure of the literal relation; no field structure or decoding is asserted. -/
def blueprintRatioCarrierMap (e : ClosedIF k K ≃o ClosedIF l L) (b : Fin 5 → Point k K) :
    Option (Quot fun r s : {u : Fin 5 → Point k K // FrobEq b u} ×
        {u : Fin 5 → Point k K // FrobEq b u} ↦
      BlueprintRatioEq b (r.1.1, r.2.1) (s.1.1, s.2.1)) ≃
      Option (Quot fun r s : {u : Fin 5 → Point l L // FrobEq (Point.map e ∘ b) u} ×
          {u : Fin 5 → Point l L // FrobEq (Point.map e ∘ b) u} ↦
        BlueprintRatioEq (Point.map e ∘ b) (r.1.1, r.2.1) (s.1.1, s.2.1)) :=
  -- Class members are mapped pointwise; class membership transfers by `frobEq_map_iff`.
  let c : {u : Fin 5 → Point k K // FrobEq b u} ≃
      {u : Fin 5 → Point l L // FrobEq (Point.map e ∘ b) u} :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).subtypeEquiv fun _ ↦ (frobEq_map_iff e).symm
  Equiv.optionCongr <| Quot.congr (c.prodCongr c) fun r s ↦ by
    change BlueprintRatioEq b (r.1.1, r.2.1) (s.1.1, s.2.1) ↔
      BlueprintRatioEq (Point.map e ∘ b) (Point.map e ∘ r.1.1, Point.map e ∘ r.2.1)
        (Point.map e ∘ s.1.1, Point.map e ∘ s.2.1)
    exact (blueprintRatioEq_map_iff e).symm

end

end AclGeom
