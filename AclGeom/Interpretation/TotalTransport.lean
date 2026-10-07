/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobTransport
import AclGeom.Interpretation.JArithTransport
import AclGeom.Interpretation.TotalOps

/-!
# Transport of the corrected total relations along lattice isomorphisms

An order isomorphism `e : ClosedIF k K ≃o ClosedIF l L` of closed-subfield lattices acts on tuples
of points by composition with `Point.map e`.  It preserves the corrected geometric relations on
the fixed Frobenius class, for an arbitrary base tuple `j₀` and arbitrary point tuples:

* `jNegTotalRel_map_iff`: the corrected negation through two generic additions;
* `jAddTotalNZRel_map_iff`: the corrected total nonzero addition;
* `ratioEq_map_iff`: the corrected four-product ratio relation.

Every witness tuple, every coupled operation and every genericity clause is kept.  Witness tuples
on the target side are pulled back by the bijection `Equiv.piCongrRight fun _ ↦ Point.map e`.
The conjuncts then transfer by `frobEq_map_iff`, `jAddRel_map_iff`, `jMulRel_map_iff` and
`pointTripleIndependent_map_iff`.  This is the fourth step of the naturality of the interpretation
(checklist I6), after `AclGeom.Interpretation.JArithTransport`.

The arguments are purely order-theoretic.  No semantics, genericity, completeness, perfection, rank
hypothesis or fresh element is used, no Frobenius setoid is assumed, and the bases and ambient
fields are arbitrary.

**Status:** corrected totalization/ratio transport is complete (#23/#8, I6b2c).
The induced map of interpreted fields, preservation of the total geometric graphs and corrected
interpreted reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The corrected negation relation is invariant** under order isomorphisms of closed lattices:
both witness tuples, both generic coupled additions and their genericity clauses transfer. -/
theorem jNegTotalRel_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {j₀ u v : Fin 5 → Point k K} :
    JNegTotalRel (Point.map e ∘ j₀) (Point.map e ∘ u) (Point.map e ∘ v) ↔
      JNegTotalRel j₀ u v := by
  -- Every target-side tuple is the image of a source-side tuple.
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨z, r, hz, hr, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩⟩
    obtain ⟨z₀, rfl⟩ := hT z
    obtain ⟨r₀, rfl⟩ := hT r
    exact ⟨z₀, r₀, (frobEq_map_iff e).1 hz, (frobEq_map_iff e).1 hr,
      ⟨(jAddRel_map_iff e).1 m₁, (pointTripleIndependent_map_iff e).1 g₁⟩,
      ⟨(jAddRel_map_iff e).1 m₂, (pointTripleIndependent_map_iff e).1 g₂⟩⟩
  · rintro ⟨z, r, hz, hr, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩⟩
    exact ⟨Point.map e ∘ z, Point.map e ∘ r, (frobEq_map_iff e).2 hz, (frobEq_map_iff e).2 hr,
      ⟨(jAddRel_map_iff e).2 m₁, (pointTripleIndependent_map_iff e).2 g₁⟩,
      ⟨(jAddRel_map_iff e).2 m₂, (pointTripleIndependent_map_iff e).2 g₂⟩⟩

/-- **The corrected total nonzero addition is invariant** under order isomorphisms of closed
lattices: all four witness tuples, the corrected negation clause, the three generic coupled
additions and their genericity clauses transfer. -/
theorem jAddTotalNZRel_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {j₀ u v w : Fin 5 → Point k K} :
    JAddTotalNZRel (Point.map e ∘ j₀) (Point.map e ∘ u) (Point.map e ∘ v) (Point.map e ∘ w) ↔
      JAddTotalNZRel j₀ u v w := by
  -- Every target-side tuple is the image of a source-side tuple.
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨z, nz, r, s, hz, hnz, hr, hs, hneg, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩⟩
    obtain ⟨z₀, rfl⟩ := hT z
    obtain ⟨nz₀, rfl⟩ := hT nz
    obtain ⟨r₀, rfl⟩ := hT r
    obtain ⟨s₀, rfl⟩ := hT s
    exact ⟨z₀, nz₀, r₀, s₀, (frobEq_map_iff e).1 hz, (frobEq_map_iff e).1 hnz,
      (frobEq_map_iff e).1 hr, (frobEq_map_iff e).1 hs, (jNegTotalRel_map_iff e).1 hneg,
      ⟨(jAddRel_map_iff e).1 m₁, (pointTripleIndependent_map_iff e).1 g₁⟩,
      ⟨(jAddRel_map_iff e).1 m₂, (pointTripleIndependent_map_iff e).1 g₂⟩,
      ⟨(jAddRel_map_iff e).1 m₃, (pointTripleIndependent_map_iff e).1 g₃⟩⟩
  · rintro ⟨z, nz, r, s, hz, hnz, hr, hs, hneg, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩⟩
    exact ⟨Point.map e ∘ z, Point.map e ∘ nz, Point.map e ∘ r, Point.map e ∘ s,
      (frobEq_map_iff e).2 hz, (frobEq_map_iff e).2 hnz, (frobEq_map_iff e).2 hr,
      (frobEq_map_iff e).2 hs, (jNegTotalRel_map_iff e).2 hneg,
      ⟨(jAddRel_map_iff e).2 m₁, (pointTripleIndependent_map_iff e).2 g₁⟩,
      ⟨(jAddRel_map_iff e).2 m₂, (pointTripleIndependent_map_iff e).2 g₂⟩,
      ⟨(jAddRel_map_iff e).2 m₃, (pointTripleIndependent_map_iff e).2 g₃⟩⟩

/-- **The corrected ratio relation is invariant** under order isomorphisms of closed lattices: all
four witness tuples and the four generic coupled cross-products with their genericity clauses
transfer. -/
theorem ratioEq_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {j₀ r₁ r₂ s₁ s₂ : Fin 5 → Point k K} :
    RatioEq (Point.map e ∘ j₀) (Point.map e ∘ r₁, Point.map e ∘ r₂)
        (Point.map e ∘ s₁, Point.map e ∘ s₂) ↔
      RatioEq j₀ (r₁, r₂) (s₁, s₂) := by
  -- Every target-side tuple is the image of a source-side tuple.
  have hT : ∀ x : Fin 5 → Point l L, ∃ x₀, Point.map e ∘ x₀ = x :=
    (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective
  constructor
  · rintro ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩, ⟨m₄, g₄⟩⟩
    obtain ⟨c₁₀, rfl⟩ := hT c₁
    obtain ⟨c₂₀, rfl⟩ := hT c₂
    obtain ⟨d₁₀, rfl⟩ := hT d₁
    obtain ⟨d₂₀, rfl⟩ := hT d₂
    exact ⟨c₁₀, c₂₀, d₁₀, d₂₀, (frobEq_map_iff e).1 hc₁, (frobEq_map_iff e).1 hc₂,
      (frobEq_map_iff e).1 hd₁, (frobEq_map_iff e).1 hd₂,
      ⟨(jMulRel_map_iff e).1 m₁, (pointTripleIndependent_map_iff e).1 g₁⟩,
      ⟨(jMulRel_map_iff e).1 m₂, (pointTripleIndependent_map_iff e).1 g₂⟩,
      ⟨(jMulRel_map_iff e).1 m₃, (pointTripleIndependent_map_iff e).1 g₃⟩,
      ⟨(jMulRel_map_iff e).1 m₄, (pointTripleIndependent_map_iff e).1 g₄⟩⟩
  · rintro ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩, ⟨m₄, g₄⟩⟩
    exact ⟨Point.map e ∘ c₁, Point.map e ∘ c₂, Point.map e ∘ d₁, Point.map e ∘ d₂,
      (frobEq_map_iff e).2 hc₁, (frobEq_map_iff e).2 hc₂, (frobEq_map_iff e).2 hd₁,
      (frobEq_map_iff e).2 hd₂,
      ⟨(jMulRel_map_iff e).2 m₁, (pointTripleIndependent_map_iff e).2 g₁⟩,
      ⟨(jMulRel_map_iff e).2 m₂, (pointTripleIndependent_map_iff e).2 g₂⟩,
      ⟨(jMulRel_map_iff e).2 m₃, (pointTripleIndependent_map_iff e).2 g₃⟩,
      ⟨(jMulRel_map_iff e).2 m₄, (pointTripleIndependent_map_iff e).2 g₄⟩⟩

end

end AclGeom
