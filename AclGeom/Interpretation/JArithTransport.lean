/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.JArithSem

/-!
# Transport of the coupled meet/join arithmetic along lattice isomorphisms

The EH95 operations `jSub` and `jDiv` (Figs. 4 and 5) on closed-lattice five-tuples are built from
joins and meets only.  So they commute with every order isomorphism
`e : ClosedIF k K ≃o ClosedIF l L` of closed-subfield lattices (`jSub_map`, `jDiv_map`), for
arbitrary tuples.  The derived negation, inversion, sum and product commute as well.  The coupled
sum and product relations on point tuples are therefore invariant under the induced map
`Point.map e` (`jAddRel_map_iff`, `jMulRel_map_iff`).  This is the third step of the naturality of
the interpretation (checklist I6), after `AclGeom.Interpretation.FrobTransport`.

The coordinates of an image tuple are the images of the coordinates, definitionally.  The
arguments are purely order-theoretic: no semantics, genericity, completeness, perfection, rank
hypothesis or fresh element is used, and the bases and ambient fields are arbitrary.

**Status:** coupled-arithmetic transport is complete (#23/#8, I6b2b).
Conditional class/carrier and graph transport, the same geometric map bundled as a RingEquiv,
and its composition with both decodings are proved in `Naturality`, given the canonical
image-base
equality and actual carrier inputs. Image-base existence, unconditional completeness,
base/scalar
recovery and general interpreted reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The meet/join difference commutes with order isomorphisms** of closed lattices (EH95,
Fig. 4): for arbitrary closed-lattice five-tuples, `jSub` of the images is the image of `jSub`. -/
theorem jSub_map (e : ClosedIF k K ≃o ClosedIF l L) (u v : Fin 5 → ClosedIF k K) :
    jSub (e ∘ u) (e ∘ v) = e ∘ jSub u v := by
  funext i
  fin_cases i <;> simp [jSub, map_sup, map_inf]

/-- **The meet/join quotient commutes with order isomorphisms** of closed lattices (EH95,
Fig. 5): for arbitrary closed-lattice five-tuples, `jDiv` of the images is the image of `jDiv`. -/
theorem jDiv_map (e : ClosedIF k K ≃o ClosedIF l L) (u v : Fin 5 → ClosedIF k K) :
    jDiv (e ∘ u) (e ∘ v) = e ∘ jDiv u v := by
  funext i
  fin_cases i <;> simp [jDiv, map_sup, map_inf]

/-- **The coupled meet/join sum is invariant** under order isomorphisms of closed lattices: `w` is
the sum of `u` and `v` exactly when the image tuples are related. -/
theorem jAddRel_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v w : Fin 5 → Point k K} :
    JAddRel (Point.map e ∘ u) (Point.map e ∘ v) (Point.map e ∘ w) ↔ JAddRel u v w := by
  -- The coordinates of an image tuple are the images of the coordinates.
  have hc : ∀ x : Fin 5 → Point k K, jCoords (Point.map e ∘ x) = e ∘ jCoords x := fun _ ↦ rfl
  -- The derived sum `x + y = x - ((x - y) - x)` commutes with `e`.
  have hadd : ∀ a b : Fin 5 → ClosedIF k K, jAdd (e ∘ a) (e ∘ b) = e ∘ jAdd a b := fun _ _ ↦ by
    simp only [jAdd, jNeg, jSub_map]
  simp only [JAddRel, hc, hadd]
  exact (Function.Injective.comp_left e.injective).eq_iff

/-- **The coupled meet/join product is invariant** under order isomorphisms of closed lattices:
`w` is the product of `u` and `v` exactly when the image tuples are related. -/
theorem jMulRel_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v w : Fin 5 → Point k K} :
    JMulRel (Point.map e ∘ u) (Point.map e ∘ v) (Point.map e ∘ w) ↔ JMulRel u v w := by
  -- The coordinates of an image tuple are the images of the coordinates.
  have hc : ∀ x : Fin 5 → Point k K, jCoords (Point.map e ∘ x) = e ∘ jCoords x := fun _ ↦ rfl
  -- The derived product `x y = x / ((x / y) / x)` commutes with `e`.
  have hmul : ∀ a b : Fin 5 → ClosedIF k K, jMul (e ∘ a) (e ∘ b) = e ∘ jMul a b := fun _ _ ↦ by
    simp only [jMul, jInv, jDiv_map]
  simp only [JMulRel, hc, hmul]
  exact (Function.Injective.comp_left e.injective).eq_iff

end

end AclGeom
