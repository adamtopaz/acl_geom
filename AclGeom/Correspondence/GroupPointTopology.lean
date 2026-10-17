/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupSchemePoints
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The Zariski topology of the points of an algebraic group

The topology on the actual k-points is transported from the closed-point subspace. It is
an explicit definition, used locally, rather than a global instance recovering a group
scheme from a hom-set. A connected algebraic group has irreducible point space, and left
translations are homeomorphisms by the existing scheme translations.

Named consumer: the fixed-boundary argument for an actual regular action in
`SchemePlaceFixed`, toward blueprint `lem:affine-action`. Only individual translations
are used; joint continuity for the product of point-space topologies is not asserted.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom.GroupPointTopology

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The explicit Zariski topology on the actual k-points, induced from closed points.
Named consumer: the finite-boundary action argument in `SchemePlaceFixed`. -/
@[instance_reducible]
def topology (G : AlgebraicGroup k) :
    TopologicalSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :=
  TopologicalSpace.induced
    (GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)) inferInstance

/-- The point/closed-point equivalence with its transported topology.
Named consumer: closedness of order conditions for an actual scheme action. -/
def pointsHomeo (G : AlgebraicGroup k) :
    letI := topology G
    (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) ≃ₜ closedPoints G.carrier := by
  letI := topology G
  exact GroupScheme.pointsEquivClosedPoints.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual k-points of a connected algebraic group form an irreducible space.
Named consumer: the finite locally closed orbit-fiber argument in `SchemePlaceFixed`. -/
theorem irreducibleSpace (G : ConnectedAlgebraicGroup k) :
    letI := topology G.toAlgebraicGroup
    IrreducibleSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) := by
  let : TopologicalSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :=
    topology G.toAlgebraicGroup
  have : JacobsonSpace G.toAlgebraicGroup.carrier :=
    LocallyOfFiniteType.jacobsonSpace G.toGroupScheme.X.hom
  have hc : IsIrreducible (closedPoints G.toAlgebraicGroup.carrier) := by
    rw [← isIrreducible_iff_closure, closure_closedPoints]
    exact IrreducibleSpace.isIrreducible_univ _
  have := Subtype.irreducibleSpace hc
  exact (pointsHomeo G.toAlgebraicGroup).irreducibleSpace_iff.mpr inferInstance

/-- Left translation as a homeomorphism of actual k-points with their explicit topology.
Named consumer: translating an open orbit fiber to the point stabilizer. -/
def leftMulHomeo (G : AlgebraicGroup k)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    letI := topology G
    (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) ≃ₜ
      (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) := by
  letI := topology G
  let h := GroupScheme.leftMulHomeo g
  let hc : closedPoints G.carrier ≃ₜ closedPoints G.carrier := h.subtype fun x ↦ by
    simpa only [mem_closedPoints_iff, Set.image_singleton] using
      (h.isClosed_image (s := {x})).symm
  exact (pointsHomeo G).trans (hc.trans (pointsHomeo G).symm)

/-- The transported translation is literal multiplication on k-points.
Named consumer: the coset/stabilizer calculation in `SchemePlaceFixed`. -/
theorem leftMulHomeo_apply (G : AlgebraicGroup k)
    (g p : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    letI := topology G
    leftMulHomeo G g p = g * p := by
  let : TopologicalSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) := topology G
  apply (pointsHomeo G).injective
  change (pointsHomeo G) ((pointsHomeo G).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact GroupScheme.leftMul_left_pointsEquivClosedPoints p g

end

end AclGeom.GroupPointTopology
