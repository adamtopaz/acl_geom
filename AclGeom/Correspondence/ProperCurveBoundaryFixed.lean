/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveBoundaryFixed
import AclGeom.Correspondence.SchemeCurvePointPlaceModel

/-!
# Joint boundary fixedness and actual proper-model places

**Status:** proved for a GIVEN actual proper normal integral dimension-one curve over an ACF
base, with an actual connected algebraic-group regular action and actual equivariant nonempty
open immersion. The literal finite boundary is fixed jointly over every test scheme in the
base universe. The SAME existing places whose actual proper centers are missing are fixed by
the existing base-field-point place action. No boundary, fixedness or transport certificate is
supplied.

The regular action on the ambient curve is an actual input. Projective presentation, joint
regularity of extended rational families, rational-action regularization and the full original
classifier remain owed. Original group/chunk/six-point statements, algebraization/descent and
every true bypassed auxiliary remain obligations. All eight original #21 work items and the
full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurveBoundary
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- For a GIVEN actual proper normal curve, the literal finite boundary is fixed jointly
on every test scheme, and the SAME actual places whose centers are missing are fixed by
the existing place action. Actual boundary points and their field-points are constructed
internally. No affine hypothesis, boundary, fixedness or transport certificate is supplied.
This proves the source finite-boundary assertion for the GIVEN regular action; construction
of a completion and joint regularity of extended rational families remain separate. -/
theorem fixed_boundary_places
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsProper V.hom]
    [ModObj G.toGroupScheme.X V] (hdim : topologicalKrullDim V.left = 1)
    (hnormal : ∀ x : V.left, IsIntegrallyClosed (V.left.presheaf.stalk x))
    (U : Over (Spec (.of k))) [Nonempty U.left] [ModObj G.toGroupScheme.X U]
    (j : U ⟶ V) [IsOpenImmersion j.left] [IsModHom G.toGroupScheme.X j] :
    ((Set.range j.left)ᶜ).Finite ∧
      (∀ x ∈ (Set.range j.left)ᶜ, IsClosed ({x} : Set V.left)) ∧
      (∀ x ∈ (Set.range j.left)ᶜ,
        ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ V,
          p.left (IsLocalRing.closedPoint k) = x ∧
          orbitMap G.toAlgebraicGroup V p = toUnit G.toGroupScheme.X ≫ p ∧
          ∀ (T : Over (Spec (.of k))) (q : T ⟶ G.toGroupScheme.X),
            q • (toUnit T ≫ p) = toUnit T ≫ p) ∧
      ∀ P : Place k V.left.functionField,
        CurvePointsPlaces.placeCenter V P ∉ Set.range j.left →
        ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
          SchemePlaceAction.placeAction G.toAlgebraicGroup V g P = P := by
  obtain ⟨hf, hc, hfix⟩ := fixed_boundary G V hdim U j
  refine ⟨hf, hc, hfix, ?_⟩
  intro P hP g
  let e := CurvePointsPlaces.closedPointEquivPlace V hdim hnormal
  let x := e.symm P
  have hx : x.val ∉ Set.range j.left := by
    rw [CurvePointsPlaces.closedPointEquivPlace_symm_val]
    exact hP
  obtain ⟨p, hp, _, hT⟩ := hfix x.val hx
  have hpoint : p ≫ ModObj.pointAct V g = p := by
    change p ≫ ((toUnit V ≫ g) • 𝟙 V) = p
    rw [ModObj.comp_smul, Category.comp_id, comp_toUnit_assoc,
      toUnit_unit, Category.id_comp]
    simpa only [toUnit_unit, Category.id_comp] using hT (𝟙_ (Over (Spec (.of k)))) g
  have heval := congrArg (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ V ↦
    z.left (IsLocalRing.closedPoint k)) hpoint
  change (ModObj.pointAct V g).left (p.left (IsLocalRing.closedPoint k)) =
    p.left (IsLocalRing.closedPoint k) at heval
  rw [hp] at heval
  have hmap : CurvePointsPlaces.mapClosedPoint (ModObj.pointAut V g) x = x :=
    Subtype.ext heval
  have hact := CurvePointsPlaces.closedPointEquivPlace_action V hdim hnormal
    G.toAlgebraicGroup g x
  have hPx : e x = P := e.apply_symm_apply P
  calc
    SchemePlaceAction.placeAction G.toAlgebraicGroup V g P =
        SchemePlaceAction.placeAction G.toAlgebraicGroup V g (e x) :=
      congrArg (SchemePlaceAction.placeAction G.toAlgebraicGroup V g) hPx.symm
    _ = e (CurvePointsPlaces.mapClosedPoint (ModObj.pointAut V g) x) := hact.symm
    _ = e x := congrArg e hmap
    _ = P := hPx

end
end AclGeom.CurveBoundary
