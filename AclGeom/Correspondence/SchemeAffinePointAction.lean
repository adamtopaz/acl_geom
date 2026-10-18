/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.FixedPlaceAffine
import AclGeom.Correspondence.SchemeCurveGenus
import AclGeom.Correspondence.SchemePlaceFixed

/-!
# Faithful affine coordinates for actual curve-action points

Named source consumer: the affine action formula in blueprint `lem:affine-action` (#21).

**Status:** proved for the k-points of a connected algebraic group of dimension at least
 two acting regularly on an integral affine locally finite-type dimension-one curve over
 an algebraically closed base, with the genuine global-point kernel criterion. The actual
 generic-stalk field has an internally chosen transcendental generator on which the
 original point action is affine, through an injective group homomorphism. The fixed
 boundary place, one-variable field, genus and faithful field action are internal.
 `SchemeAffineParameters` now uses the same coordinate to construct rational coefficients
 on an actual group chart and a finite extension of their two-parameter field. Global regular
 coefficient maps, a scheme-group morphism and scheme finite-cover coordinate maps remain open,
 as do rational-action regularization, completion/points identification,
 the normal subgroup and full classifier remain open. All eight original #21 items and
 the full durable goal stay open.
-/

namespace AclGeom.SchemeAffinePointAction

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A regular point-faithful action of a connected algebraic group of dimension at least two
 on an integral affine curve has faithful affine coordinates on its actual function field.
 The fixed place, genus, rational coordinate and faithful field action are internal. -/
theorem exists_faithful_affine_coordinates
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.toAlgebraicGroup.carrier)
    (hdimV : topologicalKrullDim V.left = 1) :
    letI := ActionFunctionField.functionFieldAlgebra V
    ∃ t : V.left.functionField, Transcendental k t ∧
      IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤ ∧
      ∃ Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →*
          AffineTransformation k, Function.Injective Φ ∧
        ∀ g, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V g).unop t =
          algebraMap k V.left.functionField ((Φ g).multiplier : k) * t +
            algebraMap k V.left.functionField (Φ g).shift := by
  let := ActionFunctionField.functionFieldAlgebra V
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdimV
  have hg : genus k V.left.functionField = 0 :=
    SchemeCurveGenus.genus_eq_zero G.toGroupScheme.X V hker hdimG hdimV
  obtain ⟨P, _, hP⟩ := SchemePlaceAction.exists_fixed_boundary_place G V hdimV
  exact FixedPlaceAffine.exists_faithful_affine_representation
    (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V)
    (ActionFunctionField.functionFieldAction_injective G.toAlgebraicGroup V hker)
    P (fun g ↦ (SchemePlaceAction.placeAction_apply G.toAlgebraicGroup V g P).symm.trans
      (hP g)) hg

end

end AclGeom.SchemeAffinePointAction
