/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePointPlaceAutomorphisms
import AclGeom.Correspondence.SchemePlaceAction

/-!
# The actual proper-normal-curve point-place model

**Status:** proved over every field from actual properness, integrality, dimension one and
integrally closed stalks. ONE internally constructed equivalence couples literal stalk images,
actual stalk/place-ring isomorphisms, unique proper centers, every actual curve automorphism
and actual regular group actions at base-field points. The one-variable class and
Noetherianity are internal; no point-place, center or transport certificate is a premise.

The given proper normal curve is an actual input. Completion construction, joint regularity of
extended families, rational-action regularization and the full original classifier remain
owed, alongside group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary. All eight original #21 work items and the full durable goal remain active
and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The actual regular scheme action transports the corresponding places exactly as it
transports the actual closed points. Named consumer: the complete actual point/place model. -/
theorem closedPointEquivPlace_action
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (G : AlgebraicGroup k) [ModObj G.toGroupScheme.X X]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) :
    closedPointEquivPlace X hdim hnormal (mapClosedPoint (ModObj.pointAut X g) x) =
      SchemePlaceAction.placeAction G X g (closedPointEquivPlace X hdim hnormal x) := by
  exact (closedPointPlace_comap X hdim hnormal (ModObj.pointAut X g) x).symm.trans
    (SchemePlaceAction.placeAction_apply G X g (closedPointPlace X hdim hnormal x)).symm

/-- The actual proper-normal-curve point/place model, over every field. ONE internally
constructed equivalence retains literal stalk images, actual stalk/place-ring isomorphisms,
actual centers and compatibility with every curve automorphism and regular group action.
The one-variable property and Noetherianity are internal; no point/place, center, local-ring
comparison or transport certificate is supplied. This constructs no completion and proves
no joint regularity for a family of extended automorphisms. -/
theorem exists_point_place_model
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x)) :
    IsFunctionFieldOneVar k X.left.functionField ∧
    ∃ e : {x : X.left // IsClosed ({x} : Set X.left)} ≃ Place k X.left.functionField,
      (∀ (x : {x : X.left // IsClosed ({x} : Set X.left)}) (z : X.left.functionField),
        z ∈ (e x).val ↔ ∃ r : X.left.presheaf.stalk x.val,
          algebraMap (X.left.presheaf.stalk x.val) X.left.functionField r = z) ∧
      (∀ x : {x : X.left // IsClosed ({x} : Set X.left)},
        ∃ L : (X.left.presheaf.stalk x.val) ≃+* (e x).val,
          ∀ r : X.left.presheaf.stalk x.val,
            (L r : X.left.functionField) =
              algebraMap (X.left.presheaf.stalk x.val) X.left.functionField r) ∧
      (∀ P : Place k X.left.functionField, (e.symm P).val = placeCenter X P) ∧
      (∀ (a : X ≅ X) (x : {x : X.left // IsClosed ({x} : Set X.left)}),
        e (mapClosedPoint a x) = (e x).comap (ActionFunctionField.algEquivOfIso a)) ∧
      ∀ (G : AlgebraicGroup k) [ModObj G.toGroupScheme.X X]
        (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
        (x : {x : X.left // IsClosed ({x} : Set X.left)}),
        e (mapClosedPoint (ModObj.pointAut X g) x) = SchemePlaceAction.placeAction G X g (e x) := by
  refine ⟨scheme_functionField_isFunctionFieldOneVar k X hdim,
    closedPointEquivPlace X hdim hnormal, mem_closedPointEquivPlace X hdim hnormal,
    ?_, closedPointEquivPlace_symm_val X hdim hnormal, ?_, ?_⟩
  · intro x
    exact ⟨closedPointStalkEquiv X hdim hnormal x, coe_closedPointStalkEquiv X hdim hnormal x⟩
  · intro a x
    exact (closedPointPlace_comap X hdim hnormal a x).symm
  · intro G _ g x
    exact closedPointEquivPlace_action X hdim hnormal G g x

end
end AclGeom.CurvePointsPlaces
