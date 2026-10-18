/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePointPlaceInverse
import AclGeom.Curves.PlaceAction

/-!
# Actual closed points are actual places

**Status:** proved over every field for an actual proper normal integral curve of dimension
one. The equivalence uses closed points, excluding the generic point. Its inverse is the
actual proper center, and literal membership is exactly the image of the canonical actual
stalk embedding. Named consumer: exists_point_place_model.

The given proper normal curve is an actual input. Completion construction, the scheme API from
smoothness to local normality, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Actual closed points of a proper normal integral curve are exactly the existing places
of its actual generic-stalk field, over every field. All centers, local-ring comparisons
and inverse identities are internal. Named source consumer: the actual point/place model. -/
def closedPointEquivPlace
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x)) :
    {x : X.left // IsClosed ({x} : Set X.left)} ≃ Place k X.left.functionField where
  toFun := closedPointPlace X hdim hnormal
  invFun P := ⟨placeCenter X P, placeCenter_isClosed X hdim hnormal P⟩
  left_inv x := Subtype.ext (placeCenter_closedPointPlace X hdim hnormal x)
  right_inv P := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    exact Place.ext_val (stalkValuationSubring_placeCenter X hdim hnormal P)

/-- The equivalence retains literal equality with the actual stalk image in the field.
Named source consumer: the coupled point/place model. -/
theorem mem_closedPointEquivPlace
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) (z : X.left.functionField) :
    z ∈ (closedPointEquivPlace X hdim hnormal x).val ↔
      ∃ r : X.left.presheaf.stalk x.val,
        algebraMap (X.left.presheaf.stalk x.val) X.left.functionField r = z :=
  mem_closedPointPlace X hdim hnormal x z

/-- The inverse is the actual center of the place's canonical proper model map.
Named source consumer: the coupled point/place model. -/
theorem closedPointEquivPlace_symm_val
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (P : Place k X.left.functionField) :
    ((closedPointEquivPlace X hdim hnormal).symm P).val = placeCenter X P := rfl

end
end AclGeom.CurvePointsPlaces
