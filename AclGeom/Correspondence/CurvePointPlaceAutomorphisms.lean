/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePointPlaceEquivalence
import AclGeom.Correspondence.CurveStalkNaturality
import AclGeom.Curves.PlaceAction

/-!
# Automorphisms preserve the actual point-place model

**Status:** proved for every actual automorphism of a proper normal integral curve of
dimension one. The actual closed-point image corresponds to comap by the actual contravariant
function-field automorphism. Named consumer: exists_point_place_model and its regular-action
compatibility.

The given proper normal curve is an actual input. Projective presentation, joint regularity of
extended families, rational-action regularization and the full original classifier remain
owed, alongside group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary. All eight original #21 work items and the full durable goal remain active
and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra
  ActionFunctionField.isIso_hom_left

/-- The actual image of a closed point under an actual curve automorphism.
Named consumer: the closed-point/place transport formula. -/
def mapClosedPoint {X : Over (Spec (.of k))} (a : X ≅ X)
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) :
    {x : X.left // IsClosed ({x} : Set X.left)} :=
  ⟨a.hom.left x.val, by
    simpa only [Set.image_singleton, Scheme.Hom.homeomorph_apply] using
      a.hom.left.homeomorph.isClosedMap ({x.val} : Set X.left) x.property⟩

/-- The actual point/place correspondence intertwines curve automorphisms with pullback
of the actual valuation rings along their actual function-field automorphisms.
Named source consumer: the coupled actual point/place model. -/
theorem closedPointPlace_comap
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (a : X ≅ X) (x : {x : X.left // IsClosed ({x} : Set X.left)}) :
    (closedPointPlace X hdim hnormal x).comap (ActionFunctionField.algEquivOfIso a) =
      closedPointPlace X hdim hnormal (mapClosedPoint a x) := by
  let σ := ActionFunctionField.algEquivOfIso a
  let u := a.hom.left.stalkMap x.val
  have hsurj : Function.Surjective u.hom :=
    (asIso u).commRingCatIsoToRingEquiv.surjective
  have hfield (r : X.left.presheaf.stalk (a.hom.left x.val)) :
      σ (algebraMap (X.left.presheaf.stalk (a.hom.left x.val)) X.left.functionField r) =
        algebraMap (X.left.presheaf.stalk x.val) X.left.functionField (u.hom r) :=
    congrArg (fun f ↦ f.hom r) (functionFieldMap_stalkMap a.hom.left x.val)
  apply Place.ext_val
  apply ValuationSubring.ext
  intro z
  change σ z ∈ (closedPointPlace X hdim hnormal x).val ↔
    z ∈ (closedPointPlace X hdim hnormal (mapClosedPoint a x)).val
  rw [mem_closedPointPlace, mem_closedPointPlace]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hsurj r
    refine ⟨s, σ.injective ?_⟩
    exact (hfield s).trans
      ((congrArg (algebraMap (X.left.presheaf.stalk x.val) X.left.functionField) hs).trans hr)
  · rintro ⟨r, hr⟩
    refine ⟨u.hom r, ?_⟩
    exact (hfield r).symm.trans (congrArg σ hr)

end
end AclGeom.CurvePointsPlaces
