/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePlaceCenter

/-!
# Actual stalk equivalences and the point-place inverse

**Status:** proved for actual proper normal integral curves of dimension one over any field.
Each closed-point stalk is isomorphic to its actual place ring, retaining the literal
canonical embedding in the function field. Uniqueness of the proper valuation model recovers
the original point. Named consumer: closedPointEquivPlace.

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

/-- The actual local ring is isomorphic to the corresponding place ring, with its given
field embedding. Named consumer: the inverse identity of the closed-point/place equivalence. -/
def closedPointStalkEquiv
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) :
    (X.left.presheaf.stalk x.val) ≃+* (closedPointPlace X hdim hnormal x).val := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := hnormal x.val
  have := ProperCurve.stalk_valuationRing X.left hdim.le x.val
  exact ValuationRing.equivInteger (X.left.presheaf.stalk x.val) X.left.functionField

/-- The stalk/place-ring isomorphism is literally the canonical embedding into the field.
Named consumer: the actual inverse identity, without a local-ring comparison certificate. -/
theorem coe_closedPointStalkEquiv
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) (r : X.left.presheaf.stalk x.val) :
    ((closedPointStalkEquiv X hdim hnormal x) r : X.left.functionField) =
      algebraMap (X.left.presheaf.stalk x.val) X.left.functionField r := rfl

/-- The center of the actual place attached to a closed point is that same point.
Named consumer: the left inverse of the actual closed-point/place equivalence. -/
theorem placeCenter_closedPointPlace
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) :
    placeCenter X (closedPointPlace X hdim hnormal x) = x.val := by
  let P := closedPointPlace X hdim hnormal x
  let E := closedPointStalkEquiv X hdim hnormal x
  let u := CommRingCat.ofHom E.toRingHom
  let v := CommRingCat.ofHom P.val.subtype
  let t := X.left.fromSpecStalk x.val
  let m := Spec.map u ≫ t
  have huv : u ≫ v = CommRingCat.ofHom
      (algebraMap (X.left.presheaf.stalk x.val) X.left.functionField) := by
    ext r
    exact coe_closedPointStalkEquiv X hdim hnormal x r
  have hcanonical : Spec.map (CommRingCat.ofHom
      (algebraMap (X.left.presheaf.stalk x.val) X.left.functionField)) ≫ t =
      X.left.fromSpecStalk (genericPoint X.left) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x.val)
  have hmgen : Spec.map v ≫ m = X.left.fromSpecStalk (genericPoint X.left) := by
    calc
      _ = (Spec.map v ≫ Spec.map u) ≫ t := (Category.assoc _ _ _).symm
      _ = Spec.map (u ≫ v) ≫ t :=
        congrArg (fun f ↦ f ≫ t) (Spec.map_comp u v).symm
      _ = Spec.map (CommRingCat.ofHom
          (algebraMap (X.left.presheaf.stalk x.val) X.left.functionField)) ≫ t :=
        congrArg (fun f ↦ Spec.map f ≫ t) huv
      _ = _ := hcanonical
  have : IsLocalHom u.hom := IsLocalHom.of_surjective _ E.surjective
  have hp : Spec.map u (IsLocalRing.closedPoint P.val) =
      IsLocalRing.closedPoint (X.left.presheaf.stalk x.val) := Spec_closedPoint
  have ht : t (IsLocalRing.closedPoint (X.left.presheaf.stalk x.val)) = x.val :=
    Scheme.fromSpecStalk_closedPoint
  have hmPoint : m (IsLocalRing.closedPoint P.val) = x.val :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (fun q ↦ t q) hp).trans ht)
  have hmEq : m = placeModelMap X P :=
    (existsUnique_placeModelMap X P).choose_spec.2 m hmgen
  change placeModelMap X P (IsLocalRing.closedPoint P.val) = x.val
  exact (congrArg (fun f ↦ f (IsLocalRing.closedPoint P.val)) hmEq).symm.trans hmPoint

end
end AclGeom.CurvePointsPlaces
