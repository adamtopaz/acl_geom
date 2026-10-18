/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePlaceModel

/-!
# Actual centers recover place rings

**Status:** proved for actual proper normal integral curves of dimension one. The actual
center stalk maps into the place ring with the literal canonical field embedding. The
dimension-one valuation comparison identifies the two subrings and proves the center is
closed. Named consumer: closedPointEquivPlace.

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

/-- The actual local map at the center commutes with the canonical field embedding.
Named consumer: equality of the actual center's stalk image with the place ring. -/
theorem placeModelMap_stalk_comp_subtype
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (P : Place k X.left.functionField) :
    Scheme.stalkClosedPointTo (placeModelMap X P) ≫ CommRingCat.ofHom P.val.subtype =
      CommRingCat.ofHom
        (algebraMap (X.left.presheaf.stalk (placeCenter X P)) X.left.functionField) := by
  let m := placeModelMap X P
  let u := Scheme.stalkClosedPointTo m
  let v := CommRingCat.ofHom P.val.subtype
  let t := X.left.fromSpecStalk (placeCenter X P)
  have hlocal : Spec.map u ≫ t = m :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk m
  have hgeneric : Spec.map v ≫ m =
      X.left.fromSpecStalk (genericPoint X.left) := placeModelMap_generic X P
  have hcanonical : Spec.map (CommRingCat.ofHom
      (algebraMap (X.left.presheaf.stalk (placeCenter X P)) X.left.functionField)) ≫ t =
      X.left.fromSpecStalk (genericPoint X.left) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (placeCenter X P))
  apply Spec.map_injective
  apply (cancel_mono t).mp
  exact ((congrArg (fun f ↦ f ≫ t) (Spec.map_comp u v)).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun f ↦ Spec.map v ≫ f) hlocal).trans
      hgeneric))).trans hcanonical.symm

/-- The actual center's local ring has image exactly the given place ring.
The dimension-one valuation-overring theorem is applied internally.
Named consumer: the closed-point/place equivalence. -/
theorem stalkValuationSubring_placeCenter
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsLocallyNoetherian X.left] (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (P : Place k X.left.functionField) :
    stalkValuationSubring X.left hdim.le hnormal (placeCenter X P) = P.val := by
  have hle : stalkValuationSubring X.left hdim.le hnormal (placeCenter X P) ≤ P.val := by
    intro z hz
    obtain ⟨r, hr⟩ :=
      (mem_stalkValuationSubring X.left hdim.le hnormal (placeCenter X P) z).mp hz
    have hval : ((Scheme.stalkClosedPointTo (placeModelMap X P)).hom r :
        X.left.functionField) = z :=
      (congrArg (fun f ↦ f.hom r) (placeModelMap_stalk_comp_subtype X P)).trans hr
    rw [← hval]
    exact ((Scheme.stalkClosedPointTo (placeModelMap X P)).hom r).property
  have : Ring.KrullDimLE 1
      (stalkValuationSubring X.left hdim.le hnormal (placeCenter X P)) :=
    stalkValuationSubring_krullDimLE X.left hdim.le hnormal (placeCenter X P)
  exact ValuationSubring.eq_of_le_of_ne_top
    (stalkValuationSubring X.left hdim.le hnormal (placeCenter X P)) hle P.ne_top

/-- The actual center of every place on a proper normal integral curve is a closed point.
Named consumer: the inverse of the actual closed-point/place equivalence. -/
theorem placeCenter_isClosed
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (P : Place k X.left.functionField) : IsClosed ({placeCenter X P} : Set X.left) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  apply (isClosed_singleton_iff_ne_genericPoint X.left hdim (placeCenter X P)).mpr
  intro h
  apply P.ne_top
  exact (stalkValuationSubring_placeCenter X hdim hnormal P).symm.trans
    ((stalkValuationSubring_eq_top_iff X.left hdim.le hnormal (placeCenter X P)).mpr h)

end
end AclGeom.CurvePointsPlaces
