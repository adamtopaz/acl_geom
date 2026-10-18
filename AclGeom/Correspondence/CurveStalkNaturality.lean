/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ActionFunctionField

/-!
# Actual function-field maps commute with stalk maps

**Status:** proved for actual dominant morphisms of integral schemes. The canonical stalk
embeddings commute with the actual contravariant function-field map. Named consumer:
closedPointPlace_comap for actual curve automorphisms.

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

/-- Pullback on the actual function fields commutes with the actual map on every stalk.
Named consumer: automorphism compatibility of the closed-point/place equivalence. -/
theorem functionFieldMap_stalkMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
        f.toPartialMap.functionFieldMap =
      f.stalkMap x ≫ CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField) := by
  let q := f.toPartialMap.functionFieldMap
  let u := f.stalkMap x
  let sx := CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)
  let sy := CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField)
  let tx := X.fromSpecStalk x
  let ty := Y.fromSpecStalk (f x)
  have hx : Spec.map sx ≫ tx = X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hy : Spec.map sy ≫ ty = Y.fromSpecStalk (genericPoint Y) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (f x))
  have hstalk : Spec.map u ≫ ty = tx ≫ f :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hg : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map q ≫ Y.fromSpecStalk (genericPoint Y) :=
    (Scheme.Hom.fromFunctionField_toPartialMap f).symm.trans
      (Scheme.PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom f.toPartialMap)
  apply Spec.map_injective
  apply (cancel_mono ty).mp
  calc
    _ = Spec.map q ≫ (Spec.map sy ≫ ty) :=
      (congrArg (fun h ↦ h ≫ ty) (Spec.map_comp sy q)).trans (Category.assoc _ _ _)
    _ = Spec.map q ≫ Y.fromSpecStalk (genericPoint Y) := congrArg _ hy
    _ = X.fromSpecStalk (genericPoint X) ≫ f := hg.symm
    _ = (Spec.map sx ≫ tx) ≫ f := congrArg (fun h ↦ h ≫ f) hx.symm
    _ = Spec.map sx ≫ (tx ≫ f) := Category.assoc _ _ _
    _ = Spec.map sx ≫ (Spec.map u ≫ ty) := congrArg _ hstalk.symm
    _ = Spec.map (u ≫ sx) ≫ ty :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun h ↦ h ≫ ty) (Spec.map_comp u sx).symm)

end
end AclGeom.CurvePointsPlaces
