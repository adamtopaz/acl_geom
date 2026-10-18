/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.BirationalMorphism
import AclGeom.Correspondence.CurveCoordinateField

/-!
# Restricting the given curve coordinate to an open isomorphism

**Status:** proved criterion (#21). A coordinate on a given open of an integral affine
locally finite-type scheme, whose generic value is a transcendental generator of the
original function field, restricts to an isomorphism with a nonempty standard-line open.
The literal square retains the GIVEN coordinate by restriction; the new generic lift
factors the GIVEN old lift. No normality or birationality certificate is supplied.
Named consumer: `SchemeAffineCurveCover.exists_curve_coordinate_cover` supplies every
coordinate and field premise internally from the genuine regular-affine action.
-/

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- A dominant open immersion of integral schemes induces an isomorphism on their actual
 generic-stalk fields. Named consumer: `exists_coordinate_restriction_iso`. -/
theorem isIso_functionFieldMap_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (j : X ⟶ Y) [IsOpenImmersion j] [IsDominant j] :
    IsIso j.toPartialMap.functionFieldMap := by
  have : IsIso (Scheme.stalkClosedPointTo j.toPartialMap.fromFunctionField) := by
    rw [Scheme.Hom.fromFunctionField_toPartialMap, Scheme.stalkClosedPointTo_comp,
      Scheme.stalkClosedPointTo_fromSpecStalk]
    apply IsIso.comp_isIso'
    · exact (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion j›).2 _
    · exact Iso.isIso_hom _
  dsimp only [Scheme.PartialMap.functionFieldMap]
  infer_instance
end
end AclGeom.CurveCoordinateCover

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The GIVEN coordinate with generic value a transcendental generator restricts to an
 isomorphism of nonempty curve and line opens. Its actual generic lift factors the GIVEN
 lift. No normality or birationality certificate is a premise. Named consumer:
 `SchemeAffineCurveCover.exists_curve_coordinate_cover`. -/
theorem exists_coordinate_restriction_iso
    (V U : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (x : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    (g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U)
    (hgj : g ≫ j = SchemeGenericTranslate.genericParameter V)
    (hgx : g ≫ x = AffineSchemeAction.linePoint k t) :
    ∃ (U₁ T : Over (Spec (.of k))) (j₁ : U₁ ⟶ U)
      (jT : T ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
      (e : U₁ ≅ T) (g₁ : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U₁),
      IsOpenImmersion j₁.left ∧ IsOpenImmersion jT.left ∧
      Nonempty U₁.left ∧ Nonempty T.left ∧
      j₁ ≫ x = e.hom ≫ jT ∧ g₁ ≫ j₁ = g := by
  classical
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  have hU : Nonempty U.left := ⟨g.left (IsLocalRing.closedPoint V.left.functionField)⟩
  have : IsIntegral U.left := isIntegral_of_isOpenImmersion j.left
  have : LocallyOfFiniteType U.hom := by rw [← Over.w j]; infer_instance
  have : IsIntegral L.left := inferInstanceAs
    (IsIntegral (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1))))
  let : Algebra k (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1))).functionField :=
    ActionFunctionField.functionFieldAlgebra L
  have : IsDominant (g.left ≫ j.left) := by
    rw [← Over.comp_left, hgj]
    exact Scheme.isDominant_fromSpecStalk_genericPoint
  have : IsDominant j.left := IsDominant.of_comp g.left j.left
  have : IsIso j.left.toPartialMap.functionFieldMap :=
    isIso_functionFieldMap_of_isOpenImmersion j.left
  let η : V.left.functionField ≃ₐ[k] U.left.functionField :=
    AlgEquiv.ofRingEquiv
      (f := (asIso j.left.toPartialMap.functionFieldMap).commRingCatIsoToRingEquiv)
      (ActionFunctionField.functionFieldMap_algebraMap j)
  let tU := η t
  have htU : Transcendental k tU :=
    (not_congr (isAlgebraic_algHom_iff η.toAlgHom η.injective)).mpr ht
  have htopU : IntermediateField.adjoin k ({tU} : Set U.left.functionField) = ⊤ := by
    have h := congrArg (fun K : IntermediateField k V.left.functionField ↦ K.map η.toAlgHom) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top] at h
    exact h
  let δ : (Spec U.left.functionField).asOver (Spec (.of k)) ⟶
      (Spec V.left.functionField).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom η.toAlgHom).op
  have hnat : SchemeGenericTranslate.genericParameter U ≫ j =
      δ ≫ SchemeGenericTranslate.genericParameter V := by
    apply Over.OverMorphism.ext
    exact (Scheme.Hom.fromFunctionField_toPartialMap j.left).symm.trans
      (Scheme.PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom j.left.toPartialMap)
  have hδg : δ ≫ g = SchemeGenericTranslate.genericParameter U := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).mp
    change ((δ ≫ g) ≫ j).left = (SchemeGenericTranslate.genericParameter U ≫ j).left
    rw [Category.assoc, hgj, hnat]
  have hxgen : SchemeGenericTranslate.genericParameter U ≫ x =
      AffineSchemeAction.linePoint k tU := by
    rw [← hδg, Category.assoc, hgx]
    exact linePoint_baseChange η.toAlgHom t
  obtain ⟨E, _, hEgen⟩ := exists_line_functionField_equiv tU htU htopU
  have hgeneric : x.left.toPartialMap.fromFunctionField =
      Scheme.functionFieldMorphismOfHom (CommRingCat.ofHom E.toRingHom) := by
    rw [Scheme.Hom.fromFunctionField_toPartialMap]
    change (SchemeGenericTranslate.genericParameter U ≫ x).left = _
    rw [hxgen]
    exact hEgen.symm
  have hdomP : IsDominant x.left.toPartialMap.hom :=
    Scheme.PartialMap.isDominant_of_fromFunctionField_closedPoint x.left.toPartialMap (by
      rw [hgeneric]
      exact Scheme.functionFieldMorphismOfHom_closedPoint _)
  have : IsDominant (U.left.topIso.hom ≫ x.left) := hdomP
  have : IsDominant x.left := IsDominant.of_comp U.left.topIso.hom x.left
  have hFF : x.left.toPartialMap.functionFieldMap = CommRingCat.ofHom E.toRingHom :=
    Scheme.PartialMap.functionFieldMap_eq_of_fromFunctionField_eq_hom x.left.toPartialMap
      _ hgeneric
  have : IsIso x.left.toPartialMap.functionFieldMap := by
    rw [hFF]
    exact (E.toRingEquiv.toCommRingCatIso).isIso_hom
  have : U.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from j.left]
    infer_instance
  have : L.left.IsSeparated := inferInstanceAs
    ((Spec (.of (AdditiveGroupScheme.CoordinateRing k 1))).IsSeparated)
  obtain ⟨U₁, T, j₁, jT, e, hj₁, hjT, hU₁, hT, hsq⟩ :=
    exists_openIso_of_isIso_functionFieldMap U L x
  have := hj₁
  have hnew : IsOpenImmersion (j₁ ≫ j).left := by
    change IsOpenImmersion (j₁.left ≫ j.left)
    infer_instance
  have : IsIntegral U₁.left := isIntegral_of_isOpenImmersion (j₁ ≫ j).left
  have : Subsingleton ((Spec V.left.functionField).asOver (Spec (.of k))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum V.left.functionField))
  have hrange : Set.range (SchemeGenericTranslate.genericParameter V).left ⊆
      Set.range (j₁ ≫ j).left := by
    rintro y ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint V.left.functionField := Subsingleton.elim _ _
    subst p
    have hpoint : (SchemeGenericTranslate.genericParameter V).left
        (IsLocalRing.closedPoint V.left.functionField) = genericPoint V.left :=
      Scheme.fromSpecStalk_closedPoint
    rw [hpoint]
    exact ⟨genericPoint U₁.left, genericPoint_eq_of_isOpenImmersion (j₁ ≫ j).left⟩
  let g₁ : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U₁ :=
    Over.homMk (IsOpenImmersion.lift (j₁ ≫ j).left
      (SchemeGenericTranslate.genericParameter V).left hrange) (by
      rw [← Over.w (j₁ ≫ j), ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w (SchemeGenericTranslate.genericParameter V))
  refine ⟨U₁, T, j₁, jT, e, g₁, hj₁, hjT, hU₁, hT, hsq, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  change (g₁ ≫ j₁ ≫ j).left = (g ≫ j).left
  rw [hgj]
  exact IsOpenImmersion.lift_fac _ _ hrange
end
end AclGeom.CurveCoordinateCover
