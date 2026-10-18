/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.BirationalGluing
import AclGeom.Correspondence.FunctionFieldEquivalence
import AclGeom.Correspondence.SchemeGenericTranslate

/-!
# Actual birational morphisms on nonempty opens

**Status:** proved generic criterion (#21). A dominant morphism of integral separated
locally finite-type schemes over a field, inducing a function-field isomorphism, restricts
to an isomorphism of nonempty opens with the literal commuting square. The existing mutual-
inverse-map construction supplies the isomorphism; its forward-map law is proved here.
Named consumer: `CurveCoordinateCover.exists_coordinate_restriction_iso`, which derives
its function-field isomorphism internally from the SAME generator.
-/

namespace AclGeom.BirationalGluing
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The existing mutual-inverse partial-map construction preserves its forward rational map.
 Named consumer: `partialIsoOfMutualInverseRationalMaps_toRationalMap`. -/
theorem partialIsoOfMutualInversePartialMaps_toRationalMap
    (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap X) [IsDominant g.hom]
    (hfg : (f.comp g).hom = (f.comp g).domain.ι)
    (hgf : (g.comp f).hom = (g.comp f).domain.ι) :
    (partialIsoOfMutualInversePartialMaps f g hfg hgf).toRationalMap = f.toRationalMap := by
  let fPre := f.hom ⁻¹ᵁ g.domain
  let gPre := g.hom ⁻¹ᵁ f.domain
  let U := f.domain.ι ''ᵁ fPre
  let V := g.domain.ι ''ᵁ gPre
  let uToF : U.toScheme ⟶ f.domain.toScheme :=
    (f.domain.ι.isoImage fPre).inv ≫ fPre.ι
  let fToG : U.toScheme ⟶ g.domain.toScheme :=
    (f.domain.ι.isoImage fPre).inv ≫ f.hom ∣_ g.domain
  have hu : uToF ≫ f.domain.ι = U.ι := f.domain.ι.isoImage_inv_ι fPre
  have hfg' : fToG ≫ g.hom = U.ι := by
    have h := hfg
    dsimp [Scheme.PartialMap.comp, fToG, U, fPre] at h ⊢
    simpa only [Category.assoc] using h
  have hsq : uToF ≫ f.domain.ι = fToG ≫ g.hom := hu.trans hfg'.symm
  let F : U.toScheme ⟶ V.toScheme :=
    (isPullback_morphismRestrict g.hom f.domain).lift uToF fToG hsq ≫
      (g.domain.ι.isoImage gPre).hom
  have hle : U ≤ f.domain := f.comp_domain_le g
  apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
  refine ⟨U, (f.comp g).dense_domain, le_rfl, hle, ?_⟩
  change X.homOfLE (show U ≤ U from le_rfl) ≫ (F ≫ V.ι) = X.homOfLE hle ≫ f.hom
  rw [Scheme.homOfLE_rfl, Category.id_comp]
  dsimp only [F]
  rw [Category.assoc, Scheme.Hom.isoImage_hom_ι, ← Category.assoc,
    (isPullback_morphismRestrict g.hom f.domain).lift_snd]
  change ((f.domain.ι.isoImage fPre).inv ≫ f.hom ∣_ g.domain) ≫ g.domain.ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  apply congrArg (fun q ↦ q ≫ f.hom)
  apply (cancel_mono f.domain.ι).mp
  rw [Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
end
end AclGeom.BirationalGluing

namespace AclGeom.BirationalGluing
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

/-- The existing mutual-inverse rational-map construction preserves its forward rational map.
 Named consumer: `CurveCoordinateCover.exists_openIso_of_isIso_functionFieldMap`. -/
theorem partialIsoOfMutualInverseRationalMaps_toRationalMap
    [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X) [g.IsDominant]
    (hfg : f.comp g = Scheme.RationalMap.id X)
    (hgf : g.comp f = Scheme.RationalMap.id Y) :
    (partialIsoOfMutualInverseRationalMaps f g hfg hgf).toRationalMap = f := by
  unfold partialIsoOfMutualInverseRationalMaps
  rw [partialIsoOfMutualInversePartialMaps_toRationalMap]
  exact f.toRationalMap_toPartialMap
end
end AclGeom.BirationalGluing

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- An actual dominant morphism inducing a function-field isomorphism restricts to an
 isomorphism of nonempty opens, with the literal commuting square. The field isomorphism
 is an explicit premise of this generic criterion, discharged internally by its named
 consumer `exists_coordinate_restriction_iso`. -/
theorem exists_openIso_of_isIso_functionFieldMap
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [X.left.IsSeparated] [Y.left.IsSeparated]
    (f : X ⟶ Y) [IsDominant f.left] [IsIso f.left.toPartialMap.functionFieldMap] :
    ∃ (U T : Over (Spec (.of k))) (jU : U ⟶ X) (jT : T ⟶ Y) (e : U ≅ T),
      IsOpenImmersion jU.left ∧ IsOpenImmersion jT.left ∧
      Nonempty U.left ∧ Nonempty T.left ∧ jU ≫ f = e.hom ≫ jT := by
  classical
  let Fmap := f.left.toPartialMap.functionFieldMap
  let A : Y.left.functionField ≃ₐ[k] X.left.functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso Fmap).commRingCatIsoToRingEquiv)
      (ActionFunctionField.functionFieldMap_algebraMap f)
  let E := A.symm
  have hF : Fmap = CommRingCat.ofHom E.symm.toRingHom := by
    ext z
    rfl
  have hf : f.left.toRationalMap.fromFunctionField =
      Scheme.functionFieldMorphism E.toRingEquiv :=
    Scheme.PartialMap.fromFunctionField_eq_of_functionFieldMap_eq f.left.toPartialMap
      E.toRingEquiv hF
  let ψ : (Spec Y.left.functionField).asOver (Spec (.of k)) ⟶ X :=
    (algSpec (.of k)).map (CommAlgCat.ofHom E.toAlgHom).op ≫
      SchemeGenericTranslate.genericParameter X
  have hψ : ψ.left = Scheme.functionFieldMorphism E.symm.toRingEquiv := by rfl
  have hbase : ψ.left ≫ X.hom =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫ Y.hom :=
    (Over.w ψ).trans (Over.w (SchemeGenericTranslate.genericParameter Y)).symm
  let g := Scheme.RationalMap.ofFunctionField Y.hom X.hom ψ.left hbase
  have hg : g.fromFunctionField = Scheme.functionFieldMorphism E.symm.toRingEquiv :=
    (Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _).trans hψ
  have : g.IsDominant := by
    apply Scheme.RationalMap.isDominant_of_fromFunctionField_closedPoint
    rw [hg]
    exact Scheme.functionFieldMorphism_closedPoint _
  have hfg : f.left.toRationalMap.comp g = Scheme.RationalMap.id X.left :=
    Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq _ _ E.toRingEquiv hf hg
  have hgf : g.comp f.left.toRationalMap = Scheme.RationalMap.id Y.left :=
    Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq _ _ E.symm.toRingEquiv hg hf
  let e := BirationalGluing.partialIsoOfMutualInverseRationalMaps
    f.left.toRationalMap g hfg hgf
  have he : e.toRationalMap = f.left.toRationalMap :=
    BirationalGluing.partialIsoOfMutualInverseRationalMaps_toRationalMap _ _ hfg hgf
  have hsquare : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f.left :=
    (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he)
  have hfbase : f.left.toRationalMap.compHom Y.hom = X.hom.toRationalMap := by
    rw [← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.Hom.toPartialMap_compHom, Over.w f]
  have heover : e.IsOver X.hom Y.hom :=
    BirationalGluing.partialIsoOfMutualInverseRationalMaps_isOver _ _ _ _ hfg hgf hfbase
  let U : Over (Spec (.of k)) := Over.mk (e.source.ι ≫ X.hom)
  let T : Over (Spec (.of k)) := Over.mk (e.target.ι ≫ Y.hom)
  let jU : U ⟶ X := Over.homMk e.source.ι
  let jT : T ⟶ Y := Over.homMk e.target.ι
  let eU : U ≅ T := Over.isoMk e.iso heover
  refine ⟨U, T, jU, jT, eU, ?_, ?_, ?_, ?_, ?_⟩
  · change IsOpenImmersion e.source.ι
    infer_instance
  · change IsOpenImmersion e.target.ι
    infer_instance
  · exact e.dense_source.nonempty.to_subtype
  · exact e.dense_target.nonempty.to_subtype
  · exact Over.OverMorphism.ext hsquare.symm
end
end AclGeom.CurveCoordinateCover
