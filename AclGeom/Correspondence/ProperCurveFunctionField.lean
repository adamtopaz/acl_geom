/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ProperCurveExtension
import AclGeom.Correspondence.FunctionFieldEquivalence
import AclGeom.Correspondence.SchemeGenericTranslate

/-!
# Function fields determine proper normal curves

**Status:** proved over every field for actual proper normal integral curves of dimension at
most one. Normality is explicitly the integral closedness of every stalk. Noetherianity is
derived internally from properness over the field. Every actual k-function-field isomorphism
induces a unique global curve isomorphism with the literal generic-point formula. A dominant
morphism whose actual field map is an isomorphism is itself an isomorphism. This proves the
degree-one/birational-map assertion in the source genus-zero argument; no finite-map
certificate is needed.

For a given actual proper normal integral dimension-one curve, the closed-point/place
identification is now proved by CurvePointsPlaces.exists_point_place_model, including actual
stalk ring equivalences and automorphism compatibility. The given proper normal curve is an
actual input. Projective presentation, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.ProperCurve
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- An isomorphism of the actual function fields of proper normal integral curves is
induced contravariantly by a unique global curve isomorphism. Normality is local integral
closedness, not an extension certificate. Named source consumer: individual translation and
automorphism extension in the proof of `lem:affine-action`. This does not construct a
completion or prove joint regularity of a family. -/
theorem existsUnique_iso_of_functionFieldEquiv
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    (hdimX : topologicalKrullDim X.left ≤ 1)
    (hdimY : topologicalKrullDim Y.left ≤ 1)
    (hnormalX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (hnormalY : ∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y))
    [IsProper X.hom] [IsProper Y.hom]
    (E : X.left.functionField ≃ₐ[k] Y.left.functionField) :
    ∃! e : X ≅ Y, e.hom.left.toRationalMap.fromFunctionField =
      Scheme.functionFieldMorphism E.toRingEquiv := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : X.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from X.hom]
    infer_instance
  have : Y.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from Y.hom]
    infer_instance
  let φ : (Spec X.left.functionField).asOver (Spec (.of k)) ⟶ Y :=
    (algSpec (.of k)).map (CommAlgCat.ofHom E.symm.toAlgHom).op ≫
      SchemeGenericTranslate.genericParameter Y
  let ψ : (Spec Y.left.functionField).asOver (Spec (.of k)) ⟶ X :=
    (algSpec (.of k)).map (CommAlgCat.ofHom E.toAlgHom).op ≫
      SchemeGenericTranslate.genericParameter X
  have hφ : φ.left = Scheme.functionFieldMorphism E.toRingEquiv := rfl
  have hψ : ψ.left = Scheme.functionFieldMorphism E.symm.toRingEquiv := rfl
  have hφbase : φ.left ≫ Y.hom =
      X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom :=
    (Over.w φ).trans (Over.w (SchemeGenericTranslate.genericParameter X)).symm
  have hψbase : ψ.left ≫ X.hom =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫ Y.hom :=
    (Over.w ψ).trans (Over.w (SchemeGenericTranslate.genericParameter Y)).symm
  let f := Scheme.RationalMap.ofFunctionField X.hom Y.hom φ.left hφbase
  let g := Scheme.RationalMap.ofFunctionField Y.hom X.hom ψ.left hψbase
  have hf : f.fromFunctionField = Scheme.functionFieldMorphism E.toRingEquiv :=
    (Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _).trans hφ
  have hg : g.fromFunctionField = Scheme.functionFieldMorphism E.symm.toRingEquiv :=
    (Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _).trans hψ
  have hfbase : f.compHom Y.hom = X.hom.toRationalMap :=
    ((Scheme.RationalMap.equivFunctionField X.hom Y.hom) ⟨φ.left, hφbase⟩).property
  have hgbase : g.compHom X.hom = Y.hom.toRationalMap :=
    ((Scheme.RationalMap.equivFunctionField Y.hom X.hom) ⟨ψ.left, hψbase⟩).property
  have : f.IsDominant := by
    apply Scheme.RationalMap.isDominant_of_fromFunctionField_closedPoint
    rw [hf]
    exact Scheme.functionFieldMorphism_closedPoint _
  have : g.IsDominant := by
    apply Scheme.RationalMap.isDominant_of_fromFunctionField_closedPoint
    rw [hg]
    exact Scheme.functionFieldMorphism_closedPoint _
  have hfg := Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq
    f g E.toRingEquiv hf hg
  have hgf := Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq
    g f E.symm.toRingEquiv hg hf
  obtain ⟨F, ⟨hF, hFbase⟩, _⟩ :=
    existsUnique_extension hdimX hnormalX X.hom Y.hom f hfbase
  obtain ⟨H, ⟨hH, hHbase⟩, _⟩ :=
    existsUnique_extension hdimY hnormalY Y.hom X.hom g hgbase
  have hFH : F ≫ H = 𝟙 X.left := by
    apply hom_eq_of_toRationalMap_eq
    change (F ≫ H).toPartialMap.toRationalMap = _
    rw [← Scheme.Hom.toPartialMap_compHom,
      Scheme.RationalMap.compHom_toRationalMap]
    change F.toRationalMap.compHom H = _
    rw [hF, ← Scheme.RationalMap.comp_toRationalMap, hH]
    exact hfg
  have hHF : H ≫ F = 𝟙 Y.left := by
    apply hom_eq_of_toRationalMap_eq
    change (H ≫ F).toPartialMap.toRationalMap = _
    rw [← Scheme.Hom.toPartialMap_compHom,
      Scheme.RationalMap.compHom_toRationalMap]
    change H.toRationalMap.compHom F = _
    rw [hH, ← Scheme.RationalMap.comp_toRationalMap, hF]
    exact hgf
  let e : X ≅ Y := Over.isoMk
    { hom := F, inv := H, hom_inv_id := hFH, inv_hom_id := hHF } hFbase
  have he : e.hom.left.toRationalMap.fromFunctionField =
      Scheme.functionFieldMorphism E.toRingEquiv :=
    (congrArg Scheme.RationalMap.fromFunctionField hF).trans hf
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply hom_eq_of_toRationalMap_eq
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  exact hd.trans he.symm

/-- A birational morphism between proper normal integral curves is an isomorphism.
Its field isomorphism and global inverse are constructed internally from the actual
function-field map. Named source consumer: the degree-one map assertion in the genus-zero
argument of `lem:affine-action`. Finiteness need not be an extra premise. -/
theorem isIso_of_isIso_functionFieldMap
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    (hdimX : topologicalKrullDim X.left ≤ 1)
    (hdimY : topologicalKrullDim Y.left ≤ 1)
    (hnormalX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (hnormalY : ∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y))
    [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) [IsDominant f.left] [IsIso f.left.toPartialMap.functionFieldMap] :
    IsIso f := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : Y.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from Y.hom]
    infer_instance
  let A : Y.left.functionField ≃ₐ[k] X.left.functionField :=
    AlgEquiv.ofRingEquiv
      (f := (asIso f.left.toPartialMap.functionFieldMap).commRingCatIsoToRingEquiv)
      (ActionFunctionField.functionFieldMap_algebraMap f)
  let E := A.symm
  have hmap : f.left.toPartialMap.functionFieldMap =
      CommRingCat.ofHom E.symm.toRingHom := by
    ext z
    rfl
  have hgeneric : f.left.toRationalMap.fromFunctionField =
      Scheme.functionFieldMorphism E.toRingEquiv :=
    Scheme.PartialMap.fromFunctionField_eq_of_functionFieldMap_eq
      f.left.toPartialMap E.toRingEquiv hmap
  obtain ⟨e, he, _⟩ := existsUnique_iso_of_functionFieldEquiv
    X Y hdimX hdimY hnormalX hnormalY E
  have hfe : f = e.hom := by
    apply Over.OverMorphism.ext
    apply hom_eq_of_toRationalMap_eq
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    exact hgeneric.trans he.symm
  rw [hfe]
  infer_instance

end
end AclGeom.ProperCurve
