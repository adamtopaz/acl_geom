/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.OpenEmbeddingFromInverse
import AclGeom.Correspondence.CurveCoordinateCover

/-!
# Birational Open Embedding

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- A birational morphism to an integral scheme with valuation stalks is an open
immersion when the source is separated and locally of finite type over the field.
Named consumer: the original smooth curve's actual completion embedding. -/
theorem isOpenImmersion_of_target_valuation
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [X.left.IsSeparated] [Y.left.IsSeparated]
    (hval : ∀ y : Y.left, ValuationRing (Y.left.presheaf.stalk y))
    (f : X ⟶ Y) [IsDominant f.left]
    [IsIso f.left.toPartialMap.functionFieldMap] : IsOpenImmersion f.left := by
  have hstalk (x : X.left) : IsIso (f.left.stalkMap x) := by
    have := hval (f.left x)
    exact stalkMap_isIso_of_target_valuation f.left x
  let Fmap := f.left.toPartialMap.functionFieldMap
  let A : Y.left.functionField ≃ₐ[k] X.left.functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso Fmap).commRingCatIsoToRingEquiv)
      (ActionFunctionField.functionFieldMap_algebraMap f)
  let E := A.symm
  have hF : Fmap = CommRingCat.ofHom E.symm.toRingHom := by ext z; rfl
  have hf : f.left.toRationalMap.fromFunctionField =
      Scheme.functionFieldMorphism E.toRingEquiv :=
    Scheme.PartialMap.fromFunctionField_eq_of_functionFieldMap_eq f.left.toPartialMap
      E.toRingEquiv hF
  let ψ : (Spec Y.left.functionField).asOver (Spec (.of k)) ⟶ X :=
    (algSpec (.of k)).map (CommAlgCat.ofHom E.toAlgHom).op ≫
      SchemeGenericTranslate.genericParameter X
  have hψ : ψ.left = Scheme.functionFieldMorphism E.symm.toRingEquiv := rfl
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
  have hgf : g.compHom f.left = Scheme.RationalMap.id Y.left := by
    rw [← Scheme.RationalMap.comp_toRationalMap]
    exact Scheme.RationalMap.comp_eq_id_of_fromFunctionField_eq _ _ E.symm.toRingEquiv hg hf
  have hgi : Spec.map Fmap ≫ g.fromFunctionField =
      X.left.fromSpecStalk (genericPoint X.left) := by
    rw [hg, hF]
    change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom E.toRingHom) ≫
        X.left.fromSpecStalk (genericPoint X.left)) = _
    rw [← Category.assoc, ← Spec.map_comp]
    have hid : CommRingCat.ofHom E.toRingHom ≫
        CommRingCat.ofHom E.symm.toRingHom = 𝟙 (CommRingCat.of X.left.functionField) := by
      ext z
      exact E.symm_apply_apply z
    rw [hid, Spec.map_id, Category.id_comp]
  exact isOpenImmersion_of_inverse_domain f.left g hgi hgf
    (inverse_domain_contains_image X Y f hstalk g hgi)

end
end AclGeom.CurveCompletion
