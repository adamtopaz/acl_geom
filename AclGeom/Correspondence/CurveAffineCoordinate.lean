/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineSchemeAction
import AclGeom.Correspondence.SchemeGenericTranslate

/-!
# The same rational curve coordinate on actual opens

**Status:** proved generic criteria (#21). A generic-stalk element spreads to a regular
coordinate on a dense open. An affine formula for an actual curve automorphism gives an
actual commuting diagram on the nonempty common pullback open, with the SAME coordinate.
The model and generic lift are explicit in that criterion; `CurveAffineDiagram` constructs
them internally. Generic-point dominance proves the diagram. No normality is assumed.
Named consumer: the genuine regular-affine action in `SchemeAffineCurveDiagram`.
-/

namespace AclGeom.CurveAffineCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- An element of the actual generic stalk spreads to a regular line coordinate on a dense
 open of any integral scheme over a field. The generic-point morphism is literally
 `linePoint k t`. Named consumer: `exists_joint_diagram`. -/
theorem exists_partial_coordinate (V : Over (Spec (.of k))) [IsIntegral V.left]
    (t : V.left.functionField) :
    ∃ P : V.left.PartialMap (AdditiveGroupScheme.algebraicGroup k 1).carrier,
      P.hom ≫ (AdditiveGroupScheme.algebraicGroup k 1).structureMap = P.domain.ι ≫ V.hom ∧
      P.fromFunctionField = (AffineSchemeAction.linePoint k t).left := by
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  have h : (AffineSchemeAction.linePoint k t).left ≫ L.hom =
      V.left.fromSpecStalk (genericPoint V.left) ≫ V.hom :=
    (Over.w (AffineSchemeAction.linePoint k t)).trans
      (Over.w (SchemeGenericTranslate.genericParameter V)).symm
  let P := Scheme.PartialMap.ofFromSpecStalk V.hom L.hom
    (AffineSchemeAction.linePoint k t).left h
  exact ⟨P, Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _,
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _⟩

/-- The standard affine point action sends a line point with values in any commutative
 coefficient algebra in the base universe to `a*x+b`, with scalars extended from the base.
 Named consumer: `equivariance_on_pullback`. -/
theorem linePoint_comp_pointAct {C : Type u} [CommRing C] [Algebra k C]
    (a : kˣ) (b : k) (x : C) :
    AffineSchemeAction.linePoint k x ≫
      ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
        ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.groupPoint k a b) =
    AffineSchemeAction.linePoint k (algebraMap k C (a : k) * x + algebraMap k C b) := by
  change AffineSchemeAction.linePoint k x ≫ ((toUnit _ ≫ _) • 𝟙 _) = _
  rw [ModObj.comp_smul, Category.comp_id, ← Category.assoc, comp_toUnit]
  have hgroup : toUnit ((Spec (.of C)).asOver (Spec (.of k))) ≫
      ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.groupPoint k a b) =
      AffineSchemeAction.groupPoint k (Units.map (algebraMap k C) a) (algebraMap k C b) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap k C)) ≫
        (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k a b).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        (AffineGroupScheme.eval k (Units.map (algebraMap k C) a) (algebraMap k C b)).toRingHom)
    rw [Category.id_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (show
      (Algebra.ofId k C).comp (AffineGroupScheme.eval k a b) =
        AffineGroupScheme.eval k (Units.map (algebraMap k C) a) (algebraMap k C b) by
      apply AffineGroupScheme.hom_ext <;> simp)
  rw [hgroup]
  exact AffineSchemeAction.lift_groupPoint_linePoint_smul k _ _ _
end
end AclGeom.CurveAffineCoordinate

namespace AclGeom.CurveAffineCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra
  ActionFunctionField.isIso_hom_left

/-- An affine formula for an actual curve automorphism on the same generic coordinate
 gives an actual scheme diagram on the nonempty pullback where both coordinates are
 defined. The open model and generic lift are explicit here; `exists_joint_diagram`
 constructs them internally. No normality assumption is used. -/
theorem equivariance_on_pullback
    (V U : Over (Spec (.of k))) [IsIntegral V.left]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (x : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField)
    (g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U)
    (hgj : g ≫ j = SchemeGenericTranslate.genericParameter V)
    (hgx : g ≫ x = AffineSchemeAction.linePoint k t)
    (e : V ≅ V) (a : kˣ) (b : k)
    (hfield : ActionFunctionField.algEquivOfIso e t =
      algebraMap k V.left.functionField (a : k) * t + algebraMap k V.left.functionField b) :
    Nonempty (pullback (j ≫ e.hom) j).left ∧
      pullback.snd (j ≫ e.hom) j ≫ x =
        pullback.fst (j ≫ e.hom) j ≫ x ≫
          ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
            ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.groupPoint k a b) := by
  let σ := ActionFunctionField.algEquivOfIso e
  let δ : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶
      (Spec V.left.functionField).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op
  have hnat : SchemeGenericTranslate.genericParameter V ≫ e.hom =
      δ ≫ SchemeGenericTranslate.genericParameter V := by
    apply Over.OverMorphism.ext
    exact (Scheme.Hom.fromFunctionField_toPartialMap e.hom.left).symm.trans
      (Scheme.PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom e.hom.left.toPartialMap)
  have hsq : g ≫ (j ≫ e.hom) = (δ ≫ g) ≫ j := by
    rw [← Category.assoc, hgj, hnat, Category.assoc, hgj]
  let D := pullback (j ≫ e.hom) j
  let l : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ D :=
    pullback.lift g (δ ≫ g) hsq
  have hD : Nonempty D.left := ⟨l.left (IsLocalRing.closedPoint V.left.functionField)⟩
  have hpb := (IsPullback.of_hasPullback (j ≫ e.hom) j).map (Over.forget _)
  have : IsOpenImmersion (pullback.fst (j ≫ e.hom) j).left :=
    MorphismProperty.of_isPullback hpb.flip (inferInstance : IsOpenImmersion j.left)
  have : IsOpenImmersion ((pullback.fst (j ≫ e.hom) j) ≫ j).left := by
    change IsOpenImmersion ((pullback.fst (j ≫ e.hom) j).left ≫ j.left)
    infer_instance
  have : IsReduced D.left :=
    isReduced_of_isOpenImmersion ((pullback.fst (j ≫ e.hom) j) ≫ j).left
  have hl : l ≫ (pullback.fst (j ≫ e.hom) j ≫ j) =
      SchemeGenericTranslate.genericParameter V := by
    rw [← Category.assoc, pullback.lift_fst, hgj]
  have : IsDominant (l.left ≫ (pullback.fst (j ≫ e.hom) j ≫ j).left) := by
    rw [← Over.comp_left, hl]
    exact Scheme.isDominant_fromSpecStalk_genericPoint
  have : IsDominant l.left := IsDominant.of_comp_of_isOpenImmersion l.left
    ((pullback.fst (j ≫ e.hom) j) ≫ j).left
  refine ⟨hD, ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated
    (AdditiveGroupScheme.algebraicGroup k 1).structureMap
    ((Over.w _).trans (Over.w _).symm) l.left
  change (l ≫ (pullback.snd (j ≫ e.hom) j ≫ x)).left =
    (l ≫ (pullback.fst (j ≫ e.hom) j ≫ x ≫ _)).left
  rw [← Category.assoc l, pullback.lift_snd, Category.assoc, hgx,
    ← Category.assoc l, pullback.lift_fst, ← Category.assoc g, hgx]
  rw [linePoint_comp_pointAct]
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval t).toRingHom) =
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
      (algebraMap k V.left.functionField (a : k) * t +
        algebraMap k V.left.functionField b)).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (show
    σ.toAlgHom.comp (AffineSchemeAction.lineEval t) =
      AffineSchemeAction.lineEval (algebraMap k V.left.functionField (a : k) * t +
        algebraMap k V.left.functionField b) by
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate,
      AffineSchemeAction.lineEval_lineCoordinate]
    exact hfield)
end
end AclGeom.CurveAffineCoordinate
