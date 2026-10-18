/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveAffineCoordinate
import AclGeom.Correspondence.IntegralProduct

/-!
# The joint affine curve-action diagram

**Status:** proved criterion (#21). The SAME supplied generic coordinate and actual group
morphism, with their affine field formula on every base-field group point, construct a
regular coordinate on an actual nonempty curve open and the actual joint scheme action
diagram on a nonempty open of the group times the curve. Every open and generic lift is
chosen internally. Product integrality and Mathlib point extensionality prove the joint
identity. Named consumer: `SchemeAffineCurveDiagram` supplies all premises internally.
This criterion does not assert that the coordinate map is finite or an open immersion.
-/

namespace AclGeom.CurveAffineCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra
  ActionFunctionField.isIso_hom_left

/-- The supplied affine field formula for an actual group morphism gives a regular curve
 coordinate with the SAME generic value and an actual joint scheme action diagram on a
 nonempty open of the group times the curve. All opens and generic lifts are chosen
 internally. Named consumer: `SchemeAffineCurveDiagram.exists_curve_action_diagram`. -/
theorem exists_joint_diagram
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    [ModObj G.toGroupScheme.X V]
    (t : V.left.functionField)
    (f : G.toGroupScheme.X ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X)
    (hfield : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f)).multiplier : k) * t +
        algebraMap k V.left.functionField (AffineGroupScheme.pointsMulEquiv k (q ≫ f)).shift) :
    ∃ (U : Over (Spec (.of k))) (j : U ⟶ V)
      (x : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
      (g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧
      g ≫ j = SchemeGenericTranslate.genericParameter V ∧
      g ≫ x = AffineSchemeAction.linePoint k t ∧
      ∃ (D : Over (Spec (.of k))) (i : D ⟶ G.toGroupScheme.X ⊗ V)
        (s z : D ⟶ U), IsOpenImmersion i.left ∧ Nonempty D.left ∧
        s ≫ j = i ≫ snd G.toGroupScheme.X V ∧
        z ≫ j = i ≫ γ[G.toGroupScheme.X, V] ∧
        z ≫ x = lift (i ≫ fst G.toGroupScheme.X V ≫ f) (s ≫ x) ≫ AffineSchemeAction.smul k := by
  classical
  let GX := G.toGroupScheme.X
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  obtain ⟨P, hPbase, hPgen⟩ := exists_partial_coordinate V t
  let U : Over (Spec (.of k)) := Over.mk (P.domain.ι ≫ V.hom)
  let j : U ⟶ V := Over.homMk P.domain.ι
  let x : U ⟶ L := Over.homMk P.hom hPbase
  let g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U :=
    Over.homMk P.genericLift (by
      change P.genericLift ≫ (P.domain.ι ≫ V.hom) = _
      rw [← Category.assoc, P.genericLift_ι]
      exact Over.w (SchemeGenericTranslate.genericParameter V))
  have hgj : g ≫ j = SchemeGenericTranslate.genericParameter V :=
    Over.OverMorphism.ext P.genericLift_ι
  have hgx : g ≫ x = AffineSchemeAction.linePoint k t := Over.OverMorphism.ext hPgen
  have hU : Nonempty U.left := ⟨g.left (IsLocalRing.closedPoint V.left.functionField)⟩
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion P.domain.ι
    infer_instance
  have : IsIntegral U.left := isIntegral_of_isOpenImmersion j.left
  have : LocallyOfFiniteType U.hom := by rw [← Over.w j]; infer_instance
  have : IsIntegral (GX ⊗ U).left := isIntegral_pullback_of_isAlgClosed GX.hom U.hom
  have : LocallyOfFiniteType (GX ⊗ U).hom := by
    change LocallyOfFiniteType (pullback.fst GX.hom U.hom ≫ GX.hom)
    infer_instance
  let m : GX ⊗ U ⟶ V := GX ◁ j ≫ γ[GX, V]
  let D := pullback m j
  let i : D ⟶ GX ⊗ V := pullback.fst m j ≫ GX ◁ j
  let s : D ⟶ U := pullback.fst m j ≫ snd GX U
  let z : D ⟶ U := pullback.snd m j
  have hpb := (IsPullback.of_hasPullback m j).map (Over.forget _)
  have hfst : IsOpenImmersion (pullback.fst m j).left :=
    MorphismProperty.of_isPullback hpb.flip (inferInstance : IsOpenImmersion j.left)
  have hwhisker : IsOpenImmersion (GX ◁ j).left := by
    rw [Over.whiskerLeft_left]
    infer_instance
  have hi : IsOpenImmersion i.left := by
    change IsOpenImmersion ((pullback.fst m j).left ≫ (GX ◁ j).left)
    infer_instance
  have hsj : s ≫ j = i ≫ snd GX V := by simp [s, i]
  have hzj : z ≫ j = i ≫ γ[GX, V] := (pullback.condition (f := m) (g := j)).symm
  let pg : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ GX ⊗ U := lift 1 g
  have hpg : pg ≫ m = g ≫ j := by
    dsimp only [pg, m]
    rw [lift_whiskerLeft_assoc]
    change (1 : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ GX) • (g ≫ j) = _
    exact _root_.one_smul _ _
  let pd : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ D := pullback.lift pg g hpg
  have hD : Nonempty D.left := ⟨pd.left (IsLocalRing.closedPoint V.left.functionField)⟩
  have : IsReduced D.left := isReduced_of_isOpenImmersion (pullback.fst m j).left
  have : LocallyOfFiniteType D.hom := by
    rw [← Over.w (pullback.fst m j)]
    infer_instance
  refine ⟨U, j, x, g, hj, hU, hgj, hgx, D, i, s, z, hi, hD, hsj, hzj, ?_⟩
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType ((z ≫ x).left ≫ L.hom) := by
    rw [Over.w (z ≫ x)]
    infer_instance
  refine AlgebraicGeometry.ext_of_apply_eq L.hom Set.univ isClosed_univ.isLocallyClosed
    dense_univ ?_ ((Over.w _).trans (Over.w _).symm)
  intro y _ hy
  let p : 𝟙_ (Over (Spec (.of k))) ⟶ D :=
    Over.homMk (pointOfClosedPoint D.hom y hy) (pointOfClosedPoint_comp D.hom y hy)
  let q : 𝟙_ (Over (Spec (.of k))) ⟶ GX := p ≫ i ≫ fst GX V
  let u : 𝟙_ (Over (Spec (.of k))) ⟶ U := p ≫ s
  let v : 𝟙_ (Over (Spec (.of k))) ⟶ U := p ≫ z
  let φ := AffineGroupScheme.pointsMulEquiv k (q ≫ f)
  have hqf : q ≫ f = (unitIsoSpecAsOver k).hom ≫
      AffineSchemeAction.groupPoint k φ.multiplier φ.shift := by
    calc
      q ≫ f = (AffineGroupScheme.pointsMulEquiv k).symm φ :=
        ((AffineGroupScheme.pointsMulEquiv k).symm_apply_apply _).symm
      _ = _ := by
        apply Over.OverMorphism.ext
        exact (AffineGroupScheme.pointsMulEquiv_symm_apply_left k φ).trans (Category.id_comp _).symm
  have huv : u ≫ (j ≫ (ModObj.pointAut V q).hom) = v ≫ j := by
    have hqu : q • (u ≫ j) = v ≫ j := by
      change lift q (u ≫ j) ≫ γ[GX, V] = _
      have hl : lift q (u ≫ j) = p ≫ i := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [q]
        · simp only [lift_snd]
          dsimp only [u]
          rw [Category.assoc, hsj]
          exact (Category.assoc p i (snd GX V)).symm
      rw [hl, Category.assoc, ← hzj]
      exact (Category.assoc p z j).symm
    change u ≫ (j ≫ ((toUnit V ≫ q) • 𝟙 V)) = _
    rw [← Category.assoc, ModObj.comp_smul, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp, Category.comp_id]
    exact hqu
  obtain ⟨_, heq⟩ := equivariance_on_pullback V U j x t g hgj hgx
    (ModObj.pointAut V q) φ.multiplier φ.shift (hfield q)
  let pq := pullback.lift u v huv
  have hpcoord : v ≫ x = u ≫ x ≫ ModObj.pointAct L (q ≫ f) := by
    have h := congrArg (fun h ↦ pq ≫ h) heq
    dsimp only [pq] at h
    simpa only [pullback.lift_snd_assoc, pullback.lift_fst_assoc, hqf] using h
  have hp : p ≫ (z ≫ x) =
      p ≫ (lift (i ≫ fst GX V ≫ f) (s ≫ x) ≫ AffineSchemeAction.smul k) := by
    change v ≫ x = _
    rw [hpcoord]
    change (u ≫ x) ≫ ((toUnit L ≫ (q ≫ f)) • 𝟙 L) = _
    rw [ModObj.comp_smul, ← Category.assoc, comp_toUnit, toUnit_unit,
      Category.id_comp, Category.comp_id, Hom.smul_def, comp_lift_assoc]
    rfl
  have he := congrArg (fun h : 𝟙_ (Over (Spec (.of k))) ⟶ L ↦
    h.left (IsLocalRing.closedPoint k)) hp
  have hpy : p.left (IsLocalRing.closedPoint k) = y := pointOfClosedPoint_apply D.hom y hy _
  change (z ≫ x).left (p.left (IsLocalRing.closedPoint k)) =
    (lift (i ≫ fst GX V ≫ f) (s ≫ x) ≫ AffineSchemeAction.smul k).left
      (p.left (IsLocalRing.closedPoint k)) at he
  rw [hpy] at he
  exact he
end
end AclGeom.CurveAffineCoordinate
