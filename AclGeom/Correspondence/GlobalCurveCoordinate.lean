/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ActionOrbitTransitivity
import AclGeom.Correspondence.CurveAffineCoordinate
import AclGeom.Correspondence.IntegralProduct
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Extending the same rational curve coordinate over the whole curve

**Status:** proved criteria (#21). An affine pullback formula for the SAME generic
coordinate makes its translated regular charts compatible. Actual point transitivity
makes these charts cover the original curve. Reduced-source point extensionality and
Mathlib gluing produce the global regular coordinate and its point-action equivariance.
For a connected algebraic group, product integrality gives the joint scheme action
diagram on the whole group times curve. Generic categorical point-action identities keep
composition explicit without expanding the concrete scheme composition definitions.

The coordinate, pointed open, field formula and transitivity are explicit in the criteria.
Named consumer: `CurveGlobalCoordinate.exists_whole_curve_coordinate` constructs all of
them internally from the genuine regular-affine action and actual monic Ga subgroup.
-/

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Named consumer: compatibility on translated coordinate-chart overlaps. -/
theorem coordinate_points_eq
    (G : AlgebraicGroup k) (V U : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (x : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField)
    (g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U)
    (hgj : g ≫ j = SchemeGenericTranslate.genericParameter V)
    (hgx : g ≫ x = AffineSchemeAction.linePoint k t)
    (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    (A : AffineTransformation k)
    (hfield : (ActionFunctionField.functionFieldAction G V q).unop t =
      algebraMap k V.left.functionField (A.multiplier : k) * t +
        algebraMap k V.left.functionField A.shift)
    (p r : 𝟙_ (Over (Spec (.of k))) ⟶ U)
    (hpr : (p ≫ j) ≫ ModObj.pointAct V q = r ≫ j) :
    (p ≫ x) ≫ ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
      ((AffineGroupScheme.pointsMulEquiv k).symm A) = r ≫ x := by
  let e := ModObj.pointAut V q
  have hf : ActionFunctionField.algEquivOfIso e t =
      algebraMap k V.left.functionField (A.multiplier : k) * t +
        algebraMap k V.left.functionField A.shift := hfield
  obtain ⟨_, he⟩ := CurveAffineCoordinate.equivariance_on_pullback V U j x t g hgj hgx
    e A.multiplier A.shift hf
  let l : 𝟙_ (Over (Spec (.of k))) ⟶ pullback (j ≫ e.hom) j :=
    pullback.lift p r (by
      change p ≫ (j ≫ ModObj.pointAct V q) = r ≫ j
      exact (Category.assoc _ _ _).symm.trans hpr)
  have hh := congrArg (fun z ↦ l ≫ z) he
  have hA : (unitIsoSpecAsOver k).hom ≫
      AffineSchemeAction.groupPoint k A.multiplier A.shift =
        (AffineGroupScheme.pointsMulEquiv k).symm A := by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      (AffineGroupScheme.eval k A.multiplier A.shift).toRingHom) = _
    rw [Category.id_comp]
    exact (AffineGroupScheme.pointsMulEquiv_symm_apply_left k A).symm
  rw [hA] at hh
  dsimp only [l] at hh
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using hh.symm
/-- Named consumer: the translated regular coordinates glue on actual chart overlaps. -/
theorem translated_coordinate_points_compatibility
    (G : AlgebraicGroup k) (V U : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (x : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField)
    (gU : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U)
    (hgj : gU ≫ j = SchemeGenericTranslate.genericParameter V)
    (hgx : gU ≫ x = AffineSchemeAction.linePoint k t)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hΦ : ∀ q, (ActionFunctionField.functionFieldAction G V q).unop t =
      algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
        algebraMap k V.left.functionField (Φ q).shift)
    (q r : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    (p z : 𝟙_ (Over (Spec (.of k))) ⟶ U)
    (hp : p ≫ (j ≫ ModObj.pointAct V q) = z ≫ (j ≫ ModObj.pointAct V r)) :
    p ≫ (x ≫ ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
      ((AffineGroupScheme.pointsMulEquiv k).symm (Φ q))) =
    z ≫ (x ≫ ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
      ((AffineGroupScheme.pointsMulEquiv k).symm (Φ r))) := by
  let Y := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let ρ := (AffineGroupScheme.pointsMulEquiv k).symm.toMonoidHom.comp Φ
  have hp' : (p ≫ j) ≫ ModObj.pointAct V q = (z ≫ j) ≫ ModObj.pointAct V r := by
    simpa only [Category.assoc] using hp
  have hmove : (p ≫ j) ≫ ModObj.pointAct V (r⁻¹ * q) = z ≫ j := by
    rw [ModObj.pointAct_mul, ← Category.assoc, hp', Category.assoc,
      ← ModObj.pointAct_mul, inv_mul_cancel, ModObj.pointAct_one, Category.comp_id]
  have hc := coordinate_points_eq G V U j x t gU hgj hgx (r⁻¹ * q)
    (Φ (r⁻¹ * q)) (hΦ _) p z hmove
  change (p ≫ x) ≫ ModObj.pointAct Y (ρ (r⁻¹ * q)) = z ≫ x at hc
  change p ≫ (x ≫ ModObj.pointAct Y (ρ q)) = z ≫ (x ≫ ModObj.pointAct Y (ρ r))
  rw [← Category.assoc p, ← Category.assoc z, ← hc,
    Category.assoc (p ≫ x), ← ModObj.pointAct_mul, ← map_mul, mul_inv_cancel_left]

end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Point compatibility gives actual chart-overlap equality over an ACF base.
Named consumer: gluing the translated regular curve coordinates. -/
theorem pullback_eq_of_point_compatibility
    (X U Y : Over (Spec (.of k))) [IsReduced U.left] [LocallyOfFiniteType U.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (j₁ j₂ : U ⟶ X) [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (f₁ f₂ : U ⟶ Y)
    (hpoints : ∀ p q : 𝟙_ (Over (Spec (.of k))) ⟶ U,
      p ≫ j₁ = q ≫ j₂ → p ≫ f₁ = q ≫ f₂) :
    pullback.fst j₁.left j₂.left ≫ f₁.left =
      pullback.snd j₁.left j₂.left ≫ f₂.left := by
  let W : Over (Spec (.of k)) := Over.mk (pullback.fst j₁.left j₂.left ≫ U.hom)
  let π₁ : W.left ⟶ U.left := pullback.fst j₁.left j₂.left
  have : IsOpenImmersion π₁ := inferInstanceAs
    (IsOpenImmersion (pullback.fst j₁.left j₂.left))
  have : IsReduced W.left := isReduced_of_isOpenImmersion π₁
  have : LocallyOfFiniteType W.hom := by
    change LocallyOfFiniteType (π₁ ≫ U.hom)
    infer_instance
  let p₁ : W ⟶ U := Over.homMk (pullback.fst j₁.left j₂.left) rfl
  let p₂ : W ⟶ U := Over.homMk (pullback.snd j₁.left j₂.left) (by
    change pullback.snd j₁.left j₂.left ≫ U.hom = pullback.fst j₁.left j₂.left ≫ U.hom
    calc
      _ = pullback.snd j₁.left j₂.left ≫ j₂.left ≫ X.hom := by rw [Over.w j₂]
      _ = pullback.fst j₁.left j₂.left ≫ j₁.left ≫ X.hom := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = _ := by rw [Over.w j₁])
  have hp : p₁ ≫ j₁ = p₂ ≫ j₂ := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have he : p₁ ≫ f₁ = p₂ ≫ f₂ := by
    apply AdditiveRigidity.over_hom_ext_of_points
    intro p
    have hh := hpoints (p ≫ p₁) (p ≫ p₂)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ p ≫ z) hp)
    simpa only [Category.assoc] using hh
  exact congrArg Over.Hom.left he
end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M H V U Y : C} [MonObj M] [MonObj H] [ModObj M V] [ModObj H Y]

/-- Named consumer: the whole-curve action diagram from its point-action slices. -/
theorem point_comp_pointAct (p : 𝟙_ C ⟶ V) (q : 𝟙_ C ⟶ M) :
    p ≫ ModObj.pointAct V q = q • p := by
  change p ≫ ((toUnit V ≫ q) • 𝟙 V) = q • p
  rw [ModObj.comp_smul, Category.comp_id, ← Category.assoc, comp_toUnit,
    toUnit_unit, Category.id_comp]

/-- Chart formulas on a transitive action imply pointwise equivariance.
Named consumer: the glued whole-curve coordinate's actual action diagram. -/
theorem point_equivariance_of_chart
    (j : U ⟶ V) (p0 : 𝟙_ C ⟶ U) (xU : U ⟶ Y) (x : V ⟶ Y)
    (ρ : (𝟙_ C ⟶ M) →* (𝟙_ C ⟶ H))
    (hfac : ∀ q, (j ≫ ModObj.pointAct V q) ≫ x = xU ≫ ModObj.pointAct Y (ρ q))
    (htrans : ∀ a b : 𝟙_ C ⟶ V, ∃ q : 𝟙_ C ⟶ M, a ≫ ModObj.pointAct V q = b)
    (q : 𝟙_ C ⟶ M) (p : 𝟙_ C ⟶ V) :
    p ≫ (ModObj.pointAct V q ≫ x) = p ≫ (x ≫ ModObj.pointAct Y (ρ q)) := by
  obtain ⟨r, hr⟩ := htrans (p0 ≫ j) p
  rw [← hr]
  simp only [← Category.assoc]
  have hfr (a : 𝟙_ C ⟶ M) :
      ((p0 ≫ j) ≫ ModObj.pointAct V a) ≫ x =
        (p0 ≫ xU) ≫ ModObj.pointAct Y (ρ a) := by
    simpa only [Category.assoc] using congrArg (fun z ↦ p0 ≫ z) (hfac a)
  calc
    _ = ((p0 ≫ j) ≫ ModObj.pointAct V (q * r)) ≫ x := by
      simp only [ModObj.pointAct_mul, Category.assoc]
    _ = (p0 ≫ xU) ≫ ModObj.pointAct Y (ρ (q * r)) := hfr _
    _ = ((p0 ≫ xU) ≫ ModObj.pointAct Y (ρ r)) ≫ ModObj.pointAct Y (ρ q) := by
      rw [map_mul, ModObj.pointAct_mul]
      simp only [Category.assoc]
    _ = _ := by rw [hfr r]
end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra
  ActionFunctionField.isIso_hom_left

/-- Extend the given rational coordinate using actual translations. Named consumer: the
whole-curve isomorphism in the genuine regular-affine action. Transitivity and the field
coordinate are explicit in this criterion; the final consumer constructs both internally. -/
theorem exists_global_coordinate
    (G : AlgebraicGroup k) (V U : Over (Spec (.of k))) [IsIntegral V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U)
    (xU : U ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField)
    (gU : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U)
    (hgj : gU ≫ j = SchemeGenericTranslate.genericParameter V)
    (hgx : gU ≫ xU = AffineSchemeAction.linePoint k t)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hΦ : ∀ q, (ActionFunctionField.functionFieldAction G V q).unop t =
      algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
        algebraMap k V.left.functionField (Φ q).shift)
    (htrans : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ V,
      ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
        a ≫ ModObj.pointAct V q = b) :
    ∃ x : V ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X,
      j ≫ x = xU ∧ SchemeGenericTranslate.genericParameter V ≫ x =
        AffineSchemeAction.linePoint k t ∧
      ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
        ModObj.pointAct V q ≫ x = x ≫
          ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
            ((AffineGroupScheme.pointsMulEquiv k).symm (Φ q)) := by
  classical
  let GX := G.toGroupScheme.X
  let Y := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let ρ := (AffineGroupScheme.pointsMulEquiv k).symm.toMonoidHom.comp Φ
  let ig (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) := j ≫ ModObj.pointAct V q
  let fg (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) := xU ≫ ModObj.pointAct Y (ρ q)
  let Q := translatedCover G V U j p0 htrans
  have : IsReduced U.left := isReduced_of_isOpenImmersion j.left
  have : LocallyOfFiniteType U.hom := by rw [← Over.w j]; infer_instance
  have hcompat (q r : 𝟙_ (Over (Spec (.of k))) ⟶ GX) :
      pullback.fst (Q.f q) (Q.f r) ≫ (fg q).left =
        pullback.snd (Q.f q) (Q.f r) ≫ (fg r).left := by
    have : IsOpenImmersion (ig q).left := Q.map_prop q
    have : IsOpenImmersion (ig r).left := Q.map_prop r
    exact pullback_eq_of_point_compatibility V U Y (ig q) (ig r) (fg q) (fg r)
      (translated_coordinate_points_compatibility G V U j xU t gU hgj hgx Φ hΦ q r)
  let s : V.left ⟶ Y.left := Q.glueMorphisms (fun q ↦ (fg q).left) hcompat
  have hs : s ≫ Y.hom = V.hom := by
    apply Q.hom_ext
    intro q
    have he := Q.ι_glueMorphisms (fun q ↦ (fg q).left) hcompat q
    have he' : (Q.f q ≫ s) ≫ Y.hom = Q.f q ≫ V.hom :=
      (congrArg (fun z ↦ z ≫ Y.hom) he).trans
        ((Over.w (fg q)).trans (Over.w (ig q)).symm)
    exact (Category.assoc _ _ _).symm.trans he'
  let x : V ⟶ Y := Over.homMk s hs
  have hfac (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : ig q ≫ x = fg q := by
    apply Over.OverMorphism.ext
    exact Q.ι_glueMorphisms (fun q ↦ (fg q).left) hcompat q
  have hjx : j ≫ x = xU := by
    have hh := hfac 1
    change (j ≫ ModObj.pointAct V 1) ≫ x = xU ≫ ModObj.pointAct Y (ρ 1) at hh
    rw [map_one, ModObj.pointAct_one, ModObj.pointAct_one, Category.comp_id,
      Category.comp_id] at hh
    exact hh
  refine ⟨x, hjx, ?_, ?_⟩
  · rw [← hgj, Category.assoc, hjx, hgx]
  · intro q
    apply AdditiveRigidity.over_hom_ext_of_points
    exact point_equivariance_of_chart j p0 xU x ρ hfac htrans q

end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Point-action slices give the actual joint scheme diagram on the whole curve.
Named consumer: the genuine whole-curve coordinate theorem. -/
theorem joint_diagram_of_point_equivariance
    (G : ConnectedAlgebraicGroup k) (V : Over (Spec (.of k))) [IsIntegral V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (f : G.toGroupScheme.X ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X)
    (x : V ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (heq : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q ≫ x = x ≫
        ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X (q ≫ f)) :
    γ[G.toGroupScheme.X, V] ≫ x =
      lift (fst G.toGroupScheme.X V ≫ f) (snd G.toGroupScheme.X V ≫ x) ≫
        AffineSchemeAction.smul k := by
  let GX := G.toGroupScheme.X
  let Y := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  have : IsIntegral (GX ⊗ V).left := isIntegral_pullback_of_isAlgClosed GX.hom V.hom
  have : LocallyOfFiniteType (GX ⊗ V).hom := by
    change LocallyOfFiniteType (pullback.fst GX.hom V.hom ≫ GX.hom)
    infer_instance
  apply AdditiveRigidity.over_hom_ext_of_points
  intro p
  let q := p ≫ fst GX V
  let z := p ≫ snd GX V
  have hp : lift q z = p := by simp [q, z]
  have hh : (z ≫ ModObj.pointAct V q) ≫ x =
      (z ≫ x) ≫ ModObj.pointAct Y (q ≫ f) := by
    simpa only [Category.assoc] using congrArg (fun h ↦ z ≫ h) (heq q)
  rw [point_comp_pointAct, point_comp_pointAct] at hh
  calc
    _ = (q • z) ≫ x := by rw [← hp, ← Category.assoc]; rfl
    _ = (q ≫ f) • (z ≫ x) := hh
    _ = _ := by
      change lift (q ≫ f) (z ≫ x) ≫ AffineSchemeAction.smul k = _
      rw [← hp]
      change lift (q ≫ f) (z ≫ x) ≫ AffineSchemeAction.smul k =
        lift q z ≫ lift (fst GX V ≫ f) (snd GX V ≫ x) ≫ AffineSchemeAction.smul k
      simp only [comp_lift_assoc, lift_fst_assoc, lift_snd_assoc]
end
end AclGeom.CurveGlobalCoordinate
