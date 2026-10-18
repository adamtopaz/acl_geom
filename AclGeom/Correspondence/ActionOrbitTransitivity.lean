/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeAdditiveOrbit
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Actual orbit surjectivity and translated coordinate charts

**Status:** a surjective morphism of locally finite-type schemes over an ACF base is
surjective on base-field points. A surjective actual orbit gives transitivity of the
regular action on those points; translates of any pointed open cover the original scheme.
Named consumer: the whole-curve coordinate in
`CurveGlobalCoordinate.exists_whole_curve_coordinate` (#21). The final consumer supplies
the orbit and transitivity internally from the actual monic Ga subgroup and faithfulness.
-/

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Surjectivity on actual base-field points. Named consumer: the Ga orbit gives
transitivity of the actual regular curve action. -/
theorem surjective_points_of_surjective
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [Surjective f.left] :
    Function.Surjective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q ≫ f) := by
  intro p
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let y := p.left (IsLocalRing.closedPoint k)
  have hy : IsClosed {y} := (GroupScheme.pointsEquivClosedPoints p).property
  have hne : (f.left ⁻¹' ({y} : Set Y.left)).Nonempty := by
    obtain ⟨z, hz⟩ := f.left.surjective y
    exact ⟨z, hz⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
    (hy.preimage f.left.continuous).isLocallyClosed
  have hzc₀ : IsClosed ({z} : Set X.left) := hzc
  let q : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom z hzc₀) (pointOfClosedPoint_comp X.hom z hzc₀)
  refine ⟨q, ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq Y.hom (Over.w (q ≫ f)) (Over.w p)
  change f.left (pointOfClosedPoint X.hom z hzc₀ (IsLocalRing.closedPoint k)) = y
  exact (congrArg f.left
    (pointOfClosedPoint_apply X.hom z hzc₀ (IsLocalRing.closedPoint k))).trans hz

/-- Named consumer: translate the existing coordinate chart to cover the whole curve. -/
theorem transitive_points_of_surjective_orbit
    (G : AlgebraicGroup k) (N V : Over (Spec (.of k)))
    [LocallyOfFiniteType N.hom] [LocallyOfFiniteType V.hom]
    [ModObj G.toGroupScheme.X V] (i : N ⟶ G.toGroupScheme.X)
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ V)
    [Surjective (AdditiveOrbit.orbitMap i p).left]
    (a b : 𝟙_ (Over (Spec (.of k))) ⟶ V) :
    ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      a ≫ ModObj.pointAct V q = b := by
  obtain ⟨r, hr⟩ := surjective_points_of_surjective (AdditiveOrbit.orbitMap i p) a
  obtain ⟨s, hs⟩ := surjective_points_of_surjective (AdditiveOrbit.orbitMap i p) b
  change r ≫ AdditiveOrbit.orbitMap i p = a at hr
  change s ≫ AdditiveOrbit.orbitMap i p = b at hs
  refine ⟨(s ≫ i) * (r ≫ i)⁻¹, ?_⟩
  rw [← hr, ← hs, AdditiveOrbit.point_comp_orbitMap, AdditiveOrbit.point_comp_orbitMap,
    Category.assoc, ← ModObj.pointAct_mul]
  congr 2
  rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
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

/-- Actual translates of a pointed open cover a point-transitive scheme.
Named consumer: extension of the same rational curve coordinate. -/
def translatedCover
    (G : AlgebraicGroup k) (V U : Over (Spec (.of k)))
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U)
    (htrans : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ V,
      ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
        a ≫ ModObj.pointAct V q = b) : V.left.OpenCover := by
  classical
  let GX := G.toGroupScheme.X
  let ig (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) := j ≫ ModObj.pointAct V q
  have hi (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : IsOpenImmersion (ig q).left := by
    have : IsIso (ModObj.pointAct V q).left := by
      change IsIso (((Over.forget (Spec (.of k))).mapIso (ModObj.pointAut V q)).hom)
      infer_instance
    change IsOpenImmersion (j.left ≫ (ModObj.pointAct V q).left)
    infer_instance
  have hcover (z : V.left) : ∃ q w, (ig q).left w = z := by
    have : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
    let S : Set V.left := ⋃ q, Set.range (ig q).left
    have hopen : IsOpen S := isOpen_iUnion fun q ↦ by
      have := hi q
      exact IsOpenImmersion.isOpen_range _
    have hclosed (w : V.left) (hw : IsClosed {w}) : w ∈ S := by
      let b : 𝟙_ (Over (Spec (.of k))) ⟶ V :=
        Over.homMk (pointOfClosedPoint V.hom w hw) (pointOfClosedPoint_comp V.hom w hw)
      obtain ⟨q, hq⟩ := htrans (p0 ≫ j) b
      have hpoint : (ig q).left (p0.left (IsLocalRing.closedPoint k)) = w := by
        have hh := congrArg (fun z ↦ z.left (IsLocalRing.closedPoint k)) hq
        exact hh.trans (pointOfClosedPoint_apply V.hom w hw _)
      exact Set.mem_iUnion.mpr ⟨q, _, hpoint⟩
    have hzero : Sᶜ ∩ closedPoints V.left = ∅ := by
      ext w
      constructor
      · intro hw
        exact hw.1 (hclosed w hw.2)
      · intro hw
        exact hw.elim
    have hempty : Sᶜ = ∅ := by
      have hh := closure_inter_closedPoints hopen.isClosed_compl
      rw [hzero, closure_empty] at hh
      exact hh.symm
    have hz : z ∈ S := by
      by_contra hn
      have : z ∈ Sᶜ := hn
      rw [hempty] at this
      exact this
    exact Set.mem_iUnion.mp hz
  exact Scheme.Cover.mkOfCovers
    (𝟙_ (Over (Spec (.of k))) ⟶ GX) (fun _ ↦ U.left) (fun q ↦ (ig q).left) hcover hi

end
end AclGeom.CurveGlobalCoordinate
