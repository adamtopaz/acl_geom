/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.IntegralProduct
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Regular group morphisms from a nonempty open

**Status:** proved extension criterion over an ACF base (#21). An actual homomorphism of
k-points of a connected algebraic-group package, agreeing with a regular map on one actual
open with a supplied point, extends to a group-scheme morphism with that point map. The
open-model premises are explicit. Named consumer: `SchemeAffineMorphism` constructs them
internally from the actual curve action. Translated opens cover by the Jacobson property;
Mathlib point extensionality and gluing give the morphism and actual group-law diagrams.
-/

namespace AclGeom.RegularGroupMorphism

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Actual morphisms over an ACF base are determined by all base-field points when the
 source is reduced and locally finite type and the target is separated and locally finite
 type. Named consumer: overlap and multiplication compatibility in global group gluing. -/
private theorem hom_ext_points (X Y : Over (Spec (.of k))) [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  refine AlgebraicGeometry.ext_of_apply_eq Y.hom Set.univ isClosed_univ.isLocallyClosed
    dense_univ ?_ ((Over.w f).trans (Over.w g).symm)
  intro x _ hx
  let p : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
  have he := congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ Y ↦
    q.left (IsLocalRing.closedPoint k)) (h p)
  change f.left (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint k)) =
    g.left (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint k)) at he
  have hp : pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint k) = x :=
    AlgebraicGeometry.pointOfClosedPoint_apply X.hom x hx _
  simpa only [hp] using he

end

end AclGeom.RegularGroupMorphism

namespace AclGeom.RegularGroupMorphism

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem translated_isOpenImmersion (G : AlgebraicGroup k)
    (U : Over (Spec (.of k))) (j : U ⟶ G.toGroupScheme.X) [IsOpenImmersion j.left]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    IsOpenImmersion (j ≫ GroupScheme.leftMul G.toGroupScheme.X g).left := by
  have : IsIso (GroupScheme.leftMul G.toGroupScheme.X g).left := by
    change IsIso (((Over.forget (Spec (.of k))).mapIso (GroupScheme.leftMulIso g)).hom)
    infer_instance
  change IsOpenImmersion (j.left ≫ (GroupScheme.leftMul G.toGroupScheme.X g).left)
  infer_instance

private theorem translated_covers (G : AlgebraicGroup k)
    (U : Over (Spec (.of k))) (j : U ⟶ G.toGroupScheme.X) [IsOpenImmersion j.left]
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U) (x : G.carrier) :
    ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) (y : U.left),
      (j ≫ GroupScheme.leftMul G.toGroupScheme.X g).left y = x := by
  classical
  have : JacobsonSpace G.carrier := LocallyOfFiniteType.jacobsonSpace G.structureMap
  let S : Set G.carrier := ⋃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
    Set.range (j ≫ GroupScheme.leftMul G.toGroupScheme.X g).left
  have hopen : IsOpen S := isOpen_iUnion fun g ↦ by
    have := translated_isOpenImmersion G U j g
    exact IsOpenImmersion.isOpen_range _
  have hclosed (z : G.carrier) (hz : IsClosed {z}) : z ∈ S := by
    let q := GroupScheme.pointsEquivClosedPoints.symm ⟨z, hz⟩
    let g := q * (p0 ≫ j)⁻¹
    have hq : q.left (IsLocalRing.closedPoint k) = z := by
      have h := congrArg Subtype.val
        (GroupScheme.pointsEquivClosedPoints.apply_symm_apply ⟨z, hz⟩)
      exact h
    have hp : p0 ≫ (j ≫ GroupScheme.leftMul G.toGroupScheme.X g) = q := by
      rw [← Category.assoc, GroupScheme.point_comp_leftMul]
      dsimp only [g]
      rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    refine Set.mem_iUnion.mpr ⟨g, p0.left (IsLocalRing.closedPoint k), ?_⟩
    change (p0 ≫ (j ≫ GroupScheme.leftMul G.toGroupScheme.X g)).left
      (IsLocalRing.closedPoint k) = z
    rw [hp]
    exact hq
  have hzero : Sᶜ ∩ closedPoints G.carrier = ∅ := by
    ext z
    constructor
    · intro hz
      exact hz.1 (hclosed z hz.2)
    · intro hz
      exact hz.elim
  have hempty : Sᶜ = ∅ := by
    have h := closure_inter_closedPoints hopen.isClosed_compl
    rw [hzero, closure_empty] at h
    exact h.symm
  have hx : x ∈ S := by
    by_contra hn
    have : x ∈ Sᶜ := hn
    rw [hempty] at this
    exact this
  obtain ⟨g, y, hy⟩ := Set.mem_iUnion.mp hx
  exact ⟨g, y, hy⟩

/-- Every actual point translates a given nonempty group open into a cover of the group.
 Named consumer: extension of the rational affine coefficient map to the entire group. -/
private def translatedCover (G : AlgebraicGroup k)
    (U : Over (Spec (.of k))) (j : U ⟶ G.toGroupScheme.X) [IsOpenImmersion j.left]
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U) : G.carrier.OpenCover :=
  Scheme.Cover.mkOfCovers (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    (fun _ ↦ U.left) (fun g ↦ (j ≫ GroupScheme.leftMul G.toGroupScheme.X g).left)
    (translated_covers G U j p0) (translated_isOpenImmersion G U j)

end

end AclGeom.RegularGroupMorphism

namespace AclGeom.RegularGroupMorphism

noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A homomorphism on the actual group points that is regular on one actual nonempty open
 extends to a group-scheme homomorphism. Named consumer: the genuine affine-action morphism. -/
theorem exists_extension (G : ConnectedAlgebraicGroup k) (H : AlgebraicGroup k)
    (U : Over (Spec (.of k))) (j : U ⟶ G.toGroupScheme.X) [IsOpenImmersion j.left]
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →*
      (𝟙_ (Over (Spec (.of k))) ⟶ H.toGroupScheme.X))
    (fU : U ⟶ H.toGroupScheme.X)
    (hU : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ U, p ≫ fU = Φ (p ≫ j)) :
    ∃ f : G.toAlgebraicGroup.Hom H, ∀ q, q ≫ f.hom.hom = Φ q := by
  classical
  let GX := G.toGroupScheme.X
  let HX := H.toGroupScheme.X
  let ig (g : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : U ⟶ GX :=
    j ≫ GroupScheme.leftMul GX g
  let fg (g : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : U ⟶ HX :=
    fU ≫ GroupScheme.leftMul HX (Φ g)
  let Q := translatedCover G.toAlgebraicGroup U j p0
  have : IsReduced U.left := isReduced_of_isOpenImmersion j.left
  have : LocallyOfFiniteType U.hom := by
    rw [← Over.w j]
    infer_instance
  have hlocal (g : 𝟙_ (Over (Spec (.of k))) ⟶ GX)
      (p : 𝟙_ (Over (Spec (.of k))) ⟶ U) : p ≫ fg g = Φ (p ≫ ig g) := by
    dsimp only [fg, ig]
    rw [← Category.assoc, GroupScheme.point_comp_leftMul, hU, ← Φ.map_mul,
      ← GroupScheme.point_comp_leftMul, Category.assoc]
  have hcompat (g h : 𝟙_ (Over (Spec (.of k))) ⟶ GX) :
      pullback.fst (Q.f g) (Q.f h) ≫ (fg g).left =
        pullback.snd (Q.f g) (Q.f h) ≫ (fg h).left := by
    let W : Over (Spec (.of k)) := Over.mk (pullback.fst (Q.f g) (Q.f h) ≫ U.hom)
    have : IsOpenImmersion (Q.f g) := Q.map_prop g
    have : IsOpenImmersion (Q.f h) := Q.map_prop h
    have : IsOpenImmersion (pullback.fst (Q.f g) (Q.f h)) := inferInstance
    let π1 : W.left ⟶ U.left := pullback.fst (Q.f g) (Q.f h)
    have : IsOpenImmersion π1 := inferInstanceAs
      (IsOpenImmersion (pullback.fst (Q.f g) (Q.f h)))
    have : IsReduced W.left := isReduced_of_isOpenImmersion π1
    have : LocallyOfFiniteType π1 := inferInstance
    have : LocallyOfFiniteType W.hom := by
      change LocallyOfFiniteType (π1 ≫ U.hom)
      infer_instance
    have hg : Q.f g ≫ GX.hom = U.hom := Over.w (ig g)
    have hh : Q.f h ≫ GX.hom = U.hom := Over.w (ig h)
    let p1 : W ⟶ U := Over.homMk (pullback.fst (Q.f g) (Q.f h)) rfl
    let p2 : W ⟶ U := Over.homMk (pullback.snd (Q.f g) (Q.f h)) (by
      change pullback.snd (Q.f g) (Q.f h) ≫ U.hom =
        pullback.fst (Q.f g) (Q.f h) ≫ U.hom
      calc
        _ = pullback.snd (Q.f g) (Q.f h) ≫ Q.f h ≫ GX.hom := by rw [hh]
        _ = pullback.fst (Q.f g) (Q.f h) ≫ Q.f g ≫ GX.hom := by
          rw [← Category.assoc, ← pullback.condition, Category.assoc]
        _ = _ := by rw [hg])
    have hp : p1 ≫ ig g = p2 ≫ ig h := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have he := hom_ext_points W HX (p1 ≫ fg g) (p2 ≫ fg h) (fun p ↦ by
      calc
        _ = (p ≫ p1) ≫ fg g := (Category.assoc _ _ _).symm
        _ = Φ ((p ≫ p1) ≫ ig g) := hlocal g (p ≫ p1)
        _ = Φ ((p ≫ p2) ≫ ig h) := by rw [Category.assoc, hp, ← Category.assoc]
        _ = (p ≫ p2) ≫ fg h := (hlocal h (p ≫ p2)).symm
        _ = _ := Category.assoc _ _ _)
    exact congrArg (fun f : W ⟶ HX ↦ f.left) he
  let s : GX.left ⟶ HX.left := Q.glueMorphisms (fun g ↦ (fg g).left) hcompat
  have hs : s ≫ HX.hom = GX.hom := by
    apply Q.hom_ext
    intro g
    have he : Q.f g ≫ s = (fg g).left :=
      Q.ι_glueMorphisms (fun g ↦ (fg g).left) hcompat g
    have he' : (Q.f g ≫ s) ≫ HX.hom = Q.f g ≫ GX.hom :=
      (congrArg (fun t : U.left ⟶ HX.left ↦ t ≫ HX.hom) he).trans
        ((Over.w (fg g)).trans (Over.w (ig g)).symm)
    exact (Category.assoc (Q.f g) s HX.hom).symm.trans he'
  let f : GX ⟶ HX := Over.homMk s hs
  have hfac (g : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : ig g ≫ f = fg g := by
    apply Over.OverMorphism.ext
    exact Q.ι_glueMorphisms (fun g ↦ (fg g).left) hcompat g
  have hpoint (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : q ≫ f = Φ q := by
    let g := q * (p0 ≫ j)⁻¹
    have hp : p0 ≫ ig g = q := by
      dsimp only [ig]
      rw [← Category.assoc, GroupScheme.point_comp_leftMul]
      dsimp only [g]
      rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    calc
      _ = (p0 ≫ ig g) ≫ f := by rw [hp]
      _ = p0 ≫ fg g := by rw [Category.assoc, hfac]
      _ = Φ (p0 ≫ ig g) := hlocal g p0
      _ = _ := by rw [hp]
  have hone : η[GX] ≫ f = η[HX] := by
    change (1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX) ≫ f = 1
    exact (hpoint 1).trans Φ.map_one
  have hmul : μ[GX] ≫ f = (f ⊗ₘ f) ≫ μ[HX] := by
    have : IsIntegral (GX ⊗ GX).left :=
      isIntegral_pullback_of_isAlgClosed GX.hom GX.hom
    have : LocallyOfFiniteType GX.hom := G.locallyOfFiniteType
    have : LocallyOfFiniteType (pullback.fst GX.hom GX.hom) := inferInstance
    have : LocallyOfFiniteType (GX ⊗ GX).hom := by
      change LocallyOfFiniteType (pullback.fst GX.hom GX.hom ≫ GX.hom)
      infer_instance
    apply hom_ext_points (GX ⊗ GX) HX
    intro p
    calc
      _ = ((p ≫ fst GX GX) * (p ≫ snd GX GX)) ≫ f := by
        rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
      _ = Φ ((p ≫ fst GX GX) * (p ≫ snd GX GX)) := hpoint _
      _ = Φ (p ≫ fst GX GX) * Φ (p ≫ snd GX GX) := Φ.map_mul _ _
      _ = ((p ≫ fst GX GX) ≫ f) * ((p ≫ snd GX GX) ≫ f) := by rw [hpoint, hpoint]
      _ = _ := by
        simp only [MonObj.mul_eq_mul, MonObj.comp_mul, Category.assoc,
          tensorHom_fst, tensorHom_snd]
  exact ⟨Grp.homMk'' f hone hmul, hpoint⟩

end

end AclGeom.RegularGroupMorphism
