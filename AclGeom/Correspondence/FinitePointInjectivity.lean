/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Finite maps detected by their actual base-field points

**Status:** over an ACF base, a finite morphism from a locally finite-type scheme,
injective on base-field points, is universally injective. Its relative diagonal is closed;
Jacobson density of closed points makes that diagonal surjective. With scheme surjectivity,
the underlying map is a homeomorphism. No degree-one or scheme-isomorphism claim is made.
Named consumer: the dimension of the actual closed normal subgroup image in
`NormalTranslation.image_eq_translations` (#21).
-/

namespace AclGeom.GroupFinite
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Named consumer: the normal subgroup's image has its original dimension. -/
theorem universallyInjective_of_point_injective
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q ≫ f)) :
    UniversallyInjective f.left := by
  let W : Over (Spec (.of k)) := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  have : LocallyOfFiniteType W.hom := by
    change LocallyOfFiniteType (pullback.fst f.left f.left ≫ X.hom)
    infer_instance
  have : JacobsonSpace W.left := LocallyOfFiniteType.jacobsonSpace W.hom
  let p1 : W ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let p2 : W ⟶ X := Over.homMk (pullback.snd f.left f.left) (by
    calc
      _ = pullback.snd f.left f.left ≫ f.left ≫ Y.hom := by rw [Over.w f]
      _ = pullback.fst f.left f.left ≫ f.left ≫ Y.hom := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = pullback.fst f.left f.left ≫ X.hom := by rw [Over.w f]
      _ = _ := rfl)
  have hfac : p1 ≫ f = p2 ≫ f := Over.OverMorphism.ext pullback.condition
  have hclosed (w : W.left) (hw : IsClosed {w}) :
      w ∈ Set.range (pullback.diagonal f.left) := by
    let p : 𝟙_ (Over (Spec (.of k))) ⟶ W :=
      Over.homMk (pointOfClosedPoint W.hom w hw) (pointOfClosedPoint_comp W.hom w hw)
    have heq : p ≫ p1 = p ≫ p2 := hinj (by
      change (p ≫ p1) ≫ f = (p ≫ p2) ≫ f
      rw [Category.assoc, hfac, ← Category.assoc])
    have hdiag : (p ≫ p1).left ≫ pullback.diagonal f.left = p.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        rfl
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q.left) heq
    refine ⟨(p ≫ p1).left (IsLocalRing.closedPoint k), ?_⟩
    have hh := congrArg (fun q ↦ q (IsLocalRing.closedPoint k)) hdiag
    exact hh.trans (pointOfClosedPoint_apply W.hom w hw _)
  have hc : closure (closedPoints W.left) ⊆ Set.range (pullback.diagonal f.left) :=
    closure_minimal (fun w hw ↦ hclosed w hw)
      (pullback.diagonal f.left).isClosedMap.isClosed_range
  have hd : closure (closedPoints W.left) = Set.univ := by
    simpa only [Set.univ_inter, closure_univ] using
      closure_inter_closedPoints (isClosed_univ : IsClosed (Set.univ : Set W.left))
  rw [hd] at hc
  apply (UniversallyInjective.iff_diagonal f.left).mpr
  exact ⟨fun w ↦ hc (Set.mem_univ w)⟩

/-- Named consumer: carry the actual normal subgroup's dimension to its closed image. -/
theorem isHomeomorph_of_finite_surjective_point_injective
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q ≫ f)) :
    IsHomeomorph f.left := by
  have := universallyInjective_of_point_injective f hinj
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f.left.continuous, f.left.isClosedMap, f.left.injective, f.left.surjective⟩

end
end AclGeom.GroupFinite
