/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.BirationalStalkIsomorphism
import AclGeom.Correspondence.ProperCurveExtension

/-!
# Inverse Domain

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

set_option backward.isDefEq.respectTransparency false in
/-- A rational inverse is defined at every image point of a morphism that is an
isomorphism on actual stalks. The scoped elaborator option unfolds the concrete
stalk endpoints during categorical rewriting; kernel checking is unchanged.
Named consumer: the actual completion open embedding. -/
theorem inverse_domain_contains_image
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsDominant f.left]
    [IsIso f.left.toPartialMap.functionFieldMap]
    (hstalk : ∀ x : X.left, IsIso (f.left.stalkMap x))
    (g : Y.left.RationalMap X.left)
    (hg : Spec.map f.left.toPartialMap.functionFieldMap ≫ g.fromFunctionField =
      X.left.fromSpecStalk (genericPoint X.left)) :
    ∀ x : X.left, f.left x ∈ g.domain := by
  intro x
  have := hstalk x
  let y := f.left x
  let u := f.left.stalkMap x
  let φ := Spec.map (inv u) ≫ X.left.fromSpecStalk x
  have hφf : φ ≫ f.left = Y.left.fromSpecStalk y := by
    dsimp only [φ]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f.left,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hφbase : φ ≫ X.hom = Y.left.fromSpecStalk y ≫ Y.hom := by
    rw [← Over.w f, ← Category.assoc, hφf]
  have hφgeneric : Spec.map (CommRingCat.ofHom
      (algebraMap (Y.left.presheaf.stalk y) Y.left.functionField)) ≫ φ =
        g.fromFunctionField := by
    apply (cancel_epi (Spec.map f.left.toPartialMap.functionFieldMap)).mp
    rw [← Category.assoc, ← Spec.map_comp,
      CurvePointsPlaces.functionFieldMap_stalkMap f.left x,
      Spec.map_comp, Category.assoc]
    dsimp only [φ]
    rw [← Category.assoc (Spec.map u), ← Spec.map_comp,
      IsIso.inv_hom_id, Spec.map_id, Category.id_comp]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (genericPoint_specializes x)).trans hg.symm
  let p := Scheme.PartialMap.ofFromSpecStalk Y.hom X.hom φ hφbase
  have hy : y ∈ p.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk Y.hom X.hom φ hφbase
  have hp : p.fromSpecStalkOfMem hy = φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk Y.hom X.hom φ hφbase
  have hη : genericPoint Y.left ∈ p.domain :=
    (genericPoint_specializes y).mem_open p.domain.2 hy
  have hfac : Spec.map (CommRingCat.ofHom
      (algebraMap (Y.left.presheaf.stalk y) Y.left.functionField)) ≫
      p.domain.fromSpecStalkOfMem y hy =
        p.domain.fromSpecStalkOfMem (genericPoint Y.left) hη := by
    apply (cancel_mono p.domain.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hpg : p.toRationalMap = g := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
    change p.domain.fromSpecStalkOfMem (genericPoint Y.left) hη ≫ p.hom = _
    rw [← hfac, Category.assoc]
    change _ ≫ p.fromSpecStalkOfMem hy = _
    rw [hp]
    exact hφgeneric
  exact Scheme.RationalMap.mem_domain.mpr ⟨p, hy, hpg⟩

end
end AclGeom.CurveCompletion
