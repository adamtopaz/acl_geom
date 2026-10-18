/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.InverseDomain
/-!
# Open Embedding From Inverse

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

set_option backward.isDefEq.respectTransparency false in
/-- A morphism with a rational inverse defined at its whole image is an actual open
immersion. The scoped elaborator option unfolds partial-map endpoints during categorical
rewriting; all kernel checking remains enabled. Named consumer: the curve completion embedding. -/
theorem isOpenImmersion_of_inverse_domain
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    (f : X ⟶ Y) [IsDominant f]
    (g : Y.RationalMap X)
    (hg : Spec.map f.toPartialMap.functionFieldMap ≫ g.fromFunctionField =
      X.fromSpecStalk (genericPoint X))
    (hgf : g.compHom f = Scheme.RationalMap.id Y)
    (hdom : ∀ x : X, f x ∈ g.domain) : IsOpenImmersion f := by
  let p := g.toPartialMap
  have hrange : Set.range f ⊆ Set.range p.domain.ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨f x, hdom x⟩, rfl⟩
  let j := IsOpenImmersion.lift p.domain.ι f hrange
  have hj : j ≫ p.domain.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hη : genericPoint Y ∈ p.domain :=
    (genericPoint_specializes (f (genericPoint X))).mem_open p.domain.2
      (hdom (genericPoint X))
  have hgen : X.fromSpecStalk (genericPoint X) ≫ j =
      Spec.map f.toPartialMap.functionFieldMap ≫
        p.domain.fromSpecStalkOfMem (genericPoint Y) hη := by
    apply (cancel_mono p.domain.ι).mp
    rw [Category.assoc, hj, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (Scheme.Hom.fromFunctionField_toPartialMap f).symm.trans
      (Scheme.PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom f.toPartialMap)
  have : IsDominant (X.fromSpecStalk (genericPoint X)) :=
    Scheme.isDominant_fromSpecStalk_genericPoint
  have hjp : j ≫ p.hom = 𝟙 X := by
    apply ext_of_isDominant (X.fromSpecStalk (genericPoint X))
    rw [← Category.assoc, hgen, Category.assoc, Category.comp_id]
    change Spec.map f.toPartialMap.functionFieldMap ≫ p.fromFunctionField = _
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      g.toRationalMap_toPartialMap]
    exact hg
  have hpf : p.hom ≫ f = p.domain.ι := by
    have he : (p.compHom f).toRationalMap = (𝟙 Y : Y ⟶ Y).toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, g.toRationalMap_toPartialMap, hgf]
    have hh := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := ⊤_ Scheme)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp he)
    change p.hom ≫ f = p.domain.ι ≫ 𝟙 Y at hh
    simpa only [Category.comp_id] using hh
  let e : X ≅ p.domain.toScheme :=
    { hom := j
      inv := p.hom
      hom_inv_id := hjp
      inv_hom_id := by
        apply (cancel_mono p.domain.ι).mp
        rw [Category.assoc, hj, Category.id_comp]
        exact hpf }
  have : IsIso j := by
    change IsIso e.hom
    exact e.isIso_hom
  have : IsOpenImmersion j := inferInstance
  rw [← hj]
  exact IsOpenImmersion.comp _ _

end
end AclGeom.CurveCompletion
