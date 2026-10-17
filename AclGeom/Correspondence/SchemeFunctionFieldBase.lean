/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ActionFunctionField

/-!
# The base algebra of an actual scheme function field

Named consumer: the scheme-curve/function-field bridge. The pullback algebra used by
`ActionFunctionField` equals the canonical map through global sections and their generic germ.
The proof uses the existing generic-point morphism and the Spec/Gamma adjunction, without
another implementation of function-field pullback.

**Status:** proved; the actual curve theorem uses this canonical base-algebra comparison.
-/

namespace AlgebraicGeometry.Scheme

noncomputable section

open CategoryTheory

universe u

/-- Pullback of rational functions commutes with taking the generic germ of a global section.
Named consumer: the base-algebra comparison used for an actual curve function field. -/
theorem Hom.germToFunctionField_top_comp {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Y.germToFunctionField ⊤ (h := ⟨⟨genericPoint Y, trivial⟩⟩) ≫
        f.toPartialMap.functionFieldMap =
      f.appTop ≫ X.germToFunctionField ⊤ (h := ⟨⟨genericPoint X, trivial⟩⟩) := by
  have h := PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom f.toPartialMap
  rw [Hom.fromFunctionField_toPartialMap] at h
  change X.fromSpecStalk (genericPoint X) ≫ f =
    Spec.map f.toPartialMap.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) at h
  apply Spec.map_injective
  change Spec.map (Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫
      f.toPartialMap.functionFieldMap) =
    Spec.map (f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial)
  calc
    _ = Spec.map f.toPartialMap.functionFieldMap ≫
        Y.fromSpecStalk (genericPoint Y) ≫ Y.toSpecΓ := by
      rw [Spec.map_comp, fromSpecStalk_toSpecΓ]
    _ = (X.fromSpecStalk (genericPoint X) ≫ f) ≫ Y.toSpecΓ := by
      rw [← Category.assoc, ← h]
    _ = _ := by
      rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
        fromSpecStalk_toSpecΓ, ← Spec.map_comp]

end

end AlgebraicGeometry.Scheme

namespace AclGeom.ActionFunctionField

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] specFunctionFieldAlgebra

/-- The pullback base algebra is the canonical global-section/generic-germ algebra.
Named consumer: the internally derived scalar tower in the actual curve field theorem. -/
theorem functionFieldAlgebra_eq_germ {k : Type u} [Field k]
    (V : Over (Spec (.of k))) [IsIntegral V.left] :
    functionFieldAlgebra V =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop ≫
        V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint V.left, trivial⟩⟩)).hom.toAlgebra := by
  have := isDominant_hom V
  apply Algebra.algebra_ext
  intro c
  change (CommRingCat.ofHom
      (algebraMap (CommRingCat.of k) (Spec (.of k)).functionField) ≫
      V.hom.toPartialMap.functionFieldMap) c = _
  have hbase : CommRingCat.ofHom
      (algebraMap (CommRingCat.of k) (Spec (.of k)).functionField) =
      (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  rw [hbase, Category.assoc, Scheme.Hom.germToFunctionField_top_comp]
  rfl

end

end AclGeom.ActionFunctionField
