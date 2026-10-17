/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveFunctionFieldAlgebra
import AclGeom.Correspondence.SchemeFunctionFieldBase
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The actual function field of an integral curve scheme

Named source consumer: the curve-action proof of blueprint Lemma `affine-action` (#21 row 2).
The curve is integral and locally of finite type over a field, with scheme dimension one.
The field is its actual generic stalk; its base algebra, finite generation and transcendence
witness are derived internally. No perfectness, genus, coordinate or field-finiteness oracle
is used.

**Status:** proved over arbitrary fields, with the same derived base algebra as the
regular scheme-action theorem.
-/

namespace AclGeom

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

/-- The actual generic-stalk function field of an integral curve is a one-variable function
field. The base algebra is derived from the given structure morphism. Named consumer:
blueprint `lem:affine-action`, the passage from a curve scheme to the curve field library. -/
theorem scheme_functionField_isFunctionFieldOneVar (k : Type u) [Field k]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    (hdim : topologicalKrullDim V.left = 1) :
    letI := ActionFunctionField.functionFieldAlgebra V
    IsFunctionFieldOneVar k V.left.functionField := by
  rw [ActionFunctionField.functionFieldAlgebra_eq_germ]
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  let : Algebra k V.left.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop ≫
      V.left.germToFunctionField ⊤).hom.toAlgebra
  obtain ⟨U, hU, hne, hUdim⟩ := exists_isAffineOpen_dimension_one V.left hdim
  have : Nonempty U := hne
  let A := Γ(V.left, U)
  let f : CommRingCat.of k ⟶ CommRingCat.of A :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appLE ⊤ U (by simp)
  let : Algebra k A := f.hom.toAlgebra
  have : Algebra.FiniteType k A :=
    (V.hom.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have hres : V.hom.appLE ⊤ U (by simp) ≫ V.left.germToFunctionField U =
      V.hom.appTop ≫ V.left.germToFunctionField ⊤ := by
    change (V.hom.appTop ≫
      V.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) ≫
        V.left.germToFunctionField U = V.hom.appTop ≫ V.left.germToFunctionField ⊤
    exact (Category.assoc _ _ _).trans (congrArg
      (fun q : Γ(V.left, ⊤) ⟶ V.left.functionField ↦ V.hom.appTop ≫ q)
      (V.left.presheaf.germ_res (homOfLE (show U ≤ ⊤ from le_top)) (genericPoint V.left)
        (((genericPoint_spec V.left).mem_open_set_iff U.isOpen).2 (by simpa using hne))))
  have : IsScalarTower k A V.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop ≫
        V.left.germToFunctionField ⊤) r =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appLE ⊤ U (by simp) ≫
            V.left.germToFunctionField U) r
      rw [hres]
  have : IsFractionRing A V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left U hU
  have : Algebra.EssFiniteType A V.left.functionField :=
    Algebra.EssFiniteType.of_isLocalization V.left.functionField (nonZeroDivisors A)
  have : Algebra.EssFiniteType k V.left.functionField :=
    Algebra.EssFiniteType.comp k A V.left.functionField
  have hAdim : ringKrullDim A = 1 := by
    have he := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
    change topologicalKrullDim U = topologicalKrullDim (PrimeSpectrum A) at he
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
    exact he.symm.trans hUdim
  obtain ⟨n, hn, ht⟩ := exists_ringKrullDim_trdeg_eq_of_finiteType k A V.left.functionField
  have hn1 : n = 1 := by exact_mod_cast hn.symm.trans hAdim
  apply isFunctionFieldOneVar_of_trdeg_eq_one k V.left.functionField
  simpa only [hn1, Nat.cast_one] using ht

end

end AclGeom
