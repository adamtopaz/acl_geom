/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditivePolynomialMaps
import AclGeom.Correspondence.AffineTranslationSubgroup
import Mathlib.Algebra.Polynomial.Degree.Units

/-!
# Actual Ga group morphisms into the affine group are translations

**Status:** every actual Ga group-scheme morphism into the affine group factors as an
actual Ga group morphism followed by the translation inclusion, over any field (#21).
The actual universal affine-point coordinates give an invertible polynomial multiplier.
A polynomial unit over a field is constant; preservation of the group unit makes it one.
Cancel through the monic translation inclusion to prove the factor's actual group laws.
Named consumer: `SchemeAffineTranslations.exists_subgroup_translation_coordinate`.
No multiplier, polynomial or factorization certificate is a caller premise.
-/

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k]

/-- Every actual Ga group morphism into the affine group factors through translations.
Named consumer: the finite-isogeny identification in an actual regular-affine curve action. -/
theorem exists_group_factor
    (h : (AdditiveGroupScheme.algebraicGroup k 1).Hom (AffineGroupScheme.algebraicGroup k)) :
    ∃ β : (AdditiveGroupScheme.algebraicGroup k 1).Hom (AdditiveGroupScheme.algebraicGroup k 1),
      β.hom.hom ≫ inclusion k = h.hom.hom := by
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let N := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let A := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  let P := polynomialCoordinates k
  obtain ⟨u, z, huz⟩ := AffineSchemeAction.exists_groupPoint k h.hom.hom
  have hp₀ : AffineSchemeAction.linePoint k (0 : k) ≫
      AffineSchemeAction.groupPoint k u z = AffineSchemeAction.groupPoint k 1 (0 : k) := by
    rw [huz, linePoint_zero, one_comp, AffineSchemeAction.groupPoint_one]
  rw [linePoint_comp_groupPoint] at hp₀
  have hmaps := (Spec.mapMulEquiv (R := k) (S := AffineGroupScheme.CoordinateRing k)
    (T := k)).injective hp₀
  have hvalue := congrArg (fun f : WithConv (AffineGroupScheme.CoordinateRing k →ₐ[k] k) ↦
    f.ofConv (AffineGroupScheme.dilationUnit k)) hmaps
  simp only [AffineGroupScheme.eval_dilation, Units.coe_map, Units.val_one] at hvalue
  have hu : IsUnit (P (u : R)) := u.isUnit.map P.toRingHom
  obtain ⟨a, _, ha⟩ := Polynomial.isUnit_iff.mp hu
  have ha₁ : a = 1 := by
    have hh := congrArg (Polynomial.aeval (0 : k)) ha
    rw [Polynomial.aeval_C] at hh
    exact hh.trans ((lineEval_polynomialCoordinates k 0 (u : R)).symm.trans hvalue)
  have hu₁ : u = 1 := by
    apply Units.ext
    apply P.injective
    rw [← ha, ha₁, Polynomial.C_1, Units.val_one, map_one]
  rw [hu₁] at huz
  let β : N ⟶ N := AffineSchemeAction.linePoint k z
  have hfactor : β ≫ inclusion k = h.hom.hom :=
    (linePoint_comp_inclusion k z).trans huz
  have : IsMonHom β := by
    constructor
    · apply (cancel_mono (inclusion k)).mp
      simp only [Category.assoc, hfactor, IsMonHom.one_hom]
    · apply (cancel_mono (inclusion k)).mp
      calc
        (μ[N] ≫ β) ≫ inclusion k = μ[N] ≫ h.hom.hom := by
          rw [Category.assoc, hfactor]
        _ = (h.hom.hom ⊗ₘ h.hom.hom) ≫ μ[A] := IsMonHom.mul_hom _
        _ = ((β ≫ inclusion k) ⊗ₘ (β ≫ inclusion k)) ≫ μ[A] := by rw [hfactor]
        _ = (β ⊗ₘ β) ≫ (inclusion k ⊗ₘ inclusion k) ≫ μ[A] := by
          rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
        _ = ((β ⊗ₘ β) ≫ μ[N]) ≫ inclusion k := by
          rw [Category.assoc, IsMonHom.mul_hom]
  exact ⟨Grp.homMk β, hfactor⟩
end
end AclGeom.AdditiveTranslation
