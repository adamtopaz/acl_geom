/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditivePolynomialMaps
import AclGeom.Correspondence.AffineTranslationSubgroup

/-!
# An actual nontrivial additive endomorphism as a finite surjective map

**Status:** a Ga group endomorphism nontrivial at a base-field point internally supplies a
nonconstant polynomial, the actual finite surjective scheme map and its point formula and
additivity over every commutative coefficient algebra in the base universe. This holds over
every field, in every characteristic. Preservation of the unit gives zero constant term.
Named consumer: `SchemeAffineTranslations.exists_subgroup_translation_coordinate`, which
derives the nontrivial point from genuine faithfulness and a monic subgroup internally.
No polynomial or finiteness certificate is supplied. Inseparability is allowed (#21).
-/

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k]

/-- A genuinely nontrivial actual Ga endomorphism is a finite surjective polynomial map.
Named consumer: the actual regular-affine subgroup translation identification. -/
theorem exists_finite_coordinate
    (β : (AdditiveGroupScheme.algebraicGroup k 1).Hom (AdditiveGroupScheme.algebraicGroup k 1))
    (hne : ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X, q ≫ β.hom.hom ≠ 1) :
    ∃ p : Polynomial k, Polynomial.eval 0 p = 0 ∧ p.natDegree ≠ 0 ∧
      IsFinite β.hom.hom.left ∧ Surjective β.hom.hom.left ∧
      (∀ (C : Type u) [CommRing C] [Algebra k C] (x : C),
        AffineSchemeAction.linePoint k x ≫ β.hom.hom =
          AffineSchemeAction.linePoint k (Polynomial.aeval x p)) ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C] (x y : C),
        Polynomial.aeval (x + y) p = Polynomial.aeval x p + Polynomial.aeval y p := by
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let P := polynomialCoordinates k
  obtain ⟨z, hz⟩ := AffineSchemeAction.exists_linePoint k (C := R) β.hom.hom
  let p := P z
  have hz₀ : AffineSchemeAction.lineEval (k := k) (0 : k) z = 0 := by
    apply AffineSchemeAction.linePoint_injective k
    rw [← linePoint_comp_linePoint, hz, linePoint_zero, one_comp]
  have hp₀ : Polynomial.eval 0 p = 0 :=
    (lineEval_polynomialCoordinates k 0 z).symm.trans hz₀
  have hp : p.natDegree ≠ 0 := by
    intro hp
    have hconst : p = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp]
      have hc : p.coeff 0 = 0 := by
        have hh := hp₀
        rw [Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.eval_C] at hh
        exact hh
      rw [hc, Polynomial.C_0]
    have hz₀' : z = 0 := by
      apply P.injective
      change p = P 0
      rw [hconst, map_zero]
    obtain ⟨q, hq⟩ := hne
    apply hq
    rw [← hz, hz₀', linePoint_zero]
    change q ≫ (1 : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) = 1
    exact comp_one q
  refine ⟨p, hp₀, hp, ?_, ?_, ?_, ?_⟩
  · rw [← hz]
    exact isFinite_linePoint k z hp
  · rw [← hz]
    exact surjective_linePoint k z hp
  · intro C _ _ x
    rw [← hz, linePoint_comp_linePoint, lineEval_polynomialCoordinates]
  · intro C _ _ x y
    have hformula (w : C) : AffineSchemeAction.linePoint k w ≫ β.hom.hom =
        AffineSchemeAction.linePoint k (Polynomial.aeval w p) := by
      rw [← hz, linePoint_comp_linePoint, lineEval_polynomialCoordinates]
    apply AffineSchemeAction.linePoint_injective k
    calc
      AffineSchemeAction.linePoint k (Polynomial.aeval (x + y) p) =
          AffineSchemeAction.linePoint k (x + y) ≫ β.hom.hom := (hformula _).symm
      _ = (AffineSchemeAction.linePoint k x * AffineSchemeAction.linePoint k y) ≫
          β.hom.hom := by rw [linePoint_mul]
      _ = (AffineSchemeAction.linePoint k x ≫ β.hom.hom) *
          (AffineSchemeAction.linePoint k y ≫ β.hom.hom) := mul_comp _ _ _
      _ = _ := by rw [hformula, hformula, linePoint_mul]

end
end AclGeom.AdditiveTranslation
