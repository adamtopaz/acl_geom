/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteGaLineCover
import AclGeom.Correspondence.GaFrobenius
import AclGeom.Correspondence.SchemePointExt
import AclGeom.Correspondence.IntegralProduct

/-!
# A finite Ga cover of the actual normal subgroup

**Status:** an actual connected one-dimensional algebraic group N over an ACF base, with
a finite surjective point-injective group morphism beta:N to Ga, internally has a finite
surjective GROUP morphism alpha:Ga to N. Alpha followed by beta is relative Frobenius,
with the literal formula over every coefficient algebra. Beta gives affineness internally;
N is not assumed Ga or affine, and no coordinate or cover certificate is a premise.
Group laws follow from beta's injectivity on base-field points and reduced-source scheme
extensionality. Beta is never cancelled as a scheme mono. Named consumer:
`RegularAffineModel.exists_whole_curve_model` chooses beta internally from the genuine
regular-affine action and actual normal closed subgroup (#21). No N-isomorphism, degree-one
or separability assertion is made.
-/

namespace AclGeom.FiniteGaCover
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A finite point-injective isogeny from the actual connected one-dimensional group to
Ga is dominated by a finite Ga isogeny. The composite is relative Frobenius, not an inverse.
Named consumer: the whole-curve model with the original normal subgroup. -/
theorem exists_group_cover
    (N : ConnectedAlgebraicGroup k)
    (hdim : topologicalKrullDim N.toAlgebraicGroup.carrier = 1)
    (β : N.toAlgebraicGroup.Hom (AdditiveGroupScheme.algebraicGroup k 1))
    [IsFinite β.hom.hom.left] [Surjective β.hom.hom.left]
    (hinj : Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ N.toGroupScheme.X ↦
      q ≫ β.hom.hom))
    (p : ℕ) [ExpChar k p] :
    ∃ (n : ℕ) (α : (AdditiveGroupScheme.algebraicGroup k 1).Hom N.toAlgebraicGroup),
      IsFinite α.hom.hom.left ∧ Surjective α.hom.hom.left ∧
      α.hom.hom ≫ β.hom.hom = relativeFrobenius k p n ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C] (c : C),
        AffineSchemeAction.linePoint k c ≫ α.hom.hom ≫ β.hom.hom =
          AffineSchemeAction.linePoint k (c ^ p ^ n) := by
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let NX := N.toGroupScheme.X
  have : IsAffineHom β.hom.hom.left := inferInstance
  have hLaff : IsAffine L.left := by
    change IsAffine (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1)))
    infer_instance
  have : IsAffine NX.left :=
    @isAffine_of_isAffineHom _ _ β.hom.hom.left inferInstance hLaff
  obtain ⟨n, a, hfinite, hsurj, hcomp, hformula⟩ :=
    exists_line_cover NX hdim β.hom.hom hinj p
  have hF : a ≫ β.hom.hom = relativeFrobenius k p n := hcomp
  have : IsIntegral L.left := by
    change IsIntegral (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1)))
    infer_instance
  have : IsIntegral (L ⊗ L).left := isIntegral_pullback_of_isAlgClosed L.hom L.hom
  have : LocallyOfFiniteType (L ⊗ L).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst L.hom L.hom ≫ L.hom)
    infer_instance
  have ha : IsMonHom a := by
    constructor
    · apply hinj
      change (η[L] ≫ a) ≫ β.hom.hom = η[NX] ≫ β.hom.hom
      rw [Category.assoc, hF, IsMonHom.one_hom, IsMonHom.one_hom]
    · have he : (μ[L] ≫ a) ≫ β.hom.hom =
          ((a ⊗ₘ a) ≫ μ[NX]) ≫ β.hom.hom := by
        calc
          _ = μ[L] ≫ relativeFrobenius k p n := by rw [Category.assoc, hF]
          _ = (relativeFrobenius k p n ⊗ₘ relativeFrobenius k p n) ≫ μ[L] :=
            IsMonHom.mul_hom _
          _ = ((a ≫ β.hom.hom) ⊗ₘ (a ≫ β.hom.hom)) ≫ μ[L] := by rw [hF]
          _ = (a ⊗ₘ a) ≫ (β.hom.hom ⊗ₘ β.hom.hom) ≫ μ[L] := by
            rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
          _ = _ := by rw [Category.assoc, IsMonHom.mul_hom]
      apply AdditiveRigidity.over_hom_ext_of_points
      intro q
      apply hinj
      change (q ≫ (μ[L] ≫ a)) ≫ β.hom.hom =
        (q ≫ ((a ⊗ₘ a) ≫ μ[NX])) ≫ β.hom.hom
      simpa only [Category.assoc] using congrArg (fun z ↦ q ≫ z) he
  let α : (AdditiveGroupScheme.algebraicGroup k 1).Hom N.toAlgebraicGroup := Grp.homMk a
  exact ⟨n, α, hfinite, hsurj, hF, hformula⟩

end
end AclGeom.FiniteGaCover
