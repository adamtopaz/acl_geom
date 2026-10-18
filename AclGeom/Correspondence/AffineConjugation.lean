/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineDilation
import AclGeom.Correspondence.NormalCoordinateConjugation
import AclGeom.Correspondence.NormalTranslationImage
import AclGeom.Correspondence.SchemePointExt
import AclGeom.Correspondence.IntegralProduct
import AclGeom.Correspondence.AffineGroupGeometry

/-!
# The standard affine group conjugates translations by its multiplier

**Status:** the joint scheme identity is proved over an ACF base by reduced-source
point extensionality and the literal affine conjugation formula. Named consumer: the
arbitrary actual normal subgroup's finite-coordinate character diagram (#21).
-/

namespace AclGeom.AffineDilation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The actual standard affine group conjugates translations by its multiplier.
Named consumer: the arbitrary normal subgroup's finite-coordinate conjugation diagram. -/
theorem standard_conjugation :
    (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ◁ AdditiveTranslation.inclusion k ≫
        conj (AffineGroupScheme.algebraicGroup k).toGroupScheme.X =
      (lift (fst (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
          (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫ projection k)
        (snd (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
          (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) ≫
          AdditiveRigidity.scalarMul k) ≫ AdditiveTranslation.inclusion k := by
  let A := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let EA := AffineGroupScheme.pointsMulEquiv k
  let EM := multiplicativeGroup.pointsMulEquiv k
  have : IsIntegral L.left := by
    change IsIntegral (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1)))
    infer_instance
  have : IsIntegral A.left := by
    change IsIntegral (Spec (.of (AffineGroupScheme.CoordinateRing k)))
    infer_instance
  have : IsIntegral (A ⊗ L).left := isIntegral_pullback_of_isAlgClosed A.hom L.hom
  have : LocallyOfFiniteType (A ⊗ L).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst A.hom L.hom ≫ A.hom)
    infer_instance
  apply AdditiveRigidity.over_hom_ext_of_points
  intro p
  let q := p ≫ fst A L
  let n := p ≫ snd A L
  let a := EA q
  obtain ⟨x, hx⟩ := AffineSchemeAction.exists_linePoint k ((unitIsoSpecAsOver k).inv ≫ n)
  have hn : n = (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k x := by
    rw [hx, Iso.hom_inv_id_assoc]
  have hp : lift q n = p := by
    apply CartesianMonoidalCategory.hom_ext
    · exact lift_fst q n
    · exact lift_snd q n
  have hleft : p ≫ (A ◁ AdditiveTranslation.inclusion k ≫ conj A) =
      EA.symm (AffineTransformation.translation ((a.multiplier : k) * x)) := by
    calc
      _ = lift q n ≫ A ◁ AdditiveTranslation.inclusion k ≫ conj A :=
        congrArg (fun z ↦ z ≫ (A ◁ AdditiveTranslation.inclusion k ≫ conj A)) hp.symm
      _ = q * (n ≫ AdditiveTranslation.inclusion k) * q⁻¹ := by
        rw [lift_whiskerLeft_assoc, lift_conj_eq_mul_mul_inv]
      _ = _ := by
        rw [hn, NormalTranslation.point_inclusion]
        apply EA.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
        exact AffineTransformation.mul_translation_mul_inv (EA q) x
  have hright : p ≫ ((lift (fst A L ≫ projection k) (snd A L) ≫
        AdditiveRigidity.scalarMul k) ≫ AdditiveTranslation.inclusion k) =
      EA.symm (AffineTransformation.translation ((a.multiplier : k) * x)) := by
    calc
      _ = (lift (q ≫ projection k) n ≫ AdditiveRigidity.scalarMul k) ≫
          AdditiveTranslation.inclusion k := by
        simp only [q, n, Category.assoc, comp_lift_assoc]
      _ = ((unitIsoSpecAsOver k).hom ≫
          AffineSchemeAction.linePoint k ((a.multiplier : k) * x)) ≫
            AdditiveTranslation.inclusion k := by
        have hproj : q ≫ projection k = EM.symm a.multiplier := point_comp_projection k q
        rw [hproj, hn, ← AdditiveRigidity.unitPoint_eq_points,
          ← comp_lift_assoc, AdditiveRigidity.unitPoint_linePoint_scalarMul]
      _ = _ := NormalTranslation.point_inclusion ((a.multiplier : k) * x)
  exact hleft.trans hright.symm

end
end AclGeom.AffineDilation
