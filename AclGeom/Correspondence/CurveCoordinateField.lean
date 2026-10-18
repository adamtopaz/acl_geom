/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeGenericTranslate
import AclGeom.Correspondence.AffineSchemeAction
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The actual standard-line function field

**Status:** proved criteria (#21). Literal evaluation at a transcendental generator
identifies the standard line's actual generic stalk with the generated field. The actual
base algebra, coordinate-ring algebra and generic Spec map agree. Named consumer:
`CurveCoordinateCover.exists_coordinate_restriction_iso`. No action classification is a
premise or conclusion of these algebraic criteria.
-/

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- The actual generic-stalk base algebra on an affine domain is compatible with the
 canonical coordinate-ring algebra. Named consumer: `exists_line_functionField_equiv`. -/
theorem spec_functionField_isScalarTower (k : Type u) [Field k]
    (A : CommRingCat.{u}) [IsDomain A] [Algebra k A] :
    let : Algebra k (Spec A).functionField := @ActionFunctionField.functionFieldAlgebra k _
      ((Spec A).asOver (Spec (.of k))) (inferInstanceAs (IsIntegral (Spec A)))
    IsScalarTower k A (Spec A).functionField := by
  let V := (Spec A).asOver (Spec (.of k))
  have : IsIntegral V.left := inferInstanceAs (IsIntegral (Spec A))
  let : Algebra k (Spec A).functionField := ActionFunctionField.functionFieldAlgebra V
  have : (algSpec (.of k)).Full := algSpec.instFull
  let p : (algSpec (.of k)).obj (.op (CommAlgCat.of k (Spec A).functionField)) ⟶
      (algSpec (.of k)).obj (.op (CommAlgCat.of k A)) :=
    SchemeGenericTranslate.genericParameter V
  let φ : A →ₐ[k] (Spec A).functionField := ((algSpec (.of k)).preimage p).unop.hom
  have hm : (algSpec (.of k)).map (CommAlgCat.ofHom φ).op = p :=
    (algSpec (.of k)).map_preimage p
  have hφ : φ.toRingHom = algebraMap A (Spec A).functionField := by
    have h := congrArg Over.Hom.left hm
    change Spec.map (CommRingCat.ofHom φ.toRingHom) =
      (Spec A).fromSpecStalk (genericPoint (Spec A)) at h
    rw [Spec.fromSpecStalk_eq'] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [← φ.commutes c]
  exact congrArg (fun f : A →+* (Spec A).functionField ↦ f (algebraMap k A c)) hφ
end
end AclGeom.CurveCoordinateCover

namespace AclGeom.CurveCoordinateCover
noncomputable section

/-- Evaluation at a transcendental element is injective for the actual standard-line
 coordinate algebra. Named consumer: `exists_line_functionField_equiv`. -/
theorem lineEval_injective_of_transcendental {k F : Type*} [Field k] [Field F]
    [Algebra k F] (t : F) (ht : Transcendental k t) :
    Function.Injective (AffineSchemeAction.lineEval (k := k) t) := by
  let e : AdditiveGroupScheme.CoordinateRing k 1 ≃ₐ[k] Polynomial k :=
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1))).trans
      (MvPolynomial.uniqueAlgEquiv k (Fin 1))
  have he : e (AffineSchemeAction.lineCoordinate k) = Polynomial.X := by
    change (MvPolynomial.uniqueAlgEquiv k (Fin 1))
      ((SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1)))
        (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0))) = Polynomial.X
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
    rw [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]
  have h : AffineSchemeAction.lineEval (k := k) t = (Polynomial.aeval t).comp e.toAlgHom := by
    apply AffineSchemeAction.lineHom_ext
    rw [AffineSchemeAction.lineEval_lineCoordinate, AlgHom.comp_apply]
    change t = Polynomial.aeval t (e (AffineSchemeAction.lineCoordinate k))
    rw [he, Polynomial.aeval_X]
  rw [h]
  exact (transcendental_iff_injective.mp ht).comp e.injective
end
end AclGeom.CurveCoordinateCover

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- A transcendental generator identifies the actual standard-line generic stalk with the
 given field, extending literal coordinate evaluation and preserving the generic Spec map.
 Named consumer: `exists_coordinate_restriction_iso`. -/
theorem exists_line_functionField_equiv {k F : Type u} [Field k] [Field F] [Algebra k F]
    (t : F) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set F) = ⊤) :
    let A : CommRingCat.{u} := .of (AdditiveGroupScheme.CoordinateRing k 1)
    letI : Algebra A (Spec A).functionField := instAlgebraCarrierFunctionFieldSpec A
    letI : Algebra k (Spec A).functionField := @ActionFunctionField.functionFieldAlgebra k _
      ((Spec A).asOver (Spec (.of k))) (inferInstanceAs (IsIntegral (Spec A)))
    ∃ E : (Spec A).functionField ≃ₐ[k] F,
      (∀ r : A, E (algebraMap A (Spec A).functionField r) =
        AffineSchemeAction.lineEval (k := k) t r) ∧
      Spec.map (CommRingCat.ofHom E.toRingHom) ≫
        (Spec A).fromSpecStalk (genericPoint (Spec A)) =
          (AffineSchemeAction.linePoint k t).left := by
  let A : CommRingCat.{u} := .of (AdditiveGroupScheme.CoordinateRing k 1)
  let : Algebra A (Spec A).functionField := instAlgebraCarrierFunctionFieldSpec A
  let : IsFractionRing A (Spec A).functionField := functionField_isFractionRing_of_affine A
  let : Algebra k (Spec A).functionField := @ActionFunctionField.functionFieldAlgebra k _
    ((Spec A).asOver (Spec (.of k))) (inferInstanceAs (IsIntegral (Spec A)))
  have : IsScalarTower k A (Spec A).functionField := spec_functionField_isScalarTower k A
  let χ : A →ₐ[k] F := AffineSchemeAction.lineEval t
  have hχ : Function.Injective χ := lineEval_injective_of_transcendental t ht
  let η : (Spec A).functionField →ₐ[k] F := IsFractionRing.liftAlgHom hχ
  have hη (r : A) : η (algebraMap A (Spec A).functionField r) = χ r :=
    IsFractionRing.lift_algebraMap hχ r
  have htopη : η.fieldRange = ⊤ := by
    apply top_unique
    rw [← htop]
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    have hz : z = t := Set.mem_singleton_iff.mp hz
    subst z
    apply AlgHom.mem_fieldRange.mpr
    refine ⟨algebraMap A (Spec A).functionField (AffineSchemeAction.lineCoordinate k), ?_⟩
    exact (hη _).trans (AffineSchemeAction.lineEval_lineCoordinate t)
  let E : (Spec A).functionField ≃ₐ[k] F :=
    AlgEquiv.ofBijective η ⟨η.injective, AlgHom.fieldRange_eq_top.mp htopη⟩
  refine ⟨E, hη, ?_⟩
  let i : A ⟶ (Spec A).functionField :=
    CommRingCat.ofHom (algebraMap A (Spec A).functionField)
  let φ : (Spec A).functionField ⟶ CommRingCat.of F := CommRingCat.ofHom E.toRingHom
  have hcomp : i ≫ φ = CommRingCat.ofHom χ.toRingHom := by
    ext r
    exact hη r
  change Spec.map φ ≫ (Spec A).fromSpecStalk (genericPoint (Spec A)) = _
  calc
    _ = Spec.map φ ≫ Spec.map i := congrArg (fun q ↦ Spec.map φ ≫ q)
      (Spec.fromSpecStalk_eq' A (genericPoint (Spec A)))
    _ = Spec.map (i ≫ φ) := (Spec.map_comp i φ).symm
    _ = Spec.map (CommRingCat.ofHom χ.toRingHom) := congrArg Spec.map hcomp
    _ = _ := rfl

end
end AclGeom.CurveCoordinateCover

namespace AclGeom.CurveCoordinateCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- The actual standard-line point commutes with scalar-algebra maps.
 Named consumer: `exists_coordinate_restriction_iso`, with the SAME transported generator. -/
theorem linePoint_baseChange {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (x : A) :
    (algSpec (.of k)).map (CommAlgCat.ofHom f).op ≫ AffineSchemeAction.linePoint k x =
      AffineSchemeAction.linePoint k (f x) := by
  have h : f.comp (AffineSchemeAction.lineEval x) = AffineSchemeAction.lineEval (f x) := by
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate,
      AffineSchemeAction.lineEval_lineCoordinate]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval x).toRingHom) =
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (f x)).toRingHom)
  exact (Spec.map_comp _ _).symm.trans
    (congrArg Spec.map (congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom h)))
end
end AclGeom.CurveCoordinateCover
