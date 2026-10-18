/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.MultiplicativeValue

/-!
# The actual multiplicative scalar map on Ga

**Status:** the actual scheme map Gm times Ga to Ga and its literal scalar formula on every
commutative coefficient algebra in the base universe are proved over any field. This is
an actual scheme map, not a classification of automorphisms over nonreduced rings. Named
consumer: `AdditiveRigidity.normal_additiveGroup_conj`, the joint source diagram (#21).
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

/-- Named consumer: the actual normal additive-subgroup conjugation character. -/
def scalarMul : (multiplicativeGroup k).toGroupScheme.X ⊗
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  (AffineSchemeAction.tensorSpecIso k (AddMonoidAlgebra k ℤ)
    (AdditiveGroupScheme.CoordinateRing k 1)).hom ≫
    (Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
      (AddMonoidAlgebra.single (1 : ℤ) (1 : k) ⊗ₜ[k]
        AffineSchemeAction.lineCoordinate k)).toRingHom)).asOver (Spec (.of k))

/-- Named consumer: the joint actual conjugation identity, including all characteristics. -/
theorem unitPoint_linePoint_scalarMul {C : Type u} [CommRing C] [Algebra k C] (a : Cˣ) (x : C) :
    lift (unitPoint k a) (AffineSchemeAction.linePoint k x) ≫ scalarMul k =
      AffineSchemeAction.linePoint k ((a : C) * x) := by
  let evalUnit : AddMonoidAlgebra k ℤ →ₐ[k] C := ((unitsMulEquivConv k C).symm a).ofConv
  let θ : AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k]
      AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1 :=
    AffineSchemeAction.lineEval
    (AddMonoidAlgebra.single (1 : ℤ) (1 : k) ⊗ₜ[k] AffineSchemeAction.lineCoordinate k)
  have hevalUnit : evalUnit (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = (a : C) :=
    unitsMulEquivConv_symm_apply_single k C a
  have hco : (Algebra.TensorProduct.lift evalUnit (AffineSchemeAction.lineEval x)
      (fun _ _ ↦ Commute.all _ _)).comp θ = AffineSchemeAction.lineEval ((a : C) * x) := by
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate,
      AffineSchemeAction.lineEval_lineCoordinate, Algebra.TensorProduct.lift_tmul,
      hevalUnit, AffineSchemeAction.lineEval_lineCoordinate]
  change lift ((Spec.map (CommRingCat.ofHom evalUnit.toRingHom)).asOver (Spec (.of k)))
      ((Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval x).toRingHom)).asOver
        (Spec (.of k))) ≫ (AffineSchemeAction.tensorSpecIso k _ _).hom ≫
      (Spec.map (CommRingCat.ofHom θ.toRingHom)).asOver (Spec (.of k)) =
    (Spec.map (CommRingCat.ofHom
      (AffineSchemeAction.lineEval ((a : C) * x)).toRingHom)).asOver (Spec (.of k))
  rw [← Category.assoc, AffineSchemeAction.lift_tensorSpecIso_hom, ← hco]
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl
end
end AclGeom.AdditiveRigidity
