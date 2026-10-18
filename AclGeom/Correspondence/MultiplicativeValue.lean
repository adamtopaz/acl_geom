/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveScaling
import AclGeom.Correspondence.MultiplicativeGroupScheme

/-!
# Multiplicative-group points and their actual line values

**Status:** unit-valued points of Gm map to their actual line coordinates over every
commutative coefficient algebra in the base universe. Base-field coordinates agree with
the existing multiplicative point equivalence. Named consumers: the regular character
lift and the actual normal additive-subgroup conjugation diagram (#21).
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable (k : Type u) [Field k]

/-- Named consumers: the regular character lift and its scalar action formula. -/
def unitPoint {C : Type u} [CommRing C] [Algebra k C] (a : Cˣ) :
    (Spec (.of C)).asOver (Spec (.of k)) ⟶ (multiplicativeGroup k).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom ((unitsMulEquivConv k C).symm a).ofConv).op

/-- Named consumer: a unit-valued regular line coefficient lifts to the multiplicative group. -/
def multiplicativeValue : (multiplicativeGroup k).toGroupScheme.X ⟶
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom (AffineSchemeAction.lineEval
    (AddMonoidAlgebra.single (1 : ℤ) (1 : k)))).op

/-- Named consumer: the regular conjugation character and its scalar formula. -/
theorem unitPoint_comp_multiplicativeValue {C : Type u} [CommRing C] [Algebra k C] (a : Cˣ) :
    unitPoint k a ≫ multiplicativeValue k = AffineSchemeAction.linePoint k (a : C) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((unitsMulEquivConv k C).symm a).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
        (AddMonoidAlgebra.single (1 : ℤ) (1 : k))).toRingHom) =
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (a : C)).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (((unitsMulEquivConv k C).symm a).ofConv.comp (AffineSchemeAction.lineEval
    (AddMonoidAlgebra.single (1 : ℤ) (1 : k)))).toRingHom = _
  apply congrArg AlgHom.toRingHom
  apply AffineSchemeAction.lineHom_ext
  rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate,
    AffineSchemeAction.lineEval_lineCoordinate]
  exact unitsMulEquivConv_symm_apply_single k C a

/-- Named consumer: identifying the actual character's point coordinates. -/
theorem unitPoint_eq_points (a : kˣ) :
    (unitIsoSpecAsOver k).hom ≫ unitPoint k a = (multiplicativeGroup.pointsMulEquiv k).symm a := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((unitsMulEquivConv k k).symm a).ofConv.toRingHom) =
    ((hopfPointsMulEquiv k (AddMonoidAlgebra k ℤ)).symm ((unitsMulEquivConv k k).symm a)).left
  rw [Category.id_comp]
  exact (hopfPointsMulEquiv_symm_apply_left k (AddMonoidAlgebra k ℤ)
    ((unitsMulEquivConv k k).symm a).ofConv).symm
end
end AclGeom.AdditiveRigidity
