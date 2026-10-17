/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AlgebraicGroup
import AclGeom.Correspondence.SymmetricHopf
import AclGeom.Correspondence.HopfSpecPoints
import AclGeom.Correspondence.GroupSchemePoints
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The actual additive algebraic group

The symmetric algebra on a finite free module represents the vector group. Its existing
primitive comultiplication and the proved antipode give actual scheme group operations.
Named consumers: the additive-plane curve-coset invocation and the affine group and regular
action in blueprint equation (8.4a). Classification of an arbitrary curve action remains owed.

**Status:** proved; used by the concrete additive and affine group schemes.
-/

namespace AclGeom.AdditiveGroupScheme

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u v

/-- The coordinate ring of the additive vector group. -/
abbrev CoordinateRing (k : Type u) [Field k] (n : ℕ) :=
  SymmetricAlgebra k (Fin n → k)

instance coordinateRingFiniteType (k : Type u) [Field k] (n : ℕ) :
    Algebra.FiniteType k (CoordinateRing k n) :=
  Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType k (MvPolynomial (Fin n) k)))
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin n))).symm

/-- The split additive vector group, with its actual scheme structure. -/
def algebraicGroup (k : Type u) [Field k] (n : ℕ) : AlgebraicGroup k :=
  @AlgebraicGroup.ofGroupScheme k _
    (Grp.mk ((Spec (.of (CoordinateRing k n))).asOver (Spec (.of k))))
    (locallyOfFiniteType_specOverSpec :
      LocallyOfFiniteType (Spec (.of (CoordinateRing k n)) ↘ Spec (.of k)))
    (inferInstance : QuasiCompact (Spec (.of (CoordinateRing k n)) ↘ Spec (.of k)))

instance isCommMonObj (k : Type u) [Field k] (n : ℕ) :
    CategoryTheory.IsCommMonObj (algebraicGroup k n).toGroupScheme.X :=
  (inferInstance : CategoryTheory.IsCommMonObj
    ((Spec (.of (CoordinateRing k n))).asOver (Spec (.of k))))

/-- Algebra maps out of the coordinate ring are exactly choices of the vector coordinates. -/
def algebraCoordinates (k : Type u) [Field k] (n : ℕ) (C : Type v)
    [CommRing C] [Algebra k C] : (CoordinateRing k n →ₐ[k] C) ≃ (Fin n → C) :=
  (SymmetricAlgebra.lift : ((Fin n → k) →ₗ[k] C) ≃ _).symm.trans
    ((Pi.basisFun k (Fin n)).constr k).toEquiv.symm

@[simp]
theorem algebraCoordinates_apply {k : Type u} {C : Type v} [Field k] [CommRing C] [Algebra k C]
    {n : ℕ} (f : CoordinateRing k n →ₐ[k] C) (i : Fin n) :
    algebraCoordinates k n C f i =
      f (SymmetricAlgebra.ι k (Fin n → k) (Pi.basisFun k (Fin n) i)) := by
  change (SymmetricAlgebra.lift.symm f) (Pi.basisFun k (Fin n) i) = _
  have h := SymmetricAlgebra.lift_comp_ι (SymmetricAlgebra.lift.symm f)
  rw [Equiv.apply_symm_apply] at h
  exact (LinearMap.congr_fun h (Pi.basisFun k (Fin n) i)).symm

/-- Evaluating the algebra map of a vector recovers each coordinate. -/
theorem algebraCoordinates_symm_apply_ι {k : Type u} {C : Type v} [Field k] [CommRing C]
    [Algebra k C] {n : ℕ} (v : Fin n → C) (i : Fin n) :
    (algebraCoordinates k n C).symm v
      (SymmetricAlgebra.ι k (Fin n → k) (Pi.basisFun k (Fin n) i)) = v i := by
  have h := congrFun ((algebraCoordinates k n C).apply_symm_apply v) i
  rw [algebraCoordinates_apply] at h
  exact h

/-- Convolution of algebra maps is addition of vector coordinates. -/
def characterCoordinates (k : Type u) [Field k] (n : ℕ) (C : Type v)
    [CommRing C] [Algebra k C] :
    WithConv (CoordinateRing k n →ₐ[k] C) ≃* Multiplicative (Fin n → C) where
  toEquiv := (WithConv.equiv _).trans ((algebraCoordinates k n C).trans Multiplicative.ofAdd)
  map_mul' f g := by
    apply Multiplicative.toAdd.injective
    ext i
    change algebraCoordinates k n C (f * g).ofConv i =
      algebraCoordinates k n C f.ofConv i + algebraCoordinates k n C g.ofConv i
    rw [algebraCoordinates_apply, algebraCoordinates_apply, algebraCoordinates_apply]
    rw [AlgHom.convMul_apply, SymmetricAlgebra.comul_ι]
    simp

/-- The actual group of base-field points of the vector group is vector addition. -/
def pointsMulEquiv (k : Type u) [Field k] (n : ℕ) :
    (𝟙_ (Over (Spec (.of k))) ⟶ (algebraicGroup k n).toGroupScheme.X) ≃*
      Multiplicative (Fin n → k) :=
  (hopfPointsMulEquiv k (CoordinateRing k n)).trans (characterCoordinates k n k)

/-- A vector gives the point obtained by applying `Spec` to its evaluation map. -/
theorem pointsMulEquiv_symm_apply_left {k : Type u} [Field k] {n : ℕ} (v : Fin n → k) :
    ((pointsMulEquiv k n).symm (Multiplicative.ofAdd v)).left =
      Spec.map (CommRingCat.ofHom ((algebraCoordinates k n k).symm v).toRingHom) := by
  change ((hopfPointsMulEquiv k (CoordinateRing k n)).symm
    (WithConv.toConv ((algebraCoordinates k n k).symm v))).left = _
  exact hopfPointsMulEquiv_symm_apply_left k (CoordinateRing k n) _

/-- Over an algebraically closed field, the closed points of the vector group are the vectors. -/
def closedPointsEquiv (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    closedPoints (algebraicGroup k n).carrier ≃ (Fin n → k) :=
  GroupScheme.pointsEquivClosedPoints.symm.trans
    ((pointsMulEquiv k n).toEquiv.trans Multiplicative.toAdd)

end

end AclGeom.AdditiveGroupScheme
