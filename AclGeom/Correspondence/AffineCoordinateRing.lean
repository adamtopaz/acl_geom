/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.AdditiveGroupScheme
import AclGeom.Correspondence.MultiplicativeGroupScheme
import Mathlib.RingTheory.FiniteStability

/-!
# The two coordinates of the algebraic affine group

The coordinate algebra is `k[a,a⁻¹,b]`. Its algebra maps into a commutative `k`-algebra
are exactly an invertible dilation and an arbitrary translation. The named consumer is
the noncocommutative Hopf structure and actual standard action in blueprint equation (8.4a).
The type synonym names the chosen affine semidirect-product Hopf structure separately
from the coordinate factors' usual direct-product structure.

**Status:** proved: the universal property holds over every commutative coefficient algebra.
-/

namespace AclGeom.AffineGroupScheme

noncomputable section

open scoped TensorProduct

universe u v

/-- The coordinate algebra `k[a,a⁻¹,b]` of the algebraic affine group. -/
def CoordinateRing (k : Type u) [Field k] : Type u :=
  AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1

instance coordinateRingCommRing (k : Type u) [Field k] : CommRing (CoordinateRing k) :=
  inferInstanceAs (CommRing
    (AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1))

instance coordinateRingAlgebra (k : Type u) [Field k] : Algebra k (CoordinateRing k) :=
  inferInstanceAs (Algebra k
    (AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1))

instance coordinateRingFiniteType (k : Type u) [Field k] :
    Algebra.FiniteType k (CoordinateRing k) := by
  change Algebra.FiniteType k
    (AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1)
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k (AddMonoidAlgebra k ℤ))
    (inferInstance : Algebra.FiniteType (AddMonoidAlgebra k ℤ)
      (AddMonoidAlgebra k ℤ ⊗[k] AdditiveGroupScheme.CoordinateRing k 1))

/-- The Laurent-polynomial factor of the affine coordinate algebra. -/
def includeDilation (k : Type u) [Field k] : AddMonoidAlgebra k ℤ →ₐ[k] CoordinateRing k :=
  Algebra.TensorProduct.includeLeft

/-- The polynomial factor of the affine coordinate algebra. -/
def includeTranslation (k : Type u) [Field k] :
    AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k] CoordinateRing k :=
  Algebra.TensorProduct.includeRight

/-- The invertible coordinate `a` of an affine transformation. -/
def dilationUnit (k : Type u) [Field k] : (CoordinateRing k)ˣ :=
  Units.map (includeDilation k).toMonoidHom
    ((AddMonoidAlgebra.of k ℤ).toHomUnits (Multiplicative.ofAdd (1 : ℤ)))

theorem dilationUnit_val (k : Type u) [Field k] :
    (dilationUnit k : CoordinateRing k) = includeDilation k (AddMonoidAlgebra.single 1 1) :=
  rfl

/-- The translation coordinate `b` of an affine transformation. -/
def translation (k : Type u) [Field k] : CoordinateRing k :=
  includeTranslation k
    (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0))

/-- Evaluation of affine coordinates at an invertible dilation and a translation. -/
def eval (k : Type u) [Field k] {C : Type v} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) : CoordinateRing k →ₐ[k] C :=
  Algebra.TensorProduct.lift ((unitsMulEquivConv k C).symm a).ofConv
    ((AdditiveGroupScheme.algebraCoordinates k 1 C).symm (fun _ ↦ b))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem eval_includeDilation {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) (f : AddMonoidAlgebra k ℤ) :
    eval k a b (includeDilation k f) = (unitsMulEquivConv k C).symm a f := by
  change (Algebra.TensorProduct.lift _ _ _) (f ⊗ₜ[k] 1) = _
  simp

@[simp]
theorem eval_includeTranslation {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) (f : AdditiveGroupScheme.CoordinateRing k 1) :
    eval k a b (includeTranslation k f) =
      (AdditiveGroupScheme.algebraCoordinates k 1 C).symm (fun _ ↦ b) f := by
  change (Algebra.TensorProduct.lift _ _ _) (1 ⊗ₜ[k] f) = _
  simp

@[simp]
theorem eval_dilation {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) : eval k a b (dilationUnit k) = a := by
  rw [dilationUnit_val, eval_includeDilation, unitsMulEquivConv_symm_apply_single]

@[simp]
theorem eval_translation {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) : eval k a b (translation k) = b := by
  change eval k a b (includeTranslation k _) = b
  rw [eval_includeTranslation]
  exact AdditiveGroupScheme.algebraCoordinates_symm_apply_ι (fun _ ↦ b) 0

/-- An algebra map out of the affine coordinate algebra is determined by `a` and `b`. -/
theorem hom_ext {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    {f g : CoordinateRing k →ₐ[k] C}
    (ha : f (dilationUnit k) = g (dilationUnit k))
    (hb : f (translation k) = g (translation k)) : f = g := by
  apply Algebra.TensorProduct.ext
  · apply WithConv.toConv_injective
    apply (unitsMulEquivConv k C).injective
    apply Units.ext
    change f (dilationUnit k) = g (dilationUnit k)
    exact ha
  · apply (AdditiveGroupScheme.algebraCoordinates k 1 C).injective
    ext i
    rw [AdditiveGroupScheme.algebraCoordinates_apply,
      AdditiveGroupScheme.algebraCoordinates_apply]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hb

/-- The universal property of affine coordinates, over every commutative coefficient algebra. -/
def homCoordinates (k : Type u) [Field k] (C : Type v) [CommRing C] [Algebra k C] :
    (CoordinateRing k →ₐ[k] C) ≃ Cˣ × C where
  toFun f := (Units.map f.toMonoidHom (dilationUnit k), f (translation k))
  invFun p := eval k p.1 p.2
  left_inv f := by
    apply hom_ext
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      simp
    · simp

end

end AclGeom.AffineGroupScheme
