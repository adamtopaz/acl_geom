/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.AffineCoordinateRing
import AclGeom.Correspondence.AffineAction

/-!
# The algebraic affine group

The coordinate algebra `k[a,a⁻¹,b]` has comultiplication `a ↦ a ⊗ a` and
`b ↦ a ⊗ b + b ⊗ 1`. Its spectrum is the actual semidirect-product algebraic group
in blueprint equation (8.4a). The multiplication, unit and inverse are scheme morphisms;
the base-field point group is the existing `AffineTransformation k`.

Named consumer: the actual standard affine action, and the target of the original
curve-action classification. The classification of an arbitrary action remains owed.

**Status:** the actual affine algebraic group and its point coordinates are constructed.
Arbitrary-action classification remains open.
-/

namespace AclGeom.AffineGroupScheme

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable (k : Type u) [Field k]

/-- The semidirect-product comultiplication on affine coordinates. -/
def comul : CoordinateRing k →ₐ[k] CoordinateRing k ⊗[k] CoordinateRing k :=
  eval k
    (Units.map (Algebra.TensorProduct.includeLeft :
        CoordinateRing k →ₐ[k] CoordinateRing k ⊗[k] CoordinateRing k).toMonoidHom
        (dilationUnit k) *
      Units.map (Algebra.TensorProduct.includeRight :
        CoordinateRing k →ₐ[k] CoordinateRing k ⊗[k] CoordinateRing k).toMonoidHom
        (dilationUnit k))
    ((dilationUnit k : CoordinateRing k) ⊗ₜ[k] translation k + translation k ⊗ₜ[k] 1)

/-- The identity affine transformation has coordinates `(1,0)`. -/
def counit : CoordinateRing k →ₐ[k] k := eval k 1 0

/-- The inverse affine transformation has coordinates `(a⁻¹,-a⁻¹b)`. -/
def inverse : CoordinateRing k →ₐ[k] CoordinateRing k :=
  eval k (dilationUnit k)⁻¹ (-(↑((dilationUnit k)⁻¹) : CoordinateRing k) * translation k)

@[simp]
theorem comul_dilation : comul k (dilationUnit k) =
    (dilationUnit k : CoordinateRing k) ⊗ₜ[k] (dilationUnit k : CoordinateRing k) := by
  change eval k _ _ (dilationUnit k) = _
  rw [eval_dilation]
  simp

@[simp]
theorem comul_translation : comul k (translation k) =
    (dilationUnit k : CoordinateRing k) ⊗ₜ[k] translation k + translation k ⊗ₜ[k] 1 :=
  eval_translation _ _

@[simp]
theorem counit_dilation : counit k (dilationUnit k) = 1 := eval_dilation _ _

@[simp]
theorem counit_translation : counit k (translation k) = 0 := eval_translation _ _

@[simp]
theorem inverse_dilation :
    inverse k (dilationUnit k) = (↑((dilationUnit k)⁻¹) : CoordinateRing k) :=
  eval_dilation _ _

@[simp]
theorem inverse_translation : inverse k (translation k) =
    -(↑((dilationUnit k)⁻¹) : CoordinateRing k) * translation k :=
  eval_translation _ _

/-- The affine coordinate algebra with its semidirect-product bialgebra structure. -/
instance instBialgebra : Bialgebra k (CoordinateRing k) :=
  .ofAlgHom (comul k) (counit k)
    (by
      apply hom_ext
      · simp
      · simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
        abel)
    (by apply hom_ext <;> simp)
    (by apply hom_ext <;> simp)

@[simp]
theorem coalgebra_comul (f : CoordinateRing k) : Coalgebra.comul (R := k) f = comul k f :=
  rfl

@[simp]
theorem coalgebra_counit (f : CoordinateRing k) : Coalgebra.counit (R := k) f = counit k f :=
  rfl

/-- The affine coordinate algebra with its actual antipode. -/
instance instHopfAlgebra : HopfAlgebra k (CoordinateRing k) :=
  .ofAlgHom (inverse k)
    (by
      apply hom_ext
      · simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
          coalgebra_comul, comul_dilation, Bialgebra.counitAlgHom_apply, coalgebra_counit,
          counit_dilation, map_one]
        change inverse k (dilationUnit k) * (dilationUnit k : CoordinateRing k) = 1
        simp
      · simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
          coalgebra_comul, comul_translation, map_add, Bialgebra.counitAlgHom_apply,
          coalgebra_counit, counit_translation, map_zero]
        change inverse k (dilationUnit k) * translation k + inverse k (translation k) * 1 = 0
        simp)
    (by
      apply hom_ext
      · simp
      · simp [← _root_.mul_assoc])

/-- The affine algebraic group whose point law is `(c,d)(a,b)=(ca,cb+d)`. -/
def algebraicGroup : AlgebraicGroup k :=
  @AlgebraicGroup.ofGroupScheme k _
    (Grp.mk ((Spec (.of (CoordinateRing k))).asOver (Spec (.of k))))
    (locallyOfFiniteType_specOverSpec :
      LocallyOfFiniteType (Spec (.of (CoordinateRing k)) ↘ Spec (.of k)))
    (inferInstance : QuasiCompact (Spec (.of (CoordinateRing k)) ↘ Spec (.of k)))

/-- Characters of the affine Hopf algebra form the existing affine-transformation group. -/
def characterCoordinates : WithConv (CoordinateRing k →ₐ[k] k) ≃* AffineTransformation k where
  toEquiv := (WithConv.equiv _).trans ((homCoordinates k k).trans
    ({ toFun := fun p ↦ ⟨p.1, p.2⟩
       invFun := fun g ↦ (g.multiplier, g.shift)
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl } : (kˣ × k) ≃ AffineTransformation k))
  map_mul' f g := by
    apply AffineTransformation.ext
    · apply Units.ext
      change (f * g) (dilationUnit k) = f (dilationUnit k) * g (dilationUnit k)
      rw [AlgHom.convMul_apply, coalgebra_comul, comul_dilation]
      simp
    · change (f * g) (translation k) = f (dilationUnit k) * g (translation k) + f (translation k)
      rw [AlgHom.convMul_apply, coalgebra_comul, comul_translation]
      simp

/-- The actual group of `k`-points is the group of invertible affine transformations. -/
def pointsMulEquiv :
    (𝟙_ (Over (Spec (.of k))) ⟶ (algebraicGroup k).toGroupScheme.X) ≃* AffineTransformation k :=
  (hopfPointsMulEquiv k (CoordinateRing k)).trans (characterCoordinates k)

/-- An affine transformation gives the `Spec` of its coordinate-evaluation map. -/
theorem pointsMulEquiv_symm_apply_left (g : AffineTransformation k) :
    ((pointsMulEquiv k).symm g).left =
      Spec.map (CommRingCat.ofHom (eval k g.multiplier g.shift).toRingHom) := by
  change ((hopfPointsMulEquiv k (CoordinateRing k)).symm
    (WithConv.toConv (eval k g.multiplier g.shift))).left = _
  exact hopfPointsMulEquiv_symm_apply_left k (CoordinateRing k) _

end

end AclGeom.AffineGroupScheme
