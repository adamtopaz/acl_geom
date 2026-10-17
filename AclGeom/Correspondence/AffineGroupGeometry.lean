/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineGroupScheme
import AclGeom.Correspondence.IntegralProduct
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Geometry of the concrete affine-group model

The named consumer is the actual affine action in blueprint (8.4a): the line has dimension
one, the multiplicative parameter has dimension one and the affine group has dimension two.
The affine coordinate ring is a polynomial ring over the Laurent-polynomial ring, which is
a nonfield principal ideal domain. Over an algebraically closed base, integrality also
constructs the required connected algebraic-group package internally.

**Status:** the additive, multiplicative and affine dimensions and the ACF connected affine
group are constructed.
-/

namespace AclGeom

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

/-- Localization preserves principal ideal rings. Named consumer: the dimension of the
multiplicative coordinate in the affine-group model. -/
theorem isPrincipalIdealRing_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing S where
  principal I := by
    refine ⟨⟨algebraMap R S (Submodule.IsPrincipal.generator (I.under R)), ?_⟩⟩
    calc
      I = Ideal.map (algebraMap R S) (I.under R) := (IsLocalization.map_under M S I).symm
      _ = Ideal.map (algebraMap R S)
          (Ideal.span {Submodule.IsPrincipal.generator (I.under R)}) := by
        rw [Ideal.span_singleton_generator]
      _ = Ideal.span {algebraMap R S (Submodule.IsPrincipal.generator (I.under R))} := by
        rw [Ideal.map_span, Set.image_singleton]

/-- The Laurent-polynomial ring of the multiplicative coordinate is a principal ideal ring. -/
theorem multiplicativeCoordinate_isPrincipal (k : Type u) [Field k] :
    IsPrincipalIdealRing (AddMonoidAlgebra k ℤ) :=
  isPrincipalIdealRing_of_isLocalization
    (S := LaurentPolynomial k) (Submonoid.powers (Polynomial.X : Polynomial k))

/-- The multiplicative coordinate algebra is not a field: evaluation at `T=1` identifies
two distinct Laurent polynomials. -/
theorem multiplicativeCoordinate_not_isField (k : Type u) [Field k] :
    ¬ IsField (AddMonoidAlgebra k ℤ) := by
  intro h
  let := h.toField
  let f := ((unitsMulEquivConv k k).symm (1 : kˣ)).ofConv
  have heq : f (AddMonoidAlgebra.single 1 1) = f 1 := by
    rw [unitsMulEquivConv_symm_apply_single, map_one]
    rfl
  have hbad := f.toRingHom.injective heq
  have hcoeff := congrArg (fun p : AddMonoidAlgebra k ℤ ↦ p.coeff (1 : ℤ)) hbad
  change (Finsupp.single (1 : ℤ) (1 : k)) 1 = (Finsupp.single (0 : ℤ) (1 : k)) 1 at hcoeff
  norm_num [Finsupp.single_apply] at hcoeff

/-- The multiplicative coordinate has Krull dimension one over every field. -/
theorem multiplicativeCoordinate_dimension (k : Type u) [Field k] :
    ringKrullDim (AddMonoidAlgebra k ℤ) = 1 := by
  have := multiplicativeCoordinate_isPrincipal k
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (multiplicativeCoordinate_not_isField k)

/-- Every additive vector group has its expected scheme dimension. -/
theorem additiveGroup_dimension (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (AdditiveGroupScheme.algebraicGroup k n).carrier = n := by
  change topologicalKrullDim (PrimeSpectrum (AdditiveGroupScheme.CoordinateRing k n)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin n))).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- The multiplicative algebraic group is one-dimensional. -/
theorem multiplicativeGroup_dimension (k : Type u) [Field k] :
    topologicalKrullDim (multiplicativeGroup k).carrier = 1 := by
  change topologicalKrullDim (PrimeSpectrum (AddMonoidAlgebra k ℤ)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact multiplicativeCoordinate_dimension k

namespace AffineGroupScheme

/-- The affine coordinate algebra is a polynomial ring in its translation coordinate over
the Laurent-polynomial dilation algebra. Named consumers: integrality and dimension. -/
def polynomialEquiv (k : Type u) [Field k] :
    CoordinateRing k ≃ₐ[k] MvPolynomial (Fin 1) (AddMonoidAlgebra k ℤ) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : AddMonoidAlgebra k ℤ ≃ₐ[k] AddMonoidAlgebra k ℤ)
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1)))).trans
    ((MvPolynomial.algebraTensorAlgEquiv k (AddMonoidAlgebra k ℤ)).restrictScalars k)

instance coordinateRingIsDomain (k : Type u) [Field k] : IsDomain (CoordinateRing k) := by
  have : Nontrivial (CoordinateRing k) := (polynomialEquiv k).toEquiv.nontrivial
  have : NoZeroDivisors (CoordinateRing k) := (polynomialEquiv k).toMulEquiv.noZeroDivisors
  exact NoZeroDivisors.to_isDomain _

/-- The actual affine algebraic group has dimension two. -/
theorem dimension (k : Type u) [Field k] :
    topologicalKrullDim (algebraicGroup k).carrier = 2 := by
  have := multiplicativeCoordinate_isPrincipal k
  change topologicalKrullDim (PrimeSpectrum (CoordinateRing k)) = 2
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (polynomialEquiv k).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, multiplicativeCoordinate_dimension]
  norm_num

/-- Over an algebraically closed base the model is an actual connected algebraic group. -/
def connectedAlgebraicGroup (k : Type u) [Field k] [IsAlgClosed k] :
    ConnectedAlgebraicGroup k := by
  haveI : IsIntegral (algebraicGroup k).carrier :=
    (inferInstance : IsIntegral (Spec (.of (CoordinateRing k))))
  exact
    { toAlgebraicGroup := algebraicGroup k
      geometricallyIntegral :=
        geometricallyIntegral_of_isAlgClosed (algebraicGroup k).structureMap }

end AffineGroupScheme

end

end AclGeom
