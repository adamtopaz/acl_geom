/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineSchemeAction
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Nonconstant polynomial maps on the actual additive line

**Status:** nonconstant polynomial coordinate maps of Ga are finite and surjective over
every field, in every characteristic (#21). The variable is integral over the range of
polynomial evaluation: its leading coefficient is a unit. Finite generation gives a finite
ring map; nonconstant substitution is injective and integral lying-over gives surjectivity
on spectra. The actual symmetric-algebra coordinates and point formulas are retained.
Named consumer: `AdditiveTranslation.exists_finite_coordinate`, and then the actual
regular-affine subgroup translation theorem. No finite-map certificate is a premise.
-/

namespace AclGeom.AdditiveTranslation
noncomputable section
open Polynomial

/-- Named consumer: a nontrivial actual additive subgroup maps finitely to translations. -/
theorem polynomial_aeval_finite {k : Type*} [Field k] (p : k[X]) (hp : p.natDegree ≠ 0) :
    (aeval (R := k) p).toRingHom.Finite := by
  classical
  let f : k[X] →ₐ[k] k[X] := aeval p
  let S := f.range
  let p₀ : S := ⟨p, X, aeval_X p⟩
  let q : S[X] := p.map (algebraMap k S) - C p₀
  have hdeg : (C p₀ : S[X]).degree < (p.map (algebraMap k S)).degree := by
    rw [degree_map]
    exact lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hp))
  have hlead : q.leadingCoeff = algebraMap k S p.leadingCoeff :=
    (leadingCoeff_sub_of_degree_lt hdeg).trans
      (leadingCoeff_map_of_injective (algebraMap k S).injective p)
  have hq : aeval (X : k[X]) q = 0 := by
    simp only [q, map_sub, aeval_map_algebraMap, aeval_X_left_apply, aeval_C]
    change p - p = 0
    exact sub_self p
  have hi := isIntegral_leadingCoeff_smul q (X : k[X]) hq
  have hc : IsUnit q.leadingCoeff := by
    rw [hlead]
    exact (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (by
      intro hz; exact hp (hz ▸ natDegree_zero)))).map (algebraMap k S)
  let v : Sˣ := hc.unit
  have hv : (v : S) = q.leadingCoeff := hc.unit_spec
  have hx : IsIntegral S (X : k[X]) := by
    have hh := hi.smul ((v⁻¹ : Sˣ) : S)
    rw [← hv] at hh
    simpa only [smul_smul, Units.inv_mul, one_smul] using hh
  have ht : Algebra.adjoin S ({X} : Set k[X]) = ⊤ := by
    have hle : Algebra.adjoin k ({X} : Set k[X]) ≤
        (Algebra.adjoin S ({X} : Set k[X])).restrictScalars k :=
      Algebra.adjoin_le (show ({X} : Set k[X]) ⊆
        (Algebra.adjoin S ({X} : Set k[X])).restrictScalars k from by
          intro z hz
          change z ∈ Algebra.adjoin S ({X} : Set k[X])
          exact Algebra.subset_adjoin hz)
    rw [Polynomial.adjoin_X] at hle
    exact top_unique (fun _ _ ↦ hle trivial)
  have hfinite : Module.Finite S k[X] := by
    apply Module.finite_def.mpr
    rw [← Algebra.top_toSubmodule, ← ht]
    exact hx.fg_adjoin_singleton
  have hval : S.val.toRingHom.Finite := by
    change (algebraMap S k[X]).Finite
    exact RingHom.finite_algebraMap.mpr hfinite
  have hrange : f.rangeRestrict.toRingHom.Finite :=
    RingHom.Finite.of_surjective _ f.rangeRestrict_surjective
  have hcomp : S.val.toRingHom.comp f.rangeRestrict.toRingHom =
      (aeval (R := k) p).toRingHom := rfl
  rw [← hcomp]
  exact RingHom.Finite.comp hval hrange
end
end AclGeom.AdditiveTranslation

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable (k : Type u) [Field k]

/-- Named consumers: the actual additive-to-affine factorization and its finite coordinate. -/
def polynomialCoordinates : AdditiveGroupScheme.CoordinateRing k 1 ≃ₐ[k] Polynomial k :=
  (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1))).trans
    (MvPolynomial.uniqueAlgEquiv k (Fin 1))

/-- Named consumers: triviality of the multiplier and polynomial finiteness. -/
theorem polynomialCoordinates_coordinate :
    polynomialCoordinates k (AffineSchemeAction.lineCoordinate k) = Polynomial.X := by
  change (MvPolynomial.uniqueAlgEquiv k (Fin 1))
    ((SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1)))
      (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0))) = Polynomial.X
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]

end
end AclGeom.AdditiveTranslation

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k]

/-- Named consumers: the finite additive isogeny and its point translation formula. -/
theorem lineEval_polynomialCoordinates {C : Type u} [CommRing C] [Algebra k C]
    (x : C) (z : AdditiveGroupScheme.CoordinateRing k 1) :
    AffineSchemeAction.lineEval (k := k) x z =
      Polynomial.aeval x (polynomialCoordinates k z) := by
  have hh : (Polynomial.aeval x).comp (polynomialCoordinates k).toAlgHom =
      AffineSchemeAction.lineEval (k := k) x := by
    apply AffineSchemeAction.lineHom_ext
    change Polynomial.aeval x
      (polynomialCoordinates k (AffineSchemeAction.lineCoordinate k)) = _
    rw [polynomialCoordinates_coordinate, Polynomial.aeval_X,
      AffineSchemeAction.lineEval_lineCoordinate]
  exact (AlgHom.congr_fun hh z).symm

/-- Named consumers: nonconstancy and surjectivity of an actual additive isogeny. -/
theorem linePoint_comp_linePoint {C : Type u} [CommRing C] [Algebra k C]
    (x : C) (z : AdditiveGroupScheme.CoordinateRing k 1) :
    AffineSchemeAction.linePoint k x ≫ AffineSchemeAction.linePoint k z =
      AffineSchemeAction.linePoint k (AffineSchemeAction.lineEval (k := k) x z) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (k := k) x).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (k := k) z).toRingHom) =
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
        (AffineSchemeAction.lineEval (k := k) x z)).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((AffineSchemeAction.lineEval (k := k) x).comp
    (AffineSchemeAction.lineEval (k := k) z)).toRingHom = _
  apply congrArg AlgHom.toRingHom
  apply AffineSchemeAction.lineHom_ext
  rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate,
    AffineSchemeAction.lineEval_lineCoordinate]

/-- Named consumers: finiteness and surjectivity of the actual additive isogeny. -/
theorem lineEval_ringHom_eq (z : AdditiveGroupScheme.CoordinateRing k 1) :
    (AffineSchemeAction.lineEval (k := k) z).toRingHom =
      (polynomialCoordinates k).symm.toRingHom.comp
        ((Polynomial.aeval (R := k) (polynomialCoordinates k z)).toRingHom.comp
          (polynomialCoordinates k).toRingHom) := by
  let P := polynomialCoordinates k
  let p := P z
  change (AffineSchemeAction.lineEval (k := k) z).toRingHom =
    (P.symm.toAlgHom.comp ((Polynomial.aeval (R := k) p).comp P.toAlgHom)).toRingHom
  apply congrArg AlgHom.toRingHom
  apply AffineSchemeAction.lineHom_ext
  rw [AffineSchemeAction.lineEval_lineCoordinate]
  change z = P.symm (Polynomial.aeval p (P (AffineSchemeAction.lineCoordinate k)))
  rw [polynomialCoordinates_coordinate, Polynomial.aeval_X, AlgEquiv.symm_apply_apply]

/-- Named consumer: the actual nontrivial additive-subgroup translation factor is finite. -/
theorem isFinite_linePoint (z : AdditiveGroupScheme.CoordinateRing k 1)
    (hp : (polynomialCoordinates k z).natDegree ≠ 0) :
    IsFinite (AffineSchemeAction.linePoint k z).left := by
  let P := polynomialCoordinates k
  let p := P z
  change IsFinite (Spec.map (CommRingCat.ofHom
    (AffineSchemeAction.lineEval (k := k) z).toRingHom))
  apply (IsFinite.SpecMap_iff _).mpr
  rw [lineEval_ringHom_eq]
  exact P.symm.toRingEquiv.finite.comp ((polynomial_aeval_finite p hp).comp P.toRingEquiv.finite)

/-- Named consumer: the actual nontrivial additive-subgroup isogeny is surjective. -/
theorem surjective_linePoint (z : AdditiveGroupScheme.CoordinateRing k 1)
    (hp : (polynomialCoordinates k z).natDegree ≠ 0) :
    Surjective (AffineSchemeAction.linePoint k z).left := by
  let P := polynomialCoordinates k
  have hf : (AffineSchemeAction.lineEval (k := k) z).toRingHom.Finite :=
    (IsFinite.SpecMap_iff _).mp (isFinite_linePoint k z hp)
  have hinj : Function.Injective (AffineSchemeAction.lineEval (k := k) z).toRingHom := by
    rw [lineEval_ringHom_eq]
    have hpne : P z ≠ 0 := fun hz ↦ hp (hz ▸ Polynomial.natDegree_zero)
    have ht : Transcendental k (P z) := (P z).transcendental hp
      (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hpne))
    exact P.symm.injective.comp ((transcendental_iff_injective.mp ht).comp P.injective)
  constructor
  change Function.Surjective
    (PrimeSpectrum.comap (AffineSchemeAction.lineEval (k := k) z).toRingHom)
  exact hf.to_isIntegral.comap_surjective hinj

end
end AclGeom.AdditiveTranslation
