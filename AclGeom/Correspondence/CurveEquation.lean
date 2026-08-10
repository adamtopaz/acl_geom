/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Composition
import AclGeom.Correspondence.CurveIdeal
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Canonical equations of finite-correspondence germs

A generic finite correspondence on the affine line has a principal prime
vanishing ideal.  A generator of that ideal is only determined up to a
nonzero scalar, so its coefficients do not yet give intrinsic coordinates
on a family of correspondences.  This file removes that ambiguity by making
the generator monic for the fixed lexicographic monomial order.

The resulting `curveEquation` is determined by the branch ideal itself.
This is the normalization needed before adjoining its coefficients to form
the parameter field of a correspondence germ.
-/

namespace AclGeom

open MvPolynomial
open scoped MonomialOrder

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The source coordinate of a finite-correspondence pair is transcendental
over the field of definition. -/
theorem source_transcendental' : Transcendental k P.source := by
  intro h
  exact P.source_generic (mem_racl_empty_of_isAlgebraic h)

/-- An arbitrary prime generator of the curve ideal.  Its scalar ambiguity
is removed in `curveEquation` below. -/
private def rawCurveEquation : MvPolynomial (Fin 2) k :=
  Classical.choose
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)

private theorem rawCurveEquation_prime : Prime P.rawCurveEquation :=
  (Classical.choose_spec
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)).1

private theorem ideal_eq_span_rawCurveEquation :
    P.ideal = Ideal.span {P.rawCurveEquation} :=
  (Classical.choose_spec
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)).2

/-- The intrinsic equation of a finite-correspondence branch: the prime
generator of its ideal, scaled to have lexicographic leading coefficient
one. -/
def curveEquation : MvPolynomial (Fin 2) k :=
  C ((MonomialOrder.lex.leadingCoeff P.rawCurveEquation)⁻¹) * P.rawCurveEquation

private theorem leadingCoeff_rawCurveEquation_ne_zero :
    MonomialOrder.lex.leadingCoeff P.rawCurveEquation ≠ 0 :=
  MonomialOrder.leadingCoeff_ne_zero_iff.mpr P.rawCurveEquation_prime.ne_zero

/-- The canonical curve equation is monic in the fixed lexicographic order. -/
theorem curveEquation_monic : MonomialOrder.lex.Monic P.curveEquation := by
  rw [MonomialOrder.Monic, curveEquation, MonomialOrder.leadingCoeff_mul,
    MonomialOrder.leadingCoeff_C]
  exact inv_mul_cancel₀ P.leadingCoeff_rawCurveEquation_ne_zero

private theorem curveEquation_associated_raw :
    Associated P.curveEquation P.rawCurveEquation := by
  apply associated_unit_mul_left
  exact IsUnit.map MvPolynomial.C
    (isUnit_iff_ne_zero.mpr (inv_ne_zero P.leadingCoeff_rawCurveEquation_ne_zero))

/-- Scaling to the monic generator preserves primality. -/
theorem curveEquation_prime : Prime P.curveEquation :=
  P.curveEquation_associated_raw.symm.prime P.rawCurveEquation_prime

/-- The canonical equation generates exactly the branch ideal. -/
theorem ideal_eq_span_curveEquation :
    P.ideal = Ideal.span {P.curveEquation} := by
  rw [P.ideal_eq_span_rawCurveEquation]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    P.curveEquation_associated_raw.symm

/-- The selected generic endpoint pair satisfies its canonical equation. -/
theorem aeval_curveEquation :
    aeval ![P.source, P.target] P.curveEquation = 0 := by
  rw [← mem_idealOf_iff k]
  change P.curveEquation ∈ P.ideal
  rw [P.ideal_eq_span_curveEquation]
  exact Ideal.subset_span (Set.mem_singleton P.curveEquation)

/-- Two monic multivariate polynomials over a field which are associated are
equal. -/
private theorem eq_of_monic_of_associated
    {f g : MvPolynomial (Fin 2) k}
    (hf : MonomialOrder.lex.Monic f) (hg : MonomialOrder.lex.Monic g)
    (hfg : Associated f g) : f = g := by
  obtain ⟨u, hu⟩ := hfg
  obtain ⟨c, hcunit, huc⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hlc : MonomialOrder.lex.leadingCoeff (f * (u : MvPolynomial (Fin 2) k)) = c := by
    rw [huc, MonomialOrder.leadingCoeff_mul, MonomialOrder.leadingCoeff_C,
      hf.leadingCoeff_eq_one, one_mul]
  have hc : c = 1 := by
    rw [hu, hg.leadingCoeff_eq_one] at hlc
    exact hlc.symm
  rw [← hu, huc, hc, map_one, mul_one]

/-- The monic curve equation depends only on the selected branch ideal.
Thus its coefficients are intrinsic coordinates of the correspondence germ,
independent of all choices in the principal-generator theorem. -/
theorem curveEquation_eq_of_ideal_eq
    (Q : FiniteCorrespondencePair k Ω) (h : P.ideal = Q.ideal) :
    P.curveEquation = Q.curveEquation := by
  apply eq_of_monic_of_associated P.curveEquation_monic Q.curveEquation_monic
  rw [← Ideal.span_singleton_eq_span_singleton]
  rw [← P.ideal_eq_span_curveEquation, ← Q.ideal_eq_span_curveEquation, h]

section CoefficientField

variable (k : Type*) [Field k] [Algebra k Ω]
variable (E : IntermediateField k Ω)
variable (P : FiniteCorrespondencePair E Ω)

/-- The coefficients of the canonical curve equation, viewed in the common
ambient field.  Taking the range over all monomials is harmless: all but
finitely many entries are zero. -/
def curveCoefficientSet : Set Ω :=
  Set.range fun d : (Fin 2 →₀ ℕ) => ((P.curveEquation.coeff d : E) : Ω)

/-- The field generated over `k` by the intrinsic coefficients of a finite
correspondence germ defined over an intermediate field `E`. -/
def curveCoefficientField : IntermediateField k Ω :=
  IntermediateField.adjoin k (P.curveCoefficientSet k E)

/-- Every canonical coefficient belongs to the coefficient field. -/
theorem coeff_mem_curveCoefficientField (d : Fin 2 →₀ ℕ) :
    ((P.curveEquation.coeff d : E) : Ω) ∈ P.curveCoefficientField k E :=
  IntermediateField.subset_adjoin k _ ⟨d, rfl⟩

/-- The intrinsic coefficient field is contained in every field of
definition used to present the correspondence. -/
theorem curveCoefficientField_le : P.curveCoefficientField k E ≤ E := by
  rw [curveCoefficientField]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro z ⟨d, rfl⟩
  exact (P.curveEquation.coeff d).2

/-- The canonical equation descended to its own coefficient field. -/
def curveEquationOverCoefficientField :
    MvPolynomial (Fin 2) (P.curveCoefficientField k E) :=
  P.curveEquation.support.sum fun d =>
    monomial d
      ⟨((P.curveEquation.coeff d : E) : Ω),
        P.coeff_mem_curveCoefficientField k E d⟩

/-- After inclusion into the ambient field, the descended equation is the
original canonical equation with its coefficients included from `E`. -/
theorem map_curveEquationOverCoefficientField :
    MvPolynomial.map (algebraMap (P.curveCoefficientField k E) Ω)
        (P.curveEquationOverCoefficientField k E) =
      MvPolynomial.map (algebraMap E Ω) P.curveEquation := by
  classical
  rw [curveEquationOverCoefficientField, map_sum]
  conv_rhs => rw [P.curveEquation.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp

/-- The descended canonical equation remains nonzero. -/
theorem curveEquationOverCoefficientField_ne_zero :
    P.curveEquationOverCoefficientField k E ≠ 0 := by
  intro h
  have hm := congrArg
    (MvPolynomial.map (algebraMap (P.curveCoefficientField k E) Ω)) h
  rw [P.map_curveEquationOverCoefficientField k E, map_zero] at hm
  exact P.curveEquation_prime.ne_zero
    ((MvPolynomial.map_injective (algebraMap E Ω) (algebraMap E Ω).injective) hm)

/-- The selected generic endpoint pair satisfies the canonical equation
already over its intrinsic coefficient field. -/
theorem aeval_curveEquationOverCoefficientField :
    aeval ![P.source, P.target] (P.curveEquationOverCoefficientField k E) = 0 := by
  have hm := congrArg (aeval ![P.source, P.target])
    (P.map_curveEquationOverCoefficientField k E)
  rw [MvPolynomial.aeval_map_algebraMap,
    MvPolynomial.aeval_map_algebraMap, P.aeval_curveEquation] at hm
  exact hm

/-- Equal branch ideals have equal intrinsic coefficient sets. -/
theorem curveCoefficientSet_eq_of_ideal_eq
    (Q : FiniteCorrespondencePair E Ω) (h : P.ideal = Q.ideal) :
    P.curveCoefficientSet k E = Q.curveCoefficientSet k E := by
  rw [curveCoefficientSet, curveCoefficientSet,
    P.curveEquation_eq_of_ideal_eq Q h]

/-- Equal branch ideals therefore have the same intrinsic coefficient
field. -/
theorem curveCoefficientField_eq_of_ideal_eq
    (Q : FiniteCorrespondencePair E Ω) (h : P.ideal = Q.ideal) :
    P.curveCoefficientField k E = Q.curveCoefficientField k E := by
  rw [curveCoefficientField, curveCoefficientField,
    P.curveCoefficientSet_eq_of_ideal_eq k E Q h]

end CoefficientField

end FiniteCorrespondencePair

end

end AclGeom
