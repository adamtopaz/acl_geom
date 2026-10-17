/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveEquation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Selected branches after extending a coefficient field

A scalar finite-correspondence branch stays a selected minimal prime after coefficient
extension whenever its endpoints still present a finite correspondence. The extended ideal
may split. Named intended consumer: the literal parameter-field branch of the six-point
incidence calculation (8.4c) in `Config.ParameterField`.

The selected ideal may be a proper component of the extension; the other branches and a
common normal cover require separate arguments.
-/

namespace AclGeom

open MvPolynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The same finite-correspondence endpoints select a minimal prime of the extended curve
ideal over a larger coefficient field. Neither coefficient field needs to be closed. -/
theorem FiniteCorrespondencePair.ideal_mem_minimalPrimes_baseChange
    {E F : IntermediateField k Ω} (hEF : E ≤ F)
    (P : FiniteCorrespondencePair E Ω) (Q : FiniteCorrespondencePair F Ω)
    (hs : P.source = Q.source) (ht : P.target = Q.target) :
    Q.ideal ∈ (P.ideal.map
      (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F))).minimalPrimes := by
  have hle :
      P.ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F)) ≤ Q.ideal := by
    simpa only [FiniteCorrespondencePair.ideal, hs, ht] using
      idealOf_map_le_of_intermediateField_le hEF ![Q.source, Q.target]
  have hnonzero :
      MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F) P.curveEquation ≠ 0 := by
    intro h
    exact P.curveEquation_prime.ne_zero
      ((MvPolynomial.map_injective _ (IntermediateField.inclusion hEF).injective)
        (h.trans (map_zero _).symm))
  have hsmall : Q.ideal.height ≤ 1 := by
    rw [Q.ideal_eq_span_curveEquation]
    exact Ideal.height_span_singleton_le_one Q.curveEquation_prime.not_isUnit
  have hlarge :
      1 ≤ (P.ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F))).height := by
    rw [P.ideal_eq_span_curveEquation, Ideal.map_span, Set.image_singleton]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero)
  have : Q.ideal.IsPrime := by
    change (idealOf F ![Q.source, Q.target]).IsPrime
    infer_instance
  exact Ideal.mem_minimalPrimes_of_height_le hle (hsmall.trans hlarge)

end AclGeom
