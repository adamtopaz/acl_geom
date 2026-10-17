/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Reconstruct.Scalar
import AclGeom.Transfer.JCorrectness

/-!
# The class-field map in the source setting

Blueprint Prop `interpreted-reconstruction` asserts that a geometry isomorphism maps a chosen
Frobenius class to a Frobenius class, induces a field isomorphism between the interpreted fields,
and, composed with the two decoding equivalences, gives a field isomorphism `K ≃+* L`.  The
advertised literal decoded interpretation is obstructed: the literal ratio relation is not an
equivalence relation and the advertised literal decoder is refuted.  Its corrected counterpart is
the conditional `interpretedRingEquiv`, built from the corrected ratio carriers.

`exists_interpretedRingEquiv_ratio` states this corrected counterpart in the source setting, with
the chosen class and the decoding diagram retained.  For perfect fields, `K` of transcendence
degree at least five and a closed-lattice order isomorphism `e`, the class of the chosen semantic
base tuple `j(x₀, a)` is carried to the class of a semantic image base `j(x₀', a')`, and there is
a field isomorphism `φ : K ≃+* L` with `φ(x₁/x₂) = y₁/y₂` whenever `e` carries `j(x₁, a)` and
`j(x₂, a)` to `j(y₁, a')` and `j(y₂, a')`.  This is the decoding diagram on representatives: the
class pair `(j(x₁, a), j(x₂, a))` decodes to `x₁/x₂`, and its image decodes to `y₁/y₂`.

The ratio statement is not vacuous: every member `j(x, a)` of the chosen class has a semantic
image `j(y, a')` in the class of the image base, since the class map preserves the Frobenius
relation (`frobEq_map_iff`) and, under these hypotheses, the class of `j(x₀', a')` consists of the
tuples `j(y, a')` (`frobEq_jTupleOf_iff`).

The rank of `L`, the characteristic exponents, both ACF completeness proofs and the image base
are supplied internally.  No relatively algebraically closed base is assumed: base recovery and
the compatibility of `φ` with `e` are separate statements (`closedIFMap_interpretedRingEquiv`).
This is the corrected source-setting record of the proposition; it is not a new reconstruction
endpoint, and it does not repair the literal decoder.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the corrected class-field map with its decoding diagram is proved in the source
setting (#8).
-/

namespace AclGeom

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- **The class-field map in the source setting** (the corrected counterpart of blueprint Prop
`interpreted-reconstruction`).  For perfect fields with `trdeg(K/k) ≥ 5` and a closed-lattice
order isomorphism `e`, the chosen semantic base tuple `j(x₀, a)` is carried to a semantic image
base `j(x₀', a')`, and some field isomorphism `φ : K ≃+* L` satisfies the decoding diagram
`φ(x₁/x₂) = y₁/y₂` whenever `e` carries `j(x₁, a)` and `j(x₂, a)` to `j(y₁, a')` and
`j(y₂, a')`.  Completeness, the characteristic exponents and the rank of `L` are supplied
internally. -/
theorem exists_interpretedRingEquiv_ratio [PerfectField K] [PerfectField L]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (e : ClosedIF k K ≃o ClosedIF l L)
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    ∃ (x₀' a' : L) (h₀' : AlgebraicIndependent l ![x₀', a']),
      Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀' ∧
      ∃ φ : K ≃+* L, ∀ {x₁ x₂ : K} {y₁ y₂ : L} (h₁ : AlgebraicIndependent k ![x₁, a])
        (h₂ : AlgebraicIndependent k ![x₂, a]) (h₁' : AlgebraicIndependent l ![y₁, a'])
        (h₂' : AlgebraicIndependent l ![y₂, a']),
        Point.map e ∘ jTupleOf x₁ a h₁ = jTupleOf y₁ a' h₁' →
        Point.map e ∘ jTupleOf x₂ a h₂ = jTupleOf y₂ a' h₂' → φ (x₁ / x₂) = y₁ / y₂ := by
  -- The rank of `L`, both completeness proofs and the image base.
  have htr' : (5 : Cardinal) ≤ Algebra.trdeg l L :=
    Cardinal.ofNat_le_lift_iff.1 <| (Cardinal.ofNat_le_lift_iff.2 htr).trans
      (lift_trdeg_le_of_orderIso e)
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have : IsAlgClosed ↥(algebraicClosure l (AlgebraicClosure L)) := IsAlgClosure.isAlgClosed l
  have hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K)))
      (AlgebraicClosure K) := jCompletenessACF (five_le_trdeg_algebraicClosure htr)
  have hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L)))
      (AlgebraicClosure L) := jCompletenessACF (five_le_trdeg_algebraicClosure htr')
  obtain ⟨x₀', a', h₀', hφ⟩ := exists_map_jTupleOf_eq (ringExpChar L) hcomp' e htr h₀
  refine ⟨x₀', a', h₀', hφ,
    interpretedRingEquiv (ringExpChar K) htr hcomp (ringExpChar L) htr' hcomp' e h₀ h₀' hφ,
    fun {x₁ x₂ y₁ y₂} h₁ h₂ h₁' h₂' e₁ e₂ ↦ ?_⟩
  -- The coordinate diagram `yᵢ · φ(x₀) = φ(xᵢ) · x₀'` for both representatives.
  have c₁ := interpretedRingEquiv_coord (ringExpChar K) htr hcomp (ringExpChar L) htr' hcomp'
    e h₀ h₀' hφ h₁ h₁' e₁
  have c₂ := interpretedRingEquiv_coord (ringExpChar K) htr hcomp (ringExpChar L) htr' hcomp'
    e h₀ h₀' hφ h₂ h₂' e₂
  have hx₀' : x₀' ≠ 0 := AlgebraicIndependent.ne_zero h₀' 0
  have hφx₂ : interpretedRingEquiv (ringExpChar K) htr hcomp (ringExpChar L) htr' hcomp' e h₀ h₀'
      hφ x₂ ≠ 0 := (map_ne_zero _).2 (AlgebraicIndependent.ne_zero h₂ 0)
  have hy₂ : y₂ ≠ 0 := AlgebraicIndependent.ne_zero h₂' 0
  rw [map_div₀, div_eq_div_iff hφx₂ hy₂]
  exact mul_right_cancel₀ hx₀' (by linear_combination (-y₂) * c₁ + y₁ * c₂)

end AclGeom
