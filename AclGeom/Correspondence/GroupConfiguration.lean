/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.GroupChunk

/-!
# The six-point group-configuration bookkeeping

The group-theoretic identities in the final part of blueprint Theorem
`six-point-group`, separated from the geometric extraction of the group:

* `differenceChart e a = e⁻¹a` is the chart based at the generic arrow `e`;
* `differenceChart_mul` and `differenceChart_inv` compute multiplication and
  inverse in that chart;
* `groupoidComposite_eq` is the four-arrow cancellation calculation used to
  prove closure of the chart;
* `sixPointGroupTuple α γ ε` is the ordered sextuple
  `(α, γ, αγ, ε, αγε, γε)`, and
  `sixPointGroupTuple_relations` proves its four named product relations.

These lemmas are valid in every group.  The still-geometric part of the
blueprint theorem must construct the group and the finite-cover coordinates;
once it has done so, the conclusions below supply its exact normalized output.

**Status:** complete algebraic bookkeeping for M4a / blueprint (8.3); the
geometric six-point extraction remains in progress.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

section DifferenceChart

variable {G : Type*} [Group G]

/-- The difference chart based at `e`, sending a family member `a` to
the endomorphism `e⁻¹a`. -/
def differenceChart (e a : G) : G := e⁻¹ * a

/-- The family parameter representing the product of two elements in the
difference chart. -/
def differenceProduct (e a b : G) : G := a * e⁻¹ * b

/-- Multiplication in the difference chart is represented by
`a e⁻¹ b`, exactly as in blueprint (8.4). -/
theorem differenceChart_mul (e a b : G) :
    differenceChart e a * differenceChart e b =
      differenceChart e (differenceProduct e a b) := by
  simp [differenceChart, differenceProduct, mul_assoc]

/-- The family parameter representing the inverse of `e⁻¹a`. -/
def differenceInverse (e a : G) : G := e * a⁻¹ * e

/-- Inversion is closed in the difference chart, represented by
`e a⁻¹ e`. -/
theorem differenceChart_inv (e a : G) :
    (differenceChart e a)⁻¹ = differenceChart e (differenceInverse e a) := by
  simp [differenceChart, differenceInverse, mul_assoc]

/-- The explicit cancellation calculation in the three-object
correspondence groupoid.  With
`u = se`, `sₐ = ua⁻¹`, `u_b = sb`, and `c = sₐ⁻¹u_b`, the output is
`c = ae⁻¹b`. -/
theorem groupoidComposite_eq (s e a b : G) :
    (((s * e) * a⁻¹)⁻¹) * (s * b) = differenceProduct e a b := by
  simp [differenceProduct, mul_assoc]

/-- The parameter formula from the groupoid cancellation agrees with
multiplication in the difference chart. -/
theorem groupoidComposite_chart (s e a b : G) :
    differenceChart e a * differenceChart e b =
      differenceChart e ((((s * e) * a⁻¹)⁻¹) * (s * b)) := by
  rw [groupoidComposite_eq]
  exact differenceChart_mul e a b

end DifferenceChart

section SixPointPattern

variable {G : Type*} [Group G]

/-- The normalized six-point group configuration of blueprint (8.3), in
the order `(S, T, U, S', T', U')`. -/
def sixPointGroupTuple (α γ ε : G) : Fin 6 → G :=
  ![α, γ, α * γ, ε, α * γ * ε, γ * ε]

@[simp] theorem sixPointGroupTuple_zero (α γ ε : G) :
    sixPointGroupTuple α γ ε 0 = α := rfl

@[simp] theorem sixPointGroupTuple_one (α γ ε : G) :
    sixPointGroupTuple α γ ε 1 = γ := rfl

@[simp] theorem sixPointGroupTuple_two (α γ ε : G) :
    sixPointGroupTuple α γ ε 2 = α * γ := rfl

@[simp] theorem sixPointGroupTuple_three (α γ ε : G) :
    sixPointGroupTuple α γ ε 3 = ε := rfl

@[simp] theorem sixPointGroupTuple_four (α γ ε : G) :
    sixPointGroupTuple α γ ε 4 = α * γ * ε := rfl

@[simp] theorem sixPointGroupTuple_five (α γ ε : G) :
    sixPointGroupTuple α γ ε 5 = γ * ε := rfl

/-- The four product identities corresponding to the four dependent
triples of a partial quadrangle. -/
theorem sixPointGroupTuple_relations (α γ ε : G) :
    sixPointGroupTuple α γ ε 2 =
        sixPointGroupTuple α γ ε 0 * sixPointGroupTuple α γ ε 1 ∧
    sixPointGroupTuple α γ ε 4 =
        sixPointGroupTuple α γ ε 0 * sixPointGroupTuple α γ ε 5 ∧
    sixPointGroupTuple α γ ε 5 =
        sixPointGroupTuple α γ ε 1 * sixPointGroupTuple α γ ε 3 ∧
    sixPointGroupTuple α γ ε 4 =
        sixPointGroupTuple α γ ε 2 * sixPointGroupTuple α γ ε 3 := by
  simp [mul_assoc]

end SixPointPattern

end

end AclGeom
