/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.CurveIdeal
import AclGeom.Closure.ClosedLattice

/-!
# The multiplicative correspondence theorem: setup and bookkeeping

The hypothesis block of blueprint Theorem `mulcorr` (8.9), two-pair core:
two finite correspondences with independent generic points whose *products*
are interalgebraic, all coordinates nonzero. The chain mirrors the additive
one — relocation over the enlarged base, product-locus preservation
(`idealOf_mul_eq_of_joint`), the scaling machinery in place of translation —
with the classification running through the support-comparison lemma
`monomial_prod_eq_of_span_scale_eq` instead of the Hopf argument.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3, checklist C5/C7).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The hypothesis block of the multiplicative correspondence theorem
(blueprint Thm 8.9, two-pair core): finite correspondences over `k` with
independent generic points, nonzero coordinates, and interalgebraic
products. -/
structure MulCorrSetup (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] where
  /-- First coordinate of the first correspondence. -/
  x₁ : Ω
  /-- Second coordinate of the first correspondence. -/
  y₁ : Ω
  /-- First coordinate of the second correspondence. -/
  x₂ : Ω
  /-- Second coordinate of the second correspondence. -/
  y₂ : Ω
  /-- The generic points are independent. -/
  indep : AlgebraicIndependent k ![x₁, x₂]
  /-- The second coordinates are nonzero. -/
  y₁_ne : y₁ ≠ 0
  /-- … both of them. -/
  y₂_ne : y₂ ≠ 0
  /-- The first pair is a finite correspondence. -/
  y₁_mem : y₁ ∈ racl k {x₁}
  /-- … in both directions. -/
  x₁_mem : x₁ ∈ racl k {y₁}
  /-- The second pair is a finite correspondence. -/
  y₂_mem : y₂ ∈ racl k {x₂}
  /-- … in both directions. -/
  x₂_mem : x₂ ∈ racl k {y₂}
  /-- The products are interalgebraic: `y₁y₂` over `x₁x₂`. -/
  mul_mem : y₁ * y₂ ∈ racl k {x₁ * x₂}
  /-- … and conversely. -/
  mul_mem' : x₁ * x₂ ∈ racl k {y₁ * y₂}

namespace MulCorrSetup

variable (S : MulCorrSetup k Ω)

/-- The base field of the joint relocation: `k(x₁, y₁)`. -/
def base : IntermediateField k Ω :=
  adjoin k {S.x₁, S.y₁}

/-- The base is contained in the closure of `x₁`. -/
theorem base_le_racl : S.base ≤ racl k {S.x₁} := by
  refine adjoin_le_iff.2 ?_
  rintro z (rfl | rfl)
  · exact subset_racl k _ rfl
  · exact S.y₁_mem

/-- The independence counts, exactly as in the additive setup. -/
theorem x₂_notMem : S.x₂ ∉ racl k {S.x₁} :=
  AlgebraicIndependent.notMem_racl_pair S.indep

/-- … and symmetrically. -/
theorem x₁_notMem : S.x₁ ∉ racl k {S.x₂} :=
  AlgebraicIndependent.notMem_racl_pair' S.indep

/-- The transcendental coordinates are nonzero. -/
theorem x₁_ne : S.x₁ ≠ 0 := by
  intro h
  refine S.x₁_notMem ?_
  rw [h]
  exact zero_mem _

/-- … both of them. -/
theorem x₂_ne : S.x₂ ≠ 0 := by
  intro h
  refine S.x₂_notMem ?_
  rw [h]
  exact zero_mem _

/-- `x₂` remains transcendental over the enlarged base `k(x₁, y₁)`. -/
theorem transcendental_x₂ : Transcendental ↥S.base S.x₂ := by
  intro halg
  refine S.x₂_notMem ((isRAC_racl {S.x₁}).mem_of_isAlgebraic ?_)
  exact isAlgebraic_of_le S.base_le_racl halg

/-- The second correspondence relation persists over the enlarged base. -/
theorem y₂_mem_baseRacl : S.y₂ ∈ racl ↥S.base {S.x₂} :=
  racl_subset_racl_base S.base {S.x₂} S.y₂_mem

/-- The first coordinate of the product correspondence is transcendental:
dividing by `x₁` would otherwise make `x₂` algebraic over `k(x₁)`. -/
theorem mul_fst_transcendental : Transcendental k (S.x₁ * S.x₂) := by
  intro halg
  have hmem : S.x₁ * S.x₂ ∈ racl k {S.x₁} :=
    (mem_racl_iff k).2 (halg.tower_top _)
  have hx₂ : S.x₂ ∈ racl k {S.x₁} := by
    have hdiv := div_mem hmem (subset_racl k ({S.x₁} : Set Ω) rfl)
    have hcancel : S.x₁ * S.x₂ / S.x₁ = S.x₂ := by
      rw [mul_comm, mul_div_assoc, div_self S.x₁_ne, mul_one]
    rwa [hcancel] at hdiv
  exact S.x₂_notMem hx₂

/-- The product pair is a two-way correspondence in the first coordinate. -/
theorem mul_fst_ne : S.x₁ * S.x₂ ≠ 0 :=
  mul_ne_zero S.x₁_ne S.x₂_ne

/-- … and in the second. -/
theorem mul_snd_ne : S.y₁ * S.y₂ ≠ 0 :=
  mul_ne_zero S.y₁_ne S.y₂_ne

end MulCorrSetup

end

end AclGeom
