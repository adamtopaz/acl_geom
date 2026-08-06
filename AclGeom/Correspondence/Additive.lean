/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.AddPolynomial
import AclGeom.Closure.ClosedLattice

/-!
# The additive correspondence theorem: setup and bookkeeping

The hypothesis block of blueprint Theorem `addcorr` (8.8), two-pair core:
two finite correspondences `(x₁, y₁)`, `(x₂, y₂)` over `k` whose independent
generic points have interalgebraic sums. This file develops the pregeometry
bookkeeping of the fused curve-coset chain (design on the tracking issue):

* `AddCorrSetup`: the hypothesis block;
* `AddCorrSetup.transcendental_x₂`: `x₂` remains transcendental over
  `k(x₁, y₁)` — the base for the joint relocation;
* `AddCorrSetup.y₂_mem_baseRacl`: the correspondence relation persists over
  the enlarged base.

The conclusion of the theorem (equations `Q(yᵢ) = P(xᵢ) + dᵢ` with additive
`P, Q`) is assembled in later slices.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C6).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The hypothesis block of the additive correspondence theorem
(blueprint Thm 8.8, two-pair core): finite correspondences over `k` with
independent generic points and interalgebraic sums. -/
structure AddCorrSetup (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] where
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
  /-- The first pair is a finite correspondence: `y₁` is algebraic over `x₁`. -/
  y₁_mem : y₁ ∈ racl k {x₁}
  /-- … and `x₁` is algebraic over `y₁`. -/
  x₁_mem : x₁ ∈ racl k {y₁}
  /-- The second pair is a finite correspondence. -/
  y₂_mem : y₂ ∈ racl k {x₂}
  /-- … in both directions. -/
  x₂_mem : x₂ ∈ racl k {y₂}
  /-- The sums are interalgebraic: `y₁ + y₂` over `x₁ + x₂`. -/
  sum_mem : y₁ + y₂ ∈ racl k {x₁ + x₂}
  /-- … and conversely. -/
  sum_mem' : x₁ + x₂ ∈ racl k {y₁ + y₂}

namespace AddCorrSetup

variable (S : AddCorrSetup k Ω)

/-- The base field of the joint relocation: `k(x₁, y₁)`. -/
def base : IntermediateField k Ω :=
  adjoin k {S.x₁, S.y₁}

/-- The base is contained in the closure of `x₁`. -/
theorem base_le_racl : S.base ≤ racl k {S.x₁} := by
  refine adjoin_le_iff.2 ?_
  rintro z (rfl | rfl)
  · exact subset_racl k _ rfl
  · exact S.y₁_mem

/-- `x₂` is not algebraic over `x₁` (blueprint Lemma 4.2(a) applied to the
independence hypothesis). -/
theorem x₂_notMem : S.x₂ ∉ racl k {S.x₁} :=
  AlgebraicIndependent.notMem_racl_pair S.indep

/-- `x₂` remains transcendental over the enlarged base `k(x₁, y₁)`
(first pregeometry count of the curve-coset chain). -/
theorem transcendental_x₂ : Transcendental ↥S.base S.x₂ := by
  intro halg
  refine S.x₂_notMem ((isRAC_racl {S.x₁}).mem_of_isAlgebraic ?_)
  exact isAlgebraic_of_le S.base_le_racl halg

/-- The second correspondence relation persists over the enlarged base. -/
theorem y₂_mem_baseRacl : S.y₂ ∈ racl ↥S.base {S.x₂} :=
  racl_subset_racl_base S.base {S.x₂} S.y₂_mem

/-- … in both directions. -/
theorem x₂_mem_baseRacl : S.x₂ ∈ racl ↥S.base {S.y₂} :=
  racl_subset_racl_base S.base {S.y₂} S.x₂_mem

section Relocation

open MvPolynomial

/-- Joint relocation of the second pair (step 1 of the fused curve-coset
chain, instantiated to the `AddCorrSetup` data): given `s` transcendental over
the base `k(x₁, y₁)`, the pair `(x₂, y₂)` relocates to a pair `c₂'` satisfying
exactly the same joint `k`-polynomial relations with `(x₁, y₁)` and algebraic
over `k(x₁, y₁, s)`. -/
theorem exists_pair_relocation [IsAlgClosed Ω] {s : Ω}
    (hs : Transcendental ↥S.base s) :
    ∃ c₂' : Fin 2 → Ω,
      (∀ f : MvPolynomial (Fin 2 ⊕ Fin 2) k,
        aeval (Sum.elim ![S.x₁, S.y₁] c₂') f = 0 ↔
          aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) f = 0) ∧
      ∀ j, IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) (c₂' j) := by
  have hbase : S.base = adjoin k (Set.range ![S.x₁, S.y₁]) :=
    congrArg (adjoin k) (Matrix.range_cons_cons_empty S.x₁ S.y₁ ![]).symm
  have hx₂ : Transcendental ↥S.base S.x₂ := S.transcendental_x₂
  have hy₂ : S.y₂ ∈ racl ↥S.base {S.x₂} := S.y₂_mem_baseRacl
  rw [hbase] at hs hx₂ hy₂ ⊢
  -- The transcendence basis `![S.x₂]` of the pair over the base.
  have ht : AlgebraicIndependent ↥(adjoin k (Set.range ![S.x₁, S.y₁]))
      ![S.x₂] := algebraicIndependent_unique_type_iff.2 hx₂
  have hs' : AlgebraicIndependent ↥(adjoin k (Set.range ![S.x₁, S.y₁]))
      ![s] := algebraicIndependent_unique_type_iff.2 hs
  have hsub : (Set.range ![S.x₂] : Set Ω) ⊆ Set.range ![S.x₂, S.y₂] := by
    rw [Matrix.range_cons_empty, Matrix.range_cons_cons_empty]
    exact Set.singleton_subset_iff.2 (Set.mem_insert _ _)
  have hle : adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂]) ≤
      adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂, S.y₂]) :=
    adjoin.mono _ _ _ hsub
  -- Everything in the pair is algebraic over the basis.
  have hgen : ∀ x ∈ Set.range ![S.x₂, S.y₂], IsAlgebraic
      ↥(adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂])) x := by
    rw [Matrix.range_cons_empty, Matrix.range_cons_cons_empty]
    rintro x (rfl | rfl)
    · exact isAlgebraic_algebraMap
        (⟨S.x₂, subset_adjoin _ _ rfl⟩ :
          ↥(adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) {S.x₂}))
    · exact (mem_racl_iff _).1 hy₂
  obtain ⟨c₂', hrel, halg⟩ := exists_joint_relocation ![S.x₁, S.y₁] ht hle
    (isAlgebraic_extendScalars_adjoin hle hgen) hs'
  refine ⟨c₂', hrel, fun j ↦ ?_⟩
  have h := halg j
  rwa [Matrix.range_cons_empty] at h

end Relocation

end AddCorrSetup

end

end AclGeom
