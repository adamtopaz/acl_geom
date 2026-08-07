/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.Algebra.MvPolynomial.Funext
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.AddPolynomial
import AclGeom.Correspondence.CurveIdeal
import AclGeom.Correspondence.BaseChange
import AclGeom.Correspondence.TranslationDescent
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

/-- … and symmetrically. -/
theorem x₁_notMem : S.x₁ ∉ racl k {S.x₂} :=
  AlgebraicIndependent.notMem_racl_pair' S.indep

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

/-- `x₂` is not algebraic over the base, in `racl` form. -/
theorem x₂_notMem_base : S.x₂ ∉ racl k {S.x₁, S.y₁} := fun hmem ↦
  S.transcendental_x₂ ((mem_racl_iff k).1 hmem)

/-- The first coordinate of the sum correspondence is transcendental:
subtracting `x₁` would otherwise make `x₂` algebraic over `k(x₁)`. -/
theorem sum_fst_transcendental : Transcendental k (S.x₁ + S.x₂) := by
  intro halg
  have hmem : S.x₁ + S.x₂ ∈ racl k {S.x₁} :=
    (mem_racl_iff k).2 (halg.tower_top _)
  have hx₂ : S.x₂ ∈ racl k {S.x₁} := by
    have := sub_mem hmem (subset_racl k _ rfl)
    simpa using this
  exact S.x₂_notMem hx₂

section Relocation

open MvPolynomial

/-- The relation-preservation property produced by `exists_pair_relocation`:
`c₂'` satisfies exactly the joint `k`-polynomial relations with `(x₁, y₁)`
that `(x₂, y₂)` does. -/
def JointRel (c₂' : Fin 2 → Ω) : Prop :=
  ∀ f : MvPolynomial (Fin 2 ⊕ Fin 2) k,
    aeval (Sum.elim ![S.x₁, S.y₁] c₂') f = 0 ↔
      aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) f = 0

/-- Joint relocation of the second pair (step 1 of the fused curve-coset
chain, instantiated to the `AddCorrSetup` data): given `s` transcendental over
the base `k(x₁, y₁)`, the pair `(x₂, y₂)` relocates to a pair `c₂'` satisfying
exactly the same joint `k`-polynomial relations with `(x₁, y₁)` and algebraic
over `k(x₁, y₁, s)`. -/
theorem exists_pair_relocation [IsAlgClosed Ω] {s : Ω}
    (hs : Transcendental ↥S.base s) :
    ∃ c₂' : Fin 2 → Ω, S.JointRel c₂' ∧
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

variable {S} {c₂' : Fin 2 → Ω}

/-- A joint relocation has the same joint vanishing ideal. -/
theorem JointRel.idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k (Sum.elim ![S.x₁, S.y₁] c₂') =
      idealOf k (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) :=
  idealOf_eq_of_aeval_iff k hrel

/-- The sum pair of a joint relocation is a generic point of the same
sum locus (step 2a of the fused curve-coset chain, instantiated). -/
theorem JointRel.sum_idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k (![S.x₁, S.y₁] + c₂') =
      idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) :=
  idealOf_add_eq_of_joint hrel

/-- The relocated pair is still a finite correspondence: second coordinate
algebraic over the first. -/
theorem JointRel.snd_mem (hrel : S.JointRel c₂') : c₂' 1 ∈ racl k {c₂' 0} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 1) ∈ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inr 0}) := by
    simpa [Set.image_singleton] using S.y₂_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- … and conversely. -/
theorem JointRel.fst_mem (hrel : S.JointRel c₂') : c₂' 0 ∈ racl k {c₂' 1} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 0) ∈ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inr 1}) := by
    simpa [Set.image_singleton] using S.x₂_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- The relocated first coordinate stays generic over the base `k(x₁, y₁)`. -/
theorem JointRel.fst_notMem_base (hrel : S.JointRel c₂') :
    c₂' 0 ∉ racl k {S.x₁, S.y₁} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 0) ∉ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inl 0, Sum.inl 1}) := by
    simpa [Set.image_insert_eq, Set.image_singleton] using S.x₂_notMem_base
  have h := notMem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_insert_eq, Set.image_singleton] using h

/-- The sum pair of a joint relocation is still a finite correspondence. -/
theorem JointRel.sum_snd_mem (hrel : S.JointRel c₂') :
    S.y₁ + c₂' 1 ∈ racl k {S.x₁ + c₂' 0} := by
  have hv : (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) 1 ∈ racl k
      ((![S.x₁, S.y₁] + ![S.x₂, S.y₂]) '' {(0 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.sum_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.sum_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- … and conversely. -/
theorem JointRel.sum_fst_mem (hrel : S.JointRel c₂') :
    S.x₁ + c₂' 0 ∈ racl k {S.y₁ + c₂' 1} := by
  have hv : (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) 0 ∈ racl k
      ((![S.x₁, S.y₁] + ![S.x₂, S.y₂]) '' {(1 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.sum_mem'
  have h := mem_racl_image_of_idealOf_eq k hrel.sum_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- The relocated sum coordinate is transcendental: the relocated sum pair
is a generic point of a one-dimensional locus. -/
theorem JointRel.sum_fst_transcendental (hrel : S.JointRel c₂') :
    Transcendental k (S.x₁ + c₂' 0) := by
  have hv : Transcendental k ((![S.x₁, S.y₁] + ![S.x₂, S.y₂]) 0) := by
    simpa using S.sum_fst_transcendental
  have h := transcendental_of_idealOf_eq k hrel.sum_idealOf_eq.symm hv
  simpa using h

variable {s : Ω}

/-- Convert the algebraicity output of `exists_pair_relocation` to closure
form over `k`: the relocated coordinates lie in `racl k {x₁, s}` — the
generator `y₁` is absorbed by `y₁ ∈ racl k {x₁}`. -/
theorem racl_pair_of_relocation {z : Ω}
    (halg : IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) z) :
    z ∈ racl k {S.x₁, s} := by
  have h1 : z ∈ racl k (insert s {S.x₁, S.y₁}) := mem_racl_insert_iff.2 halg
  have hy₁ : S.y₁ ∈ racl k {S.x₁, s} :=
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) S.y₁_mem
  have hins : (insert s {S.x₁, S.y₁} : Set Ω) = insert S.y₁ {S.x₁, s} := by
    rw [Set.insert_comm s S.x₁, Set.pair_comm s S.y₁, Set.insert_comm S.x₁ S.y₁]
  rw [hins, racl_insert_of_mem hy₁] at h1
  exact h1

/-- With `s` chosen independent from `{x₁, x₂}`, the relocated first
coordinate stays outside `racl k {x₁, x₂}`: by exchange it is
interalgebraic with `s` over `k(x₁)`. -/
theorem JointRel.fst_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    c₂' 0 ∉ racl k {S.x₁, S.x₂} := by
  intro hmem
  have h0 : c₂' 0 ∉ racl k {S.x₁} := fun h ↦ hrel.fst_notMem_base
    (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) h)
  have hexch : s ∈ racl k (insert (c₂' 0) {S.x₁}) := by
    refine racl_exchange ?_ h0
    rwa [Set.pair_comm S.x₁ s] at halg
  have hsub : (insert (c₂' 0) {S.x₁} : Set Ω) ⊆ racl k {S.x₁, S.x₂} := by
    rintro z (rfl | rfl)
    · exact hmem
    · exact subset_racl k _ (Set.mem_insert _ _)
  exact hs (racl_le_of_subset_racl hsub hexch)

/-- The independent fresh element keeps `x₂` transcendental over
`k(x₁, s)`. -/
theorem x₂_notMem_fresh (hs : s ∉ racl k {S.x₁, S.x₂}) :
    S.x₂ ∉ racl k {S.x₁, s} := by
  intro hmem
  have hexch : s ∈ racl k (insert S.x₂ {S.x₁}) := by
    refine racl_exchange ?_ S.x₂_notMem
    rwa [Set.pair_comm S.x₁ s] at hmem
  refine hs ?_
  rwa [Set.pair_comm S.x₂ S.x₁] at hexch

/-- The first coordinate of the translation element is transcendental
over `k`: otherwise `x₂` would fall into `k(x₁, s)`. -/
theorem delta_fst_transcendental (hs : s ∉ racl k {S.x₁, S.x₂})
    {c₂'' : Fin 2 → Ω} (halg : c₂'' 0 ∈ racl k {S.x₁, s}) :
    Transcendental k (S.x₂ - c₂'' 0) := by
  intro h
  have hδ : S.x₂ - c₂'' 0 ∈ racl k {S.x₁, s} :=
    (mem_racl_iff k).2 (h.tower_top _)
  have hx₂ : S.x₂ ∈ racl k {S.x₁, s} := by
    have := add_mem hδ halg
    simpa using this
  exact x₂_notMem_fresh hs hx₂

/-- Triple independence, permuted: `x₁` is not algebraic over `{x₂, x₂'}`. -/
theorem JointRel.x₁_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ ∉ racl k {S.x₂, c₂' 0} := by
  intro hmem
  have hexch : c₂' 0 ∈ racl k (insert S.x₁ {S.x₂}) := by
    refine racl_exchange ?_ S.x₁_notMem
    rwa [Set.pair_comm S.x₂ (c₂' 0)] at hmem
  exact hrel.fst_notMem_pair hs halg hexch

/-- The δ-side genericity count of the fused curve-coset chain (step 2b):
the first coordinate of the relocated sum point is not algebraic over the
translation element `δ = c₂ − c₂'`. Hence the relocated sum point stays a
generic point of the sum locus even over `k(δ)`. -/
theorem JointRel.sum_fst_notMem_delta (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ + c₂' 0 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  -- Both coordinates of `δ` lie in `racl k {x₂, x₂'}` …
  have hx₂'mem : c₂' 0 ∈ racl k {S.x₂, c₂' 0} :=
    subset_racl k _ (Set.mem_insert_iff.2 (Or.inr rfl))
  have hy₂'mem : c₂' 1 ∈ racl k {S.x₂, c₂' 0} := by
    refine racl_le_of_subset_racl ?_ hrel.snd_mem
    rintro z rfl
    exact hx₂'mem
  have hy₂mem : S.y₂ ∈ racl k {S.x₂, c₂' 0} := by
    refine racl_le_of_subset_racl ?_ S.y₂_mem
    rintro z rfl
    exact subset_racl k _ (Set.mem_insert _ _)
  have hδsub : ({S.x₂ - c₂' 0, S.y₂ - c₂' 1} : Set Ω) ⊆ racl k {S.x₂, c₂' 0} := by
    rintro z (rfl | rfl)
    · exact sub_mem (subset_racl k _ (Set.mem_insert _ _)) hx₂'mem
    · exact sub_mem hy₂mem hy₂'mem
  -- … so the sum coordinate would land there, forcing `x₁` in as well.
  have hsum : S.x₁ + c₂' 0 ∈ racl k {S.x₂, c₂' 0} :=
    racl_le_of_subset_racl hδsub hmem
  have hx₁ : S.x₁ ∈ racl k {S.x₂, c₂' 0} := by
    have := sub_mem hsum hx₂'mem
    simpa using this
  exact hrel.x₁_notMem_pair hs halg hx₁

/-- The unrelocated sum coordinate is also transcendental over `k(δ)`
(subtracting `δ₁` moves between the two sum points). -/
theorem JointRel.sum_fst_notMem_delta' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ + S.x₂ ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  have hδ₁ : S.x₂ - c₂' 0 ∈ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} :=
    subset_racl k _ (Set.mem_insert _ _)
  have h2 : S.x₁ + c₂' 0 ∈ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
    have h3 := sub_mem hmem hδ₁
    have h4 : S.x₁ + S.x₂ - (S.x₂ - c₂' 0) = S.x₁ + c₂' 0 := by ring
    rwa [h4] at h3
  exact hrel.sum_fst_notMem_delta hs halg h2

end Relocation

section SumLocus

open MvPolynomial

/-- The sum locus is a plane curve: its vanishing ideal is generated by a
single prime polynomial (the curve-ideal brick applied to the sum pair). -/
theorem exists_prime_span_sum :
    ∃ F : MvPolynomial (Fin 2) k, Prime F ∧
      idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F} := by
  have hconv : ![S.x₁, S.y₁] + ![S.x₂, S.y₂] = ![S.x₁ + S.x₂, S.y₁ + S.y₂] := by
    rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  rw [hconv]
  exact exists_prime_span_idealOf k S.sum_fst_transcendental S.sum_mem

variable {S} {c₂' : Fin 2 → Ω}

/-- **Generic translation invariance** (step 3 of the fused curve-coset
chain): the generator `F` of the sum-locus prime, with the translation
element `δ = c₂ − c₂'` substituted into its variables, vanishes on the joint
locus of the sum point and `δ`. Every joint polynomial consequence of the
pair `(d, δ)` may therefore be played against `F(X−U, Y−V)` in the
minimal-degree argument. -/
theorem JointRel.subSubst_mem (hrel : S.JointRel c₂')
    {F : MvPolynomial (Fin 2) k}
    (hF : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    subSubst (k := k) F ∈ idealOf k
      (Sum.elim (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) (![S.x₂, S.y₂] - c₂')) := by
  rw [mem_idealOf_iff, aeval_subSubst]
  have harith : ![S.x₁, S.y₁] + ![S.x₂, S.y₂] - (![S.x₂, S.y₂] - c₂') =
      ![S.x₁, S.y₁] + c₂' := by
    abel
  rw [harith]
  have hmem : F ∈ idealOf k (![S.x₁, S.y₁] + c₂') := by
    rw [hrel.sum_idealOf_eq, hF]
    exact Ideal.subset_span rfl
  exact (mem_idealOf_iff _).1 hmem

end SumLocus

section TranslationIdentity

open MvPolynomial

/-- The field generated by the translation element `δ = c₂ − c₂'`. -/
def deltaField (S : AddCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    IntermediateField k Ω :=
  adjoin k {S.x₂ - c₂' 0, S.y₂ - c₂' 1}

/-- The translation element as a vector over `k(δ)`. -/
def deltaVec (S : AddCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    Fin 2 → ↥(deltaField S c₂') :=
  ![⟨S.x₂ - c₂' 0, subset_adjoin k _ (Set.mem_insert _ _)⟩,
    ⟨S.y₂ - c₂' 1, subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)⟩]

variable {S} {c₂' : Fin 2 → Ω} {s : Ω}

/-- The unrelocated sum's second coordinate is also transcendental over
`k(δ)`. -/
theorem JointRel.sum_snd_notMem_delta' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ + S.y₂ ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := fun hmem ↦
  hrel.sum_fst_notMem_delta' hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) S.sum_mem')

/-- … and the relocated sum's second coordinate. -/
theorem JointRel.sum_snd_notMem_delta (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ + c₂' 1 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := fun hmem ↦
  hrel.sum_fst_notMem_delta hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) hrel.sum_fst_mem)

/-- **The exact translation identity** (the fused chain assembled through
step 4): the extension to `k(δ)` of the sum-locus generator is literally
invariant under the translation substitution by `δ = c₂ − c₂'`. -/
theorem JointRel.translate_deltaVec_eq [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    translate (deltaVec S c₂')
        (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) F) =
      MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) F := by
  classical
  set FK := MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) F with hFK
  -- Genericity of the original sum point over `k(δ)`.
  have hu : Transcendental ↥(deltaField S c₂') (S.x₁ + S.x₂) := fun h ↦
    hrel.sum_fst_notMem_delta' hs halg ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(deltaField S c₂') (S.y₁ + S.y₂) := fun h ↦
    hrel.sum_snd_notMem_delta' hs halg ((mem_racl_iff k).2 h)
  -- The span at the clean sum tuple.
  have hconv : ![S.x₁, S.y₁] + ![S.x₂, S.y₂] = ![S.x₁ + S.x₂, S.y₁ + S.y₂] := by
    rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  rw [hconv] at hFspan
  have hspan_d : idealOf ↥(deltaField S c₂') ![S.x₁ + S.x₂, S.y₁ + S.y₂] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hu S.sum_mem hv' S.sum_mem' hF0 hFspan
  -- Genericity of the relocated sum point over `k(δ)`, and its span.
  have hud' : Transcendental ↥(deltaField S c₂') (S.x₁ + c₂' 0) := fun h ↦
    hrel.sum_fst_notMem_delta hs halg ((mem_racl_iff k).2 h)
  have hvd'' : Transcendental ↥(deltaField S c₂') (S.y₁ + c₂' 1) := fun h ↦
    hrel.sum_snd_notMem_delta hs halg ((mem_racl_iff k).2 h)
  have hFspan_d' : idealOf k ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] = Ideal.span {F} := by
    have h1 := hrel.sum_idealOf_eq
    have hconv' : ![S.x₁, S.y₁] + c₂' = ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] := by
      funext i
      fin_cases i <;> simp
    rw [hconv', hconv] at h1
    rw [h1, hFspan]
  have hspan_d' : idealOf ↥(deltaField S c₂') ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hud' hrel.sum_snd_mem hvd'' hrel.sum_fst_mem hF0 hFspan_d'
  -- Transport the `d`-span along the translation and compare with the
  -- `d'`-span.
  have htrans := idealOf_translate_span (c := deltaVec S c₂') hspan_d
  have htuple : (fun j ↦ (![S.x₁ + S.x₂, S.y₁ + S.y₂] : Fin 2 → Ω) j -
      algebraMap ↥(deltaField S c₂') Ω (deltaVec S c₂' j)) =
      ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] := by
    funext j
    fin_cases j
    · show (S.x₁ + S.x₂) - (S.x₂ - c₂' 0) = S.x₁ + c₂' 0
      ring
    · show (S.y₁ + S.y₂) - (S.y₂ - c₂' 1) = S.y₁ + c₂' 1
      ring
  rw [htuple, hspan_d'] at htrans
  have hFK0 : FK ≠ 0 := fun h ↦ hF0 (MvPolynomial.map_injective _
    (algebraMap k ↥(deltaField S c₂')).injective (by rw [map_zero]; exact h))
  exact translate_eq_self_of_span_eq hFK0 htrans.symm

/-- The translation element has interalgebraic coordinates: its locus is a
genuine curve. Independence would make the stabilizer improper; the
degenerate direction is ruled out by exchange against the transcendence of
`δ₁`. -/
theorem JointRel.delta_snd_mem [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    S.y₂ - c₂' 1 ∈ racl k {S.x₂ - c₂' 0} := by
  classical
  have hid := hrel.translate_deltaVec_eq hs halg hFp.ne_zero hFspan
  have hnindK : ¬AlgebraicIndependent k (deltaVec S c₂') := fun h ↦
    not_algebraicIndependent_of_translate_eq hFp hid h
  have hnind : ¬AlgebraicIndependent k ![S.x₂ - c₂' 0, S.y₂ - c₂' 1] := by
    intro h
    refine hnindK (AlgebraicIndependent.of_comp (deltaField S c₂').val ?_)
    have hcomp : (⇑(deltaField S c₂').val ∘ deltaVec S c₂') =
        ![S.x₂ - c₂' 0, S.y₂ - c₂' 1] := by
      funext i
      fin_cases i <;> rfl
    rwa [hcomp]
  rw [algebraicIndependent_iff_forall_notMem_racl] at hnind
  push Not at hnind
  rw [Fin.exists_fin_two] at hnind
  rcases hnind with hi | hi
  · have himg : (![S.x₂ - c₂' 0, S.y₂ - c₂' 1] ''
        ({(0 : Fin 2)}ᶜ : Set (Fin 2))) = {S.y₂ - c₂' 1} := by
      have hcompl : ({(0 : Fin 2)}ᶜ : Set (Fin 2)) = {1} := by
        ext i
        fin_cases i <;> simp
      rw [hcompl, Set.image_singleton]
      simp
    rw [himg] at hi
    have hδ₁ : S.x₂ - c₂' 0 ∉ racl k (∅ : Set Ω) :=
      notMem_racl_empty_of_transcendental (delta_fst_transcendental hs halg)
    have hxy : S.x₂ - c₂' 0 ∈
        racl k (insert (S.y₂ - c₂' 1) (∅ : Set Ω)) := by
      simpa using hi
    have hexch := racl_exchange hxy hδ₁
    simpa using hexch
  · have himg : (![S.x₂ - c₂' 0, S.y₂ - c₂' 1] ''
        ({(1 : Fin 2)}ᶜ : Set (Fin 2))) = {S.x₂ - c₂' 0} := by
      have hcompl : ({(1 : Fin 2)}ᶜ : Set (Fin 2)) = {0} := by
        ext i
        fin_cases i <;> simp
      rw [hcompl, Set.image_singleton]
      simp
    rw [himg] at hi
    exact hi

/-- The translation locus is a plane curve: its vanishing ideal is generated
by a single prime polynomial. -/
theorem JointRel.exists_prime_span_delta [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    ∃ G : MvPolynomial (Fin 2) k, Prime G ∧
      idealOf k ![S.x₂ - c₂' 0, S.y₂ - c₂' 1] = Ideal.span {G} :=
  exists_prime_span_idealOf k (delta_fst_transcendental hs halg)
    (hrel.delta_snd_mem hs halg hFp hFspan)

/-- The relocated pair is a generic point of the same correspondence curve:
its own vanishing ideal is preserved (restriction of the joint ideal
equality to the second block of variables). -/
theorem JointRel.pair_idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k c₂' = idealOf k ![S.x₂, S.y₂] := by
  refine idealOf_eq_of_aeval_iff k fun g ↦ ?_
  have hcomp₁ : (Sum.elim ![S.x₁, S.y₁] c₂' ∘ Sum.inr : Fin 2 → Ω) = c₂' := by
    funext j
    rfl
  have hcomp₂ : (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] ∘ Sum.inr :
      Fin 2 → Ω) = ![S.x₂, S.y₂] := by
    funext j
    rfl
  have h1 : aeval (Sum.elim ![S.x₁, S.y₁] c₂') (rename Sum.inr g) =
      aeval c₂' g := by
    rw [aeval_rename, hcomp₁]
  have h2 : aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) (rename Sum.inr g) =
      aeval ![S.x₂, S.y₂] g := by
    rw [aeval_rename, hcomp₂]
  rw [← h1, ← h2]
  exact hrel (rename Sum.inr g)

/-- The unrelocated pair coordinate stays transcendental over `k(δ)`: the
δ-locus is one-dimensional, and pulling `x₂` into it would drag `c₂' 0`
into `k(x₂)`. -/
theorem JointRel.pair_fst_notMem_delta [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    S.x₂ ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  -- The δ-locus is one-dimensional.
  have hδ₁ : S.y₂ - c₂' 1 ∈ racl k {S.x₂ - c₂' 0} :=
    hrel.delta_snd_mem hs halg hFp hFspan
  have hD : racl k ({S.x₂ - c₂' 0, S.y₂ - c₂' 1} : Set Ω) ≤
      racl k {S.x₂ - c₂' 0} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact subset_racl k _ rfl
    · exact hδ₁
  have hx₂δ : S.x₂ ∈ racl k {S.x₂ - c₂' 0} := hD hmem
  -- Exchange against the transcendence of δ₀.
  have hx₂e : S.x₂ ∉ racl k (∅ : Set Ω) := fun h ↦
    S.x₂_notMem (racl_mono (Set.empty_subset _) h)
  have hins₀ : (insert (S.x₂ - c₂' 0) (∅ : Set Ω)) = {S.x₂ - c₂' 0} := by
    simp
  have hins₂ : (insert S.x₂ (∅ : Set Ω)) = {S.x₂} := by simp
  have hexch : S.x₂ - c₂' 0 ∈ racl k {S.x₂} := by
    have h1 : S.x₂ ∈ racl k (insert (S.x₂ - c₂' 0) (∅ : Set Ω)) := by
      rw [hins₀]
      exact hx₂δ
    have h2 := racl_exchange h1 hx₂e
    rwa [hins₂] at h2
  have hc₂'0 : c₂' 0 ∈ racl k {S.x₂} := by
    have hx₂self : S.x₂ ∈ racl k {S.x₂} := subset_racl k _ rfl
    have hsub := sub_mem hx₂self hexch
    have hcancel : S.x₂ - (S.x₂ - c₂' 0) = c₂' 0 := by ring
    rwa [hcancel] at hsub
  refine hrel.fst_notMem_pair hs halg ?_
  exact racl_mono (Set.subset_insert _ _) hc₂'0

/-- … and so does the second coordinate. -/
theorem JointRel.pair_snd_notMem_delta [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    S.y₂ ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := fun hmem ↦
  hrel.pair_fst_notMem_delta hs halg hFp hFspan
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) S.x₂_mem)

/-- The relocated pair coordinates stay transcendental over `k(δ)` as well:
adding `δ₀` moves between the two pair points. -/
theorem JointRel.reloc_fst_notMem_delta [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    c₂' 0 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  have hδ₀m : S.x₂ - c₂' 0 ∈ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} :=
    subset_racl k _ (Set.mem_insert _ _)
  have hx₂m := add_mem hδ₀m hmem
  have hcancel : S.x₂ - c₂' 0 + c₂' 0 = S.x₂ := by ring
  rw [hcancel] at hx₂m
  exact hrel.pair_fst_notMem_delta hs halg hFp hFspan hx₂m

/-- … in both coordinates. -/
theorem JointRel.reloc_snd_notMem_delta [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    c₂' 1 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := fun hmem ↦
  hrel.reloc_fst_notMem_delta hs halg hFp hFspan
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) hrel.fst_mem)

/-- **The exact translation identity at the correspondence curve**: the
generator of `Loc(x₂, y₂)` over `k(δ)` is literally fixed by the
translation substitution by `δ = c₂ − c₂'`. This upgrades the generic coset
statement `C₂ − δ = C₂` to an identity of polynomials, the input to the
group-chunk argument of the additive endgame. -/
theorem JointRel.translate_pair_eq [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G : MvPolynomial (Fin 2) k} (hG0 : G ≠ 0)
    (hGspan : idealOf k ![S.x₂, S.y₂] = Ideal.span {G}) :
    translate (deltaVec S c₂')
        (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) =
      MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G := by
  classical
  set GK := MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G with hGK
  -- Genericity of the pair over `k(δ)`, and its span.
  have hu : Transcendental ↥(deltaField S c₂') S.x₂ := fun h ↦
    hrel.pair_fst_notMem_delta hs halg hFp hFspan ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(deltaField S c₂') S.y₂ := fun h ↦
    hrel.pair_snd_notMem_delta hs halg hFp hFspan ((mem_racl_iff k).2 h)
  have hspan_d : idealOf ↥(deltaField S c₂') ![S.x₂, S.y₂] =
      Ideal.span {GK} :=
    idealOf_map_eq_span hu S.y₂_mem hv' S.x₂_mem hG0 hGspan
  -- Genericity of the relocated pair over `k(δ)`, and its span.
  have hud' : Transcendental ↥(deltaField S c₂') (c₂' 0) := fun h ↦
    hrel.reloc_fst_notMem_delta hs halg hFp hFspan ((mem_racl_iff k).2 h)
  have hvd'' : Transcendental ↥(deltaField S c₂') (c₂' 1) := fun h ↦
    hrel.reloc_snd_notMem_delta hs halg hFp hFspan ((mem_racl_iff k).2 h)
  have hpair : c₂' = ![c₂' 0, c₂' 1] := by
    funext i
    fin_cases i <;> rfl
  have hGspan_d' : idealOf k ![c₂' 0, c₂' 1] = Ideal.span {G} := by
    rw [← hpair, hrel.pair_idealOf_eq, hGspan]
  have hspan_d' : idealOf ↥(deltaField S c₂') ![c₂' 0, c₂' 1] =
      Ideal.span {GK} :=
    idealOf_map_eq_span hud' hrel.snd_mem hvd'' hrel.fst_mem hG0 hGspan_d'
  -- Transport the pair span along the translation and compare.
  have htrans := idealOf_translate_span (c := deltaVec S c₂') hspan_d
  have htuple : (fun j ↦ (![S.x₂, S.y₂] : Fin 2 → Ω) j -
      algebraMap ↥(deltaField S c₂') Ω (deltaVec S c₂' j)) =
      ![c₂' 0, c₂' 1] := by
    funext j
    fin_cases j
    · show S.x₂ - (S.x₂ - c₂' 0) = c₂' 0
      ring
    · show S.y₂ - (S.y₂ - c₂' 1) = c₂' 1
      ring
  rw [htuple, hspan_d'] at htrans
  have hGK0 : GK ≠ 0 := fun h ↦ hG0 (MvPolynomial.map_injective _
    (algebraMap k ↥(deltaField S c₂')).injective (by rw [map_zero]; exact h))
  exact translate_eq_self_of_span_eq hGK0 htrans.symm

/-- The relocated first coordinate stays transcendental over `k(x₂, y₂)`. -/
theorem JointRel.fst_notMem_pairRacl (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    c₂' 0 ∉ racl k {S.x₂, S.y₂} := by
  intro hmem
  have hD : racl k ({S.x₂, S.y₂} : Set Ω) ≤ racl k {S.x₂} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact subset_racl k _ rfl
    · exact S.y₂_mem
  refine hrel.fst_notMem_pair hs halg ?_
  exact racl_mono (Set.subset_insert _ _) (hD hmem)

/-- … and the second. -/
theorem JointRel.snd_notMem_pairRacl (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    c₂' 1 ∉ racl k {S.x₂, S.y₂} := fun hmem ↦
  hrel.fst_notMem_pairRacl hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) hrel.fst_mem)

/-- The relocated pair spans the extended curve ideal over `k(x₂, y₂)`:
base-change irreducibility at the relocated point over the field generated
by the original pair. -/
theorem JointRel.reloc_span_pairField [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {G : MvPolynomial (Fin 2) k} (hG0 : G ≠ 0)
    (hGspan : idealOf k ![S.x₂, S.y₂] = Ideal.span {G}) :
    idealOf ↥(adjoin k ({S.x₂, S.y₂} : Set Ω)) c₂' =
      Ideal.span {MvPolynomial.map
        (algebraMap k ↥(adjoin k ({S.x₂, S.y₂} : Set Ω))) G} := by
  have hu : Transcendental ↥(adjoin k ({S.x₂, S.y₂} : Set Ω)) (c₂' 0) :=
    fun h ↦ hrel.fst_notMem_pairRacl hs halg ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(adjoin k ({S.x₂, S.y₂} : Set Ω)) (c₂' 1) :=
    fun h ↦ hrel.snd_notMem_pairRacl hs halg ((mem_racl_iff k).2 h)
  have hpair : c₂' = ![c₂' 0, c₂' 1] := by
    funext i
    fin_cases i <;> rfl
  have hGspan' : idealOf k ![c₂' 0, c₂' 1] = Ideal.span {G} := by
    rw [← hpair, hrel.pair_idealOf_eq, hGspan]
  have h := idealOf_map_eq_span hu hrel.snd_mem hv' hrel.fst_mem hG0 hGspan'
  rwa [← hpair] at h

variable {c₂'' : Fin 2 → Ω} {s' : Ω}

/-- **Joint-type determination at the correspondence curve**: two joint
relocations of the pair have the same joint vanishing ideal with it. -/
theorem joint_idealOf_eq_of_two_relocations [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'') (hs' : s' ∉ racl k {S.x₁, S.x₂})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {G : MvPolynomial (Fin 2) k} (hG0 : G ≠ 0)
    (hGspan : idealOf k ![S.x₂, S.y₂] = Ideal.span {G}) :
    idealOf k (Sum.elim ![S.x₂, S.y₂] c₂') =
      idealOf k (Sum.elim ![S.x₂, S.y₂] c₂'') := by
  have hx₂K : S.x₂ ∈ adjoin k ({S.x₂, S.y₂} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert _ _)
  have hy₂K : S.y₂ ∈ adjoin k ({S.x₂, S.y₂} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  have h := joint_idealOf_eq
    (c := (![⟨S.x₂, hx₂K⟩, ⟨S.y₂, hy₂K⟩] :
      Fin 2 → ↥(adjoin k ({S.x₂, S.y₂} : Set Ω))))
    (hrel.reloc_span_pairField hs halg hG0 hGspan)
    (hrel'.reloc_span_pairField hs' halg' hG0 hGspan)
  have hcoe : (fun j ↦ algebraMap ↥(adjoin k ({S.x₂, S.y₂} : Set Ω)) Ω
      ((![⟨S.x₂, hx₂K⟩, ⟨S.y₂, hy₂K⟩] :
        Fin 2 → ↥(adjoin k ({S.x₂, S.y₂} : Set Ω))) j)) = ![S.x₂, S.y₂] := by
    funext j
    fin_cases j <;> rfl
  rwa [hcoe] at h

/-- **The δ-curve does not depend on the choice of relocation**: the two
translation elements have the same vanishing ideal. -/
theorem delta_idealOf_eq_of_two_relocations [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'') (hs' : s' ∉ racl k {S.x₁, S.x₂})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {G : MvPolynomial (Fin 2) k} (hG0 : G ≠ 0)
    (hGspan : idealOf k ![S.x₂, S.y₂] = Ideal.span {G}) :
    idealOf k (![S.x₂, S.y₂] - c₂') = idealOf k (![S.x₂, S.y₂] - c₂'') := by
  have h := joint_idealOf_eq_of_two_relocations hrel hs halg hrel' hs' halg'
    hG0 hGspan
  refine idealOf_sub_eq_of_joint fun f ↦ ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · have h1 := aeval_eq_aeval_of_idealOf_eq k h (f := f) (g := 0)
      (by simpa using h0)
    simpa using h1
  · have h1 := aeval_eq_aeval_of_idealOf_eq k h.symm (f := f) (g := 0)
      (by simpa using h0)
    simpa using h1

/-- The original pair stays generic over the field generated by the
relocated pair. -/
theorem JointRel.pair_fst_notMem_relocRacl (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₂ ∉ racl k {c₂' 0, c₂' 1} := by
  intro hmem
  have hD : racl k ({c₂' 0, c₂' 1} : Set Ω) ≤ racl k {S.x₁, s} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact halg
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 halg)
        hrel.snd_mem
  exact S.x₂_notMem_fresh hs (hD hmem)

/-- … in both coordinates. -/
theorem JointRel.pair_snd_notMem_relocRacl (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₂ ∉ racl k {c₂' 0, c₂' 1} := fun hmem ↦
  hrel.pair_fst_notMem_relocRacl hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) S.x₂_mem)

/-- The pair spans the extended curve ideal over the field generated by the
relocated pair. -/
theorem JointRel.pair_span_relocField [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂}) :
    idealOf ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω)) ![S.x₂, S.y₂] =
      Ideal.span {MvPolynomial.map
        (algebraMap k ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω))) G₂} := by
  have hu : Transcendental ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω)) S.x₂ :=
    fun h ↦ hrel.pair_fst_notMem_relocRacl hs halg ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω)) S.y₂ :=
    fun h ↦ hrel.pair_snd_notMem_relocRacl hs halg ((mem_racl_iff k).2 h)
  exact idealOf_map_eq_span hu S.y₂_mem hv' S.x₂_mem hG₂0 hG₂span

/-- Joint relations at `(pair, c₂')` transfer to `(pair, w)` for any zero
`w` of the curve generator (Ω-level wrapper of joint-type determination). -/
theorem JointRel.joint_transfer_pairField [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {w : Fin 2 → Ω} (hw : aeval w G₂ = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim ![S.x₂, S.y₂] c₂') f = 0) :
    aeval (Sum.elim ![S.x₂, S.y₂] w) f = 0 := by
  have hx₂K : S.x₂ ∈ adjoin k ({S.x₂, S.y₂} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert _ _)
  have hy₂K : S.y₂ ∈ adjoin k ({S.x₂, S.y₂} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  have hcoe : (fun j ↦ algebraMap ↥(adjoin k ({S.x₂, S.y₂} : Set Ω)) Ω
      ((![⟨S.x₂, hx₂K⟩, ⟨S.y₂, hy₂K⟩] : Fin 2 →
        ↥(adjoin k ({S.x₂, S.y₂} : Set Ω))) j)) = ![S.x₂, S.y₂] := by
    funext j
    fin_cases j <;> rfl
  exact joint_aeval_eq_zero' (c := ![⟨S.x₂, hx₂K⟩, ⟨S.y₂, hy₂K⟩]) hcoe
    (hrel.reloc_span_pairField hs halg hG₂0 hG₂span) hw hf

/-- … and symmetrically with the relocated pair as the base block. -/
theorem JointRel.joint_transfer_relocField [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {w : Fin 2 → Ω} (hw : aeval w G₂ = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim c₂' ![S.x₂, S.y₂]) f = 0) :
    aeval (Sum.elim c₂' w) f = 0 := by
  have h0K : c₂' 0 ∈ adjoin k ({c₂' 0, c₂' 1} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert _ _)
  have h1K : c₂' 1 ∈ adjoin k ({c₂' 0, c₂' 1} : Set Ω) :=
    subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  have hcoe : (fun j ↦ algebraMap ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω)) Ω
      ((![⟨c₂' 0, h0K⟩, ⟨c₂' 1, h1K⟩] : Fin 2 →
        ↥(adjoin k ({c₂' 0, c₂' 1} : Set Ω))) j)) = c₂' := by
    funext j
    fin_cases j <;> rfl
  exact joint_aeval_eq_zero' (c := ![⟨c₂' 0, h0K⟩, ⟨c₂' 1, h1K⟩]) hcoe
    (hrel.pair_span_relocField hs halg hG₂0 hG₂span) hw hf

/-- **The δ-curve passes through the origin**: transferring the difference
relation from `(c₂', pair)` to `(c₂', c₂')` evaluates the generator at
zero. -/
theorem JointRel.constantCoeff_delta_gen [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k}
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    constantCoeff G = 0 := by
  classical
  have hpair : c₂' = ![c₂' 0, c₂' 1] := by
    funext i
    fin_cases i <;> rfl
  -- The swapped difference polynomial vanishes at `(c₂', pair)`.
  have hswap : ((Sum.elim c₂' ![S.x₂, S.y₂] : Fin 2 ⊕ Fin 2 → Ω) ∘
      Sum.swap) = Sum.elim ![S.x₂, S.y₂] c₂' := by
    funext i
    rcases i with j | j <;> rfl
  have hf : aeval (Sum.elim c₂' ![S.x₂, S.y₂])
      (rename Sum.swap (subSubst (k := k) G)) = 0 := by
    rw [aeval_rename, hswap, aeval_subSubst]
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  -- The relocated pair is itself a zero of the curve generator.
  have hw : aeval ![c₂' 0, c₂' 1] G₂ = 0 := by
    rw [← hpair]
    have hmem : G₂ ∈ idealOf k c₂' := by
      rw [hrel.pair_idealOf_eq, hG₂span]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  -- Transfer and evaluate at the origin.
  have h := hrel.joint_transfer_relocField hs halg hG₂0 hG₂span hw hf
  have hswap2 : ((Sum.elim c₂' ![c₂' 0, c₂' 1] : Fin 2 ⊕ Fin 2 → Ω) ∘
      Sum.swap) = Sum.elim ![c₂' 0, c₂' 1] c₂' := by
    funext i
    rcases i with j | j <;> rfl
  rw [aeval_rename, hswap2, aeval_subSubst] at h
  have hzero : (![c₂' 0, c₂' 1] - c₂' : Fin 2 → Ω) = 0 := by
    rw [← hpair]
    exact sub_self _
  rw [hzero, MvPolynomial.aeval_zero] at h
  exact (map_eq_zero _).1 h

variable (S) in
/-- The c-point lies on the correspondence curve: the exact identity at the
second relocation moves `c₂'` by `−δ*`. -/
theorem cpoint_aeval_zero [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hrel' : S.JointRel c₂'')
    (hs' : s' ∉ racl k {S.x₁, S.x₂}) (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂}) :
    aeval (c₂' + c₂'' - ![S.x₂, S.y₂]) G₂ = 0 := by
  have hid := hrel'.translate_pair_eq hs' halg' hFp hFspan hG₂0 hG₂span
  have h := congrArg
    (fun g ↦ aeval (c₂' + c₂'' - ![S.x₂, S.y₂] : Fin 2 → Ω) g) hid
  rw [aeval_translate] at h
  have hpt : (fun j ↦ (c₂' + c₂'' - ![S.x₂, S.y₂] : Fin 2 → Ω) j +
      algebraMap ↥(deltaField S c₂'') Ω (deltaVec S c₂'' j)) = c₂' := by
    funext j
    fin_cases j
    · show c₂' 0 + c₂'' 0 - S.x₂ + (S.x₂ - c₂'' 0) = c₂' 0
      ring
    · show c₂' 1 + c₂'' 1 - S.y₂ + (S.y₂ - c₂'' 1) = c₂' 1
      ring
  rw [hpt] at h
  have hc₂' : aeval c₂' (MvPolynomial.map
      (algebraMap k ↥(deltaField S c₂'')) G₂) = 0 := by
    rw [aeval_map_algebraMap]
    have hmem : G₂ ∈ idealOf k c₂' := by
      rw [hrel.pair_idealOf_eq, hG₂span]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  rw [hc₂', aeval_map_algebraMap] at h
  exact h.symm

/-- **The group chunk**: the sum of the two translation elements lies on
the δ-curve — the fused, elementwise form of the Hopf property of the
stabilizer subgroup. -/
theorem JointRel.chunk_add [IsAlgClosed k]
    (hrel : S.JointRel c₂') (hs : s ∉ racl k {S.x₁, S.x₂})
    (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'') (hs' : s' ∉ racl k {S.x₁, S.x₂})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k}
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    aeval ((![S.x₂, S.y₂] - c₂') + (![S.x₂, S.y₂] - c₂'')) G = 0 := by
  have hf : aeval (Sum.elim ![S.x₂, S.y₂] c₂') (subSubst (k := k) G) = 0 := by
    rw [aeval_subSubst]
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  have hc := S.cpoint_aeval_zero hrel hrel' hs' halg' hFp hFspan hG₂0 hG₂span
  have h := hrel.joint_transfer_pairField hs halg hG₂0 hG₂span hc hf
  rw [aeval_subSubst] at h
  have harith : (![S.x₂, S.y₂] - (c₂' + c₂'' - ![S.x₂, S.y₂]) :
      Fin 2 → Ω) = (![S.x₂, S.y₂] - c₂') + (![S.x₂, S.y₂] - c₂'') := by
    abel
  rwa [harith] at h

/-- The second coordinate of the translation element is also transcendental
over `k`. -/
theorem JointRel.delta_snd_transcendental (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    Transcendental k (S.y₂ - c₂' 1) := by
  intro h
  have hδ₁ : S.y₂ - c₂' 1 ∈ racl k (∅ : Set Ω) :=
    (mem_racl_iff k).2 (h.tower_top _)
  have hc₂'1 : c₂' 1 ∈ racl k {S.x₁, s} :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 halg) hrel.snd_mem
  have hy₂ : S.y₂ ∈ racl k {S.x₁, s} := by
    have h2 := add_mem (racl_mono (Set.empty_subset _) hδ₁) hc₂'1
    have hcancel : S.y₂ - c₂' 1 + c₂' 1 = S.y₂ := by ring
    rwa [hcancel] at h2
  have hx₂ : S.x₂ ∈ racl k {S.x₁, s} :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hy₂) S.x₂_mem
  exact S.x₂_notMem_fresh hs hx₂

/-- The translation element is two-way interalgebraic: exchange upgrades
`delta_snd_mem`. -/
theorem JointRel.delta_fst_mem [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    S.x₂ - c₂' 0 ∈ racl k {S.y₂ - c₂' 1} := by
  have hδ₁tr : S.y₂ - c₂' 1 ∉ racl k (∅ : Set Ω) :=
    notMem_racl_empty_of_transcendental
      (hrel.delta_snd_transcendental hs halg)
  have hins : (insert (S.x₂ - c₂' 0) (∅ : Set Ω)) = {S.x₂ - c₂' 0} := by simp
  have h1 : S.y₂ - c₂' 1 ∈ racl k (insert (S.x₂ - c₂' 0) (∅ : Set Ω)) := by
    rw [hins]
    exact hrel.delta_snd_mem hs halg hFp hFspan
  have h2 := racl_exchange h1 hδ₁tr
  have hins2 : (insert (S.y₂ - c₂' 1) (∅ : Set Ω)) = {S.y₂ - c₂' 1} := by simp
  rwa [hins2] at h2

/-- With the second fresh element independent of the whole first
configuration, the second translation element stays generic over `k(δ)`. -/
theorem JointRel.deltaStar_fst_notMem_delta (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'}) :
    S.x₂ - c₂'' 0 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  -- Everything on the `c₂'` side lives in `racl k {x₁, x₂, s}`.
  have hx₁T : S.x₁ ∈ racl k {S.x₁, S.x₂, s} :=
    subset_racl k _ (Set.mem_insert _ _)
  have hx₂T : S.x₂ ∈ racl k {S.x₁, S.x₂, s} :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsT : s ∈ racl k {S.x₁, S.x₂, s} :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hc₂'0T : c₂' 0 ∈ racl k {S.x₁, S.x₂, s} := by
    refine racl_le_of_subset_racl ?_ halg
    rintro z (rfl | rfl)
    · exact hx₁T
    · exact hsT
  have hy₂T : S.y₂ ∈ racl k {S.x₁, S.x₂, s} :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₂T) S.y₂_mem
  have hc₂'1T : c₂' 1 ∈ racl k {S.x₁, S.x₂, s} :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hc₂'0T) hrel.snd_mem
  have hT : racl k ({S.x₂ - c₂' 0, S.y₂ - c₂' 1} : Set Ω) ≤
      racl k {S.x₁, S.x₂, s} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact sub_mem hx₂T hc₂'0T
    · exact sub_mem hy₂T hc₂'1T
  have hδT : S.x₂ - c₂'' 0 ∈ racl k {S.x₁, S.x₂, s} := hT hmem
  have hc₂''0T : c₂'' 0 ∈ racl k {S.x₁, S.x₂, s} := by
    have h1 := sub_mem hx₂T hδT
    have hcancel : S.x₂ - (S.x₂ - c₂'' 0) = c₂'' 0 := by ring
    rwa [hcancel] at h1
  -- Exchange the second fresh element into the configuration.
  have hc₂''0base : c₂'' 0 ∉ racl k {S.x₁} := fun h ↦
    hrel'.fst_notMem_base (racl_mono (Set.singleton_subset_iff.2
      (Set.mem_insert _ _)) h)
  have hs'exch : s' ∈ racl k {c₂'' 0, S.x₁} := by
    refine racl_exchange ?_ hc₂''0base
    rwa [Set.pair_comm S.x₁ s'] at halg'
  have hs'T : s' ∈ racl k {S.x₁, S.x₂, s} := by
    refine racl_le_of_subset_racl ?_ hs'exch
    rintro z (rfl | rfl)
    · exact hc₂''0T
    · exact hx₁T
  exact hss' hs'T

/-- … in both coordinates. -/
theorem JointRel.deltaStar_snd_notMem_delta [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F}) :
    S.y₂ - c₂'' 1 ∉ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} := by
  intro hmem
  have hs'₂ : s' ∉ racl k {S.x₁, S.x₂} := fun h ↦
    hss' (racl_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) h)
  have hfst : S.x₂ - c₂'' 0 ∈ racl k {S.x₂ - c₂' 0, S.y₂ - c₂' 1} :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem)
      (hrel'.delta_fst_mem hs'₂ halg' hFp hFspan)
  exact hrel.deltaStar_fst_notMem_delta hs halg hrel' hss' halg' hfst

/-- Base-change irreducibility at the second translation element over
`k(δ)`: the δ-curve generator stays a generator. -/
theorem JointRel.deltaStar_span [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    idealOf ↥(deltaField S c₂') (![S.x₂, S.y₂] - c₂'') =
      Ideal.span {MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G} := by
  have hs'₂ : s' ∉ racl k {S.x₁, S.x₂} := fun h ↦
    hss' (racl_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) h)
  have htuple : (![S.x₂, S.y₂] - c₂'' : Fin 2 → Ω) =
      ![S.x₂ - c₂'' 0, S.y₂ - c₂'' 1] := by
    funext j
    fin_cases j <;> rfl
  have hGspan' : idealOf k ![S.x₂ - c₂'' 0, S.y₂ - c₂'' 1] =
      Ideal.span {G} := by
    rw [← htuple, ← delta_idealOf_eq_of_two_relocations hrel hs halg hrel'
      hs'₂ halg' hG₂0 hG₂span, hGspan]
  have hu : Transcendental ↥(deltaField S c₂') (S.x₂ - c₂'' 0) := fun h ↦
    hrel.deltaStar_fst_notMem_delta hs halg hrel' hss' halg'
      ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(deltaField S c₂') (S.y₂ - c₂'' 1) := fun h ↦
    hrel.deltaStar_snd_notMem_delta hs halg hrel' hss' halg' hFp hFspan
      ((mem_racl_iff k).2 h)
  have h := idealOf_map_eq_span hu
    (hrel'.delta_snd_mem hs'₂ halg' hFp hFspan) hv'
    (hrel'.delta_fst_mem hs'₂ halg' hFp hFspan) hGp.ne_zero hGspan'
  rwa [← htuple] at h

/-- **Self-invariance of the δ-curve generator** (the Hopf identity in
exact form): the generator over `k(δ)` is fixed by translation by `δ`
itself. The pair-additivity defect of `G`, first-block evaluated at `δ`,
is `translate δ G_K − G_K`; it lies in the span of `G_K` by the group
chunk, and the translation degree drop forces the quotient to vanish. -/
theorem JointRel.translate_delta_self_eq [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    translate (deltaVec S c₂')
        (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) =
      MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G := by
  classical
  have hs'₂ : s' ∉ racl k {S.x₁, S.x₂} := fun h ↦
    hss' (racl_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) h)
  -- The three vanishing statements feeding the joint defect.
  have hδG : aeval (![S.x₂, S.y₂] - c₂') G = 0 := by
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  have hδsG : aeval (![S.x₂, S.y₂] - c₂'') G = 0 := by
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂'') := by
      rw [← delta_idealOf_eq_of_two_relocations hrel hs halg hrel' hs'₂
        halg' hG₂0 hG₂span, hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  have hsumG := hrel.chunk_add hs halg hrel' hs'₂ halg' hFp hFspan hG₂0
    hG₂span hGspan
  -- The pair-additivity defect vanishes at `(δ, δ*)`.
  have hD : aeval (Sum.elim (![S.x₂, S.y₂] - c₂') (![S.x₂, S.y₂] - c₂''))
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) = 0 := by
    have hinl : ((Sum.elim (![S.x₂, S.y₂] - c₂') (![S.x₂, S.y₂] - c₂'') ∘
        Sum.inl : Fin 2 → Ω)) = ![S.x₂, S.y₂] - c₂' := by
      funext j
      rfl
    have hinr : ((Sum.elim (![S.x₂, S.y₂] - c₂') (![S.x₂, S.y₂] - c₂'') ∘
        Sum.inr : Fin 2 → Ω)) = ![S.x₂, S.y₂] - c₂'' := by
      funext j
      rfl
    rw [map_sub, map_sub, aeval_addSubst, aeval_rename, aeval_rename, hinl,
      hinr, hsumG, hδG, hδsG, sub_zero, sub_zero]
  -- First-block evaluation lands in the span of the extended generator.
  have hcoe : (fun j ↦ algebraMap ↥(deltaField S c₂') Ω
      (deltaVec S c₂' j)) = ![S.x₂, S.y₂] - c₂' := by
    funext j
    fin_cases j <;> rfl
  have hmemK : aevalFst (k := k) (deltaVec S c₂')
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) ∈
      idealOf ↥(deltaField S c₂') (![S.x₂, S.y₂] - c₂'') := by
    rw [mem_idealOf_iff, aeval_aevalFst, hcoe]
    exact hD
  rw [hrel.deltaStar_span hs halg hrel' hss' halg' hFp hFspan hG₂0 hG₂span
    hGp hGspan, Ideal.mem_span_singleton'] at hmemK
  obtain ⟨q, hq⟩ := hmemK
  -- The first-block evaluation is the translation defect.
  have hzeroK : aeval (deltaVec S c₂') G = (0 : ↥(deltaField S c₂')) := by
    apply (algebraMap ↥(deltaField S c₂') Ω).injective
    rw [map_zero, ← aeval_algebraMap_apply]
    have hcomp : (algebraMap ↥(deltaField S c₂') Ω ∘ deltaVec S c₂') =
        ![S.x₂, S.y₂] - c₂' := by
      funext j
      fin_cases j <;> rfl
    rw [hcomp]
    exact hδG
  have hDsplit : aevalFst (k := k) (deltaVec S c₂')
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) =
      translate (deltaVec S c₂')
          (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) -
        MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G := by
    rw [map_sub, map_sub, aevalFst_addSubst, aevalFst_rename_inl,
      aevalFst_rename_inr, hzeroK, map_zero, sub_zero]
  have hqid : q * MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G =
      translate (deltaVec S c₂')
          (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) -
        MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G :=
    hq.trans hDsplit
  -- Degree bookkeeping kills the quotient.
  have hGK0 : MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G ≠ 0 :=
    fun h ↦ hGp.ne_zero (MvPolynomial.map_injective _
      (algebraMap k ↥(deltaField S c₂')).injective
      (by rw [map_zero]; exact h))
  have hpos : 0 < G.totalDegree := by
    rcases Nat.eq_zero_or_pos G.totalDegree with h0 | h
    · exfalso
      have hC := totalDegree_eq_zero_iff_eq_C.1 h0
      have ha : G.coeff 0 ≠ 0 := fun h00 ↦
        hGp.ne_zero (by rw [hC, h00, map_zero])
      exact hGp.not_unit
        (by rw [hC]; exact (isUnit_iff_ne_zero.2 ha).map C)
    · exact h
  have hposK : 0 < (MvPolynomial.map
      (algebraMap k ↥(deltaField S c₂')) G).totalDegree := by
    have hdegeq : (MvPolynomial.map
        (algebraMap k ↥(deltaField S c₂')) G).totalDegree =
        G.totalDegree := by
      rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree,
        support_map_of_injective G
          (algebraMap k ↥(deltaField S c₂')).injective]
    rwa [hdegeq]
  rcases eq_or_ne (translate (deltaVec S c₂')
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G))
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) with heq | hne
  · exact heq
  exfalso
  have hsubne : translate (deltaVec S c₂')
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) -
      MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G ≠ 0 :=
    sub_ne_zero.2 hne
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hqid
    exact hsubne hqid.symm
  have hdeg1 := totalDegree_mul_of_isDomain hq0 hGK0
  have hdeg2 : (translate (deltaVec S c₂')
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) -
      MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G).totalDegree <
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G).totalDegree :=
    totalDegree_translate_sub_lt _ hposK
  rw [← hqid, hdeg1] at hdeg2
  omega

/-- **Additivity of the δ-curve generator** (blueprint Lemma 8.7(a), the
division argument): the generator splits sums, as an identity of joint
polynomials. The additivity defect is divisible by the generator in each
variable block, the two block extensions are coprime primes, and the total
degree bound leaves no room for the product. -/
theorem JointRel.addSubst_delta_gen_eq [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    addSubst (k := k) G = rename Sum.inl G + rename Sum.inr G := by
  classical
  -- Push the self-invariance to `Ω`.
  have hself := hrel.translate_delta_self_eq hs halg hrel' hss' halg' hFp
    hFspan hG₂0 hG₂span hGp hGspan
  have hcoe : (fun j ↦ algebraMap ↥(deltaField S c₂') Ω
      (deltaVec S c₂' j)) = ![S.x₂, S.y₂] - c₂' := by
    funext j
    fin_cases j <;> rfl
  have hmapmap : MvPolynomial.map (algebraMap ↥(deltaField S c₂') Ω)
      (MvPolynomial.map (algebraMap k ↥(deltaField S c₂')) G) =
      MvPolynomial.map (algebraMap k Ω) G := by
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hselfΩ : translate (![S.x₂, S.y₂] - c₂' : Fin 2 → Ω)
      (MvPolynomial.map (algebraMap k Ω) G) =
      MvPolynomial.map (algebraMap k Ω) G := by
    have h := congrArg (MvPolynomial.map (algebraMap ↥(deltaField S c₂') Ω))
      hself
    rwa [map_translate, hmapmap, hcoe] at h
  -- The additivity defect has vanishing first-block evaluation at δ.
  have hδG : aeval (![S.x₂, S.y₂] - c₂') G = 0 := by
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  have hf : aevalFst (k := k) (![S.x₂, S.y₂] - c₂' : Fin 2 → Ω)
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) = 0 := by
    rw [map_sub, map_sub, aevalFst_addSubst, aevalFst_rename_inl,
      aevalFst_rename_inr, hselfΩ, hδG, map_zero, sub_zero, sub_self]
  -- Hence it is a multiple of the generator in the first block.
  have hker : ∀ h : MvPolynomial (Fin 2) k,
      aeval (![S.x₂, S.y₂] - c₂' : Fin 2 → Ω) h = 0 →
      h ∈ Ideal.span {G} := by
    intro h hh
    rw [← hGspan]
    exact (mem_idealOf_iff _).2 hh
  have hmeml := mem_span_rename_inl_of_aevalFst_eq_zero hker hf
  -- The defect is symmetric under the block swap …
  have hswapAdd : rename Sum.swap (addSubst (k := k) G) =
      addSubst (k := k) G := by
    have hcomp : ((rename
        (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom.comp
        (addSubst (k := k)).toRingHom) = (addSubst (k := k)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
      · simp [addSubst, MvPolynomial.algebraMap_eq]
      · simp [addSubst, add_comm]
    exact congrArg (fun (F : MvPolynomial (Fin 2) k →+* _) ↦ F G) hcomp
  have hswapl : rename Sum.swap
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G) = rename Sum.inr G := by
    rw [rename_rename]
    congr 1
  have hswapr : rename Sum.swap
      (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G) = rename Sum.inl G := by
    rw [rename_rename]
    congr 1
  have hswapD : rename Sum.swap
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) =
      addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G := by
    rw [map_sub, map_sub, hswapAdd, hswapl, hswapr]
    ring
  -- … so it is a multiple in the second block as well.
  have hmemr : (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) ∈
      Ideal.span {rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G} := by
    rw [Ideal.mem_span_singleton'] at hmeml ⊢
    obtain ⟨R, hR⟩ := hmeml
    refine ⟨rename Sum.swap R, ?_⟩
    have h := congrArg
      (rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)) hR
    rwa [map_mul, hswapl, hswapD] at h
  -- The two block extensions are coprime primes.
  have hpl := prime_rename_inl (k := k) hGp
  have hpr := prime_rename_inr (k := k) hGp
  have hndvd : ¬ rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G ∣
      rename Sum.inr G := by
    intro hdvd
    obtain ⟨u, hu⟩ := hdvd
    have h := congrArg
      (aeval (Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin 2) k)) X)) hu
    rw [map_mul] at h
    have h1 : aeval (Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin 2) k)) X)
        (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G) = G := by
      rw [aeval_rename]
      have hcompr : ((Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin 2) k)) X :
          Fin 2 ⊕ Fin 2 → MvPolynomial (Fin 2) k) ∘ Sum.inr) = X := by
        funext j
        rfl
      rw [hcompr, aeval_X_left_apply]
    have h2 : aeval (Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin 2) k)) X)
        (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G) = 0 := by
      rw [aeval_rename]
      have hcompl : ((Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin 2) k)) X :
          Fin 2 ⊕ Fin 2 → MvPolynomial (Fin 2) k) ∘ Sum.inl) =
          (0 : Fin 2 → MvPolynomial (Fin 2) k) := by
        funext j
        rfl
      rw [hcompl, MvPolynomial.aeval_zero,
        hrel.constantCoeff_delta_gen hs halg hG₂0 hG₂span hGspan, map_zero]
    rw [h1, h2, zero_mul] at h
    exact hGp.ne_zero h
  -- Combine the divisibilities and compare degrees.
  by_contra hne
  have hDne : addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G
      ≠ 0 := by
    intro h0
    rw [sub_sub, sub_eq_zero] at h0
    exact hne h0
  have hdvdl : rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G ∣
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) :=
    Ideal.mem_span_singleton.1 hmeml
  have hdvdr : rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G ∣
      (addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G) :=
    Ideal.mem_span_singleton.1 hmemr
  obtain ⟨m, hm⟩ := hdvdr
  have hpm : rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G ∣ m := by
    rcases hpl.dvd_or_dvd (hm ▸ hdvdl) with h | h
    · exact absurd h hndvd
    · exact h
  obtain ⟨t, ht⟩ := hpm
  have hDfact : addSubst (k := k) G - rename Sum.inl G - rename Sum.inr G =
      rename Sum.inr G * rename Sum.inl G * t := by
    rw [hm, ht, mul_assoc]
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hDfact
    exact hDne hDfact
  have hpos : 0 < G.totalDegree := by
    rcases Nat.eq_zero_or_pos G.totalDegree with h0 | h
    · exfalso
      have hC := totalDegree_eq_zero_iff_eq_C.1 h0
      have ha : G.coeff 0 ≠ 0 := fun h00 ↦
        hGp.ne_zero (by rw [hC, h00, map_zero])
      exact hGp.not_unit
        (by rw [hC]; exact (isUnit_iff_ne_zero.2 ha).map C)
    · exact h
  have htotl : (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G).totalDegree =
      G.totalDegree := totalDegree_rename_of_injective Sum.inl_injective G
  have htotr : (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G).totalDegree =
      G.totalDegree := totalDegree_rename_of_injective Sum.inr_injective G
  have hDdeg : (addSubst (k := k) G - rename Sum.inl G -
      rename Sum.inr G).totalDegree ≤ G.totalDegree := by
    refine le_trans (totalDegree_sub _ _) (max_le ?_ (le_of_eq htotr))
    refine le_trans (totalDegree_sub _ _) (max_le ?_ (le_of_eq htotl))
    exact totalDegree_addSubst_le G
  have hmul1 := totalDegree_mul_of_isDomain
    (mul_ne_zero hpr.ne_zero hpl.ne_zero) ht0
  have hmul2 := totalDegree_mul_of_isDomain hpr.ne_zero hpl.ne_zero
  rw [hDfact, hmul1, hmul2, htotl, htotr] at hDdeg
  omega

/-- Evaluation form of the additivity: the generator value splits sums of
tuples. -/
theorem JointRel.aeval_delta_gen_add [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G})
    (u v : Fin 2 → Ω) :
    aeval (u + v) G = aeval u G + aeval v G := by
  have hadd := hrel.addSubst_delta_gen_eq hs halg hrel' hss' halg' hFp
    hFspan hG₂0 hG₂span hGp hGspan
  have h := congrArg (aeval (Sum.elim u v) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] Ω) hadd
  have hinl : ((Sum.elim u v : Fin 2 ⊕ Fin 2 → Ω) ∘ Sum.inl) = u := by
    funext j
    rfl
  have hinr : ((Sum.elim u v : Fin 2 ⊕ Fin 2 → Ω) ∘ Sum.inr) = v := by
    funext j
    rfl
  rwa [aeval_addSubst, map_add, aeval_rename, aeval_rename, hinl, hinr] at h

/-- **The coset constants** (towards blueprint Theorem 8.8): the generator
value at each correspondence pair is a constant from `k` — the additive
form of the relocation-invariance descent. -/
theorem JointRel.exists_coset_constants [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    ∃ d₁ d₂ : k, aeval ![S.x₁, S.y₁] G = algebraMap k Ω d₁ ∧
      aeval ![S.x₂, S.y₂] G = algebraMap k Ω d₂ := by
  classical
  have hν := hrel.aeval_delta_gen_add hs halg hrel' hss' halg' hFp hFspan
    hG₂0 hG₂span hGp hGspan
  have hδG : aeval (![S.x₂, S.y₂] - c₂') G = 0 := by
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  -- Membership helper: the generator value at a tuple with coordinates in
  -- an intermediate field lies in it.
  have hmemT : ∀ (T : IntermediateField k Ω) (a : Fin 2 → Ω),
      (∀ j, a j ∈ T) → aeval a G ∈ T := by
    intro T a ha
    have hcomp : (algebraMap ↥T Ω ∘ fun j ↦ (⟨a j, ha j⟩ : ↥T)) = a := by
      funext j
      rfl
    have h := aeval_algebraMap_apply Ω (fun j ↦ (⟨a j, ha j⟩ : ↥T)) G
    rw [hcomp] at h
    rw [h]
    exact (aeval (fun j ↦ (⟨a j, ha j⟩ : ↥T)) G).2
  -- The value at the second pair is relocation-invariant.
  have hpair : c₂' = ![c₂' 0, c₂' 1] := by
    funext i
    fin_cases i <;> rfl
  have hinv₂ : aeval ![S.x₂, S.y₂] G = aeval c₂' G := by
    have harith : (![S.x₂, S.y₂] : Fin 2 → Ω) =
        c₂' + (![S.x₂, S.y₂] - c₂') := by
      abel
    rw [harith, hν, hδG, add_zero]
  -- Descend the value into `k`.
  have hw₂x₂ : aeval ![S.x₂, S.y₂] G ∈ racl k {S.x₂} := by
    refine hmemT _ _ ?_
    intro j
    fin_cases j
    · exact subset_racl k _ rfl
    · exact S.y₂_mem
  have hw₂x₁s : aeval ![S.x₂, S.y₂] G ∈ racl k {S.x₁, s} := by
    rw [hinv₂]
    refine hmemT _ _ ?_
    intro j
    fin_cases j
    · exact halg
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 halg)
        hrel.snd_mem
  have hw₂x₁ : aeval ![S.x₂, S.y₂] G ∈ racl k {S.x₁} := by
    refine mem_racl_of_mem_racl_insert (a := S.x₂) (b := s) ?_ ?_ ?_
    · exact racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hw₂x₂
    · rwa [Set.pair_comm S.x₁ s] at hw₂x₁s
    · rwa [Set.pair_comm S.x₁ S.x₂] at hs
  have hins₁ : (insert S.x₁ (∅ : Set Ω)) = {S.x₁} := by simp
  have hins₂ : (insert S.x₂ (∅ : Set Ω)) = {S.x₂} := by simp
  have hw₂empty : aeval ![S.x₂, S.y₂] G ∈ racl k (∅ : Set Ω) := by
    refine mem_racl_of_mem_racl_insert (a := S.x₁) (b := S.x₂) ?_ ?_ ?_
    · rw [hins₁]
      exact hw₂x₁
    · rw [hins₂]
      exact hw₂x₂
    · rw [hins₁]
      exact S.x₂_notMem
  obtain ⟨d₂, hd₂⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hw₂empty)
  -- The value at the sum pair is also relocation-invariant, and descends.
  have hinvD : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G =
      aeval ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] G := by
    have harith : (![S.x₁ + S.x₂, S.y₁ + S.y₂] : Fin 2 → Ω) =
        ![S.x₁ + c₂' 0, S.y₁ + c₂' 1] + (![S.x₂, S.y₂] - c₂') := by
      funext j
      fin_cases j
      · show S.x₁ + S.x₂ = S.x₁ + c₂' 0 + (S.x₂ - c₂' 0)
        ring
      · show S.y₁ + S.y₂ = S.y₁ + c₂' 1 + (S.y₂ - c₂' 1)
        ring
    rw [harith, hν, hδG, add_zero]
  have hwDsum : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G ∈
      racl k {S.x₁ + S.x₂} := by
    refine hmemT _ _ ?_
    intro j
    fin_cases j
    · exact subset_racl k _ rfl
    · exact S.sum_mem
  have hwDx₁s : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G ∈
      racl k {S.x₁, s} := by
    rw [hinvD]
    have hx₁m : S.x₁ ∈ racl k {S.x₁, s} := subset_racl k _ (Set.mem_insert _ _)
    refine hmemT _ _ ?_
    intro j
    fin_cases j
    · exact add_mem hx₁m halg
    · refine add_mem ?_ ?_
      · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₁m)
          S.y₁_mem
      · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 halg)
          hrel.snd_mem
  have hwDx₁x₂ : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G ∈
      racl k {S.x₂, S.x₁} := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_) hwDsum
    exact add_mem (subset_racl k _ (Set.mem_insert_of_mem _ rfl))
      (subset_racl k _ (Set.mem_insert _ _))
  have hwDx₁ : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G ∈ racl k {S.x₁} := by
    refine mem_racl_of_mem_racl_insert (a := S.x₂) (b := s) hwDx₁x₂ ?_ ?_
    · rwa [Set.pair_comm S.x₁ s] at hwDx₁s
    · rwa [Set.pair_comm S.x₁ S.x₂] at hs
  have hwDempty : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G ∈
      racl k (∅ : Set Ω) := by
    have hinsD : (insert (S.x₁ + S.x₂) (∅ : Set Ω)) = {S.x₁ + S.x₂} := by
      simp
    refine mem_racl_of_mem_racl_insert (a := S.x₁) (b := S.x₁ + S.x₂)
      ?_ ?_ ?_
    · rw [hins₁]
      exact hwDx₁
    · rw [hinsD]
      exact hwDsum
    · rw [hins₁]
      intro hmem
      have hx₁m : S.x₁ ∈ racl k {S.x₁} := subset_racl k _ rfl
      have h1 := sub_mem hmem hx₁m
      have hcancel : S.x₁ + S.x₂ - S.x₁ = S.x₂ := by ring
      rw [hcancel] at h1
      exact S.x₂_notMem h1
  obtain ⟨dD, hdD⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hwDempty)
  -- Split the sum value into the two pair values.
  have hsplit : aeval ![S.x₁ + S.x₂, S.y₁ + S.y₂] G =
      aeval ![S.x₁, S.y₁] G + aeval ![S.x₂, S.y₂] G := by
    have hconv : (![S.x₁ + S.x₂, S.y₁ + S.y₂] : Fin 2 → Ω) =
        ![S.x₁, S.y₁] + ![S.x₂, S.y₂] := by
      rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
    rw [hconv, hν]
  refine ⟨dD - d₂, d₂, ?_, hd₂.symm⟩
  rw [map_sub, hdD, hd₂, hsplit]
  ring

/-- First-coordinate specialization of a bivariate polynomial. -/
theorem polynomial_aeval_fst (g : MvPolynomial (Fin 2) k) (u : Ω) :
    Polynomial.aeval u (aeval ![Polynomial.X, (0 : Polynomial k)] g) =
      aeval ![u, 0] g := by
  have hcomp : (Polynomial.aeval u).comp
      (aeval ![Polynomial.X, (0 : Polynomial k)] :
        MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) =
      aeval ![u, (0 : Ω)] := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  exact congrArg (fun (φ : MvPolynomial (Fin 2) k →ₐ[k] Ω) ↦ φ g) hcomp

/-- Second-coordinate specialization of a bivariate polynomial. -/
theorem polynomial_aeval_snd (g : MvPolynomial (Fin 2) k) (v : Ω) :
    Polynomial.aeval v (aeval ![(0 : Polynomial k), Polynomial.X] g) =
      aeval ![0, v] g := by
  have hcomp : (Polynomial.aeval v).comp
      (aeval ![(0 : Polynomial k), Polynomial.X] :
        MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) =
      aeval ![(0 : Ω), v] := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  exact congrArg (fun (φ : MvPolynomial (Fin 2) k →ₐ[k] Ω) ↦ φ g) hcomp

/-- The generator value splits into one-variable specializations. -/
theorem JointRel.aeval_delta_gen_split [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G})
    (u v : Ω) :
    aeval ![u, v] G =
      Polynomial.aeval u (aeval ![Polynomial.X, (0 : Polynomial k)] G) +
      Polynomial.aeval v (aeval ![(0 : Polynomial k), Polynomial.X] G) := by
  have htuple : (![u, v] : Fin 2 → Ω) = ![u, 0] + ![0, v] := by
    funext j
    fin_cases j
    · show u = u + 0
      ring
    · show v = 0 + v
      ring
  rw [polynomial_aeval_fst, polynomial_aeval_snd, htuple]
  exact hrel.aeval_delta_gen_add hs halg hrel' hss' halg' hFp hFspan hG₂0
    hG₂span hGp hGspan _ _

/-- The δ-curve generator is literally the sum of its one-variable
specializations, as a polynomial identity — its support lies on the two
coordinate axes. -/
theorem JointRel.delta_gen_eq_split [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    G = Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k)
        (aeval ![Polynomial.X, (0 : Polynomial k)] G) +
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k)
        (aeval ![(0 : Polynomial k), Polynomial.X] G) := by
  classical
  have hsplit := hrel.aeval_delta_gen_split hs halg hrel' hss' halg' hFp
    hFspan hG₂0 hG₂span hGp hGspan
  haveI : Infinite Ω := Infinite.of_injective (algebraMap k Ω)
    (algebraMap k Ω).injective
  apply MvPolynomial.map_injective (algebraMap k Ω)
    (algebraMap k Ω).injective
  apply MvPolynomial.funext
  intro x
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, ← MvPolynomial.aeval_def,
    ← MvPolynomial.aeval_def]
  have hx : x = ![x 0, x 1] := by
    funext j
    fin_cases j <;> rfl
  rw [map_add]
  have h1 : aeval x (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k)
      (aeval ![Polynomial.X, (0 : Polynomial k)] G)) =
      Polynomial.aeval (x 0) (aeval ![Polynomial.X, (0 : Polynomial k)] G) := by
    rw [← Polynomial.aeval_algHom_apply, aeval_X]
  have h2 : aeval x (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k)
      (aeval ![(0 : Polynomial k), Polynomial.X] G)) =
      Polynomial.aeval (x 1) (aeval ![(0 : Polynomial k), Polynomial.X] G) := by
    rw [← Polynomial.aeval_algHom_apply, aeval_X]
  rw [h1, h2]
  have hs2 := hsplit (x 0) (x 1)
  rw [show (![x 0, x 1] : Fin 2 → Ω) = x from hx.symm] at hs2
  exact hs2

/-- The first one-variable specialization is an additive polynomial. -/
theorem JointRel.isAdditive_delta_gen_fst [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    IsAdditive (aeval ![Polynomial.X, (0 : Polynomial k)] G) := by
  intro x y
  apply (algebraMap k Ω).injective
  rw [map_add, ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    map_add, polynomial_aeval_fst, polynomial_aeval_fst, polynomial_aeval_fst]
  have htuple : (![algebraMap k Ω x + algebraMap k Ω y, 0] : Fin 2 → Ω) =
      ![algebraMap k Ω x, 0] + ![algebraMap k Ω y, 0] := by
    funext j
    fin_cases j
    · show algebraMap k Ω x + algebraMap k Ω y = _ + _
      rfl
    · show (0 : Ω) = 0 + 0
      ring
  rw [htuple]
  exact hrel.aeval_delta_gen_add hs halg hrel' hss' halg' hFp hFspan hG₂0
    hG₂span hGp hGspan _ _

/-- … and so is the second. -/
theorem JointRel.isAdditive_delta_gen_snd [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    (hrel' : S.JointRel c₂'')
    (hss' : s' ∉ racl k {S.x₁, S.x₂, s})
    (halg' : c₂'' 0 ∈ racl k {S.x₁, s'})
    {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hFspan : idealOf k (![S.x₁, S.y₁] + ![S.x₂, S.y₂]) = Ideal.span {F})
    {G₂ : MvPolynomial (Fin 2) k} (hG₂0 : G₂ ≠ 0)
    (hG₂span : idealOf k ![S.x₂, S.y₂] = Ideal.span {G₂})
    {G : MvPolynomial (Fin 2) k} (hGp : Prime G)
    (hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G}) :
    IsAdditive (aeval ![(0 : Polynomial k), Polynomial.X] G) := by
  intro x y
  apply (algebraMap k Ω).injective
  rw [map_add, ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    map_add, polynomial_aeval_snd, polynomial_aeval_snd, polynomial_aeval_snd]
  have htuple : (![(0 : Ω), algebraMap k Ω x + algebraMap k Ω y] :
      Fin 2 → Ω) = ![0, algebraMap k Ω x] + ![0, algebraMap k Ω y] := by
    funext j
    fin_cases j
    · show (0 : Ω) = 0 + 0
      ring
    · show algebraMap k Ω x + algebraMap k Ω y = _ + _
      rfl
  rw [htuple]
  exact hrel.aeval_delta_gen_add hs halg hrel' hss' halg' hFp hFspan hG₂0
    hG₂span hGp hGspan _ _

end TranslationIdentity

section Endgame

open MvPolynomial

/-- **The additive correspondence theorem** (blueprint Theorem 8.8,
two-pair core): two finite correspondences with independent generic points
and interalgebraic sums satisfy additive coset equations
`Q(yᵢ) = P(xᵢ) + dᵢ` with common nonzero additive polynomials `P, Q` and
constants from `k`. -/
theorem exists_coset_equations [IsAlgClosed k] [IsAlgClosed Ω] {s s' : Ω}
    (hs : s ∉ racl k {S.x₁, S.x₂}) (hss' : s' ∉ racl k {S.x₁, S.x₂, s}) :
    ∃ P Q : Polynomial k, IsAdditive P ∧ IsAdditive Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      ∃ d₁ d₂ : k,
        Polynomial.aeval S.y₁ Q =
          Polynomial.aeval S.x₁ P + algebraMap k Ω d₁ ∧
        Polynomial.aeval S.y₂ Q =
          Polynomial.aeval S.x₂ P + algebraMap k Ω d₂ := by
  classical
  -- The two relocations.
  have hbaseLe : racl k ({S.x₁, S.y₁} : Set Ω) ≤ racl k {S.x₁, S.x₂} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2
        (subset_racl k _ (Set.mem_insert _ _))) S.y₁_mem
  have hbaseLe' : racl k ({S.x₁, S.y₁} : Set Ω) ≤
      racl k {S.x₁, S.x₂, s} := by
    refine racl_le_of_subset_racl ?_
    rintro z (rfl | rfl)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2
        (subset_racl k _ (Set.mem_insert _ _))) S.y₁_mem
  have hstr : Transcendental ↥S.base s := fun halg ↦
    hs (hbaseLe ((mem_racl_iff k).2 halg))
  have hstr' : Transcendental ↥S.base s' := fun halg ↦
    hss' (hbaseLe' ((mem_racl_iff k).2 halg))
  obtain ⟨c₂', hrel, halgraw⟩ := S.exists_pair_relocation hstr
  obtain ⟨c₂'', hrel', halgraw'⟩ := S.exists_pair_relocation hstr'
  have halg : c₂' 0 ∈ racl k {S.x₁, s} :=
    S.racl_pair_of_relocation (halgraw 0)
  have halg' : c₂'' 0 ∈ racl k {S.x₁, s'} :=
    S.racl_pair_of_relocation (halgraw' 0)
  -- The three generators.
  obtain ⟨F, hFp, hFspan⟩ := S.exists_prime_span_sum
  have hx₂tr : Transcendental k S.x₂ := fun h ↦
    S.x₂_notMem (racl_mono (Set.empty_subset _)
      ((mem_racl_iff k).2 (h.tower_top _)))
  obtain ⟨G₂, hG₂p, hG₂span⟩ := exists_prime_span_idealOf k hx₂tr S.y₂_mem
  obtain ⟨G, hGp, hGspan₀⟩ := hrel.exists_prime_span_delta hs halg hFp hFspan
  have htuple : (![S.x₂, S.y₂] - c₂' : Fin 2 → Ω) =
      ![S.x₂ - c₂' 0, S.y₂ - c₂' 1] := by
    funext j
    fin_cases j <;> rfl
  have hGspan : idealOf k (![S.x₂, S.y₂] - c₂') = Ideal.span {G} := by
    rw [htuple, hGspan₀]
  -- The coset constants and the split.
  obtain ⟨d₁, d₂, hd₁, hd₂⟩ := hrel.exists_coset_constants hs halg hrel'
    hss' halg' hFp hFspan hG₂p.ne_zero hG₂span hGp hGspan
  have hsplit := hrel.aeval_delta_gen_split hs halg hrel' hss' halg' hFp
    hFspan hG₂p.ne_zero hG₂span hGp hGspan
  have hpadd := hrel.isAdditive_delta_gen_fst hs halg hrel' hss' halg' hFp
    hFspan hG₂p.ne_zero hG₂span hGp hGspan
  have hqadd := hrel.isAdditive_delta_gen_snd hs halg hrel' hss' halg' hFp
    hFspan hG₂p.ne_zero hG₂span hGp hGspan
  -- Nondegeneracy of the two specializations.
  have hδG : aeval (![S.x₂, S.y₂] - c₂') G = 0 := by
    have hmem : G ∈ idealOf k (![S.x₂, S.y₂] - c₂') := by
      rw [hGspan]
      exact Ideal.subset_span rfl
    exact (mem_idealOf_iff _).1 hmem
  have hδsplit : Polynomial.aeval (S.x₂ - c₂' 0)
      (aeval ![Polynomial.X, (0 : Polynomial k)] G) +
      Polynomial.aeval (S.y₂ - c₂' 1)
        (aeval ![(0 : Polynomial k), Polynomial.X] G) = 0 := by
    rw [← hsplit (S.x₂ - c₂' 0) (S.y₂ - c₂' 1), ← htuple]
    exact hδG
  haveI : Infinite Ω := Infinite.of_injective (algebraMap k Ω)
    (algebraMap k Ω).injective
  have hG0_of : aeval ![Polynomial.X, (0 : Polynomial k)] G = 0 →
      aeval ![(0 : Polynomial k), Polynomial.X] G = 0 → False := by
    intro hp0 hq0
    refine hGp.ne_zero ?_
    have hmapG : MvPolynomial.map (algebraMap k Ω) G = 0 := by
      apply MvPolynomial.funext
      intro x
      have hx : x = ![x 0, x 1] := by
        funext j
        fin_cases j <;> rfl
      rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, map_zero, hx,
        hsplit (x 0) (x 1), hp0, hq0, map_zero, map_zero, add_zero]
    exact MvPolynomial.map_injective _ (algebraMap k Ω).injective
      (by rw [hmapG, map_zero])
  have hq0 : aeval ![(0 : Polynomial k), Polynomial.X] G ≠ 0 := by
    intro hq
    rcases eq_or_ne (aeval ![Polynomial.X, (0 : Polynomial k)] G) 0 with
      hp | hp
    · exact hG0_of hp hq
    · have hroot : Polynomial.aeval (S.x₂ - c₂' 0)
          (aeval ![Polynomial.X, (0 : Polynomial k)] G) = 0 := by
        have h := hδsplit
        rwa [hq, map_zero, add_zero] at h
      exact delta_fst_transcendental hs halg ⟨_, hp, hroot⟩
  have hp0 : aeval ![Polynomial.X, (0 : Polynomial k)] G ≠ 0 := by
    intro hp
    have hroot : Polynomial.aeval (S.y₂ - c₂' 1)
        (aeval ![(0 : Polynomial k), Polynomial.X] G) = 0 := by
      have h := hδsplit
      rwa [hp, map_zero, zero_add] at h
    exact hrel.delta_snd_transcendental hs halg ⟨_, hq0, hroot⟩
  -- Package `P := −p`, `Q := q`.
  refine ⟨-(aeval ![Polynomial.X, (0 : Polynomial k)] G),
    aeval ![(0 : Polynomial k), Polynomial.X] G, ?_, hqadd,
    neg_ne_zero.2 hp0, hq0, d₁, d₂, ?_, ?_⟩
  · intro x y
    simp only [Polynomial.eval_neg]
    rw [hpadd x y]
    ring
  · have h₁ : Polynomial.aeval S.x₁
        (aeval ![Polynomial.X, (0 : Polynomial k)] G) +
        Polynomial.aeval S.y₁
          (aeval ![(0 : Polynomial k), Polynomial.X] G) =
        algebraMap k Ω d₁ := by
      rw [← hsplit S.x₁ S.y₁]
      exact hd₁
    rw [map_neg]
    linear_combination h₁
  · have h₂ : Polynomial.aeval S.x₂
        (aeval ![Polynomial.X, (0 : Polynomial k)] G) +
        Polynomial.aeval S.y₂
          (aeval ![(0 : Polynomial k), Polynomial.X] G) =
        algebraMap k Ω d₂ := by
      rw [← hsplit S.x₂ S.y₂]
      exact hd₂
    rw [map_neg]
    linear_combination h₂

end Endgame

end AddCorrSetup

end

end AclGeom
