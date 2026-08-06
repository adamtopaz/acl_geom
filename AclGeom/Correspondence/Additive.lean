/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.AddPolynomial
import AclGeom.Correspondence.CurveIdeal
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

end AddCorrSetup

end

end AclGeom
