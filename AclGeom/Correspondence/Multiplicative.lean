/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.CurveIdeal
import AclGeom.Correspondence.BaseChange
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

section Relocation

open MvPolynomial

/-- The relation-preservation property for the multiplicative chain:
`c₂'` satisfies exactly the joint `k`-polynomial relations with `(x₁, y₁)`
that `(x₂, y₂)` does. -/
def JointRel (c₂' : Fin 2 → Ω) : Prop :=
  ∀ f : MvPolynomial (Fin 2 ⊕ Fin 2) k,
    aeval (Sum.elim ![S.x₁, S.y₁] c₂') f = 0 ↔
      aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) f = 0

/-- Joint relocation of the second pair, exactly as in the additive chain:
the construction is independent of the group operation. -/
theorem exists_pair_relocation [IsAlgClosed Ω] {s : Ω}
    (hs : Transcendental ↥S.base s) :
    ∃ c₂' : Fin 2 → Ω, S.JointRel c₂' ∧
      ∀ j, IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) (c₂' j) := by
  have hbase : S.base = adjoin k (Set.range ![S.x₁, S.y₁]) :=
    congrArg (adjoin k) (Matrix.range_cons_cons_empty S.x₁ S.y₁ ![]).symm
  have hx₂ : Transcendental ↥S.base S.x₂ := S.transcendental_x₂
  have hy₂ : S.y₂ ∈ racl ↥S.base {S.x₂} := S.y₂_mem_baseRacl
  rw [hbase] at hs hx₂ hy₂ ⊢
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

/-- The product pair of a joint relocation is a generic point of the same
product locus (the multiplicative step 2a, instantiated). -/
theorem JointRel.mul_idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k (![S.x₁, S.y₁] * c₂') =
      idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) :=
  idealOf_mul_eq_of_joint hrel

/-- The relocated pair is still a finite correspondence. -/
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

/-- The relocated product pair is still a two-way correspondence. -/
theorem JointRel.mul_snd_mem (hrel : S.JointRel c₂') :
    S.y₁ * c₂' 1 ∈ racl k {S.x₁ * c₂' 0} := by
  have hv : (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 1 ∈ racl k
      ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) '' {(0 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.mul_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- … and conversely. -/
theorem JointRel.mul_fst_mem (hrel : S.JointRel c₂') :
    S.x₁ * c₂' 0 ∈ racl k {S.y₁ * c₂' 1} := by
  have hv : (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 0 ∈ racl k
      ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) '' {(1 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.mul_mem'
  have h := mem_racl_image_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- The relocated product coordinate is transcendental. -/
theorem JointRel.mul_fst_transcendental (hrel : S.JointRel c₂') :
    Transcendental k (S.x₁ * c₂' 0) := by
  have hv : Transcendental k ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 0) := by
    simpa using S.mul_fst_transcendental
  have h := transcendental_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa using h

/-- The relocated coordinates stay nonzero: vanishing is a joint relation. -/
theorem JointRel.fst_ne (hrel : S.JointRel c₂') : c₂' 0 ≠ 0 := by
  intro h0
  have h := (hrel (MvPolynomial.X (Sum.inr 0))).1 (by simp [h0])
  simp at h
  exact S.x₂_ne h

/-- … both of them. -/
theorem JointRel.snd_ne (hrel : S.JointRel c₂') : c₂' 1 ≠ 0 := by
  intro h0
  have h := (hrel (MvPolynomial.X (Sum.inr 1))).1 (by simp [h0])
  simp at h
  exact S.y₂_ne h

variable (S) in
/-- `x₂` is not algebraic over the base, in `racl` form. -/
theorem x₂_notMem_base : S.x₂ ∉ racl k {S.x₁, S.y₁} := fun hmem ↦
  S.transcendental_x₂ ((mem_racl_iff k).1 hmem)

/-- The relocated first coordinate stays generic over the base. -/
theorem JointRel.fst_notMem_base (hrel : S.JointRel c₂') :
    c₂' 0 ∉ racl k {S.x₁, S.y₁} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 0) ∉ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inl 0, Sum.inl 1}) := by
    simpa [Set.image_insert_eq, Set.image_singleton] using S.x₂_notMem_base
  have h := notMem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_insert_eq, Set.image_singleton] using h

variable {s : Ω}

variable (S) in
/-- Convert the algebraicity output of `exists_pair_relocation` to closure
form over `k`. -/
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

variable (S) in
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

/-- With `s` independent from `{x₁, x₂}`, the relocated first coordinate
stays outside `racl k {x₁, x₂}`. -/
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

/-- Triple independence, permuted. -/
theorem JointRel.x₁_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ ∉ racl k {S.x₂, c₂' 0} := by
  intro hmem
  have hexch : c₂' 0 ∈ racl k (insert S.x₁ {S.x₂}) := by
    refine racl_exchange ?_ S.x₁_notMem
    rwa [Set.pair_comm S.x₂ (c₂' 0)] at hmem
  exact hrel.fst_notMem_pair hs halg hexch

/-- The ρ-side genericity count: the relocated product coordinate is not
algebraic over the ratio element `ρ = c₂ / c₂'`. -/
theorem JointRel.mul_fst_notMem_rho (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ * c₂' 0 ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
  intro hmem
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
  have hρsub : ({S.x₂ / c₂' 0, S.y₂ / c₂' 1} : Set Ω) ⊆
      racl k {S.x₂, c₂' 0} := by
    rintro z (rfl | rfl)
    · exact div_mem (subset_racl k _ (Set.mem_insert _ _)) hx₂'mem
    · exact div_mem hy₂mem hy₂'mem
  have hmul : S.x₁ * c₂' 0 ∈ racl k {S.x₂, c₂' 0} :=
    racl_le_of_subset_racl hρsub hmem
  have hx₁ : S.x₁ ∈ racl k {S.x₂, c₂' 0} := by
    have hdiv := div_mem hmul hx₂'mem
    have hcancel : S.x₁ * c₂' 0 / c₂' 0 = S.x₁ := by
      rw [mul_div_assoc, div_self hrel.fst_ne, mul_one]
    rwa [hcancel] at hdiv
  exact hrel.x₁_notMem_pair hs halg hx₁

end Relocation

section ProductLocus

open MvPolynomial

/-- The product locus is a plane curve: its vanishing ideal is generated by
a single prime polynomial (the curve-ideal brick applied to the product
pair). -/
theorem exists_prime_span_mul :
    ∃ F : MvPolynomial (Fin 2) k, Prime F ∧
      idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F} := by
  have hconv : ![S.x₁, S.y₁] * ![S.x₂, S.y₂] = ![S.x₁ * S.x₂, S.y₁ * S.y₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hconv]
  exact exists_prime_span_idealOf k S.mul_fst_transcendental S.mul_mem

variable {S} {c₂' : Fin 2 → Ω}

/-- **Generic scaling invariance** (step 3 of the multiplicative chain): the
generator `F` of the product-locus prime, with the ratio element
`ρ = c₂ / c₂'` multiplied into its variables, vanishes on the joint locus of
the relocated product point and `ρ`. Every joint polynomial consequence of
the pair may therefore be played against `F(X·U, Y·V)` in the
minimal-degree argument. -/
theorem JointRel.mulSubst_mem (hrel : S.JointRel c₂')
    {F : MvPolynomial (Fin 2) k}
    (hF : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F}) :
    mulSubst (k := k) F ∈ idealOf k
      (Sum.elim (![S.x₁, S.y₁] * c₂') (![S.x₂, S.y₂] / c₂')) := by
  rw [mem_idealOf_iff, aeval_mulSubst]
  have hne : ∀ i, c₂' i ≠ 0 := Fin.forall_fin_two.2 ⟨hrel.fst_ne, hrel.snd_ne⟩
  have harith : ![S.x₁, S.y₁] * c₂' * (![S.x₂, S.y₂] / c₂') =
      ![S.x₁, S.y₁] * ![S.x₂, S.y₂] := by
    funext i
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [mul_assoc, mul_comm (c₂' i), div_mul_cancel₀ _ (hne i)]
  rw [harith]
  have hmem : F ∈ idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) := by
    rw [hF]
    exact Ideal.subset_span rfl
  exact (mem_idealOf_iff _).1 hmem

end ProductLocus

section ScalingIdentity

open MvPolynomial

/-- The field generated by the ratio element `ρ = c₂ / c₂'`. -/
def rhoField (S : MulCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    IntermediateField k Ω :=
  adjoin k {S.x₂ / c₂' 0, S.y₂ / c₂' 1}

/-- The ratio element as a vector over `k(ρ)`. -/
def rhoVec (S : MulCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    Fin 2 → ↥(rhoField S c₂') :=
  ![⟨S.x₂ / c₂' 0, subset_adjoin k _ (Set.mem_insert _ _)⟩,
    ⟨S.y₂ / c₂' 1, subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)⟩]

variable {S} {c₂' : Fin 2 → Ω} {s : Ω}

/-- The unrelocated product coordinate is also transcendental over `k(ρ)`
(dividing by `ρ₁` moves between the two product points). -/
theorem JointRel.mul_fst_notMem_rho' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ * S.x₂ ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
  intro hmem
  have hρ₁ : S.x₂ / c₂' 0 ∈ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} :=
    subset_racl k _ (Set.mem_insert _ _)
  have h2 : S.x₁ * c₂' 0 ∈ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
    have h3 := div_mem hmem hρ₁
    have h4 : S.x₁ * S.x₂ / (S.x₂ / c₂' 0) = S.x₁ * c₂' 0 := by
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.x₂_ne,
        mul_one]
    rwa [h4] at h3
  exact hrel.mul_fst_notMem_rho hs halg h2

/-- The unrelocated product's second coordinate is also transcendental over
`k(ρ)`. -/
theorem JointRel.mul_snd_notMem_rho' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ * S.y₂ ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := fun hmem ↦
  hrel.mul_fst_notMem_rho' hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) S.mul_mem')

/-- … and the relocated product's second coordinate. -/
theorem JointRel.mul_snd_notMem_rho (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ * c₂' 1 ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := fun hmem ↦
  hrel.mul_fst_notMem_rho hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) hrel.mul_fst_mem)

/-- **The exact scaling identity** (the multiplicative chain assembled
through step 4): the extension to `k(ρ)` of the product-locus generator has
its span fixed by the scaling substitution by `ρ = c₂ / c₂'`, so by scaling
rigidity the monomial values of `ρ` agree across its support — the
`ρ^(m−m') = 1` relations feeding the exponent-lattice classification. -/
theorem JointRel.monomial_prod_rhoVec_eq [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F}) :
    ∀ m ∈ (MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F).support,
      ∀ m' ∈ (MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F).support,
        (m.prod fun j e ↦ rhoVec S c₂' j ^ e) =
          (m'.prod fun j e ↦ rhoVec S c₂' j ^ e) := by
  classical
  set FK := MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F with hFK
  -- Genericity of the original product point over `k(ρ)`.
  have hu : Transcendental ↥(rhoField S c₂') (S.x₁ * S.x₂) := fun h ↦
    hrel.mul_fst_notMem_rho' hs halg ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(rhoField S c₂') (S.y₁ * S.y₂) := fun h ↦
    hrel.mul_snd_notMem_rho' hs halg ((mem_racl_iff k).2 h)
  -- The span at the clean product tuple.
  have hconv : ![S.x₁, S.y₁] * ![S.x₂, S.y₂] = ![S.x₁ * S.x₂, S.y₁ * S.y₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hconv] at hFspan
  have hspan_d : idealOf ↥(rhoField S c₂') ![S.x₁ * S.x₂, S.y₁ * S.y₂] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hu S.mul_mem hv' S.mul_mem' hF0 hFspan
  -- Genericity of the relocated product point over `k(ρ)`, and its span.
  have hud' : Transcendental ↥(rhoField S c₂') (S.x₁ * c₂' 0) := fun h ↦
    hrel.mul_fst_notMem_rho hs halg ((mem_racl_iff k).2 h)
  have hvd'' : Transcendental ↥(rhoField S c₂') (S.y₁ * c₂' 1) := fun h ↦
    hrel.mul_snd_notMem_rho hs halg ((mem_racl_iff k).2 h)
  have hFspan_d' : idealOf k ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] = Ideal.span {F} := by
    have h1 := hrel.mul_idealOf_eq
    have hconv' : ![S.x₁, S.y₁] * c₂' = ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] := by
      funext i
      fin_cases i <;> simp
    rw [hconv', hconv] at h1
    rw [h1, hFspan]
  have hspan_d' : idealOf ↥(rhoField S c₂') ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hud' hrel.mul_snd_mem hvd'' hrel.mul_fst_mem hF0
      hFspan_d'
  -- Transport the `d`-span along the scaling and compare with the `d'`-span.
  have hρne : ∀ j, rhoVec S c₂' j ≠ 0 := by
    intro j
    fin_cases j
    · exact fun h0 ↦
        div_ne_zero S.x₂_ne hrel.fst_ne (congrArg Subtype.val h0)
    · exact fun h0 ↦
        div_ne_zero S.y₂_ne hrel.snd_ne (congrArg Subtype.val h0)
  have htrans := idealOf_scale_span (c := rhoVec S c₂') hρne hspan_d
  have htuple : (fun j ↦ (![S.x₁ * S.x₂, S.y₁ * S.y₂] : Fin 2 → Ω) j /
      algebraMap ↥(rhoField S c₂') Ω (rhoVec S c₂' j)) =
      ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] := by
    funext j
    fin_cases j
    · show S.x₁ * S.x₂ / (S.x₂ / c₂' 0) = S.x₁ * c₂' 0
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.x₂_ne,
        mul_one]
    · show S.y₁ * S.y₂ / (S.y₂ / c₂' 1) = S.y₁ * c₂' 1
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.y₂_ne,
        mul_one]
  rw [htuple, hspan_d'] at htrans
  have hFK0 : FK ≠ 0 := fun h ↦ hF0 (MvPolynomial.map_injective _
    (algebraMap k ↥(rhoField S c₂')).injective (by rw [map_zero]; exact h))
  exact monomial_prod_eq_of_span_scale_eq hρne hFK0 htrans.symm

end ScalingIdentity

end MulCorrSetup

end

end AclGeom
