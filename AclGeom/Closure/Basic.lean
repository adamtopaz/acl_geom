/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Relative algebraic closure as a pregeometry

`racl k S`: elements of `K` algebraic over `k(S)`, built from
`IntermediateField.adjoin` and `algebraicClosure` with restriction of scalars.
This file exposes the carrier-level membership theorem immediately; subsequent
files should almost never unfold the tower of intermediate-field definitions
(blueprint §Foundation I).

Contents (blueprint Prop 4.1):
* `racl` and `mem_racl_iff`, the public membership criterion;
* extensivity (`subset_racl`), monotonicity (`racl_mono`), and
  idempotence (`racl_racl`);
* finite character (`exists_finset_racl`);
* exchange (`isAlgebraic_adjoin_exchange`, `racl_exchange`).

Still to come here (checklist F1, F2): equivariance, Frobenius invariance,
and the finite representative calculus (blueprint Lemma 4.2).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M1).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The relative algebraic closure of a set `S` in a field extension `K/k`:
the intermediate field of all elements of `K` algebraic over `k(S)`.

Implementation: the relative algebraic closure of `k(S) = adjoin k S` in `K`,
restricted back to a `k`-intermediate field. Do not unfold this; use
`mem_racl_iff`. -/
def racl (S : Set K) : IntermediateField k K :=
  (algebraicClosure (adjoin k S) K).restrictScalars k

/-- The public membership criterion for `racl` (blueprint §Foundation I):
`x ∈ racl k S` iff `x` is algebraic over `k(S)`. -/
theorem mem_racl_iff {S : Set K} {x : K} :
    x ∈ racl k S ↔ IsAlgebraic (adjoin k S) x := by
  rw [racl, mem_restrictScalars, mem_algebraicClosure_iff]

/-- `k(S)` is contained in the relative algebraic closure of `S`. -/
theorem adjoin_le_racl (S : Set K) : adjoin k S ≤ racl k S := by
  intro x hx
  rw [mem_racl_iff]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : adjoin k S)

/-- Extensivity: `S ⊆ racl k S`. -/
theorem subset_racl (S : Set K) : S ⊆ (racl k S : Set K) :=
  (subset_adjoin k S).trans (adjoin_le_racl k S)

variable {k}

/-- An intermediate field is contained in `racl k S` iff it is algebraic
over `k(S)` elementwise. -/
theorem le_racl_iff {S : Set K} {E : IntermediateField k K} :
    E ≤ racl k S ↔ ∀ x ∈ E, IsAlgebraic (adjoin k S) x :=
  ⟨fun h _ hx ↦ (mem_racl_iff k).1 (h hx), fun h x hx ↦ (mem_racl_iff k).2 (h x hx)⟩

/-- Monotonicity of `racl` in the set argument. -/
theorem racl_mono {S T : Set K} (h : S ⊆ T) : racl k S ≤ racl k T := by
  intro x hx
  rw [mem_racl_iff] at hx ⊢
  -- Pass through the tower `k(S) ⊆ k(S)(T) = k(T)`.
  have hx' : IsAlgebraic (adjoin (adjoin k S) T) x := hx.tower_top _
  rw [isAlgebraic_iff_isIntegral] at hx' ⊢
  rwa [show adjoin k T = (adjoin (adjoin k S) T).restrictScalars k by
    rw [adjoin_adjoin_left, Set.union_eq_self_of_subset_left h]]

variable (k)

/-- Idempotence: taking `racl` twice gives nothing new (blueprint Prop 4.1). -/
theorem racl_racl (S : Set K) : racl k (racl k S : Set K) = racl k S := by
  refine le_antisymm ?_ (fun x hx ↦ (racl_mono (subset_racl k S)) hx)
  intro x hx
  rw [mem_racl_iff, adjoin_self] at hx
  rw [mem_racl_iff]
  -- `x` is algebraic over `racl k S`, which is algebraic over `k(S)`;
  -- conclude by transitivity of integrality. `racl k S` is by definition a
  -- scalar restriction of `algebraicClosure (adjoin k S) K`, with the same
  -- carrier and the same algebra map into `K`, so the hypothesis transports
  -- definitionally.
  have : Algebra.IsIntegral (adjoin k S) (algebraicClosure (adjoin k S) K) :=
    Algebra.IsAlgebraic.isIntegral
  rw [isAlgebraic_iff_isIntegral] at hx ⊢
  have hx' : IsIntegral (algebraicClosure (adjoin k S) K) x := hx
  exact isIntegral_trans x hx'

variable {k}

/-- An element annihilated by a nonzero polynomial whose coefficients lie in an
intermediate field `E` is algebraic over `E`. -/
theorem isAlgebraic_of_coeff_mem {E : IntermediateField k K} {x : K} {p : Polynomial K}
    (hp : p ≠ 0) (hpx : p.eval x = 0) (hc : ∀ n, p.coeff n ∈ E) : IsAlgebraic E x := by
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := algebraMap E K) p).1 <|
    (Polynomial.lifts_iff_coeff_lifts p).2 fun n ↦ ⟨(⟨p.coeff n, hc n⟩ : E), rfl⟩
  refine ⟨q, fun h0 ↦ hp ?_, ?_⟩
  · rw [← hq, h0, Polynomial.map_zero]
  · rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq, hpx]

/-- Finite character: an element of `racl k S` already lies in `racl k T` for
some finite `T ⊆ S` (blueprint Prop 4.1). -/
theorem exists_finset_racl {S : Set K} {x : K} (hx : x ∈ racl k S) :
    ∃ T : Finset K, ↑T ⊆ S ∧ x ∈ racl k (T : Set K) := by
  classical
  rw [mem_racl_iff] at hx
  obtain ⟨p, hp0, hpx⟩ := hx
  -- Push the annihilating polynomial down to `K[X]` and collect, for each of
  -- its finitely many coefficients, a finite subset of `S` generating it.
  set q : Polynomial K := p.map (algebraMap (adjoin k S) K) with hq
  have hq0 : q ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (adjoin k S) K).injective).2 hp0
  have hqx : q.eval x = 0 := by
    rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def, hpx]
  have hcoeff : ∀ n, q.coeff n ∈ adjoin k S := fun n ↦ by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff n).2
  choose T hTS hTmem using fun n ↦ exists_finset_of_mem_adjoin (hcoeff n)
  refine ⟨q.support.biUnion T, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, hn⟩ := Finset.mem_biUnion.1 hy
    exact hTS n hn
  · rw [mem_racl_iff]
    refine isAlgebraic_of_coeff_mem hq0 hqx fun n ↦ ?_
    by_cases hn : n ∈ q.support
    · exact adjoin.mono _ _ _ (by exact_mod_cast Finset.subset_biUnion_of_mem T hn)
        (hTmem n)
    · simp [Polynomial.notMem_support_iff.1 hn]

section Exchange

open scoped IntermediateField.algebraAdjoinAdjoin

variable {F : Type*} [Field F] [Algebra F K]

/-- Exchange over a base field: if `x` is algebraic over `F(y)` and
transcendental over `F`, then `y` is algebraic over `F(x)`
(the exchange step of blueprint Prop 4.1). -/
theorem isAlgebraic_adjoin_exchange {x y : K}
    (hx : IsAlgebraic (adjoin F {y}) x) (hx' : Transcendental F x) :
    IsAlgebraic (adjoin F {x}) y := by
  by_contra hy
  -- Bridge `¬(algebraic over the field F(x))` down to the ring `F[x]`.
  have hy' : Transcendental (Algebra.adjoin F ({x} : Set K)) y := fun h ↦
    hy ((IsFractionRing.isAlgebraic_iff (Algebra.adjoin F ({x} : Set K)) (adjoin F {x}) K).1 h)
  -- The pair `(y, x)` is then algebraically independent over `F`.
  have hxInd : AlgebraicIndependent F (fun _ : Unit ↦ x) :=
    algebraicIndependent_unique_type_iff.2 hx'
  have hpair : AlgebraicIndependent F (fun o : Option Unit ↦ o.elim y fun _ ↦ x) := by
    refine (hxInd.option_iff_transcendental y).2 ?_
    rwa [Set.range_const]
  -- Swap the pair to `(x, y)` and read the equivalence the other way:
  -- `x` is transcendental over `F[y]`, contradicting `hx`.
  have hfun : ((fun o : Option Unit ↦ o.elim y fun _ ↦ x) ∘ Equiv.swap none (some ())) =
      fun o : Option Unit ↦ o.elim x fun _ ↦ y := by
    funext o
    rcases o with - | -
    · simp
    · simp
  have hswap : AlgebraicIndependent F (fun o : Option Unit ↦ o.elim x fun _ ↦ y) :=
    hfun ▸ hpair.comp (Equiv.swap none (some ())) (Equiv.injective _)
  have hyInd : AlgebraicIndependent F (fun _ : Unit ↦ y) :=
    hswap.comp some (Option.some_injective Unit)
  have hxTr : Transcendental (Algebra.adjoin F (Set.range fun _ : Unit ↦ y)) x :=
    (hyInd.option_iff_transcendental x).1 hswap
  rw [Set.range_const] at hxTr
  exact hxTr
    ((IsFractionRing.isAlgebraic_iff (Algebra.adjoin F ({y} : Set K)) (adjoin F {y}) K).2 hx)

/-- Exchange for `racl` (blueprint Prop 4.1): if `x ∈ racl k (S ∪ {y})` but
`x ∉ racl k S`, then `y ∈ racl k (S ∪ {x})`. -/
theorem racl_exchange {S : Set K} {x y : K}
    (hxy : x ∈ racl k (insert y S)) (hx : x ∉ racl k S) :
    y ∈ racl k (insert x S) := by
  rw [mem_racl_iff] at hxy hx ⊢
  have key : ∀ z : K, adjoin k (insert z S) =
      (adjoin (adjoin k S) {z}).restrictScalars k := fun z ↦ by
    rw [adjoin_adjoin_left, Set.union_singleton]
  rw [key y] at hxy
  rw [key x]
  -- Transport across `restrictScalars` (definitionally the same carrier and
  -- algebra map into `K`), apply exchange over the base field `adjoin k S`.
  have hxy' : IsAlgebraic (adjoin (adjoin k S) {y}) x := hxy
  have h := isAlgebraic_adjoin_exchange hxy' hx
  exact h

end Exchange

end

end AclGeom
