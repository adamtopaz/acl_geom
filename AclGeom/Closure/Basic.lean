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
* exchange (`isAlgebraic_adjoin_exchange`, `racl_exchange`);
* equivariance (`racl_map`) and power invariance (`racl_image_pow`);
* base monotonicity (`racl_subset_racl_base`);
* the representative calculus, part (a)
  (`algebraicIndependent_iff_forall_notMem_racl`): independence is exactly
  avoidance of the closures of the other members (blueprint Lemma 4.2(a)).

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

/-- An element annihilated by a nonzero polynomial whose coefficients lie in an
intermediate field `E` is algebraic over `E`. -/
theorem isAlgebraic_of_coeff_mem {E : IntermediateField k K} {x : K} {p : Polynomial K}
    (hp : p ≠ 0) (hpx : p.eval x = 0) (hc : ∀ n, p.coeff n ∈ E) : IsAlgebraic E x := by
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := algebraMap E K) p).1 <|
    (Polynomial.lifts_iff_coeff_lifts p).2 fun n ↦ ⟨(⟨p.coeff n, hc n⟩ : E), rfl⟩
  refine ⟨q, fun h0 ↦ hp ?_, ?_⟩
  · rw [← hq, h0, Polynomial.map_zero]
  · rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq, hpx]

/-- Algebraicity over an intermediate field is monotone in the base field. -/
theorem isAlgebraic_of_le {E₁ E₂ : IntermediateField k K} (h : E₁ ≤ E₂) {x : K}
    (hx : IsAlgebraic E₁ x) : IsAlgebraic E₂ x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  refine isAlgebraic_of_coeff_mem ((Polynomial.map_ne_zero_iff
    (algebraMap E₁ K).injective).2 hp0) ?_ fun n ↦ ?_
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpx]
  · rw [Polynomial.coeff_map]
    exact h (p.coeff n).2

/-- Monotonicity of `racl` in the set argument. -/
theorem racl_mono {S T : Set K} (h : S ⊆ T) : racl k S ≤ racl k T := fun _ hx ↦
  (mem_racl_iff k).2 (isAlgebraic_of_le (adjoin.mono k S T h) ((mem_racl_iff k).1 hx))

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

/-- The closure of a subset of `racl k S` is contained in `racl k S`. -/
theorem racl_le_of_subset_racl {S T : Set K} (h : T ⊆ racl k S) :
    racl k T ≤ racl k S := by
  rw [← racl_racl k S]
  exact racl_mono h

/-- Absorption: inserting an element of the closure changes nothing. -/
theorem racl_insert_of_mem {S : Set K} {y : K} (hy : y ∈ racl k S) :
    racl k (insert y S) = racl k S :=
  le_antisymm (racl_le_of_subset_racl (Set.insert_subset hy (subset_racl k S)))
    (racl_mono (Set.subset_insert y S))

/-- A transcendental element avoids the closure of the empty set. -/
theorem notMem_racl_empty_of_transcendental {x : K} (hx : Transcendental k x) :
    x ∉ racl k (∅ : Set K) := by
  intro hmem
  refine hx ?_
  have halg : IsAlgebraic ↥(adjoin k (∅ : Set K)) x := (mem_racl_iff k).1 hmem
  rw [adjoin_empty] at halg
  haveI : Algebra.IsIntegral k ↥(⊥ : IntermediateField k K) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 z.2
    have hz : z = algebraMap k ↥(⊥ : IntermediateField k K) c :=
      Subtype.ext hc.symm
    rw [hz]
    exact isIntegral_algebraMap
  rw [isAlgebraic_iff_isIntegral] at halg ⊢
  exact isIntegral_trans x halg

/-- Converse companion to `isAlgebraic_of_coeff_mem`: an element algebraic over
an intermediate field `E` is annihilated by a nonzero polynomial over `K` whose
coefficients lie in `E`. -/
theorem exists_poly_of_isAlgebraic {E : IntermediateField k K} {x : K}
    (hx : IsAlgebraic E x) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.eval x = 0 ∧ ∀ n, q.coeff n ∈ E := by
  obtain ⟨p, hp0, hpx⟩ := hx
  refine ⟨p.map (algebraMap E K),
    (Polynomial.map_ne_zero_iff (algebraMap E K).injective).2 hp0, ?_, fun n ↦ ?_⟩
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpx]
  · rw [Polynomial.coeff_map]
    exact (p.coeff n).2

/-- Finite character: an element of `racl k S` already lies in `racl k T` for
some finite `T ⊆ S` (blueprint Prop 4.1). -/
theorem exists_finset_racl {S : Set K} {x : K} (hx : x ∈ racl k S) :
    ∃ T : Finset K, ↑T ⊆ S ∧ x ∈ racl k (T : Set K) := by
  classical
  obtain ⟨q, hq0, hqx, hcoeff⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff k).1 hx)
  -- For each of the finitely many coefficients, collect a finite subset of `S`
  -- generating it.
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

/-- Adjoining then closing collapses a tower step: membership in
`racl k (insert z S)` is algebraicity over `k(S)(z)`. -/
theorem mem_racl_insert_iff {S : Set K} {z x : K} :
    x ∈ racl k (insert z S) ↔
      IsAlgebraic ↥(adjoin ↥(adjoin k S) ({z} : Set K)) x := by
  rw [mem_racl_iff]
  have key : adjoin k (insert z S) =
      (adjoin (adjoin k S) {z}).restrictScalars k := by
    rw [adjoin_adjoin_left, Set.union_singleton]
  rw [key]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

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

section Equivariance

variable {L : Type*} [Field L] [Algebra k L]

/-- A `k`-algebra isomorphism carries `racl k S` into `racl k (σ '' S)`
(one half of the equivariance in blueprint Prop 4.1). For extensions over
different base fields, transport the algebra structure along the base
isomorphism first. -/
theorem mem_racl_map (σ : K ≃ₐ[k] L) {S : Set K} {x : K} (hx : x ∈ racl k S) :
    σ x ∈ racl k (σ '' S) := by
  obtain ⟨q, hq0, hqx, hc⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff k).1 hx)
  rw [mem_racl_iff]
  refine isAlgebraic_of_coeff_mem (p := q.map (σ : K →+* L))
    ((Polynomial.map_ne_zero_iff (σ : K →+* L).injective).2 hq0) ?_ fun n ↦ ?_
  · rw [Polynomial.eval_map,
      show σ x = (σ : K →+* L) x from rfl, Polynomial.eval₂_at_apply, hqx, map_zero]
  · rw [Polynomial.coeff_map]
    have h1 : σ (q.coeff n) ∈ (adjoin k S).map σ.toAlgHom := ⟨q.coeff n, hc n, rfl⟩
    rw [adjoin_map] at h1
    simpa using h1

/-- Equivariance of `racl`, membership form. -/
theorem mem_racl_map_iff (σ : K ≃ₐ[k] L) {S : Set K} {x : K} :
    σ x ∈ racl k (σ '' S) ↔ x ∈ racl k S := by
  refine ⟨fun h ↦ ?_, mem_racl_map σ⟩
  have h2 := mem_racl_map σ.symm h
  rwa [AlgEquiv.symm_apply_apply,
    show σ.symm '' (σ '' S) = S by rw [← Set.image_comp]; simp] at h2

/-- Equivariance of `racl` (blueprint Prop 4.1): a `k`-algebra isomorphism
maps the relative algebraic closure of `S` onto that of `σ '' S`. -/
theorem racl_map (σ : K ≃ₐ[k] L) (S : Set K) :
    (racl k S).map σ.toAlgHom = racl k (σ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using mem_racl_map σ hx
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    have h2 := mem_racl_map σ.symm hy
    rwa [show σ.symm '' (σ '' S) = S by rw [← Set.image_comp]; simp] at h2

end Equivariance

section PowerInvariance

/-- `racl` is invariant under replacing every generator by a fixed positive
power. Over a perfect field this gives invariance of the closure under
positive Frobenius iterates (blueprint Prop 4.1); the negative iterates are
handled with the perfection layer, where inverse Frobenius is available. -/
theorem racl_image_pow {m : ℕ} (hm : m ≠ 0) (S : Set K) :
    racl k ((· ^ m) '' S) = racl k S := by
  refine le_antisymm ?_ ?_
  · -- Powers of members of `racl k S` stay in `racl k S`.
    refine (racl_mono ?_).trans_eq (racl_racl k S)
    rintro - ⟨s, hs, rfl⟩
    exact pow_mem (subset_racl k S hs) m
  · -- Each `s ∈ S` is a root of `X ^ m - C (s ^ m)`.
    refine (racl_mono ?_).trans_eq (racl_racl k _)
    intro s hs
    rw [SetLike.mem_coe, mem_racl_iff]
    have hsm : s ^ m ∈ adjoin k ((· ^ m) '' S) := subset_adjoin _ _ ⟨s, hs, rfl⟩
    refine isAlgebraic_of_coeff_mem (p := Polynomial.X ^ m - Polynomial.C (s ^ m))
      (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hm) _) (by simp) fun n ↦ ?_
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases eq_or_ne n m with rfl | hnm
    · simp [hm]
    · rcases eq_or_ne n 0 with rfl | hn0
      · simpa [hnm] using neg_mem hsm
      · simp [hnm, hn0]

end PowerInvariance

section RepresentativeCalculus

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Blueprint Lemma 4.2(a): a family is algebraically independent over `k`
iff no member lies in the relative algebraic closure of the others. -/
theorem algebraicIndependent_iff_forall_notMem_racl {ι : Type*} {v : ι → K} :
    AlgebraicIndependent k v ↔ ∀ i, v i ∉ racl k (v '' {i}ᶜ) := by
  constructor
  · intro h i hmem
    refine ((AlgebraicIndependent.iff_transcendental_adjoin_image (x := v) i).1 h).2 ?_
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (v '' {i}ᶜ))
      (adjoin k (v '' {i}ᶜ)) K).2 ((mem_racl_iff k).1 hmem)
  · intro h
    refine algebraicIndependent_of_finite_type' (algebraMap k K).injective
      fun t _ _ i hit halg ↦ h i ?_
    rw [mem_racl_iff]
    have h2 : IsAlgebraic (adjoin k (v '' t)) (v i) :=
      (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (v '' t))
        (adjoin k (v '' t)) K).1 halg
    refine isAlgebraic_of_le (adjoin.mono _ _ _ (Set.image_mono ?_)) h2
    exact fun j hj hji ↦ hit (hji ▸ hj)

/-- The pair form of blueprint Lemma 4.2(a), forward direction: the second
member of an independent pair is not algebraic over the first. -/
theorem AlgebraicIndependent.notMem_racl_pair {x y : K}
    (h : AlgebraicIndependent k ![x, y]) : y ∉ racl k {x} := by
  intro hy
  have h1 := algebraicIndependent_iff_forall_notMem_racl.1 h 1
  refine h1 ?_
  refine racl_mono ?_ hy
  intro z hz
  refine ⟨0, ?_, ?_⟩
  · simp
  · simpa using hz.symm

/-- The symmetric pair form of blueprint Lemma 4.2(a): the first member of
an independent pair is not algebraic over the second. -/
theorem AlgebraicIndependent.notMem_racl_pair' {x y : K}
    (h : AlgebraicIndependent k ![x, y]) : x ∉ racl k {y} := by
  intro hx
  have h0 := algebraicIndependent_iff_forall_notMem_racl.1 h 0
  refine h0 ?_
  refine racl_mono ?_ hx
  intro z hz
  refine ⟨1, ?_, ?_⟩
  · simp
  · simpa using hz.symm

end RepresentativeCalculus

section BaseMono

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Relative algebraic closure is monotone in the base field: enlarging the
base from `k` to an intermediate field `K₀` enlarges the closure. -/
theorem racl_subset_racl_base (K₀ : IntermediateField k K) (S : Set K) :
    (racl k S : Set K) ⊆ (racl ↥K₀ S : Set K) := by
  intro x hx
  rw [SetLike.mem_coe, mem_racl_iff] at hx
  obtain ⟨q, hq0, hqx, hqc⟩ := exists_poly_of_isAlgebraic hx
  have hsub : (adjoin k S : Set K) ⊆ ((adjoin ↥K₀ S : IntermediateField ↥K₀ K) : Set K) := by
    have hle : adjoin k S ≤ (adjoin ↥K₀ S).restrictScalars k :=
      adjoin_le_iff.2 fun y hy ↦ subset_adjoin ↥K₀ S hy
    exact fun y hy ↦ hle hy
  rw [SetLike.mem_coe, mem_racl_iff]
  exact isAlgebraic_of_coeff_mem (E := adjoin ↥K₀ S) hq0 hqx fun m ↦ hsub (hqc m)

end BaseMono

end

end AclGeom
