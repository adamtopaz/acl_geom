/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobEqCorrect
import AclGeom.Reconstruct.Kernel

/-!
# Coordinates on the fixed Frobenius class

Blueprint Lemma `mu-bij`: on the fixed class `J₁ = [j(x₀, a)]_FrobEq`, the coordinate map
`μ(j(x, a)) = x` is a bijection onto `K ∖ acl_k(a)`.

* Injectivity on tuples with the same literal parameter (`eq_of_jTupleOf_eq`): if
  `j(x, a) = j(y, a)`, j-rigidity (`j_rigidity_field`) gives `y^{q^v} = x^{q^u}` and
  `a^{q^v} = a^{q^u}`; a transcendental `a` forces `u = v`, and Frobenius powers are injective.
  This uses only the rank-five hypothesis, for two fresh elements.
* The bijection itself (`jClassEquiv`), with its evaluation `μ(j(x, a)) = x`
  (`jClassEquiv_jTupleOf`).  Surjectivity onto the class is the fixed-class description
  `frobEq_jTupleOf_iff`, so `K` is perfect of rank at least five and the completeness input
  `hcomp` stays explicit.

**Status:** same-parameter injectivity is proved at rank five, and the coordinate bijection
with its evaluation law is proved under the explicit ACF J-completeness input `hcomp` (#23).
Corrected generic fixed-class operations are proved in `ClassArithmetic` under the same inputs.
Corrected ratio semantics is proved in `Ratio` under the same explicit inputs.
`Decode` packages the corrected geometric ratio quotient and bijective nonzero decoding.
Adjoining zero, non-generic totalization and quotient field operations remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The coordinate is determined by the `j`-tuple** (blueprint Lemma `mu-bij`, injectivity):
two `j`-tuples with the same parameter `a` coincide only if their first coordinates do. -/
theorem eq_of_jTupleOf_eq (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {x y a : K}
    (hx : AlgebraicIndependent k ![x, a]) (hy : AlgebraicIndependent k ![y, a])
    (h : jTupleOf x a hx = jTupleOf y a hy) : x = y := by
  classical
  have : ExpChar K (ringExpChar k) :=
    expChar_of_injective_algebraMap (algebraMap k K).injective _
  have ha0 : a ∉ racl k (∅ : Set K) := fun h' ↦
    AlgebraicIndependent.notMem_racl_pair hx (racl_mono (Set.empty_subset _) h')
  -- The coordinate points of the two tuples agree.
  have hpt : ∀ i, (jTupleOf x a hx i).1 = (jTupleOf y a hy i).1 := fun i ↦ by rw [h]
  have e₀ : point k x = point k y := hpt 0
  have e₁ : point k (x + a) = point k (y + a) := hpt 1
  have e₂ : point k (x * a) = point k (y * a) := hpt 2
  have e₃ : point k (x * (1 + a)) = point k (y * (1 + a)) := by
    rw [show x * (1 + a) = x + x * a by ring, show y * (1 + a) = y + y * a by ring]
    exact hpt 3
  obtain ⟨r₀, r₀'⟩ := point_eq_point_iff.1 e₀
  obtain ⟨r₁, r₁'⟩ := point_eq_point_iff.1 e₁
  obtain ⟨r₂, r₂'⟩ := point_eq_point_iff.1 e₂
  obtain ⟨r₃, r₃'⟩ := point_eq_point_iff.1 e₃
  have haa : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  -- Two fresh elements for j-rigidity.
  have hfresh := fresh_three_of_five_le_trdeg htr
  obtain ⟨s, hs⟩ := hfresh {x, a} ((Finset.card_insert_le _ _).trans (by simp))
  obtain ⟨s', hs'⟩ := hfresh {x, a, s}
    ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))))
  have hs₂ : s ∉ racl k ({x, a} : Set K) := by simpa using hs
  have hs₂' : s' ∉ racl k ({x, a, s} : Set K) := by simpa using hs'
  obtain ⟨u, v, h₁, h₂⟩ := j_rigidity_field (ringExpChar k) hx r₀' r₀ haa haa r₁' r₁ r₂' r₂
    r₃' r₃ hs₂ hs₂'
  -- The transcendental parameter separates the exponents.
  rcases expChar_is_prime_or_one k (ringExpChar k) with hp | hq
  · rw [pow_pow_sep_of_notMem_racl_empty ha0 hp.two_le h₂] at h₁
    exact (iterateFrobenius_inj K (ringExpChar k) u
      (by simpa only [iterateFrobenius_def] using h₁)).symm
  · simpa [hq] using h₁.symm

/-- With a transcendental parameter `a`, an element outside `racl_k {a}` is independent from it. -/
private theorem pair_of_notMem {x₀ a x : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hx : x ∉ racl k ({a} : Set K)) : AlgebraicIndependent k ![x, a] := by
  have ha0 : a ∉ racl k (∅ : Set K) := fun h' ↦
    AlgebraicIndependent.notMem_racl_pair h₀ (racl_mono (Set.empty_subset _) h')
  exact algebraicIndependent_pair hx fun h ↦ hx (racl_exchange_singleton ha0 h)

/-- The tuple `j(x, a)` as a member of the class of `j(x₀, a)`. -/
private def jClassMk (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {x₀ a : K}
    (h₀ : AlgebraicIndependent k ![x₀, a]) (x : {x : K // x ∉ racl k ({a} : Set K)}) :
    {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} :=
  ⟨jTupleOf x.1 a (pair_of_notMem h₀ x.2),
    frobEq_jTupleOf_of_common htr h₀ (pair_of_notMem h₀ x.2)⟩

/-- **The coordinate bijection** (blueprint Lemma `mu-bij`): the `FrobEq` class of `j(x₀, a)` is
in bijection with `K ∖ acl_k(a)` by `j(x, a) ↦ x`.  Surjectivity uses the fixed-class description,
so `K` is perfect of rank at least five and completeness over `k̄ ⊆ K̄` (`hcomp`) is assumed. -/
def jClassEquiv [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} ≃
      {x : K // x ∉ racl k ({a} : Set K)} :=
  (Equiv.ofBijective (jClassMk htr h₀)
    ⟨fun x y hxy ↦ Subtype.ext (eq_of_jTupleOf_eq htr
      (pair_of_notMem h₀ x.2) (pair_of_notMem h₀ y.2) (congrArg Subtype.val hxy)),
      fun w ↦ by
        obtain ⟨x, hx, hw⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 w.2
        exact ⟨⟨x, AlgebraicIndependent.notMem_racl_pair' hx⟩, Subtype.ext hw.symm⟩⟩).symm

/-- The coordinate of `j(x, a)` in the class of `j(x₀, a)` is `x` (blueprint `μ(j(x, a)) = x`). -/
theorem jClassEquiv_jTupleOf [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a x : K} (h₀ : AlgebraicIndependent k ![x₀, a]) (hx : AlgebraicIndependent k ![x, a])
    (h : FrobEq (jTupleOf x₀ a h₀) (jTupleOf x a hx)) :
    (jClassEquiv q htr hcomp h₀ ⟨jTupleOf x a hx, h⟩ : K) = x := by
  unfold jClassEquiv
  exact congrArg Subtype.val ((Equiv.ofBijective (jClassMk htr h₀) _).symm_apply_apply
    ⟨x, AlgebraicIndependent.notMem_racl_pair' hx⟩)

/-- Class coordinates are nonzero: they lie outside `acl_k(a)`, which contains `0`. -/
theorem jClassEquiv_ne_zero [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (w : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w}) :
    (jClassEquiv q htr hcomp h₀ w : K) ≠ 0 := fun h0 ↦
  (jClassEquiv q htr hcomp h₀ w).2 (by rw [h0]; exact zero_mem _)

end

end AclGeom
