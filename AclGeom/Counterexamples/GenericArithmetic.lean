/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobLinkSoundness

/-!
# The blueprint's generic operation graphs are not functional

Validation for issue #23. The blueprint generic-arithmetic section (`sec:genericops`) defines graphs
`JAdd` and `JMul` on a fixed Frobenius class by four `SumPoint`/`MulPoint`
clauses on the coordinates `(X, P, Q, R, A)` of `j`-tuples.  Its Lemma
`generic-arithmetic` claims, for independent `x, y, a`,
`JAdd(j(x,a), j(y,a), w) ↔ w = j(x+y, a)` and
`JMul(j(x,a), j(y,a), w) ↔ w = j(xy, a)`.

Each clause chooses its own representatives, and `[κu] = [u]` for every
`κ ∈ kˣ`.  So for `κ ≠ 0` the tuples `j(κx + y, a)` and `j(κxy, a)` satisfy
every clause:

* addition, via the representative pairs `(κx, y)`, `(κx, y + a)`,
  `(κxa, ya)`, `(κx(1+a), y(1+a))`;
* multiplication, via `(κx, y)`, `(κxy, a)`, `(κxa, y)`, `(κx(1+a), y)`.

For `κ ≠ 1` they differ from `j(x+y, a)` and `j(xy, a)`, already in the
`P`-coordinate, because `κx + y + a` and `x + y + a` (respectively `κxy + a`
and `xy + a`) are not interalgebraic.

This module states the blueprint graphs literally (`BlueprintJAdd`,
`BlueprintJMul`) and proves both counterexamples
(`blueprintJAdd_not_functional`, `blueprintJMul_not_functional`).  All the
tuples involved lie in one Frobenius class: tuples with a common parameter
are directly linked by the multiplier point `[x/y]`
(`directFrobLink_jTupleOf`), and a fresh `j(t, a)` bridges them
(`frobEq_jTupleOf`).  So the graphs fail to be functional on the class `J₁`
itself (`blueprintJAdd_not_functional_on_class`,
`blueprintJMul_not_functional_on_class`).  Consequently the ratio
equivalence in the ratio section, stated literally as `BlueprintRatioEq`, relates
`(j(x,a), j(y,a))` to `(j(κx,a), j(y,a))` inside one class although the
decoded ratios differ (`blueprintRatioEq_counterexample`).  This is the
formal refutation recorded in issue #23. Corrected coupled operations require
class correctness and totalization; no characterization of their quotient is claimed.

The soundness direction of the configuration layer used here currently
assumes an infinite base field.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (refutation for issue #23).
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Defs

/-- The addition graph of the blueprint generic-arithmetic section, stated literally:
shared parameter coordinates, independence of `u_X, v_X, u_A`, and sum clauses on the
coordinates `X`, `P`, `Q`, `R`.  It is not functional
(`blueprintJAdd_not_functional`). -/
def BlueprintJAdd (u v w : Fin 5 → Point k K) : Prop :=
  u 4 = v 4 ∧ v 4 = w 4 ∧ PointTripleIndependent (u 0) (v 0) (u 4) ∧
    SumPoint (u 0) (v 0) (w 0) ∧ SumPoint (u 0) (v 1) (w 1) ∧
    SumPoint (u 2) (v 2) (w 2) ∧ SumPoint (u 3) (v 3) (w 3)

/-- The multiplication graph of the blueprint generic-arithmetic section, stated literally.
It is not functional (`blueprintJMul_not_functional`). -/
def BlueprintJMul (u v w : Fin 5 → Point k K) : Prop :=
  u 4 = v 4 ∧ v 4 = w 4 ∧ PointTripleIndependent (u 0) (v 0) (u 4) ∧
    MulPoint (u 0) (v 0) (w 0) ∧ SumPoint (w 0) (u 4) (w 1) ∧
    MulPoint (u 2) (v 0) (w 2) ∧ MulPoint (u 3) (v 0) (w 3)

/-- The ratio equivalence of the blueprint ratio section, stated literally relative to the
Frobenius class `J₁ = [b]`: pairs `r, s` are equivalent when there are
`c₁, c₂, d₁, d₂ ∈ J₁` with `JMul(r₁, c₁, d₁)`, `JMul(r₂, c₁, d₂)`,
`JMul(s₁, c₂, d₁)` and `JMul(s₂, c₂, d₂)`.  It does not decode to equality of
ratios (`blueprintRatioEq_counterexample`). -/
def BlueprintRatioEq (b : Fin 5 → Point k K)
    (r s : (Fin 5 → Point k K) × (Fin 5 → Point k K)) : Prop :=
  ∃ c₁ c₂ d₁ d₂ : Fin 5 → Point k K,
    FrobEq b c₁ ∧ FrobEq b c₂ ∧ FrobEq b d₁ ∧ FrobEq b d₂ ∧
      BlueprintJMul r.1 c₁ d₁ ∧ BlueprintJMul r.2 c₁ d₂ ∧
      BlueprintJMul s.1 c₂ d₁ ∧ BlueprintJMul s.2 c₂ d₂

end Defs

section Witnesses

variable {x y a : K}

/-- Rescaling the first entry of an independent pair by a nonzero constant
keeps it independent. -/
theorem AlgebraicIndependent.smul_left {p q : K} (h : AlgebraicIndependent k ![p, q])
    {κ : k} (hκ : κ ≠ 0) : AlgebraicIndependent k ![algebraMap k K κ * p, q] :=
  (algebraicIndependent_congr_racl (v := ![p, q]) (w := ![algebraMap k K κ * p, q])
    (Fin.forall_fin_two.2 ⟨(racl_algebraMap_mul hκ p).symm, rfl⟩)).1 h

/-- Two principal points are distinct when the second generator together with
a third element generates both, and the third element is not algebraic over
the second. -/
theorem point_ne_of_sub {p q r : K} {κ : k} (hκ : κ ≠ 0)
    (hsub : p - q = algebraMap k K κ * r) (hr : r ∉ racl k (∅ : Set K))
    (hq : q - r ∉ racl k ({r} : Set K)) :
    point k p ≠ point k q := by
  intro h
  have hpq : racl k ({p} : Set K) = racl k ({q} : Set K) := congrArg Subtype.val h
  have hp : p ∈ racl k ({q} : Set K) := by
    rw [← hpq]
    exact subset_racl k _ rfl
  have hqq : q ∈ racl k ({q} : Set K) := subset_racl k _ rfl
  have hrq : r ∈ racl k ({q} : Set K) := by
    have h1 : algebraMap k K κ * r ∈ racl k ({q} : Set K) := by
      rw [← hsub]
      exact sub_mem hp hqq
    have h2 := mul_mem (IntermediateField.algebraMap_mem (racl k ({q} : Set K)) κ⁻¹) h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ, map_one, one_mul] at h2
  have hqr : q ∈ racl k ({r} : Set K) := by
    have := racl_exchange (S := (∅ : Set K)) (by simpa using hrq) (by simpa using hr)
    simpa using this
  exact hq (sub_mem hqr (subset_racl k _ rfl))

end Witnesses

section Counterexamples

variable {x y a : K} (hind : AlgebraicIndependent k ![x, y, a])

include hind

private theorem triple_shift {κ : k} (hκ : κ ≠ 0) :
    AlgebraicIndependent k ![algebraMap k K κ * x + y, y, a] := by
  refine AlgebraicIndependent.triple_of_mem hind (fun i ↦ ?_) (fun i ↦ ?_)
  · have hx : x ∈ racl k (Set.range ![x, y, a]) := subset_racl k _ ⟨0, rfl⟩
    have hy : y ∈ racl k (Set.range ![x, y, a]) := subset_racl k _ ⟨1, rfl⟩
    have ha : a ∈ racl k (Set.range ![x, y, a]) := subset_racl k _ ⟨2, rfl⟩
    fin_cases i
    · exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hx) hy
    · exact hy
    · exact ha
  · have hz : algebraMap k K κ * x + y ∈
        racl k (Set.range ![algebraMap k K κ * x + y, y, a]) := subset_racl k _ ⟨0, rfl⟩
    have hy : y ∈ racl k (Set.range ![algebraMap k K κ * x + y, y, a]) :=
      subset_racl k _ ⟨1, rfl⟩
    have ha : a ∈ racl k (Set.range ![algebraMap k K κ * x + y, y, a]) :=
      subset_racl k _ ⟨2, rfl⟩
    fin_cases i
    · have h := mul_mem (IntermediateField.algebraMap_mem _ κ⁻¹) (sub_mem hz hy)
      rwa [add_sub_cancel_right, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ, map_one,
        one_mul] at h
    · exact hy
    · exact ha

private theorem pair_x_ya : AlgebraicIndependent k ![x, y + a] := by
  have htri : AlgebraicIndependent k ![x, y + a, a] := by
    refine AlgebraicIndependent.triple_of_mem hind (fun i ↦ ?_) (fun i ↦ ?_)
    · fin_cases i
      · exact subset_racl k _ ⟨0, rfl⟩
      · exact add_mem (subset_racl k _ ⟨1, rfl⟩) (subset_racl k _ ⟨2, rfl⟩)
      · exact subset_racl k _ ⟨2, rfl⟩
    · fin_cases i
      · exact subset_racl k _ ⟨0, rfl⟩
      · simpa using sub_mem (subset_racl k (Set.range ![x, y + a, a]) ⟨1, rfl⟩)
          (subset_racl k (Set.range ![x, y + a, a]) ⟨2, rfl⟩)
      · exact subset_racl k _ ⟨2, rfl⟩
  exact AlgebraicIndependent.pair_of_triple htri (i := 0) (j := 1) (by decide)

private theorem pair_za {κ : k} (hκ : κ ≠ 0) :
    AlgebraicIndependent k ![algebraMap k K κ * x + y, a] :=
  AlgebraicIndependent.pair_of_triple (triple_shift hind hκ) (i := 0) (j := 2) (by decide)

/-- **The κ-family satisfies the blueprint addition graph**: for every
`κ ∈ kˣ`, `JAdd(j(x,a), j(y,a), j(κx + y, a))`. -/
theorem blueprintJAdd_kappa [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {κ : k}
    (hκ : κ ≠ 0) :
    BlueprintJAdd (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
      (jTupleOf (algebraMap k K κ * x + y) a (pair_za hind hκ)) := by
  have hxy : AlgebraicIndependent k ![x, y] :=
    AlgebraicIndependent.pair_of_triple hind (i := 0) (j := 1) (by decide)
  have hx_ya := pair_x_ya hind
  have hxa_ya : AlgebraicIndependent k ![x * a, y * a] :=
    AlgebraicIndependent.pair_of_triple (algebraicIndependent_mul_mul_left hind)
      (i := 0) (j := 1) (by decide)
  have h1a : AlgebraicIndependent k ![x * (1 + a), y * (1 + a)] :=
    AlgebraicIndependent.pair_of_triple (algebraicIndependent_mul_one_add hind)
      (i := 0) (j := 1) (by decide)
  have h1a' : AlgebraicIndependent k ![x + x * a, y + y * a] := by
    rw [show x + x * a = x * (1 + a) by ring, show y + y * a = y * (1 + a) by ring]
    exact h1a
  have hpt : ∀ z : K, point k z = point k (algebraMap k K κ * z) := fun z ↦
    (point_algebraMap_mul hκ z).symm
  have hrank : PointTripleIndependent (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind) 0)
      (jTupleOf y a (AlgebraicIndependent.pair_one_two hind) 0)
          (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind) 4) := by
    unfold PointTripleIndependent
    rw [jTupleOf_zero, jTupleOf_zero, jTupleOf_four]
    exact rankEq_three_points hind rfl
  refine ⟨jTupleOf_four_eq _ _, jTupleOf_four_eq _ _, hrank, ?_, ?_, ?_, ?_⟩
  · exact sumPoint_of_indep htr (AlgebraicIndependent.smul_left hxy hκ)
      ((jTupleOf_zero _).trans (hpt x)) (jTupleOf_zero _) (jTupleOf_zero _)
  · refine sumPoint_of_indep htr (AlgebraicIndependent.smul_left hx_ya hκ)
      ((jTupleOf_zero _).trans (hpt x)) (jTupleOf_one _) ((jTupleOf_one _).trans ?_)
    rw [add_assoc]
  · refine sumPoint_of_indep htr (AlgebraicIndependent.smul_left hxa_ya hκ)
      ((jTupleOf_two _).trans (hpt _)) (jTupleOf_two _) ((jTupleOf_two _).trans ?_)
    congr 1
    ring
  · refine sumPoint_of_indep htr (AlgebraicIndependent.smul_left h1a' hκ)
      ((jTupleOf_three _).trans (hpt _)) (jTupleOf_three _) ((jTupleOf_three _).trans ?_)
    congr 1
    ring

/-- **The blueprint addition graph is not functional** (issue #23): for
`κ ∉ {0, 1}`, both `j(x + y, a)` and `j(κx + y, a)` are `JAdd`-outputs of
`(j(x,a), j(y,a))`, and they are distinct. -/
theorem blueprintJAdd_not_functional [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {κ : k} (hκ : κ ≠ 0) (hκ1 : κ ≠ 1) :
    BlueprintJAdd (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K κ * x + y) a (pair_za hind hκ)) ∧
      BlueprintJAdd (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
          (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K 1 * x + y) a (pair_za hind one_ne_zero)) ∧
      jTupleOf (algebraMap k K κ * x + y) a (pair_za hind hκ) ≠
        jTupleOf (algebraMap k K 1 * x + y) a (pair_za hind one_ne_zero) := by
  refine ⟨blueprintJAdd_kappa hind htr hκ, blueprintJAdd_kappa hind htr one_ne_zero, ?_⟩
  intro h
  have h1 := congrArg (fun t ↦ (t 1).1) h
  simp only [jTupleOf_one] at h1
  have hx0 : x ∉ racl k (∅ : Set K) := fun hx ↦
    AlgebraicIndependent.notMem_racl_pair' (AlgebraicIndependent.pair_zero_two hind)
        (racl_mono (Set.empty_subset _) hx)
  refine point_ne_of_sub (sub_ne_zero.2 hκ1) (r := x) ?_ hx0 ?_ h1
  · rw [map_sub, map_one]
    ring
  · rw [show algebraMap k K 1 * x + y + a - x = y + a by rw [map_one]; ring]
    exact AlgebraicIndependent.notMem_racl_pair (pair_x_ya hind)

/-- Independence of `(f, y, a)` when `f` and `x` generate each other over
`a`: the shape of every multiplicative witness below. -/
private theorem triple_of_left {f : K} (hf : f ∈ racl k (Set.range ![x, y, a]))
    (hx : x ∈ racl k (Set.range ![f, y, a])) :
    AlgebraicIndependent k ![f, y, a] := by
  refine AlgebraicIndependent.triple_of_mem hind (fun i ↦ ?_) (fun i ↦ ?_)
  · fin_cases i
    · exact hf
    · exact subset_racl k _ ⟨1, rfl⟩
    · exact subset_racl k _ ⟨2, rfl⟩
  · fin_cases i
    · exact hx
    · exact subset_racl k _ ⟨1, rfl⟩
    · exact subset_racl k _ ⟨2, rfl⟩

private theorem pair_xa_y : AlgebraicIndependent k ![x * a, y] := by
  have hr := fun i ↦ subset_racl k (Set.range ![x, y, a]) (Set.mem_range_self i)
  have hr' := fun i ↦ subset_racl k (Set.range ![x * a, y, a]) (Set.mem_range_self i)
  have hx : x ∈ racl k (Set.range ![x * a, y, a]) := by
    have h := mul_mem (hr' 0) (inv_mem (hr' 2))
    simpa [mul_inv_cancel_right₀ (show a ≠ 0 from AlgebraicIndependent.ne_zero hind 2)] using h
  have htri : AlgebraicIndependent k ![x * a, y, a] :=
    triple_of_left hind (mul_mem (hr 0) (hr 2)) hx
  exact AlgebraicIndependent.pair_of_triple htri (i := 0) (j := 1) (by decide)

private theorem pair_x1a_y : AlgebraicIndependent k ![x + x * a, y] := by
  have hr := fun i ↦ subset_racl k (Set.range ![x, y, a]) (Set.mem_range_self i)
  have hr' := fun i ↦ subset_racl k (Set.range ![x + x * a, y, a]) (Set.mem_range_self i)
  have hx : x ∈ racl k (Set.range ![x + x * a, y, a]) := by
    have h1 : 1 + a ∈ racl k (Set.range ![x + x * a, y, a]) := add_mem (one_mem _) (hr' 2)
    have h := mul_mem (hr' 0) (inv_mem h1)
    have key : (x + x * a) * (1 + a)⁻¹ = x := by
      rw [show x + x * a = x * (1 + a) by ring, mul_inv_cancel_right₀
          (AlgebraicIndependent.one_add_ne_zero_two hind)]
    simpa [key] using h
  have htri : AlgebraicIndependent k ![x + x * a, y, a] :=
    triple_of_left hind (add_mem (hr 0) (mul_mem (hr 0) (hr 2))) hx
  exact AlgebraicIndependent.pair_of_triple htri (i := 0) (j := 1) (by decide)

private theorem pair_xy_a : AlgebraicIndependent k ![x * y, a] :=
  AlgebraicIndependent.pair_of_triple (algebraicIndependent_mul_left hind)
    (i := 0) (j := 2) (by decide)

private theorem pair_zmul_a {κ : k} (hκ : κ ≠ 0) :
    AlgebraicIndependent k ![algebraMap k K κ * x * y, a] := by
  rw [mul_assoc]
  exact AlgebraicIndependent.smul_left (pair_xy_a hind) hκ

/-- **The κ-family satisfies the blueprint multiplication graph**: for every
`κ ∈ kˣ`, `JMul(j(x,a), j(y,a), j(κxy, a))`. -/
theorem blueprintJMul_kappa [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {κ : k} (hκ : κ ≠ 0) :
    BlueprintJMul (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
      (jTupleOf (algebraMap k K κ * x * y) a (pair_zmul_a hind hκ)) := by
  have hxy : AlgebraicIndependent k ![x, y] :=
    AlgebraicIndependent.pair_of_triple hind (i := 0) (j := 1) (by decide)
  have hpt : ∀ z : K, point k z = point k (algebraMap k K κ * z) := fun z ↦
    (point_algebraMap_mul hκ z).symm
  have hrank : PointTripleIndependent (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind) 0)
      (jTupleOf y a (AlgebraicIndependent.pair_one_two hind) 0)
          (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind) 4) := by
    unfold PointTripleIndependent
    rw [jTupleOf_zero, jTupleOf_zero, jTupleOf_four]
    exact rankEq_three_points hind rfl
  refine ⟨jTupleOf_four_eq _ _, jTupleOf_four_eq _ _, hrank, ?_, ?_, ?_, ?_⟩
  · exact mulPoint_of_indep htr (AlgebraicIndependent.smul_left hxy hκ)
      ((jTupleOf_zero _).trans (hpt x)) (jTupleOf_zero _) (jTupleOf_zero _)
  · exact sumPoint_of_indep htr (pair_zmul_a hind hκ) (jTupleOf_zero _) (jTupleOf_four _)
      (jTupleOf_one _)
  · refine mulPoint_of_indep htr (AlgebraicIndependent.smul_left (pair_xa_y hind) hκ)
      ((jTupleOf_two _).trans (hpt _)) (jTupleOf_zero _) ((jTupleOf_two _).trans ?_)
    congr 1
    ring
  · refine mulPoint_of_indep htr (AlgebraicIndependent.smul_left (pair_x1a_y hind) hκ)
      ((jTupleOf_three _).trans (hpt _)) (jTupleOf_zero _) ((jTupleOf_three _).trans ?_)
    congr 1
    ring

/-- **The blueprint multiplication graph is not functional** (issue #23):
for `κ ∉ {0, 1}`, both `j(xy, a)` and `j(κxy, a)` are `JMul`-outputs of
`(j(x,a), j(y,a))`, and they are distinct. -/
theorem blueprintJMul_not_functional [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {κ : k} (hκ : κ ≠ 0) (hκ1 : κ ≠ 1) :
    BlueprintJMul (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K κ * x * y) a (pair_zmul_a hind hκ)) ∧
      BlueprintJMul (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
          (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K 1 * x * y) a (pair_zmul_a hind one_ne_zero)) ∧
      jTupleOf (algebraMap k K κ * x * y) a (pair_zmul_a hind hκ) ≠
        jTupleOf (algebraMap k K 1 * x * y) a (pair_zmul_a hind one_ne_zero) := by
  refine ⟨blueprintJMul_kappa hind htr hκ, blueprintJMul_kappa hind htr one_ne_zero, ?_⟩
  intro h
  have h1 := congrArg (fun t ↦ (t 1).1) h
  simp only [jTupleOf_one] at h1
  have hxy0 : x * y ∉ racl k (∅ : Set K) := fun hm ↦
    AlgebraicIndependent.notMem_racl_pair' (pair_xy_a hind) (racl_mono (Set.empty_subset _) hm)
  refine point_ne_of_sub (sub_ne_zero.2 hκ1) (r := x * y) ?_ hxy0 ?_ h1
  · rw [map_sub, map_one]
    ring
  · rw [show algebraMap k K 1 * x * y + a - x * y = a by rw [map_one]; ring]
    exact AlgebraicIndependent.notMem_racl_pair (pair_xy_a hind)

end Counterexamples

section Existence

/-- Rank at least five supplies an independent triple. -/
theorem exists_algebraicIndependent_triple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∃ x y a : K, AlgebraicIndependent k ![x, y, a] := by
  classical
  have hfresh := fresh_four_of_five_le_trdeg htr
  obtain ⟨x, hx⟩ := hfresh ∅ (by simp)
  obtain ⟨y, hy⟩ := hfresh {x} (by simp)
  have hx' : x ∉ racl k ({y} : Set K) := by
    intro h
    have := racl_exchange (S := (∅ : Set K)) (by simpa using h) (by simpa using hx)
    exact hy (by simpa using this)
  have hxy : AlgebraicIndependent k ![x, y] := algebraicIndependent_pair hx' (by simpa using hy)
  obtain ⟨a, ha⟩ := hfresh {x, y} ((Finset.card_le_two).trans (by norm_num))
  have hsnoc := algebraicIndependent_snoc hxy (z := a) (by
    rw [range_pair]; simpa using ha)
  refine ⟨x, y, a, ?_⟩
  convert hsnoc using 1
  funext i
  fin_cases i <;> rfl

variable [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)

include htr

/-- **Blueprint Lemma `generic-arithmetic` fails for addition**: over a base
field with an element `κ ∉ {0, 1}` and rank at least five, two distinct
semantic `j`-tuples with the same parameter point are `JAdd`-outputs of the
same pair of inputs. -/
theorem blueprintJAdd_not_functional' :
    ∃ u v w₁ w₂ : Fin 5 → Point k K, JSem u ∧ JSem v ∧ JSem w₁ ∧ JSem w₂ ∧
      w₁ 4 = w₂ 4 ∧ BlueprintJAdd u v w₁ ∧ BlueprintJAdd u v w₂ ∧ w₁ ≠ w₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  obtain ⟨h1, h2, h3⟩ := blueprintJAdd_not_functional hind htr hκ.1 hκ.2
  exact ⟨_, _, _, _, jSem_jTupleOf _, jSem_jTupleOf _, jSem_jTupleOf _, jSem_jTupleOf _,
    jTupleOf_four_eq _ _, h1, h2, h3⟩

/-- **Blueprint Lemma `generic-arithmetic` fails for multiplication**, in the
same sense as `blueprintJAdd_not_functional'`. -/
theorem blueprintJMul_not_functional' :
    ∃ u v w₁ w₂ : Fin 5 → Point k K, JSem u ∧ JSem v ∧ JSem w₁ ∧ JSem w₂ ∧
      w₁ 4 = w₂ 4 ∧ BlueprintJMul u v w₁ ∧ BlueprintJMul u v w₂ ∧ w₁ ≠ w₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  obtain ⟨h1, h2, h3⟩ := blueprintJMul_not_functional hind htr hκ.1 hκ.2
  exact ⟨_, _, _, _, jSem_jTupleOf _, jSem_jTupleOf _, jSem_jTupleOf _, jSem_jTupleOf _,
    jTupleOf_four_eq _ _, h1, h2, h3⟩

end Existence

section FrobeniusClass

/-! The blueprint defines its graphs on one Frobenius class `J₁`.  The tuples
used above lie in a single `FrobEq` class: any two `j`-tuples with the same
parameter and independent first coordinates are directly linked by the
multiplier point `[x/y]`, and a fresh `j(t, a)` bridges any two of them. -/

variable [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)

include htr

/-- **The blueprint addition graph is not functional on one Frobenius
class**: there are `u, v, w₁, w₂` all Frobenius-equivalent to `u` (so in the
class `J₁ = [u]`) with `JAdd(u, v, w₁)`, `JAdd(u, v, w₂)` and `w₁ ≠ w₂`. -/
theorem blueprintJAdd_not_functional_on_class :
    ∃ u v w₁ w₂ : Fin 5 → Point k K, FrobEq u u ∧ FrobEq u v ∧ FrobEq u w₁ ∧
      FrobEq u w₂ ∧ BlueprintJAdd u v w₁ ∧ BlueprintJAdd u v w₂ ∧ w₁ ≠ w₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  simp only [Finset.coe_insert, Finset.coe_singleton] at ht
  have hsub : ∀ {p : K}, p ∈ racl k ({x, y, a} : Set K) →
      ∀ {q : K}, q ∈ racl k ({x, y, a} : Set K) → t ∉ racl k ({p, q} : Set K) :=
    fun hp _ hq hm ↦ ht (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hp
      · exact hq) hm)
  have hmem : ∀ {w : K}, w ∈ ({x, y, a} : Set K) → w ∈ racl k ({x, y, a} : Set K) :=
    fun hw ↦ subset_racl k _ hw
  have hx := hmem (Set.mem_insert x _)
  have hy := hmem (Set.mem_insert_of_mem x (Set.mem_insert y _))
  have ha := hmem (Set.mem_insert_of_mem x (Set.mem_insert_of_mem y rfl))
  have hz : ∀ c : k, algebraMap k K c * x + y ∈ racl k ({x, y, a} : Set K) := fun c ↦
    add_mem (mul_mem (IntermediateField.algebraMap_mem _ c) hx) hy
  -- The bridge triples.
  have hxt : AlgebraicIndependent k ![x, t, a] :=
    AlgebraicIndependent.insert_middle (AlgebraicIndependent.pair_zero_two hind) (hsub hx ha)
  have htx : AlgebraicIndependent k ![t, x, a] :=
    AlgebraicIndependent.insert_left (AlgebraicIndependent.pair_zero_two hind) (hsub hx ha)
  have hty : AlgebraicIndependent k ![t, y, a] :=
    AlgebraicIndependent.insert_left (AlgebraicIndependent.pair_one_two hind) (hsub hy ha)
  have htz : ∀ {c : k} (hc : c ≠ 0),
      AlgebraicIndependent k ![t, algebraMap k K c * x + y, a] := fun hc ↦
    AlgebraicIndependent.insert_left (pair_za hind hc) (hsub (hz _) ha)
  obtain ⟨h1, h2, h3⟩ := blueprintJAdd_not_functional hind htr hκ.1 hκ.2
  exact ⟨_, _, _, _, frobEq_jTupleOf htr hxt htx, frobEq_jTupleOf htr hxt hty,
    frobEq_jTupleOf htr hxt (htz hκ.1), frobEq_jTupleOf htr hxt (htz one_ne_zero),
    h1, h2, h3⟩

/-- **The blueprint multiplication graph is not functional on one Frobenius
class**, in the same sense as `blueprintJAdd_not_functional_on_class`. -/
theorem blueprintJMul_not_functional_on_class :
    ∃ u v w₁ w₂ : Fin 5 → Point k K, FrobEq u u ∧ FrobEq u v ∧ FrobEq u w₁ ∧
      FrobEq u w₂ ∧ BlueprintJMul u v w₁ ∧ BlueprintJMul u v w₂ ∧ w₁ ≠ w₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  simp only [Finset.coe_insert, Finset.coe_singleton] at ht
  have hsub : ∀ {p : K}, p ∈ racl k ({x, y, a} : Set K) →
      ∀ {q : K}, q ∈ racl k ({x, y, a} : Set K) → t ∉ racl k ({p, q} : Set K) :=
    fun hp _ hq hm ↦ ht (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hp
      · exact hq) hm)
  have hmem : ∀ {w : K}, w ∈ ({x, y, a} : Set K) → w ∈ racl k ({x, y, a} : Set K) :=
    fun hw ↦ subset_racl k _ hw
  have hx := hmem (Set.mem_insert x _)
  have hy := hmem (Set.mem_insert_of_mem x (Set.mem_insert y _))
  have ha := hmem (Set.mem_insert_of_mem x (Set.mem_insert_of_mem y rfl))
  have hz : ∀ c : k, algebraMap k K c * x * y ∈ racl k ({x, y, a} : Set K) := fun c ↦
    mul_mem (mul_mem (IntermediateField.algebraMap_mem _ c) hx) hy
  have hxt : AlgebraicIndependent k ![x, t, a] :=
    AlgebraicIndependent.insert_middle (AlgebraicIndependent.pair_zero_two hind) (hsub hx ha)
  have htx : AlgebraicIndependent k ![t, x, a] :=
    AlgebraicIndependent.insert_left (AlgebraicIndependent.pair_zero_two hind) (hsub hx ha)
  have hty : AlgebraicIndependent k ![t, y, a] :=
    AlgebraicIndependent.insert_left (AlgebraicIndependent.pair_one_two hind) (hsub hy ha)
  have htz : ∀ {c : k} (hc : c ≠ 0),
      AlgebraicIndependent k ![t, algebraMap k K c * x * y, a] := fun hc ↦
    AlgebraicIndependent.insert_left (pair_zmul_a hind hc) (hsub (hz _) ha)
  obtain ⟨h1, h2, h3⟩ := blueprintJMul_not_functional hind htr hκ.1 hκ.2
  exact ⟨_, _, _, _, frobEq_jTupleOf htr hxt htx, frobEq_jTupleOf htr hxt hty,
    frobEq_jTupleOf htr hxt (htz hκ.1), frobEq_jTupleOf htr hxt (htz one_ne_zero),
    h1, h2, h3⟩

/-- **The blueprint ratio equivalence does not decode to ratios**: there are
`j`-tuples `j(x,a), j(y,a), j(κx,a)` in one Frobenius class `J₁ = [j(x,a)]`
with `RatioEq((j(x,a), j(y,a)), (j(κx,a), j(y,a)))`, although the decoded
ratios `x/y` and `κx/y` differ.  The witnesses are `c₁ = c₂ = j(t,a)`,
`d₁ = j(xt,a)`, `d₂ = j(yt,a)` for a fresh `t`; the third product uses the
`κ⁻¹`-member of the multiplication family. -/
theorem blueprintRatioEq_counterexample :
    ∃ (x y a : K) (κ : k) (hx : AlgebraicIndependent k ![x, a])
      (hy : AlgebraicIndependent k ![y, a])
      (hκx : AlgebraicIndependent k ![algebraMap k K κ * x, a]),
      FrobEq (jTupleOf x a hx) (jTupleOf x a hx) ∧
        FrobEq (jTupleOf x a hx) (jTupleOf y a hy) ∧
        FrobEq (jTupleOf x a hx) (jTupleOf (algebraMap k K κ * x) a hκx) ∧
        BlueprintRatioEq (jTupleOf x a hx) (jTupleOf x a hx, jTupleOf y a hy)
          (jTupleOf (algebraMap k K κ * x) a hκx, jTupleOf y a hy) ∧
        x / y ≠ algebraMap k K κ * x / y := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  have hx0 : x ≠ 0 := fun h0 ↦ hind.transcendental 0 (by
    change IsAlgebraic k x
    rw [h0]
    exact isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h0 ↦ hind.transcendental 1 (by
    change IsAlgebraic k y
    rw [h0]
    exact isAlgebraic_zero)
  -- Two fresh elements: `t` for the multipliers, `t'` for the class bridges.
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  simp only [Finset.coe_insert, Finset.coe_singleton] at ht
  obtain ⟨t', ht'⟩ := fresh_four_of_five_le_trdeg htr {x, y, a, t}
    ((Finset.card_insert_le _ _).trans (by
      have := Finset.card_le_three (a := y) (b := a) (c := t)
      omega))
  simp only [Finset.coe_insert, Finset.coe_singleton] at ht'
  set S : Set K := {x, y, a, t} with hS
  have hmemS : ∀ {w : K}, w ∈ S → w ∈ racl k S := fun hw ↦ subset_racl k _ hw
  have hxS : x ∈ racl k S := hmemS (by simp [hS])
  have hyS : y ∈ racl k S := hmemS (by simp [hS])
  have haS : a ∈ racl k S := hmemS (by simp [hS])
  have htS : t ∈ racl k S := hmemS (by simp [hS])
  have hfresh' : ∀ {p q : K}, p ∈ racl k S → q ∈ racl k S → t' ∉ racl k ({p, q} : Set K) :=
    fun hp hq hm ↦ ht' (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hp
      · exact hq) hm)
  have hfresh : ∀ {p q : K}, p ∈ racl k ({x, y, a} : Set K) → q ∈ racl k ({x, y, a} : Set K) →
      t ∉ racl k ({p, q} : Set K) :=
    fun hp hq hm ↦ ht (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hp
      · exact hq) hm)
  have hx3 : x ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (by simp)
  have hy3 : y ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (by simp)
  have ha3 : a ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (by simp)
  have hκx3 : algebraMap k K κ * x ∈ racl k ({x, y, a} : Set K) :=
    mul_mem (IntermediateField.algebraMap_mem _ _) hx3
  -- Independent pairs and the multiplier triples `(p, t, a)`.
  have hxa : AlgebraicIndependent k ![x, a] := AlgebraicIndependent.pair_zero_two hind
  have hya : AlgebraicIndependent k ![y, a] := AlgebraicIndependent.pair_one_two hind
  have hκxa : AlgebraicIndependent k ![algebraMap k K κ * x, a] :=
    AlgebraicIndependent.smul_left hxa hκ.1
  have T₁ : AlgebraicIndependent k ![x, t, a] :=
    AlgebraicIndependent.insert_middle hxa (hfresh hx3 ha3)
  have T₂ : AlgebraicIndependent k ![y, t, a] :=
    AlgebraicIndependent.insert_middle hya (hfresh hy3 ha3)
  have T₃ : AlgebraicIndependent k ![algebraMap k K κ * x, t, a] :=
    AlgebraicIndependent.insert_middle hκxa (hfresh hκx3 ha3)
  -- The four blueprint products.
  have M₁ := blueprintJMul_kappa T₁ htr one_ne_zero
  have M₂ := blueprintJMul_kappa T₂ htr one_ne_zero
  have M₃ := blueprintJMul_kappa T₃ htr (inv_ne_zero hκ.1)
  have hd₁ : jTupleOf (algebraMap k K κ⁻¹ * (algebraMap k K κ * x) * t) a
        (pair_zmul_a T₃ (inv_ne_zero hκ.1)) =
      jTupleOf (algebraMap k K 1 * x * t) a (pair_zmul_a T₁ one_ne_zero) := by
    refine jTupleOf_congr _ _ ?_
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ.1]
  rw [hd₁] at M₃
  -- Class membership through the bridge `j(t', a)`.
  have bridge : ∀ {p : K} (hp : p ∈ racl k S) (hpa : AlgebraicIndependent k ![p, a]),
      AlgebraicIndependent k ![t', p, a] := fun hp hpa ↦
    AlgebraicIndependent.insert_left hpa (hfresh' hp haS)
  have hxt' : AlgebraicIndependent k ![x, t', a] :=
    AlgebraicIndependent.insert_middle hxa (hfresh' hxS haS)
  have hxtS : algebraMap k K 1 * x * t ∈ racl k S :=
    mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hxS) htS
  have hytS : algebraMap k K 1 * y * t ∈ racl k S :=
    mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hyS) htS
  have hκxS : algebraMap k K κ * x ∈ racl k S :=
    mul_mem (IntermediateField.algebraMap_mem _ _) hxS
  refine ⟨x, y, a, κ, hxa, hya, hκxa,
    frobEq_jTupleOf htr hxt' (bridge hxS hxa),
    frobEq_jTupleOf htr hxt' (bridge hyS hya),
    frobEq_jTupleOf htr hxt' (bridge hκxS hκxa), ?_, ?_⟩
  · exact ⟨_, _, _, _,
      frobEq_jTupleOf htr hxt' (bridge htS (AlgebraicIndependent.pair_one_two T₁)),
      frobEq_jTupleOf htr hxt' (bridge htS (AlgebraicIndependent.pair_one_two T₁)),
      frobEq_jTupleOf htr hxt' (bridge hxtS (pair_zmul_a T₁ one_ne_zero)),
      frobEq_jTupleOf htr hxt' (bridge hytS (pair_zmul_a T₂ one_ne_zero)),
      M₁, M₂, M₃, M₂⟩
  · intro h
    apply hκ.2
    have h' : x = algebraMap k K κ * x := (div_left_inj' hy0).1 h
    have h1 : algebraMap k K κ = 1 :=
      mul_right_cancel₀ hx0 (h'.symm.trans (one_mul x).symm)
    exact (algebraMap k K).injective (h1.trans (map_one _).symm)

end FrobeniusClass

end

end AclGeom
