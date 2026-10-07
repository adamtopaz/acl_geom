/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.JCoordinates
import AclGeom.Geometry.Representatives
import AclGeom.Interpretation.FrobClass

/-!
# Soundness of the Frobenius link on semantic `j`-tuples

Explicit geometric sum and product points from independent representatives (`sumPoint_of_indep`,
`mulPoint_of_indep`), and the semantic witnesses of the Frobenius class.

* `isJTuple_jTupleOf` puts `j(x, a)` on the geometric `J`-locus.
* `directFrobLink_jTupleOf` links tuples with a common parameter, through the multiplier `[x/y]`.
* `frobEq_jTupleOf` bridges them by a given `j(t, a)`.

These are extracted from `AclGeom.Counterexamples.GenericArithmetic`, which now imports this
module. Superseded private independence helpers use the representative-calculus API.

New here is the converse of blueprint Lemma `frobeq-correct`. Tuples with a common parameter are
Frobenius-equivalent through a fresh bridge (`frobEq_jTupleOf_of_common`). Tuples whose parameters
are Frobenius twists are Frobenius-equivalent (`frobEq_of_frobenius_twist`): the tuple with the
smaller parameter is raised to the common parameter by `jTupleOf_pow_expChar_pow`, a positive power
only.

Only soundness of `Q′` and `J` is used, never completeness. The wrappers use the rank-five
configuration soundness over arbitrary base fields (#24); no infinite-base hypothesis is needed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the displayed soundness statements are proved over arbitrary base fields. The reverse
implication is proved in `FrobEqForward` under an explicit semantic-bridge or ACF-completeness
hypothesis; unconditional bridge completeness remains open (#23).
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Witnesses

/-- A geometric sum point from an explicit independent pair of
representatives. -/
theorem sumPoint_of_indep (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {p q : K} (h : AlgebraicIndependent k ![p, q]) {U V W : Point k K}
    (hU : U.1 = point k p) (hV : V.1 = point k q) (hW : W.1 = point k (p + q)) :
    SumPoint U V W := by
  have hq0 : q ≠ 0 := fun h0 ↦ h.transcendental 1 (by
    change IsAlgebraic k q
    rw [h0]
    exact isAlgebraic_zero)
  have hpq : p / q ∉ (⊥ : ClosedIF k K) := by
    refine notMem_bot_of_mem_racl_pair (AlgebraicIndependent.notMem_racl_pair' h) ?_
    have := mul_mem (subset_racl k ({p / q, q} : Set K) (Set.mem_insert _ _))
      (subset_racl k ({p / q, q} : Set K) (Set.mem_insert_of_mem _ rfl))
    rwa [div_mul_cancel₀ p hq0] at this
  exact sumPoint_of_qSem_of_five_le_trdeg htr (R := Point.mk' k (p / q) hpq)
    ⟨p, q, h, hU, hV, hW, rfl⟩

/-- A geometric product point from an explicit independent pair of
representatives. -/
theorem mulPoint_of_indep (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {p q : K} (h : AlgebraicIndependent k ![p, q]) {U V W : Point k K}
    (hU : U.1 = point k p) (hV : V.1 = point k q) (hW : W.1 = point k (p * q)) :
    MulPoint U V W := by
  have hpq : p + q ∉ (⊥ : ClosedIF k K) := by
    refine notMem_bot_of_mem_racl_pair (AlgebraicIndependent.notMem_racl_pair' h) ?_
    simpa using sub_mem (subset_racl k ({p + q, q} : Set K) (Set.mem_insert _ _))
      (subset_racl k ({p + q, q} : Set K) (Set.mem_insert_of_mem _ rfl))
  exact mulPoint_of_q'Sem_of_five_le_trdeg htr (S := Point.mk' k (p + q) hpq)
    ⟨p, q, h, hU, hV, rfl, hW⟩

end Witnesses

section FrobeniusClass

variable (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)

include htr

/-- A semantic `j`-tuple lies on the geometric `J`-locus. -/
theorem isJTuple_jTupleOf {x a : K} (h : AlgebraicIndependent k ![x, a]) :
    IsJTuple (jTupleOf x a h) :=
  jGeom_of_jSem_of_five_le_trdeg htr (jSem_jTupleOf h)

/-- **Direct Frobenius links between tuples with a common parameter**: for
independent `x, y, a`, the multiplier point `[x/y]` links `j(x, a)` to
`j(y, a)`. -/
theorem directFrobLink_jTupleOf {x y a : K} (h : AlgebraicIndependent k ![x, y, a]) :
    DirectFrobLink (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) := by
  have hy0 : y ≠ 0 := fun h0 ↦ h.transcendental 1 (by
    change IsAlgebraic k y
    rw [h0]
    exact isAlgebraic_zero)
  have ha0 : a ≠ 0 := AlgebraicIndependent.ne_zero h 2
  have ha1 : 1 + a ≠ 0 := AlgebraicIndependent.one_add_ne_zero_two h
  have hr := fun i ↦ subset_racl k (Set.range ![x, y, a]) (Set.mem_range_self i)
  -- The three representative pairs `(x/y, y)`, `(x/y, ya)`, `(x/y, y(1+a))`.
  have hxy_in : x / y ∈ racl k (Set.range ![x, y, a]) := div_mem (hr 0) (hr 1)
  have T₁ : AlgebraicIndependent k ![x / y, y, a] := by
    refine AlgebraicIndependent.triple_of_mem h (fun i ↦ ?_) (fun i ↦ ?_)
    · fin_cases i
      · exact hxy_in
      · exact hr 1
      · exact hr 2
    · have hr' := fun i ↦ subset_racl k (Set.range ![x / y, y, a]) (Set.mem_range_self i)
      fin_cases i
      · simpa [div_mul_cancel₀ x hy0] using mul_mem (hr' 0) (hr' 1)
      · exact hr' 1
      · exact hr' 2
  have T₂ : AlgebraicIndependent k ![x / y, y * a, a] := by
    refine AlgebraicIndependent.triple_of_mem h (fun i ↦ ?_) (fun i ↦ ?_)
    · fin_cases i
      · exact hxy_in
      · exact mul_mem (hr 1) (hr 2)
      · exact hr 2
    · have hr' := fun i ↦ subset_racl k (Set.range ![x / y, y * a, a]) (Set.mem_range_self i)
      have hy : y ∈ racl k (Set.range ![x / y, y * a, a]) := by
        simpa [mul_div_cancel_right₀ y ha0] using div_mem (hr' 1) (hr' 2)
      fin_cases i
      · simpa [div_mul_cancel₀ x hy0] using mul_mem (hr' 0) hy
      · exact hy
      · exact hr' 2
  have T₃ : AlgebraicIndependent k ![x / y, y + y * a, a] := by
    refine AlgebraicIndependent.triple_of_mem h (fun i ↦ ?_) (fun i ↦ ?_)
    · fin_cases i
      · exact hxy_in
      · exact add_mem (hr 1) (mul_mem (hr 1) (hr 2))
      · exact hr 2
    · have hr' := fun i ↦
        subset_racl k (Set.range ![x / y, y + y * a, a]) (Set.mem_range_self i)
      have hy : y ∈ racl k (Set.range ![x / y, y + y * a, a]) := by
        have h1 : 1 + a ∈ racl k (Set.range ![x / y, y + y * a, a]) :=
          add_mem (one_mem _) (hr' 2)
        have key : (y + y * a) / (1 + a) = y := by
          rw [show y + y * a = y * (1 + a) by ring, mul_div_cancel_right₀ y ha1]
        simpa [key] using div_mem (hr' 1) h1
      fin_cases i
      · simpa [div_mul_cancel₀ x hy0] using mul_mem (hr' 0) hy
      · exact hy
      · exact hr' 2
  have P₁ : AlgebraicIndependent k ![x / y, y] :=
    AlgebraicIndependent.pair_of_triple T₁ (i := 0) (j := 1) (by decide)
  have P₂ : AlgebraicIndependent k ![x / y, y * a] :=
    AlgebraicIndependent.pair_of_triple T₂ (i := 0) (j := 1) (by decide)
  have P₃ : AlgebraicIndependent k ![x / y, y + y * a] :=
    AlgebraicIndependent.pair_of_triple T₃ (i := 0) (j := 1) (by decide)
  have hC : x / y ∉ (⊥ : ClosedIF k K) := fun hb ↦
    P₁.transcendental 0 (ClosedIF.mem_bot_iff.1 hb)
  refine ⟨isJTuple_jTupleOf htr _, isJTuple_jTupleOf htr _, jTupleOf_four_eq _ _, ?_,
    ⟨Point.mk' k (x / y) hC, ?_, ?_, ?_⟩⟩
  · unfold PointTripleIndependent
    rw [jTupleOf_zero, jTupleOf_zero, jTupleOf_four]
    exact rankEq_three_points h rfl
  · refine mulPoint_of_indep htr P₁ rfl (jTupleOf_zero _) ((jTupleOf_zero _).trans ?_)
    rw [div_mul_cancel₀ x hy0]
  · refine mulPoint_of_indep htr P₂ rfl (jTupleOf_two _) ((jTupleOf_two _).trans ?_)
    congr 1
    field_simp
  · refine mulPoint_of_indep htr P₃ rfl (jTupleOf_three _) ((jTupleOf_three _).trans ?_)
    congr 1
    field_simp

/-- **Frobenius equivalence of tuples with a common parameter**: a fresh
bridge `j(t, a)` joins `j(x, a)` and `j(y, a)` whenever `(x, t, a)` and
`(t, y, a)` are independent. -/
theorem frobEq_jTupleOf {x y t a : K} (hxt : AlgebraicIndependent k ![x, t, a])
    (hty : AlgebraicIndependent k ![t, y, a]) :
    FrobEq (jTupleOf x a (AlgebraicIndependent.pair_zero_two hxt))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hty)) :=
  ⟨jTupleOf t a (AlgebraicIndependent.pair_one_two hxt), isJTuple_jTupleOf htr _,
    Or.inl (directFrobLink_jTupleOf htr hxt), Or.inl (directFrobLink_jTupleOf htr hty)⟩

/-- **Common-parameter bridge**: two semantic `j`-tuples with the same literal parameter are
Frobenius-equivalent, through the bridge `j(t, a)` for a fresh `t`. -/
theorem frobEq_jTupleOf_of_common {x y a : K} (hx : AlgebraicIndependent k ![x, a])
    (hy : AlgebraicIndependent k ![y, a]) :
    FrobEq (jTupleOf x a hx) (jTupleOf y a hy) := by
  classical
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  have ht' : t ∉ racl k ({x, y, a} : Set K) := by simpa using ht
  have htx : t ∉ racl k ({x, a} : Set K) := fun h ↦ ht' (racl_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.2
      (Set.mem_insert_of_mem y (Set.mem_singleton a)))) h)
  have hty : t ∉ racl k ({y, a} : Set K) := fun h ↦ ht' (racl_mono (Set.subset_insert _ _) h)
  exact frobEq_jTupleOf htr (AlgebraicIndependent.insert_middle hx htx)
    (AlgebraicIndependent.insert_left hy hty)

/-- **Frobenius twists of the parameter give Frobenius-equivalent `j`-tuples** (the converse
direction of blueprint Lemma `frobeq-correct`).  The tuple with the smaller parameter is raised to
the common parameter by a positive power (`jTupleOf_pow_expChar_pow`), and the two are bridged by
`frobEq_jTupleOf_of_common`. -/
theorem frobEq_of_frobenius_twist (q : ℕ) [ExpChar k q] {u v : Fin 5 → Point k K}
    {x a y a' : K} (hxa : AlgebraicIndependent k ![x, a]) (hya : AlgebraicIndependent k ![y, a'])
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a')
    (htw : ∃ n : ℕ, a' = a ^ q ^ n ∨ a = a' ^ q ^ n) :
    FrobEq u v := by
  have : ExpChar K q := expChar_of_injective_algebraMap (algebraMap k K).injective q
  rw [eq_jTupleOf hxa hu, eq_jTupleOf hya hv]
  obtain ⟨n, rfl | rfl⟩ := htw
  · have hxa' := AlgebraicIndependent.pair_pow (pow_ne_zero n (expChar_pos K q).ne') hxa
    rw [← jTupleOf_pow_expChar_pow q n hxa hxa']
    exact frobEq_jTupleOf_of_common htr hxa' hya
  · have hya' := AlgebraicIndependent.pair_pow (pow_ne_zero n (expChar_pos K q).ne') hya
    rw [← jTupleOf_pow_expChar_pow q n hya hya']
    exact frobEq_jTupleOf_of_common htr hxa hya'

end FrobeniusClass

end

end AclGeom
