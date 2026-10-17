/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.BlueprintTotalGraphs
import AclGeom.Counterexamples.RatioConverse
import AclGeom.Counterexamples.TotalNonzeroExistence
import AclGeom.Interpretation.ClassCoordinates
import AclGeom.Transfer.JCorrectness

/-!
# The literal addition graph is total and satisfies the corrected reverse sum laws

Blueprint Thm `total-field-graphs` asserts that the geometric addition graph is total and
satisfies `AddGraph(r, s, t) ↔ decode(t) = decode(r) + decode(s)`.  For the literal recipe
`BlueprintRatioAddGraph` the forward direction fails (`blueprintRatioAddGraph_wrong_sum`), and the
literal relation cannot provide the advertised setoid or decoder.  This module proves the true
components.

* `blueprintRatioAddGraph_of_add_ratio_eq_zero` and `blueprintRatioAddGraph_of_add_ratio`: the
  representative-level reverse laws, a correction of the invalid quotient claim for NONZERO
  inputs.  For semantic class pairs `r = (j(p, a), j(q, a))` and `s = (j(p', a), j(q', a))`, a
  zero sum `p/q + p'/q' = 0` gives the output zero, and a semantic output
  `t = (j(p'', a), j(q'', a))` with `p''/q'' = p/q + p'/q'` is an output.  Both hold over
  arbitrary fields at rank five.  At a zero input the raw graph uses equality of
  representatives, and the reverse law fails (`blueprintRatioAddGraph_zero_reverse_counterexample`).
* `blueprintRatioAddGraph_total`: the literal graph is total on the class of a semantic base
  tuple, over perfect ambient fields at rank five.

The proof follows the source.  With `c = p/q` and `d = p'/q'`, a common denominator `e` outside
`acl_k(a, c, d)` gives the replacements `(j(ce, a), j(e, a))` and `(j(de, a), j(e, a))`, related to
the inputs by the converse of the literal ratio semantics (`blueprintRatioEq_of_mul_eq`).  If
`c + d = 0` the numerators are literal negatives (`blueprintJNeg_smul`, at the scalar `-1`).
Otherwise the total nonzero addition of the numerators has the output `j(ce + de, a)`
(`blueprintJAddTotalNZ_of_pairs`), compared with the output again by the converse.  For totality
the class members are normalized to semantic tuples, and a nonzero sum uses the output
`(j((c + d)e', a), j(e', a))` with `e'` outside `acl_k(a, c + d)`.  Each fresh choice is local,
within the rank-five bound.

These results assert no functionality, quotient operation, decoder or field structure.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the reverse sum laws (nonzero inputs) and totality of the literal addition graph are
proved (#8, #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A common denominator for two semantic class pairs: for `c = p/q`, `d = p'/q'` and `e`
outside `acl_k(a, c, d)`, the pairs `(j(ce), j(e))` and `(j(de), j(e))` are related to the inputs
by the literal ratio relation. -/
private theorem exists_common_denominator (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a p q p' q' : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hp : AlgebraicIndependent k ![p, a]) (hq : AlgebraicIndependent k ![q, a])
    (hp' : AlgebraicIndependent k ![p', a]) (hq' : AlgebraicIndependent k ![q', a])
    (r s : {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})
    (hr : (r.1.1, r.2.1) = (jTupleOf p a hp, jTupleOf q a hq))
    (hs : (s.1.1, s.2.1) = (jTupleOf p' a hp', jTupleOf q' a hq')) :
    ∃ (e : K) (he : AlgebraicIndependent k ![e, a])
      (hce : AlgebraicIndependent k ![p / q * e, a])
      (hde : AlgebraicIndependent k ![p' / q' * e, a]),
      e ∉ racl k ({a, p / q, p' / q'} : Set K) ∧
      BlueprintRatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1)
        (jTupleOf (p / q * e) a hce, jTupleOf e a he) ∧
      BlueprintRatioEq (jTupleOf x₀ a h₀) (s.1.1, s.2.1)
        (jTupleOf (p' / q' * e) a hde, jTupleOf e a he) := by
  classical
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  obtain ⟨e, he⟩ := fresh_four_of_five_le_trdeg htr {a, p / q, p' / q'}
    (Finset.card_le_three.trans (by norm_num))
  have he' : e ∉ racl k ({a, p / q, p' / q'} : Set K) := by simpa using he
  have hmono : racl k ({a} : Set K) ≤ racl k ({a, p / q, p' / q'} : Set K) :=
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hcF : p / q ∈ racl k ({a, p / q, p' / q'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hdF : p' / q' ∈ racl k ({a, p / q, p' / q'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hea : AlgebraicIndependent k ![e, a] := pair_of_notMem h₀ fun hm ↦ he' (hmono hm)
  have hmul : ∀ {c : K}, c ∈ racl k ({a, p / q, p' / q'} : Set K) → c ≠ 0 →
      AlgebraicIndependent k ![c * e, a] := fun {c} hcm hc0 ↦ pair_of_notMem h₀ fun hm ↦ he' (by
    have h' := div_mem (hmono hm) hcm
    rwa [mul_div_cancel_left₀ e hc0] at h')
  have hce := hmul hcF (div_ne_zero (hne hp) hq0)
  have hde := hmul hdF (div_ne_zero (hne hp') hq'0)
  refine ⟨e, hea, hce, hde, he', ?_, ?_⟩
  · rw [hr]
    exact blueprintRatioEq_of_mul_eq htr h₀ hp hq hce hea
      (by linear_combination (-e) * div_mul_cancel₀ p hq0)
  · rw [hs]
    exact blueprintRatioEq_of_mul_eq htr h₀ hp' hq' hde hea
      (by linear_combination (-e) * div_mul_cancel₀ p' hq'0)

/-- **The reverse sum law at a zero sum** (blueprint Thm `total-field-graphs`, addition, reverse
direction; a representative-level correction of the invalid quotient statement, for nonzero
inputs).  Semantic class pairs `r = (j(p, a), j(q, a))` and `s = (j(p', a), j(q', a))` in the
Frobenius class of `j(x₀, a)` with `p/q + p'/q' = 0` satisfy `BlueprintRatioAddGraph r s 0`, at
rank five over arbitrary fields. -/
theorem blueprintRatioAddGraph_of_add_ratio_eq_zero (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a p q p' q' : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hp : AlgebraicIndependent k ![p, a]) (hq : AlgebraicIndependent k ![q, a])
    (hp' : AlgebraicIndependent k ![p', a]) (hq' : AlgebraicIndependent k ![q', a])
    (r s : {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})
    (hr : (r.1.1, r.2.1) = (jTupleOf p a hp, jTupleOf q a hq))
    (hs : (s.1.1, s.2.1) = (jTupleOf p' a hp', jTupleOf q' a hq'))
    (h : p * q' + p' * q = 0) :
    BlueprintRatioAddGraph (jTupleOf x₀ a h₀) (some r) (some s) none := by
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  obtain ⟨e, he, hce, hde, -, R₁, R₂⟩ := exists_common_denominator htr h₀ hp hq hp' hq' r s hr hs
  have hm1 : (-1 : k) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- The numerators are literal negatives: `de = (-1) · ce`.
  have hsum : p / q + p' / q' = 0 := by
    rw [div_add_div _ _ hq0 hq'0, div_eq_zero_iff]
    exact Or.inl (by linear_combination h)
  have hdc : algebraMap k K (-1) * (p / q * e) = p' / q' * e := by
    rw [map_neg, map_one]
    linear_combination (-e) * hsum
  have N := blueprintJNeg_smul htr h₀ hce hm1
  rw [jTupleOf_congr (AlgebraicIndependent.smul_left hce hm1) hde hdc] at N
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x₀ a h₀) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr h₀ hw
  exact Or.inr (Or.inr ⟨r, s, rfl, rfl, ⟨_, hJ _ hce⟩, ⟨_, hJ _ hde⟩, ⟨_, hJ _ he⟩, R₁, R₂,
    Or.inl ⟨N, rfl⟩⟩)

/-- **The reverse sum law** (blueprint Thm `total-field-graphs`, addition, reverse direction; a
representative-level correction of the invalid quotient statement, for nonzero inputs).
Semantic class pairs `r = (j(p, a), j(q, a))`, `s = (j(p', a), j(q', a))` and
`t = (j(p'', a), j(q'', a))` in the Frobenius class of `j(x₀, a)` with
`p''/q'' = p/q + p'/q'` satisfy `BlueprintRatioAddGraph r s t`, at rank five over arbitrary
fields.  The sum is nonzero because the output is semantic. -/
theorem blueprintRatioAddGraph_of_add_ratio (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a p q p' q' p'' q'' : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hp : AlgebraicIndependent k ![p, a]) (hq : AlgebraicIndependent k ![q, a])
    (hp' : AlgebraicIndependent k ![p', a]) (hq' : AlgebraicIndependent k ![q', a])
    (hp'' : AlgebraicIndependent k ![p'', a]) (hq'' : AlgebraicIndependent k ![q'', a])
    (r s t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})
    (hr : (r.1.1, r.2.1) = (jTupleOf p a hp, jTupleOf q a hq))
    (hs : (s.1.1, s.2.1) = (jTupleOf p' a hp', jTupleOf q' a hq'))
    (ht : (t.1.1, t.2.1) = (jTupleOf p'' a hp'', jTupleOf q'' a hq''))
    (h : p'' * (q * q') = q'' * (p * q' + p' * q)) :
    BlueprintRatioAddGraph (jTupleOf x₀ a h₀) (some r) (some s) (some t) := by
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  obtain ⟨e, he, hce, hde, he', R₁, R₂⟩ := exists_common_denominator htr h₀ hp hq hp' hq' r s hr hs
  -- The sum is nonzero, since otherwise the semantic output numerator would vanish.
  have hsum : p / q + p' / q' ≠ 0 := fun h0 ↦ by
    rw [div_add_div _ _ hq0 hq'0, div_eq_zero_iff] at h0
    have hS : p * q' + p' * q = 0 := by
      linear_combination h0.resolve_right (mul_ne_zero hq0 hq'0)
    rw [hS, mul_zero] at h
    exact hne hp'' ((mul_eq_zero.1 h).resolve_right (mul_ne_zero hq0 hq'0))
  have hcF : p / q ∈ racl k ({a, p / q, p' / q'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hdF : p' / q' ∈ racl k ({a, p / q, p' / q'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcde : AlgebraicIndependent k ![p / q * e + p' / q' * e, a] := pair_of_notMem h₀ fun hm ↦
    he' (by
      have h' := div_mem (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
        (add_mem hcF hdF)
      rwa [← add_mul, mul_div_cancel_left₀ e hsum] at h')
  -- The total nonzero sum of the numerators and the output comparison.
  have A := blueprintJAddTotalNZ_of_pairs htr h₀ hce hde hcde
  have hval : (p / q + p' / q') * q'' = p'' :=
    mul_right_cancel₀ (mul_ne_zero hq0 hq'0) (by
      linear_combination (q' * q'') * div_mul_cancel₀ p hq0 + (q * q'') * div_mul_cancel₀ p' hq'0
        - h)
  have R₃ : BlueprintRatioEq (jTupleOf x₀ a h₀)
      (jTupleOf (p / q * e + p' / q' * e) a hcde, jTupleOf e a he) (t.1.1, t.2.1) := by
    rw [ht]
    exact blueprintRatioEq_of_mul_eq htr h₀ hcde he hp'' hq'' (by linear_combination e * hval)
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x₀ a h₀) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr h₀ hw
  exact Or.inr (Or.inr ⟨r, s, rfl, rfl, ⟨_, hJ _ hce⟩, ⟨_, hJ _ hde⟩, ⟨_, hJ _ he⟩, R₁, R₂,
    Or.inr ⟨⟨_, hJ _ hcde⟩, t, rfl, A, R₃⟩⟩)

/-- **The literal addition graph is total** (blueprint Thm `total-field-graphs`, addition,
totality) on the Frobenius class of a semantic base tuple `j(x₀, a)`, over perfect ambient fields
at rank five.  Completeness and the characteristic exponent are supplied internally. -/
theorem blueprintRatioAddGraph_total [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (r s : Option ({u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})) :
    ∃ t, BlueprintRatioAddGraph (jTupleOf x₀ a h₀) r s t := by
  classical
  rcases r with _ | r
  · exact ⟨s, Or.inl ⟨rfl, rfl⟩⟩
  rcases s with _ | s
  · exact ⟨some r, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  -- Normalize the four class members to semantic tuples `j(p), j(q), j(p'), j(q')`.
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K)))
      (AlgebraicClosure K) := jCompletenessACF (five_le_trdeg_algebraicClosure htr)
  have hnorm := fun {w : Fin 5 → Point k K} (hw : FrobEq (jTupleOf x₀ a h₀) w) ↦
    (frobEq_jTupleOf_iff (ringExpChar K) htr hcomp h₀).1 hw
  obtain ⟨p, hp, hpe⟩ := hnorm r.1.2
  obtain ⟨q, hq, hqe⟩ := hnorm r.2.2
  obtain ⟨p', hp', hp'e⟩ := hnorm s.1.2
  obtain ⟨q', hq', hq'e⟩ := hnorm s.2.2
  by_cases hS : p * q' + p' * q = 0
  · exact ⟨none, blueprintRatioAddGraph_of_add_ratio_eq_zero htr h₀ hp hq hp' hq' r s
      (Prod.ext hpe hqe) (Prod.ext hp'e hq'e) hS⟩
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  have hsum : p / q + p' / q' ≠ 0 := by
    rw [div_add_div _ _ hq0 hq'0]
    exact div_ne_zero (fun h0 ↦ hS (by linear_combination h0)) (mul_ne_zero hq0 hq'0)
  -- The output `(j((c + d)e'), j(e'))` with a fresh denominator `e'` over `{a, c + d}`.
  obtain ⟨e, he⟩ := fresh_four_of_five_le_trdeg htr {a, p / q + p' / q'}
    (Finset.card_le_two.trans (by norm_num))
  have he' : e ∉ racl k ({a, p / q + p' / q'} : Set K) := by simpa using he
  have hea : AlgebraicIndependent k ![e, a] := pair_of_notMem h₀ fun hm ↦ he' (racl_mono
    (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
  have hcdea : AlgebraicIndependent k ![(p / q + p' / q') * e, a] := pair_of_notMem h₀ fun hm ↦
    he' (by
      have h' := div_mem (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
        (subset_racl k ({a, p / q + p' / q'} : Set K)
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      rwa [mul_div_cancel_left₀ e hsum] at h')
  refine ⟨some (⟨_, frobEq_jTupleOf_of_common htr h₀ hcdea⟩,
    ⟨_, frobEq_jTupleOf_of_common htr h₀ hea⟩), ?_⟩
  exact blueprintRatioAddGraph_of_add_ratio htr h₀ hp hq hp' hq' hcdea hea r s _
    (Prod.ext hpe hqe) (Prod.ext hp'e hq'e) rfl (by
      linear_combination (e * q') * div_mul_cancel₀ p hq0 + (e * q) * div_mul_cancel₀ p' hq'0)

end AclGeom
