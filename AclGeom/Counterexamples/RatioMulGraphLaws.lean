/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.BlueprintTotalGraphs
import AclGeom.Counterexamples.RatioConverse
import AclGeom.Interpretation.ClassCoordinates
import AclGeom.Transfer.JCorrectness

/-!
# The literal multiplication graph is total and satisfies the reverse product law

Blueprint Thm `total-field-graphs` asserts that the geometric multiplication graph is total and
satisfies `MulGraph(r, s, t) ↔ decode(t) = decode(r) decode(s)`.  For the literal recipe
`BlueprintRatioMulGraph` the forward direction fails (`blueprintRatioMulGraph_wrong_product`), and
the literal relation cannot provide the advertised setoid or decoder.  This module proves the two
true components.

* `blueprintRatioMulGraph_of_mul_ratio`: the representative-level reverse law, a correction of the
  invalid quotient claim for NONZERO inputs.  If semantic class pairs `r = (j(p, a), j(q, a))`,
  `s = (j(p', a), j(q', a))` and `t = (j(p'', a), j(q'', a))` satisfy
  `p''/q'' = (p/q)(p'/q')`, then the literal graph relates `r, s` to `t`.  It holds over
  arbitrary fields at rank five, with no perfection or completeness hypothesis.
* `blueprintRatioMulGraph_total`: the literal graph is total on the class of a semantic base
  tuple, over perfect ambient fields at rank five.

The proof follows the source.  With `c = p/q` and `d = p'/q'`, choose `r'` outside
`acl_k(a, c, d)` and `s'` outside `acl_k(a, c, d, r')`, and replace the inputs by
`(j(cr', a), j(r', a))` and `(j(ds', a), j(s', a))`.  The numerators and the denominators have
generic literal products, and every replacement and output comparison is a literal ratio relation
between pairs of equal ratio (`blueprintRatioEq_of_mul_eq`).  For totality, the class members are
normalized to semantic tuples, and the output `(j(cde, a), j(e, a))` uses a denominator `e` outside
`acl_k(a, cd)`.  Each step chooses its fresh elements locally, within the rank-five bound.

These results assert no functionality, quotient operation, decoder or field structure.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the reverse product law (nonzero inputs) and totality of the literal multiplication
graph are proved (#8, #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The reverse product law for the literal multiplication graph** (blueprint Thm
`total-field-graphs`, multiplication, reverse direction; a representative-level correction of the
invalid quotient statement, for nonzero inputs).  Semantic class pairs `r = (j(p, a), j(q, a))`,
`s = (j(p', a), j(q', a))` and `t = (j(p'', a), j(q'', a))` in the Frobenius class of `j(x₀, a)`
with `p''/q'' = (p/q)(p'/q')` satisfy `BlueprintRatioMulGraph r s t`, at rank five over arbitrary
fields. -/
theorem blueprintRatioMulGraph_of_mul_ratio (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a p q p' q' p'' q'' : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hp : AlgebraicIndependent k ![p, a]) (hq : AlgebraicIndependent k ![q, a])
    (hp' : AlgebraicIndependent k ![p', a]) (hq' : AlgebraicIndependent k ![q', a])
    (hp'' : AlgebraicIndependent k ![p'', a]) (hq'' : AlgebraicIndependent k ![q'', a])
    (r s t : {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})
    (hr : (r.1.1, r.2.1) = (jTupleOf p a hp, jTupleOf q a hq))
    (hs : (s.1.1, s.2.1) = (jTupleOf p' a hp', jTupleOf q' a hq'))
    (ht : (t.1.1, t.2.1) = (jTupleOf p'' a hp'', jTupleOf q'' a hq''))
    (h : p'' * (q * q') = q'' * (p * p')) :
    BlueprintRatioMulGraph (jTupleOf x₀ a h₀) (some r) (some s) (some t) := by
  classical
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  have hc : p / q * q = p := div_mul_cancel₀ p hq0
  have hd : p' / q' * q' = p' := div_mul_cancel₀ p' hq'0
  have hc0 : p / q ≠ 0 := div_ne_zero (hne hp) hq0
  have hd0 : p' / q' ≠ 0 := div_ne_zero (hne hp') hq'0
  -- Successive fresh elements `r'` over `{a, c, d}` and `s'` over `{a, c, d, r'}`.
  obtain ⟨r', hr'⟩ := fresh_four_of_five_le_trdeg htr {a, p / q, p' / q'}
    (Finset.card_le_three.trans (by norm_num))
  have hr'' : r' ∉ racl k ({a, p / q, p' / q'} : Set K) := by simpa using hr'
  obtain ⟨s', hs'⟩ := fresh_four_of_five_le_trdeg htr {a, p / q, p' / q', r'} Finset.card_le_four
  have hs'' : s' ∉ racl k ({a, p / q, p' / q', r'} : Set K) := by simpa using hs'
  have hcF : p / q ∈ racl k ({a, p / q, p' / q', r'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hdF : p' / q' ∈ racl k ({a, p / q, p' / q', r'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hrF : r' ∈ racl k ({a, p / q, p' / q', r'} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have haF : a ∈ racl k ({a, p / q, p' / q', r'} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  -- The replacement tuples `j(cr'), j(r'), j(ds'), j(s')` and the two product triples.
  have hr'a : AlgebraicIndependent k ![r', a] := pair_of_notMem h₀ fun hm ↦ hr'' (racl_mono
    (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
  have hcra : AlgebraicIndependent k ![p / q * r', a] := pair_of_notMem h₀ fun hm ↦ hr'' (by
    have hm' := div_mem (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
      (subset_racl k ({a, p / q, p' / q'} : Set K) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    rwa [mul_div_cancel_left₀ r' hc0] at hm')
  have U₁ : AlgebraicIndependent k ![p / q * r', p' / q' * s', a] :=
    AlgebraicIndependent.insert_middle hcra fun hm ↦ hs'' (by
      have hle : racl k ({p / q * r', a} : Set K) ≤
          racl k ({a, p / q, p' / q', r'} : Set K) :=
        racl_le_of_subset_racl (Set.insert_subset (mul_mem hcF hrF)
          (Set.singleton_subset_iff.2 haF))
      have hm' := div_mem (hle hm) hdF
      rwa [mul_div_cancel_left₀ s' hd0] at hm')
  have U₂ : AlgebraicIndependent k ![r', s', a] :=
    AlgebraicIndependent.insert_middle hr'a fun hm ↦ hs'' (racl_le_of_subset_racl
      (Set.insert_subset hrF (Set.singleton_subset_iff.2 haF)) hm)
  have hdsa : AlgebraicIndependent k ![p' / q' * s', a] := AlgebraicIndependent.pair_one_two U₁
  have hs'a : AlgebraicIndependent k ![s', a] := AlgebraicIndependent.pair_one_two U₂
  -- The two generic products, with their outputs packaged.
  obtain ⟨w₁, hw₁, M₁, rfl⟩ : ∃ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      BlueprintJMul (jTupleOf (p / q * r') a hcra) (jTupleOf (p' / q' * s') a hdsa)
        (jTupleOf w a hw) ∧ w = algebraMap k K 1 * (p / q * r') * (p' / q' * s') :=
    ⟨_, _, blueprintJMul_kappa U₁ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  obtain ⟨w₂, hw₂, M₂, rfl⟩ : ∃ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      BlueprintJMul (jTupleOf r' a hr'a) (jTupleOf s' a hs'a) (jTupleOf w a hw) ∧
        w = algebraMap k K 1 * r' * s' :=
    ⟨_, _, blueprintJMul_kappa U₂ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  have hcd : p / q * (p' / q') * q'' = p'' :=
    mul_right_cancel₀ (mul_ne_zero hq0 hq'0) (by
      linear_combination (p' / q' * q' * q'') * hc + (p * q'') * hd - h)
  -- Every replacement and output comparison relates pairs of equal ratio.
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x₀ a h₀) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr h₀ hw
  have R₁ : BlueprintRatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1)
      (jTupleOf (p / q * r') a hcra, jTupleOf r' a hr'a) := by
    rw [hr]
    exact blueprintRatioEq_of_mul_eq htr h₀ hp hq hcra hr'a (by linear_combination (-r') * hc)
  have R₂ : BlueprintRatioEq (jTupleOf x₀ a h₀) (s.1.1, s.2.1)
      (jTupleOf (p' / q' * s') a hdsa, jTupleOf s' a hs'a) := by
    rw [hs]
    exact blueprintRatioEq_of_mul_eq htr h₀ hp' hq' hdsa hs'a (by linear_combination (-s') * hd)
  have R₃ : BlueprintRatioEq (jTupleOf x₀ a h₀)
      (jTupleOf (algebraMap k K 1 * (p / q * r') * (p' / q' * s')) a hw₁,
        jTupleOf (algebraMap k K 1 * r' * s') a hw₂) (t.1.1, t.2.1) := by
    rw [ht]
    refine blueprintRatioEq_of_mul_eq htr h₀ hw₁ hw₂ hp'' hq'' ?_
    rw [map_one, one_mul, one_mul]
    linear_combination (r' * s') * hcd
  exact Or.inr ⟨r, s, t, rfl, rfl, rfl, ⟨_, hJ _ hcra⟩, ⟨_, hJ _ hr'a⟩, ⟨_, hJ _ hdsa⟩,
    ⟨_, hJ _ hs'a⟩, ⟨_, hJ _ hw₁⟩, ⟨_, hJ _ hw₂⟩, R₁, R₂, M₁, M₂, R₃⟩

/-- **The literal multiplication graph is total** (blueprint Thm `total-field-graphs`,
multiplication, totality) on the Frobenius class of a semantic base tuple `j(x₀, a)`, over
perfect ambient fields at rank five.  Completeness and the characteristic exponent are supplied
internally. -/
theorem blueprintRatioMulGraph_total [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (r s : Option ({u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u})) :
    ∃ t, BlueprintRatioMulGraph (jTupleOf x₀ a h₀) r s t := by
  classical
  rcases r with _ | r
  · exact ⟨none, Or.inl ⟨Or.inl rfl, rfl⟩⟩
  rcases s with _ | s
  · exact ⟨none, Or.inl ⟨Or.inr rfl, rfl⟩⟩
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
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hq0 := hne hq
  have hq'0 := hne hq'
  have hcd0 : p / q * (p' / q') ≠ 0 :=
    mul_ne_zero (div_ne_zero (hne hp) hq0) (div_ne_zero (hne hp') hq'0)
  -- The output `(j(cde), j(e))` with a fresh denominator `e` over `{a, cd}`.
  obtain ⟨e, he⟩ := fresh_four_of_five_le_trdeg htr {a, p / q * (p' / q')}
    (Finset.card_le_two.trans (by norm_num))
  have he' : e ∉ racl k ({a, p / q * (p' / q')} : Set K) := by simpa using he
  have hea : AlgebraicIndependent k ![e, a] := pair_of_notMem h₀ fun hm ↦ he' (racl_mono
    (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
  have hcdea : AlgebraicIndependent k ![p / q * (p' / q') * e, a] := pair_of_notMem h₀ fun hm ↦
    he' (by
      have hm' := div_mem (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hm)
        (subset_racl k ({a, p / q * (p' / q')} : Set K)
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      rwa [mul_div_cancel_left₀ e hcd0] at hm')
  refine ⟨some (⟨_, frobEq_jTupleOf_of_common htr h₀ hcdea⟩,
    ⟨_, frobEq_jTupleOf_of_common htr h₀ hea⟩), ?_⟩
  exact blueprintRatioMulGraph_of_mul_ratio htr h₀ hp hq hp' hq' hcdea hea r s _
    (Prod.ext hpe hqe) (Prod.ext hp'e hq'e) rfl (by
      linear_combination (e * (p' / q' * q')) * div_mul_cancel₀ p hq0 +
        (e * p) * div_mul_cancel₀ p' hq'0)

end AclGeom
