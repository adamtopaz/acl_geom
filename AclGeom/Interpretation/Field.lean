/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Interp
import AclGeom.Interpretation.TotalOps

/-!
# The interpreted field and its geometric operation graphs

Blueprint §"Geometric graphs of addition and multiplication" (Thm `total-field-graphs`), with the
corrected operations.  On the interpreted carrier `RatioInterp` of the fixed class
`J₁ = [j(x₀, a)]_FrobEq` (the ratio quotient with an adjoined zero), the geometry-only graphs are:

* `RatioAddGraph r s t`: `0` is neutral.  Nonzero `r, s` have representatives `[u, e]`, `[v, e]`
  with a common denominator, and either the numerators are opposite (`JNegTotalRel`) and
  `t = 0`, or `t = [w, e]` for the total nonzero sum `JAddTotalNZRel u v w`.
* `RatioMulGraph r s t`: `t = 0` if `r` or `s` is `0`.  Otherwise `r, s` have representatives
  `[u₁, u₂]`, `[v₁, v₂]` whose numerators and denominators have generic coupled products `w₁, w₂`
  (`JMulRel` with the blueprint's genericity clause), and `t = [w₁, w₂]`.

The definitions quantify over class members and compare classes in the quotient by the corrected
geometric ratio relation `RatioEq`.  They use no coordinates, choices or `Quotient.out`.  Both
graphs decode to the field operations of `K` (`ratioAddGraph_iff`, `ratioMulGraph_iff`), so they
are total and functional (`ratioAddGraph_existsUnique`, `ratioMulGraph_existsUnique`).

The converses rescale the nonzero decoded values `c, d` by fresh elements.
* Addition uses one common denominator `b` outside `racl_k {a, c, d}`.  Then `b`, `c b`, `d b`
  and, if `c + d ≠ 0`, `(c + d) b` lie outside `acl_k(a)`.
* Multiplication uses `b₁` outside `racl_k {a, c, d}` and `b₂` outside `racl_k {a, c, d, b₁}`,
  with the generic triples `(c b₁, d b₂, a)` and `(b₁, b₂, a)`.

The addition's inner detour may use a fifth independent element; the uniform rank bound
remains five. No sixth independent element is used.

`K` is perfect of rank at least five, and completeness over `k̄ ⊆ K̄` (`hcomp`) stays explicit.

**Status:** both corrected geometric graphs are total and functional on the full ratio carrier,
with exact decoded-operation semantics under explicit perfection, rank-five and ACF J-completeness
inputs (#23). Transported field structure, graph naturality and interpreted reconstruction remain
open. The blueprint's literal graphs and argument retain their historical/open status.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF JArith

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Corrected total addition graph** on the interpreted carrier (the corrected counterpart of the
blueprint's `AddGraph`, Thm `total-field-graphs`).  Zero is neutral.  Two nonzero elements are
added through representatives `[u, e]`, `[v, e]` of a common denominator `e`: either the
numerators are opposite (`JNegTotalRel`) and the sum is `0`, or the sum is `[w, e]` for the total
nonzero sum `JAddTotalNZRel u v w` of the numerators.

The common denominator is existentially quantified, and it must be.  A given common denominator
can put the numerator sum inside `acl_k(a)`: for `x ∉ acl_k(a)`, the numerators `j(x, a)` and
`j(1 - x, a)` sum to `1`, so they have no total nonzero sum although the ratio sum is nonzero. -/
def RatioAddGraph [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) (r s t : RatioInterp q htr hcomp h₀) :
    Prop :=
  (r = 0 ∧ t = s) ∨ (s = 0 ∧ t = r) ∨
    ∃ u v e : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
      r = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (u, e) : Quotient _) :
        RatioInterp q htr hcomp h₀) ∧
      s = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (v, e) : Quotient _) :
        RatioInterp q htr hcomp h₀) ∧
      ((JNegTotalRel (jTupleOf x₀ a h₀) u.1 v.1 ∧ t = 0) ∨
        ∃ w : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
          JAddTotalNZRel (jTupleOf x₀ a h₀) u.1 v.1 w.1 ∧
            t = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (w, e) : Quotient _) :
              RatioInterp q htr hcomp h₀))

/-- **Corrected total multiplication graph** on the interpreted carrier (the corrected counterpart
of the blueprint's `MulGraph`, Thm `total-field-graphs`).  A product with a zero factor is `0`.
Two nonzero elements are multiplied through representatives `[u₁, u₂]`, `[v₁, v₂]` whose numerators
and denominators have generic coupled products `w₁`, `w₂`; the product is `[w₁, w₂]`. -/
def RatioMulGraph [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) (r s t : RatioInterp q htr hcomp h₀) :
    Prop :=
  ((r = 0 ∨ s = 0) ∧ t = 0) ∨
    ∃ u₁ u₂ v₁ v₂ w₁ w₂ : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
      r = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (u₁, u₂) : Quotient _) :
        RatioInterp q htr hcomp h₀) ∧
      s = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (v₁, v₂) : Quotient _) :
        RatioInterp q htr hcomp h₀) ∧
      (JMulRel u₁.1 v₁.1 w₁.1 ∧ PointTripleIndependent (u₁.1 0) (v₁.1 0) (u₁.1 4)) ∧
      (JMulRel u₂.1 v₂.1 w₂.1 ∧ PointTripleIndependent (u₂.1 0) (v₂.1 0) (u₂.1 4)) ∧
      t = ((Quotient.mk (ratioSetoid q htr hcomp h₀) (w₁, w₂) : Quotient _) :
        RatioInterp q htr hcomp h₀)

/-- **The corrected addition graph decodes to addition** (Thm `total-field-graphs`, addition):
`RatioAddGraph r s t` holds exactly when `t` decodes to the sum of the decoded `r` and `s`.  The
forward direction holds for every witness; the converse uses one common denominator fresh over the
parameter and the two decoded values. -/
theorem ratioAddGraph_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {r s t : RatioInterp q htr hcomp h₀} :
    RatioAddGraph q htr hcomp h₀ r s t ↔
      ratioInterpDecode q htr hcomp h₀ t =
        ratioInterpDecode q htr hcomp h₀ r + ratioInterpDecode q htr hcomp h₀ s := by
  classical
  let μ := jClassEquiv q htr hcomp h₀
  unfold RatioAddGraph
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨u, v, e, rfl, rfl, ⟨hneg, rfl⟩ | ⟨w, hadd, rfl⟩⟩)
    · rw [ratioInterpDecode_zero, zero_add]
    · rw [ratioInterpDecode_zero, add_zero]
    · have en : (μ v : K) = -(μ u : K) := JNegTotalRel.neg_eq q htr hcomp h₀ u.2 v.2 hneg
      rw [ratioInterpDecode_zero, ratioInterpDecode_coe, ratioInterpDecode_coe]
      change (0 : K) = (μ u : K) / (μ e : K) + (μ v : K) / (μ e : K)
      rw [en]
      ring
    · obtain ⟨_hw, ew⟩ := JAddTotalNZRel.exists_mem_add q htr hcomp h₀ u.2 v.2 hadd
      have ew' : (μ w : K) = (μ u : K) + (μ v : K) := ew
      rw [ratioInterpDecode_coe, ratioInterpDecode_coe, ratioInterpDecode_coe]
      change (μ w : K) / (μ e : K) = (μ u : K) / (μ e : K) + (μ v : K) / (μ e : K)
      rw [ew', add_div]
  · intro h
    -- Nonzero interpreted elements decode to nonzero field elements.
    have hne : ∀ R : Quotient (ratioSetoid q htr hcomp h₀),
        ratioInterpDecode q htr hcomp h₀ (R : RatioInterp q htr hcomp h₀) ≠ 0 := fun R h0 ↦
      WithZero.coe_ne_zero ((ratioInterpDecode q htr hcomp h₀).injective
        (h0.trans (ratioInterpDecode_zero q htr hcomp h₀).symm))
    induction r using WithZero.recZeroCoe with
    | zero =>
      refine Or.inl ⟨rfl, (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
      rw [h, ratioInterpDecode_zero, zero_add]
    | coe R =>
      induction s using WithZero.recZeroCoe with
      | zero =>
        refine Or.inr (Or.inl ⟨rfl, (ratioInterpDecode q htr hcomp h₀).injective ?_⟩)
        rw [h, ratioInterpDecode_zero, add_zero]
      | coe S =>
        obtain ⟨c, hc⟩ : ∃ c, ratioInterpDecode q htr hcomp h₀
            (R : RatioInterp q htr hcomp h₀) = c := ⟨_, rfl⟩
        obtain ⟨d, hd⟩ : ∃ d, ratioInterpDecode q htr hcomp h₀
            (S : RatioInterp q htr hcomp h₀) = d := ⟨_, rfl⟩
        have hc0 : c ≠ 0 := fun h0 ↦ hne R (hc.trans h0)
        have hd0 : d ≠ 0 := fun h0 ↦ hne S (hd.trans h0)
        rw [hc, hd] at h
        -- A common denominator `b` fresh over `a, c, d` (rank at most three before the choice).
        obtain ⟨b, hb⟩ := fresh_three_of_five_le_trdeg htr {a, c, d} Finset.card_le_three
        have hb' : b ∉ racl k ({a, c, d} : Set K) := by simpa using hb
        have hcR : c ∈ racl k ({a, c, d} : Set K) := subset_racl k _ (by simp)
        have hdR : d ∈ racl k ({a, c, d} : Set K) := subset_racl k _ (by simp)
        have hsub : ({a} : Set K) ⊆ racl k ({a, c, d} : Set K) :=
          Set.singleton_subset_iff.2 (subset_racl k _ (by simp))
        have hbA : b ∉ racl k ({a} : Set K) := fun h' ↦ hb' (racl_le_of_subset_racl hsub h')
        have hb0 : b ≠ 0 := fun h' ↦ hbA (by rw [h']; exact zero_mem _)
        have hcb : c * b ∉ racl k ({a} : Set K) := mul_fresh_notMem hb' hcR hc0 hsub
        have hdb : d * b ∉ racl k ({a} : Set K) := mul_fresh_notMem hb' hdR hd0 hsub
        -- The class members `e = j(b, a)`, `u = j(c b, a)` and `v = j(d b, a)`.
        let e := μ.symm ⟨b, hbA⟩
        let u := μ.symm ⟨c * b, hcb⟩
        let v := μ.symm ⟨d * b, hdb⟩
        have ee : (μ e : K) = b := congrArg Subtype.val (μ.apply_symm_apply ⟨b, hbA⟩)
        have eu : (μ u : K) = c * b := congrArg Subtype.val (μ.apply_symm_apply ⟨c * b, hcb⟩)
        have ev : (μ v : K) = d * b := congrArg Subtype.val (μ.apply_symm_apply ⟨d * b, hdb⟩)
        refine Or.inr (Or.inr ⟨u, v, e, (ratioInterpDecode q htr hcomp h₀).injective ?_,
          (ratioInterpDecode q htr hcomp h₀).injective ?_, ?_⟩)
        · rw [hc, ratioInterpDecode_coe]
          change c = (μ u : K) / (μ e : K)
          rw [eu, ee, mul_div_cancel_right₀ c hb0]
        · rw [hd, ratioInterpDecode_coe]
          change d = (μ v : K) / (μ e : K)
          rw [ev, ee, mul_div_cancel_right₀ d hb0]
        by_cases hcd : c + d = 0
        · -- Opposite numerators: the sum is the adjoined zero.
          refine Or.inl ⟨jNegTotalRel_of_neg_eq q htr hcomp h₀ u.2 v.2 ?_,
            (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
          · change (μ v : K) = -(μ u : K)
            rw [ev, eu]
            linear_combination b * hcd
          · rw [h, hcd, ratioInterpDecode_zero]
        · -- Otherwise the numerator `j((c + d) b, a)` is the total nonzero sum.
          have hcdb : (c + d) * b ∉ racl k ({a} : Set K) :=
            mul_fresh_notMem hb' (add_mem hcR hdR) hcd hsub
          let w := μ.symm ⟨(c + d) * b, hcdb⟩
          have ew : (μ w : K) = (c + d) * b :=
            congrArg Subtype.val (μ.apply_symm_apply ⟨(c + d) * b, hcdb⟩)
          refine Or.inr ⟨w, jAddTotalNZRel_of_add_eq q htr hcomp h₀ u.2 v.2 w.2 ?_,
            (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
          · change (μ w : K) = (μ u : K) + (μ v : K)
            rw [ew, eu, ev, add_mul]
          · rw [h, ratioInterpDecode_coe]
            change c + d = (μ w : K) / (μ e : K)
            rw [ew, ee, mul_div_cancel_right₀ (c + d) hb0]

/-- **The corrected multiplication graph decodes to multiplication** (Thm `total-field-graphs`,
multiplication): `RatioMulGraph r s t` holds exactly when `t` decodes to the product of the decoded
`r` and `s`.  The forward direction holds for every witness; the converse uses two successive
fresh elements, so the rank stays at most five. -/
theorem ratioMulGraph_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {r s t : RatioInterp q htr hcomp h₀} :
    RatioMulGraph q htr hcomp h₀ r s t ↔
      ratioInterpDecode q htr hcomp h₀ t =
        ratioInterpDecode q htr hcomp h₀ r * ratioInterpDecode q htr hcomp h₀ s := by
  classical
  let μ := jClassEquiv q htr hcomp h₀
  unfold RatioMulGraph
  constructor
  · rintro (⟨rfl | rfl, rfl⟩ | ⟨u₁, u₂, v₁, v₂, w₁, w₂, rfl, rfl, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, rfl⟩)
    · rw [ratioInterpDecode_zero, zero_mul]
    · rw [ratioInterpDecode_zero, mul_zero]
    · obtain ⟨_h₁, e₁⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ u₁.2 v₁.2 g₁ m₁
      obtain ⟨_h₂, e₂⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ u₂.2 v₂.2 g₂ m₂
      have e₁' : (μ w₁ : K) = (μ u₁ : K) * (μ v₁ : K) := e₁
      have e₂' : (μ w₂ : K) = (μ u₂ : K) * (μ v₂ : K) := e₂
      rw [ratioInterpDecode_coe, ratioInterpDecode_coe, ratioInterpDecode_coe]
      change (μ w₁ : K) / (μ w₂ : K) = (μ u₁ : K) / (μ u₂ : K) * ((μ v₁ : K) / (μ v₂ : K))
      rw [e₁', e₂', mul_div_mul_comm]
  · intro h
    -- Nonzero interpreted elements decode to nonzero field elements.
    have hne : ∀ R : Quotient (ratioSetoid q htr hcomp h₀),
        ratioInterpDecode q htr hcomp h₀ (R : RatioInterp q htr hcomp h₀) ≠ 0 := fun R h0 ↦
      WithZero.coe_ne_zero ((ratioInterpDecode q htr hcomp h₀).injective
        (h0.trans (ratioInterpDecode_zero q htr hcomp h₀).symm))
    induction r using WithZero.recZeroCoe with
    | zero =>
      refine Or.inl ⟨Or.inl rfl, (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
      rw [h, ratioInterpDecode_zero, zero_mul]
    | coe R =>
      induction s using WithZero.recZeroCoe with
      | zero =>
        refine Or.inl ⟨Or.inr rfl, (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
        rw [h, ratioInterpDecode_zero, mul_zero]
      | coe S =>
        obtain ⟨c, hc⟩ : ∃ c, ratioInterpDecode q htr hcomp h₀
            (R : RatioInterp q htr hcomp h₀) = c := ⟨_, rfl⟩
        obtain ⟨d, hd⟩ : ∃ d, ratioInterpDecode q htr hcomp h₀
            (S : RatioInterp q htr hcomp h₀) = d := ⟨_, rfl⟩
        have hc0 : c ≠ 0 := fun h0 ↦ hne R (hc.trans h0)
        have hd0 : d ≠ 0 := fun h0 ↦ hne S (hd.trans h0)
        rw [hc, hd] at h
        -- `b₁` fresh over `a, c, d` (rank at most three before the choice).
        obtain ⟨b₁, hb₁⟩ := fresh_three_of_five_le_trdeg htr {a, c, d} Finset.card_le_three
        have hb₁' : b₁ ∉ racl k ({a, c, d} : Set K) := by simpa using hb₁
        have hcR : c ∈ racl k ({a, c, d} : Set K) := subset_racl k _ (by simp)
        have hsub : ({a} : Set K) ⊆ racl k ({a, c, d} : Set K) :=
          Set.singleton_subset_iff.2 (subset_racl k _ (by simp))
        have hb₁A : b₁ ∉ racl k ({a} : Set K) := fun h' ↦ hb₁' (racl_le_of_subset_racl hsub h')
        have hcbA : c * b₁ ∉ racl k ({a} : Set K) := mul_fresh_notMem hb₁' hcR hc0 hsub
        -- `b₂` fresh over `a, c, d, b₁` (rank at most four before the choice).
        obtain ⟨b₂, hb₂⟩ := fresh_four_of_five_le_trdeg htr {a, c, d, b₁} Finset.card_le_four
        have hb₂' : b₂ ∉ racl k ({a, c, d, b₁} : Set K) := by simpa using hb₂
        have haR' : a ∈ racl k ({a, c, d, b₁} : Set K) := subset_racl k _ (by simp)
        have hcR' : c ∈ racl k ({a, c, d, b₁} : Set K) := subset_racl k _ (by simp)
        have hdR' : d ∈ racl k ({a, c, d, b₁} : Set K) := subset_racl k _ (by simp)
        have hbR' : b₁ ∈ racl k ({a, c, d, b₁} : Set K) := subset_racl k _ (by simp)
        -- The generic triples `(b₁, b₂, a)` and `(c b₁, d b₂, a)`.
        have T₂ : AlgebraicIndependent k ![b₁, b₂, a] :=
          AlgebraicIndependent.insert_middle (pair_of_notMem h₀ hb₁A) fun h' ↦ hb₂'
            (racl_le_of_subset_racl
              (Set.insert_subset_iff.2 ⟨hbR', Set.singleton_subset_iff.2 haR'⟩) h')
        have T₁ : AlgebraicIndependent k ![c * b₁, d * b₂, a] :=
          AlgebraicIndependent.insert_middle (pair_of_notMem h₀ hcbA)
            (mul_fresh_notMem hb₂' hdR' hd0
              (Set.insert_subset_iff.2 ⟨mul_mem hcR' hbR', Set.singleton_subset_iff.2 haR'⟩))
        have hb₁0 : b₁ ≠ 0 :=
          AlgebraicIndependent.ne_zero (AlgebraicIndependent.pair_zero_two T₂) 0
        have hb₂0 : b₂ ≠ 0 :=
          AlgebraicIndependent.ne_zero (AlgebraicIndependent.pair_one_two T₂) 0
        -- The representatives `[j(c b₁, a), j(b₁, a)]` and `[j(d b₂, a), j(b₂, a)]`, and the
        -- products `j(c b₁ d b₂, a)` and `j(b₁ b₂, a)`.
        refine Or.inr ⟨⟨jTupleOf (c * b₁) a (AlgebraicIndependent.pair_zero_two T₁),
            frobEq_jTupleOf_of_common htr h₀ _⟩,
          ⟨jTupleOf b₁ a (AlgebraicIndependent.pair_zero_two T₂),
            frobEq_jTupleOf_of_common htr h₀ _⟩,
          ⟨jTupleOf (d * b₂) a (AlgebraicIndependent.pair_one_two T₁),
            frobEq_jTupleOf_of_common htr h₀ _⟩,
          ⟨jTupleOf b₂ a (AlgebraicIndependent.pair_one_two T₂),
            frobEq_jTupleOf_of_common htr h₀ _⟩,
          ⟨jTupleOf (c * b₁ * (d * b₂)) a (pair_mul_a T₁), frobEq_jTupleOf_of_common htr h₀ _⟩,
          ⟨jTupleOf (b₁ * b₂) a (pair_mul_a T₂), frobEq_jTupleOf_of_common htr h₀ _⟩,
          (ratioInterpDecode q htr hcomp h₀).injective ?_,
          (ratioInterpDecode q htr hcomp h₀).injective ?_,
          ⟨jMulRel_jTupleOf T₁, pointTripleIndependent_jTupleOf T₁⟩,
          ⟨jMulRel_jTupleOf T₂, pointTripleIndependent_jTupleOf T₂⟩,
          (ratioInterpDecode q htr hcomp h₀).injective ?_⟩
        · rw [hc, ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf,
            mul_div_cancel_right₀ c hb₁0]
        · rw [hd, ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf,
            mul_div_cancel_right₀ d hb₂0]
        · rw [h, ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf,
            mul_mul_mul_comm, mul_div_cancel_right₀ (c * d) (mul_ne_zero hb₁0 hb₂0)]

/-- **The corrected addition graph is total and functional** (Thm `total-field-graphs`): any two
interpreted elements have exactly one sum. -/
theorem ratioAddGraph_existsUnique [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) (r s : RatioInterp q htr hcomp h₀) :
    ∃! t, RatioAddGraph q htr hcomp h₀ r s t :=
  ExistsUnique.intro ((ratioInterpDecode q htr hcomp h₀).symm
      (ratioInterpDecode q htr hcomp h₀ r + ratioInterpDecode q htr hcomp h₀ s))
    ((ratioAddGraph_iff q htr hcomp h₀).2 (Equiv.apply_symm_apply _ _)) fun _t ht ↦
      (ratioInterpDecode q htr hcomp h₀).injective
        (((ratioAddGraph_iff q htr hcomp h₀).1 ht).trans (Equiv.apply_symm_apply _ _).symm)

/-- **The corrected multiplication graph is total and functional** (Thm `total-field-graphs`): any
two interpreted elements have exactly one product. -/
theorem ratioMulGraph_existsUnique [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) (r s : RatioInterp q htr hcomp h₀) :
    ∃! t, RatioMulGraph q htr hcomp h₀ r s t :=
  ExistsUnique.intro ((ratioInterpDecode q htr hcomp h₀).symm
      (ratioInterpDecode q htr hcomp h₀ r * ratioInterpDecode q htr hcomp h₀ s))
    ((ratioMulGraph_iff q htr hcomp h₀).2 (Equiv.apply_symm_apply _ _)) fun _t ht ↦
      (ratioInterpDecode q htr hcomp h₀).injective
        (((ratioMulGraph_iff q htr hcomp h₀).1 ht).trans (Equiv.apply_symm_apply _ _).symm)

end

end AclGeom
