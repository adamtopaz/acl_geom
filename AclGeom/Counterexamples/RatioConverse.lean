/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.GenericArithmetic

/-!
# The true converse of the literal ratio semantics

Blueprint Lemma `ratio-semantics` asserts, for the literal ratio relation,
`RatioEq(r, s) ↔ μ(r₁)/μ(r₂) = μ(s₁)/μ(s₂)`.  Its forward direction fails for the literal
predicates (`blueprintRatioEq_counterexample`).  Its converse is true, and is proved here for
semantic representatives (`blueprintRatioEq_of_mul_eq`), with the source argument.

Let `r = (j(p₁, a), j(p₂, a))` and `s = (j(q₁, a), j(q₂, a))` with `p₁ q₂ = p₂ q₁`.  The four
values have rank at most three over `k`, since `q₂ = p₂ q₁ / p₁`, so with `a` the rank is at most
four.  For `t` outside `acl_k(a, p₁, p₂, q₁)` the multipliers `c₁ = j(q₂ t, a)`,
`c₂ = j(p₂ t, a)` and the products `d₁ = j(p₁ q₂ t, a) = j(q₁ p₂ t, a)`,
`d₂ = j(p₂ q₂ t, a)` are generic literal products, and they witness `RatioEq(r, s)` in the
Frobenius class of any `j(x₀, a)`.

The fresh element uses the fifth and final rank allowed by the hypothesis.  The base and
ambient fields are arbitrary; no perfection, infinite base or completeness input is used.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the converse of Lemma `ratio-semantics` is proved for semantic representatives
(#8, #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The converse of the literal ratio semantics** (blueprint Lemma `ratio-semantics`, reverse
implication).  Semantic pairs `(j(p₁, a), j(p₂, a))` and `(j(q₁, a), j(q₂, a))` with equal ratios,
`p₁ q₂ = p₂ q₁`, are related by the literal ratio relation on the Frobenius class of any
semantic base tuple `j(x₀, a)`, at rank five over arbitrary fields. -/
theorem blueprintRatioEq_of_mul_eq (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a p₁ p₂ q₁ q₂ : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (h₁ : AlgebraicIndependent k ![p₁, a]) (h₂ : AlgebraicIndependent k ![p₂, a])
    (h₃ : AlgebraicIndependent k ![q₁, a]) (h₄ : AlgebraicIndependent k ![q₂, a])
    (h : p₁ * q₂ = p₂ * q₁) :
    BlueprintRatioEq (jTupleOf x₀ a h₀) (jTupleOf p₁ a h₁, jTupleOf p₂ a h₂)
      (jTupleOf q₁ a h₃, jTupleOf q₂ a h₄) := by
  classical
  have hne : ∀ {w : K}, AlgebraicIndependent k ![w, a] → w ≠ 0 := fun {w} hw h0 ↦
    hw.transcendental 0 (by
      change IsAlgebraic k w
      rw [h0]
      exact isAlgebraic_zero)
  have hp₁0 := hne h₁
  have hp₂0 := hne h₂
  have hq₂0 := hne h₄
  -- A fresh multiplier over `F = racl {a, p₁, p₂, q₁}`, which contains all four endpoints.
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {a, p₁, p₂, q₁} Finset.card_le_four
  have ht' : t ∉ racl k ({a, p₁, p₂, q₁} : Set K) := by simpa using ht
  have haF : a ∈ racl k ({a, p₁, p₂, q₁} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hp₁F : p₁ ∈ racl k ({a, p₁, p₂, q₁} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hp₂F : p₂ ∈ racl k ({a, p₁, p₂, q₁} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hq₁F : q₁ ∈ racl k ({a, p₁, p₂, q₁} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hq₂F : q₂ ∈ racl k ({a, p₁, p₂, q₁} : Set K) := by
    have hq : q₂ = p₂ * q₁ / p₁ := (eq_div_iff hp₁0).2 (by rw [mul_comm, h])
    rw [hq]
    exact div_mem (mul_mem hp₂F hq₁F) hp₁F
  -- A product `c · t` with `c ∈ F` nonzero is generic with every first input in `F`.
  have hgen : ∀ {p c : K}, AlgebraicIndependent k ![p, a] → p ∈ racl k ({a, p₁, p₂, q₁} : Set K) →
      c ∈ racl k ({a, p₁, p₂, q₁} : Set K) → c ≠ 0 → AlgebraicIndependent k ![p, c * t, a] :=
    fun {p c} hp hpF hcF hc0 ↦ AlgebraicIndependent.insert_middle hp fun hm ↦ ht' (by
      have hle : racl k ({p, a} : Set K) ≤ racl k ({a, p₁, p₂, q₁} : Set K) :=
        racl_le_of_subset_racl (Set.insert_subset hpF (Set.singleton_subset_iff.2 haF))
      have h' := div_mem (hle hm) hcF
      rwa [mul_div_cancel_left₀ t hc0] at h')
  have T₁ := hgen h₁ hp₁F hq₂F hq₂0
  have T₂ := hgen h₂ hp₂F hq₂F hq₂0
  have T₃ := hgen h₃ hq₁F hp₂F hp₂0
  have T₄ := hgen h₄ hq₂F hp₂F hp₂0
  -- The four generic products; the outputs are packaged to avoid output congruence.
  obtain ⟨d₁, hd₁, M₁, rfl⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf p₁ a h₁) (jTupleOf (q₂ * t) a (AlgebraicIndependent.pair_one_two T₁))
        (jTupleOf d a hd) ∧ d = algebraMap k K 1 * p₁ * (q₂ * t) :=
    ⟨_, _, blueprintJMul_kappa T₁ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  obtain ⟨d₂, hd₂, M₂, rfl⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf p₂ a h₂) (jTupleOf (q₂ * t) a (AlgebraicIndependent.pair_one_two T₁))
        (jTupleOf d a hd) ∧ d = algebraMap k K 1 * p₂ * (q₂ * t) :=
    ⟨_, _, blueprintJMul_kappa T₂ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  obtain ⟨d₃, hd₃, M₃, rfl⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf q₁ a h₃) (jTupleOf (p₂ * t) a (AlgebraicIndependent.pair_one_two T₃))
        (jTupleOf d a hd) ∧ d = algebraMap k K 1 * q₁ * (p₂ * t) :=
    ⟨_, _, blueprintJMul_kappa T₃ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  obtain ⟨d₄, hd₄, M₄, rfl⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf q₂ a h₄) (jTupleOf (p₂ * t) a (AlgebraicIndependent.pair_one_two T₃))
        (jTupleOf d a hd) ∧ d = algebraMap k K 1 * q₂ * (p₂ * t) :=
    ⟨_, _, blueprintJMul_kappa T₄ htr (one_ne_zero : (1 : k) ≠ 0), rfl⟩
  -- The cross-product equality identifies the outputs `q₁ p₂ t = p₁ q₂ t` and `q₂ p₂ t = p₂ q₂ t`.
  rw [jTupleOf_congr hd₃ hd₁ (by rw [map_one, one_mul, one_mul]; linear_combination -t * h)]
    at M₃
  rw [jTupleOf_congr hd₄ hd₂ (by rw [map_one, one_mul, one_mul]; ring)] at M₄
  have hJ : ∀ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      FrobEq (jTupleOf x₀ a h₀) (jTupleOf w a hw) := fun _ hw ↦
    frobEq_jTupleOf_of_common htr h₀ hw
  exact ⟨_, _, _, _, hJ _ _, hJ _ _, hJ _ hd₁, hJ _ hd₂, M₁, M₂, M₃, M₄⟩

end AclGeom
