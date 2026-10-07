/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.ClassArithmetic

/-!
# The corrected ratio relation on the fixed Frobenius class

Blueprint §"The ratio quotient" defines `RatioEq r s` for pairs of members of the fixed class
`J₁ = [j(x₀, a)]_FrobEq` by four products through the refuted, nonfunctional `JMul`; its literal
ratio semantics is refuted (`AclGeom.Counterexamples.GenericArithmetic`, issue #23).  Here the four
products use the coupled EH95 product `JMulRel`, each together with the blueprint's genericity
clause `PointTripleIndependent` for its two inputs and the parameter:
`RatioEq j₀ (r₁, r₂) (s₁, s₂)` asks for class members `c₁, c₂, d₁, d₂` with
`r₁ c₁ = d₁`, `r₂ c₁ = d₂`, `s₁ c₂ = d₁`, `s₂ c₂ = d₂`, every product generic.

`ratioEq_iff` is the corrected Lemma `ratio-semantics`: `RatioEq` holds exactly when the decoded
ratios `μ(r₁)/μ(r₂)` and `μ(s₁)/μ(s₂)` agree, where `μ` is the class coordinate `jClassEquiv`.

* The forward direction holds for *every* witness: the corrected generic multiplication on the
  class (`JMulRel.jClassEquiv_mul`) turns the four products into four field equations, and the
  coordinates of class members are nonzero.
* For the converse, write `r₁, r₂, s₁, s₂` as `j(x₁, a), j(x₂, a), j(y₁, a), j(y₂, a)`.  Ratio
  equality gives `y₁ = x₁ y₂ / x₂`, so a single `t` outside `racl_k {a, x₁, x₂, y₂}` (the
  rank-five hypothesis, through a four-element set) is fresh over all five values.  The witnesses
  are `j(y₂ t, a), j(x₂ t, a), j(x₁ y₂ t, a), j(x₂ y₂ t, a)`.

`K` is perfect of rank at least five, and completeness over `k̄ ⊆ K̄` (`hcomp`) stays explicit: it
presents class members with the literal parameter `a` and defines `μ`.

**Status:** the corrected geometric ratio relation has exact decoded-ratio semantics under
explicit perfection, rank-five and ACF J-completeness inputs (#23). `Decode` constructs its
setoid/quotient and bijective nonzero decoding under the same inputs. `Interp` adjoins zero
and decodes the full carrier bijectively to `K`. `Field` proves corrected total geometric
operation graphs under the same inputs. Transported field structure and naturality remain open.
The public `mul_fresh_notMem` supplies the existing ratio witnesses and both operation-graph
converses in `Field`; its type and proof use no rank-five or completeness input.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF JArith

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The corrected ratio relation** on pairs of members of the class of `j₀` (blueprint
§"A geometry-only ratio equivalence", with the coupled product `JMulRel` and a genericity clause
for each product): there are class members `c₁, c₂, d₁, d₂` with `r₁ c₁ = d₁`, `r₂ c₁ = d₂`,
`s₁ c₂ = d₁` and `s₂ c₂ = d₂`. -/
def RatioEq (j₀ : Fin 5 → Point k K) (r s : (Fin 5 → Point k K) × (Fin 5 → Point k K)) :
    Prop :=
  ∃ c₁ c₂ d₁ d₂ : Fin 5 → Point k K,
    FrobEq j₀ c₁ ∧ FrobEq j₀ c₂ ∧ FrobEq j₀ d₁ ∧ FrobEq j₀ d₂ ∧
    (JMulRel r.1 c₁ d₁ ∧ PointTripleIndependent (r.1 0) (c₁ 0) (r.1 4)) ∧
    (JMulRel r.2 c₁ d₂ ∧ PointTripleIndependent (r.2 0) (c₁ 0) (r.2 4)) ∧
    (JMulRel s.1 c₂ d₁ ∧ PointTripleIndependent (s.1 0) (c₂ 0) (s.1 4)) ∧
    (JMulRel s.2 c₂ d₂ ∧ PointTripleIndependent (s.2 0) (c₂ 0) (s.2 4))

/-- A nonzero multiple, from `racl k S`, of an element `t` fresh over `S` avoids every set whose
closure lies in `racl k S`. -/
theorem mul_fresh_notMem {S T : Set K} {c t : K} (ht : t ∉ racl k S)
    (hc : c ∈ racl k S) (hc0 : c ≠ 0) (hT : T ⊆ racl k S) : c * t ∉ racl k T := fun h ↦
  ht (mem_racl_of_eq (mul_div_cancel_left₀ t hc0).symm
    (div_mem (racl_le_of_subset_racl hT h) hc))

/-- **Ratio semantics, forward** (corrected Lemma `ratio-semantics`): any witness of the corrected
ratio relation forces equality of the decoded ratios. -/
theorem RatioEq.div_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {r₁ r₂ s₁ s₂ : Fin 5 → Point k K}
    (hr₁ : FrobEq (jTupleOf x₀ a h₀) r₁) (hr₂ : FrobEq (jTupleOf x₀ a h₀) r₂)
    (hs₁ : FrobEq (jTupleOf x₀ a h₀) s₁) (hs₂ : FrobEq (jTupleOf x₀ a h₀) s₂)
    (h : RatioEq (jTupleOf x₀ a h₀) (r₁, r₂) (s₁, s₂)) :
    (jClassEquiv q htr hcomp h₀ ⟨r₁, hr₁⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨r₂, hr₂⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨s₁, hs₁⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨s₂, hs₂⟩ : K) := by
  obtain ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩, ⟨m₄, g₄⟩⟩ := h
  -- Class coordinates are nonzero.
  have hne : ∀ {w : Fin 5 → Point k K} (hw : FrobEq (jTupleOf x₀ a h₀) w),
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) ≠ 0 := fun hw ↦
    jClassEquiv_ne_zero q htr hcomp h₀ ⟨_, hw⟩
  -- The four products, as field equations between coordinates.
  obtain ⟨_hd₁, e₁⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ hr₁ hc₁ g₁ m₁
  obtain ⟨_hd₂, e₂⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ hr₂ hc₁ g₂ m₂
  obtain ⟨_hd₁', e₃⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ hs₁ hc₂ g₃ m₃
  obtain ⟨_hd₂', e₄⟩ := JMulRel.jClassEquiv_mul q htr hcomp h₀ hs₂ hc₂ g₄ m₄
  have h₁₃ : (jClassEquiv q htr hcomp h₀ ⟨r₁, hr₁⟩ : K) *
        (jClassEquiv q htr hcomp h₀ ⟨c₁, hc₁⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨s₁, hs₁⟩ : K) * (jClassEquiv q htr hcomp h₀ ⟨c₂, hc₂⟩ : K) :=
    e₁.symm.trans e₃
  have h₂₄ : (jClassEquiv q htr hcomp h₀ ⟨r₂, hr₂⟩ : K) *
        (jClassEquiv q htr hcomp h₀ ⟨c₁, hc₁⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨s₂, hs₂⟩ : K) * (jClassEquiv q htr hcomp h₀ ⟨c₂, hc₂⟩ : K) :=
    e₂.symm.trans e₄
  rw [div_eq_div_iff (hne hr₂) (hne hs₂)]
  apply mul_right_cancel₀ (mul_ne_zero (hne hc₁) (hne hc₂))
  linear_combination
    ((jClassEquiv q htr hcomp h₀ ⟨s₂, hs₂⟩ : K) * (jClassEquiv q htr hcomp h₀ ⟨c₂, hc₂⟩ : K)) *
        h₁₃ -
      ((jClassEquiv q htr hcomp h₀ ⟨s₁, hs₁⟩ : K) * (jClassEquiv q htr hcomp h₀ ⟨c₂, hc₂⟩ : K)) *
        h₂₄

/-- **Ratio semantics, converse** (corrected Lemma `ratio-semantics`): equal decoded ratios have a
witness of the corrected ratio relation.  One element `t`, fresh over the parameter and three of
the four coordinates, supplies all four witnesses; this uses the rank-five hypothesis. -/
theorem ratioEq_of_div_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {r₁ r₂ s₁ s₂ : Fin 5 → Point k K}
    (hr₁ : FrobEq (jTupleOf x₀ a h₀) r₁) (hr₂ : FrobEq (jTupleOf x₀ a h₀) r₂)
    (hs₁ : FrobEq (jTupleOf x₀ a h₀) s₁) (hs₂ : FrobEq (jTupleOf x₀ a h₀) s₂)
    (h : (jClassEquiv q htr hcomp h₀ ⟨r₁, hr₁⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨r₂, hr₂⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨s₁, hs₁⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨s₂, hs₂⟩ : K)) :
    RatioEq (jTupleOf x₀ a h₀) (r₁, r₂) (s₁, s₂) := by
  classical
  -- Present the four class members with the literal parameter `a`.
  obtain ⟨x₁, hx₁, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hr₁
  obtain ⟨x₂, hx₂, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hr₂
  obtain ⟨y₁, hy₁, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hs₁
  obtain ⟨y₂, hy₂, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hs₂
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf,
    jClassEquiv_jTupleOf] at h
  have hx₂0 : x₂ ≠ 0 := AlgebraicIndependent.ne_zero hx₂ 0
  have hy₂0 : y₂ ≠ 0 := AlgebraicIndependent.ne_zero hy₂ 0
  have hcross : x₁ * y₂ = y₁ * x₂ := (div_eq_div_iff hx₂0 hy₂0).1 h
  -- A fresh `t` over `a, x₁, x₂, y₂`; then `y₁ = x₁ y₂ / x₂` lies in the same closure.
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {a, x₁, x₂, y₂} Finset.card_le_four
  have ht' : t ∉ racl k ({a, x₁, x₂, y₂} : Set K) := by simpa using ht
  have ha : a ∈ racl k ({a, x₁, x₂, y₂} : Set K) := subset_racl k _ (by simp)
  have hx₁R : x₁ ∈ racl k ({a, x₁, x₂, y₂} : Set K) := subset_racl k _ (by simp)
  have hx₂R : x₂ ∈ racl k ({a, x₁, x₂, y₂} : Set K) := subset_racl k _ (by simp)
  have hy₂R : y₂ ∈ racl k ({a, x₁, x₂, y₂} : Set K) := subset_racl k _ (by simp)
  have hy₁R : y₁ ∈ racl k ({a, x₁, x₂, y₂} : Set K) := by
    rw [(eq_div_iff hx₂0).2 hcross.symm]
    exact div_mem (mul_mem hx₁R hy₂R) hx₂R
  have hsub : ∀ {z : K}, z ∈ racl k ({a, x₁, x₂, y₂} : Set K) →
      ({z, a} : Set K) ⊆ racl k ({a, x₁, x₂, y₂} : Set K) := fun hz ↦
    Set.insert_subset_iff.2 ⟨hz, Set.singleton_subset_iff.2 ha⟩
  -- The four generic triples.
  have T₁ : AlgebraicIndependent k ![x₁, y₂ * t, a] :=
    AlgebraicIndependent.insert_middle hx₁ (mul_fresh_notMem ht' hy₂R hy₂0 (hsub hx₁R))
  have T₂ : AlgebraicIndependent k ![x₂, y₂ * t, a] :=
    AlgebraicIndependent.insert_middle hx₂ (mul_fresh_notMem ht' hy₂R hy₂0 (hsub hx₂R))
  have T₃ : AlgebraicIndependent k ![y₁, x₂ * t, a] :=
    AlgebraicIndependent.insert_middle hy₁ (mul_fresh_notMem ht' hx₂R hx₂0 (hsub hy₁R))
  have T₄ : AlgebraicIndependent k ![y₂, x₂ * t, a] :=
    AlgebraicIndependent.insert_middle hy₂ (mul_fresh_notMem ht' hx₂R hx₂0 (hsub hy₂R))
  -- The witnesses `j(y₂ t, a)`, `j(x₂ t, a)`, `j(x₁ y₂ t, a)`, `j(x₂ y₂ t, a)`.
  have e₃ : jTupleOf (y₁ * (x₂ * t)) a (pair_mul_a T₃) =
      jTupleOf (x₁ * (y₂ * t)) a (pair_mul_a T₁) :=
    jTupleOf_congr _ _ (by linear_combination (-t) * hcross)
  have e₄ : jTupleOf (y₂ * (x₂ * t)) a (pair_mul_a T₄) =
      jTupleOf (x₂ * (y₂ * t)) a (pair_mul_a T₂) :=
    jTupleOf_congr _ _ (by ring)
  refine ⟨jTupleOf (y₂ * t) a (AlgebraicIndependent.pair_one_two T₁),
    jTupleOf (x₂ * t) a (AlgebraicIndependent.pair_one_two T₃),
    jTupleOf (x₁ * (y₂ * t)) a (pair_mul_a T₁), jTupleOf (x₂ * (y₂ * t)) a (pair_mul_a T₂),
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    ⟨jMulRel_jTupleOf T₁, pointTripleIndependent_jTupleOf T₁⟩,
    ⟨jMulRel_jTupleOf T₂, pointTripleIndependent_jTupleOf T₂⟩,
    ⟨e₃ ▸ jMulRel_jTupleOf T₃, pointTripleIndependent_jTupleOf T₃⟩,
    ⟨e₄ ▸ jMulRel_jTupleOf T₄, pointTripleIndependent_jTupleOf T₄⟩⟩

/-- **The corrected ratio semantics** (blueprint Lemma `ratio-semantics`, with the coupled product
and explicit genericity): for members of the class of `j(x₀, a)`, the corrected ratio relation
holds exactly when the decoded ratios agree. -/
theorem ratioEq_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {r₁ r₂ s₁ s₂ : Fin 5 → Point k K}
    (hr₁ : FrobEq (jTupleOf x₀ a h₀) r₁) (hr₂ : FrobEq (jTupleOf x₀ a h₀) r₂)
    (hs₁ : FrobEq (jTupleOf x₀ a h₀) s₁) (hs₂ : FrobEq (jTupleOf x₀ a h₀) s₂) :
    RatioEq (jTupleOf x₀ a h₀) (r₁, r₂) (s₁, s₂) ↔
      (jClassEquiv q htr hcomp h₀ ⟨r₁, hr₁⟩ : K) / (jClassEquiv q htr hcomp h₀ ⟨r₂, hr₂⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨s₁, hs₁⟩ : K) /
          (jClassEquiv q htr hcomp h₀ ⟨s₂, hs₂⟩ : K) :=
  ⟨RatioEq.div_eq q htr hcomp h₀ hr₁ hr₂ hs₁ hs₂,
    ratioEq_of_div_eq q htr hcomp h₀ hr₁ hr₂ hs₁ hs₂⟩

end

end AclGeom
