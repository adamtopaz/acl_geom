/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Ratio

/-!
# The ratio quotient and its decoding

Blueprint §"The ratio quotient and the interpreted field", nonzero part.  On pairs of members of
the fixed class `J₁ = [j(x₀, a)]_FrobEq`, the corrected geometric ratio relation `RatioEq` is an
equivalence relation (`ratioEq_equivalence`), because it is equality of decoded ratios
(`ratioEq_iff`); the blueprint likewise builds the setoid from the semantics rather than from
witnesses.  Its quotient (`ratioSetoid`) decodes by `[r₁, r₂] ↦ μ(r₁)/μ(r₂)` into the nonzero
elements of `K` (`ratioDecode`, `ratioDecode_mk`), and decoding is a bijection
(`ratioDecode_bijective`, `ratioDecodeEquiv`; blueprint Lemma `decode-equiv`, nonzero part).

Surjectivity: for `z ≠ 0` take `t` outside `racl_k {a, z, x₀}`; then `t` and `z t` lie outside
`racl_k {x₀, a}`, so `(j(z t, a), j(t, a))` is a pair of class members decoding to `z`.

`K` is perfect of rank at least five, and completeness over `k̄ ⊆ K̄` (`hcomp`) stays explicit.

**Status:** the corrected geometric ratio quotient decodes bijectively to the nonzero field
elements under explicit perfection, rank-five and ACF J-completeness inputs (#23).
`Interp` adjoins zero and decodes the full carrier bijectively to `K` under the same inputs.
Non-generic totalization, field operations and naturality remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The corrected ratio relation is an equivalence relation on pairs of class members: it is
equality of decoded ratios (`ratioEq_iff`). -/
theorem ratioEq_equivalence [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    Equivalence fun r s : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} ×
        {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} ↦
      RatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1) (s.1.1, s.2.1) := by
  have key : ∀ r s : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} ×
      {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
      RatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1) (s.1.1, s.2.1) ↔
        (jClassEquiv q htr hcomp h₀ r.1 : K) / (jClassEquiv q htr hcomp h₀ r.2 : K) =
          (jClassEquiv q htr hcomp h₀ s.1 : K) / (jClassEquiv q htr hcomp h₀ s.2 : K) :=
    fun r s ↦ ratioEq_iff q htr hcomp h₀ r.1.2 r.2.2 s.1.2 s.2.2
  exact ⟨fun r ↦ (key r r).2 rfl, fun h ↦ (key _ _).2 ((key _ _).1 h).symm,
    fun h₁ h₂ ↦ (key _ _).2 (((key _ _).1 h₁).trans ((key _ _).1 h₂))⟩

/-- The ratio setoid on pairs of members of the class of `j(x₀, a)`: the corrected geometric
relation `RatioEq`. -/
def ratioSetoid [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    Setoid ({w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w} ×
      {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w}) where
  r x y := RatioEq (jTupleOf x₀ a h₀) (x.1.1, x.2.1) (y.1.1, y.2.1)
  iseqv := ratioEq_equivalence q htr hcomp h₀

/-- **Decoding** (blueprint `decode`, nonzero part): the class of a pair `(r₁, r₂)` decodes to the
nonzero element `μ(r₁)/μ(r₂)` of `K`. -/
def ratioDecode [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    Quotient (ratioSetoid q htr hcomp h₀) → Kˣ :=
  Quotient.lift
    (fun r ↦ Units.mk0 ((jClassEquiv q htr hcomp h₀ r.1 : K) / (jClassEquiv q htr hcomp h₀ r.2 : K))
      (div_ne_zero (jClassEquiv_ne_zero q htr hcomp h₀ r.1)
        (jClassEquiv_ne_zero q htr hcomp h₀ r.2)))
    fun r s h ↦ Units.ext ((ratioEq_iff q htr hcomp h₀ r.1.2 r.2.2 s.1.2 s.2.2).1 h)

/-- The decoded value of the class of `(r₁, r₂)` is `μ(r₁)/μ(r₂)`. -/
theorem ratioDecode_mk [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (r₁ r₂ : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w}) :
    (ratioDecode q htr hcomp h₀ (Quotient.mk (ratioSetoid q htr hcomp h₀) (r₁, r₂)) : K) =
      (jClassEquiv q htr hcomp h₀ r₁ : K) / (jClassEquiv q htr hcomp h₀ r₂ : K) :=
  rfl

/-- **Decoding is a bijection onto the nonzero elements** (blueprint Lemma `decode-equiv`, nonzero
part).  Injectivity is the reverse direction of `ratioEq_iff`; for surjectivity, `z ≠ 0` is the
decoded value of `(j(z t, a), j(t, a))` with `t` outside `racl_k {a, z, x₀}`. -/
theorem ratioDecode_bijective [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    Function.Bijective (ratioDecode q htr hcomp h₀) := by
  classical
  refine ⟨fun r s hrs ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨r', rfl⟩ := Quotient.exists_rep r
    obtain ⟨s', rfl⟩ := Quotient.exists_rep s
    have h : (jClassEquiv q htr hcomp h₀ r'.1 : K) / (jClassEquiv q htr hcomp h₀ r'.2 : K) =
        (jClassEquiv q htr hcomp h₀ s'.1 : K) / (jClassEquiv q htr hcomp h₀ s'.2 : K) :=
      congrArg Units.val hrs
    exact Quotient.sound ((ratioEq_iff q htr hcomp h₀ r'.1.2 r'.2.2 s'.1.2 s'.2.2).2 h)
  · -- A fresh `t` over `a, z, x₀`.
    obtain ⟨t, ht⟩ := fresh_three_of_five_le_trdeg htr {a, (z : K), x₀} Finset.card_le_three
    have ht' : t ∉ racl k ({a, (z : K), x₀} : Set K) := by simpa using ht
    have hz : (z : K) ∈ racl k ({a, (z : K), x₀} : Set K) := subset_racl k _ (by simp)
    have hsub : ({x₀, a} : Set K) ⊆ racl k ({a, (z : K), x₀} : Set K) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp),
        Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩
    have ht₁ : t ∉ racl k ({x₀, a} : Set K) := fun h ↦ ht' (racl_le_of_subset_racl hsub h)
    have ht₂ : (z : K) * t ∉ racl k ({x₀, a} : Set K) := fun h ↦
      ht' (mem_racl_of_eq (mul_div_cancel_left₀ t z.ne_zero).symm
        (div_mem (racl_le_of_subset_racl hsub h) hz))
    have T₁ : AlgebraicIndependent k ![x₀, t, a] := AlgebraicIndependent.insert_middle h₀ ht₁
    have T₂ : AlgebraicIndependent k ![x₀, (z : K) * t, a] :=
      AlgebraicIndependent.insert_middle h₀ ht₂
    have ht0 : t ≠ 0 := AlgebraicIndependent.ne_zero (AlgebraicIndependent.pair_one_two T₁) 0
    refine ⟨Quotient.mk (ratioSetoid q htr hcomp h₀)
      (⟨jTupleOf ((z : K) * t) a (AlgebraicIndependent.pair_one_two T₂),
          frobEq_jTupleOf_of_common htr h₀ _⟩,
        ⟨jTupleOf t a (AlgebraicIndependent.pair_one_two T₁),
          frobEq_jTupleOf_of_common htr h₀ _⟩), ?_⟩
    apply Units.ext
    rw [ratioDecode_mk, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]
    exact mul_div_cancel_right₀ (z : K) ht0

/-- **The decoding equivalence** (blueprint Lemma `decode-equiv`, nonzero part): the ratio quotient
of the class of `j(x₀, a)` is in bijection with the nonzero elements of `K`. -/
def ratioDecodeEquiv [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    Quotient (ratioSetoid q htr hcomp h₀) ≃ Kˣ :=
  Equiv.ofBijective _ (ratioDecode_bijective q htr hcomp h₀)

end

end AclGeom
