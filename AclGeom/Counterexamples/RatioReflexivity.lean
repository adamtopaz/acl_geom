/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Counterexamples.GenericArithmetic
import AclGeom.Interpretation.FrobEqCorrect
import AclGeom.Transfer.JCorrectness

/-!
# Reflexivity of the blueprint's literal ratio relation

The sentence after blueprint Lemma `ratio-semantics` separately asserts reflexivity,
symmetry and transitivity of the literal ratio relation. This module proves its
reflexivity on pairs in the class of a semantic base tuple, over arbitrary base fields
and perfect ambient fields at rank five. Both class representatives are normalized
using the internally supplied ACF completeness theorem; a single fresh multiplier
then gives the two generic products and witnesses the relation to itself.

The proof supplies completeness and the characteristic exponent internally. There is
no relatively algebraically closed base or infinite-base hypothesis. Symmetry is
proved in `GenericArithmetic`; transitivity is refuted in `RatioTransitivity`, so no
setoid for the literal relation follows from these separate positive laws.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** literal ratio reflexivity proved under perfection and rank five (#8, #23).
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The literal ratio relation is reflexive** on pairs in the Frobenius class of a
semantic base tuple (blueprint ratio section, after Lemma `ratio-semantics`). Perfect
ambient fields at rank five suffice over arbitrary bases. The characteristic exponent
and both semantic normalizations are supplied internally; no completeness input or
relatively algebraically closed base is required. -/
theorem blueprintRatioEq_refl [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (r : {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
      {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u}) :
    BlueprintRatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1) (r.1.1, r.2.1) := by
  classical
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K)))
      (AlgebraicClosure K) := jCompletenessACF (five_le_trdeg_algebraicClosure htr)
  rcases r with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  obtain ⟨x, hx, rfl⟩ := (frobEq_jTupleOf_iff (ringExpChar K) htr hcomp h₀).1 hu
  obtain ⟨y, hy, rfl⟩ := (frobEq_jTupleOf_iff (ringExpChar K) htr hcomp h₀).1 hv
  obtain ⟨t, ht⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  have ht' : t ∉ racl k ({x, y, a} : Set K) := by simpa using ht
  have htx : t ∉ racl k ({x, a} : Set K) := fun h ↦ ht' (racl_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.2
      (Set.mem_insert_of_mem y (Set.mem_singleton a)))) h)
  have hty : t ∉ racl k ({y, a} : Set K) := fun h ↦ ht' (racl_mono (Set.subset_insert x _) h)
  have T₁ : AlgebraicIndependent k ![x, t, a] := AlgebraicIndependent.insert_middle hx htx
  have T₂ : AlgebraicIndependent k ![y, t, a] := AlgebraicIndependent.insert_middle hy hty
  obtain ⟨d₁, hd₁, M₁⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf x a hx) (jTupleOf t a (AlgebraicIndependent.pair_one_two T₁))
        (jTupleOf d a hd) := by
    exact ⟨_, _, blueprintJMul_kappa T₁ htr (one_ne_zero : (1 : k) ≠ 0)⟩
  obtain ⟨d₂, hd₂, M₂⟩ : ∃ (d : K) (hd : AlgebraicIndependent k ![d, a]),
      BlueprintJMul (jTupleOf y a hy) (jTupleOf t a (AlgebraicIndependent.pair_one_two T₁))
        (jTupleOf d a hd) := by
    exact ⟨_, _, blueprintJMul_kappa T₂ htr (one_ne_zero : (1 : k) ≠ 0)⟩
  have hC : ∀ (p : K) (hp : AlgebraicIndependent k ![p, a]),
      FrobEq (jTupleOf x₀ a h₀) (jTupleOf p a hp) := fun _ hp ↦
    frobEq_jTupleOf_of_common htr h₀ hp
  exact ⟨_, _, _, _, hC t _, hC t _, hC d₁ hd₁, hC d₂ hd₂, M₁, M₂, M₁, M₂⟩

end AclGeom
