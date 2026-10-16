/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteCover
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The endpoint image can lose the middle function field

Source §8.1 needs to distinguish the joint field of a fiber-product component
from that of its endpoint image. The example is the chain `t², t, t²`. Its
endpoint field is `k(t²)`, properly contained in the joint field `k(t)` in every
characteristic. The input is a genuine transcendental element; no expected
field inequality, correspondence or minimal-prime conclusion is assumed.

Reported before source changes on #5, comment6215313613. The corrected
inequality is already `FiniteCorrespondencePair.compositeBranchField_le_chainField`;
`tensor_compositum_eq_chainField` identifies the compositum with the joint field.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 source clarification).
-/

namespace AclGeom

open IntermediateField

private theorem ratFunc_X_notMem_adjoin_sq (k : Type*) [Field k] :
    (RatFunc.X : RatFunc k) ∉ adjoin k {(RatFunc.X : RatFunc k) ^ 2} := by
  have hdegree : Module.finrank (adjoin k {(RatFunc.X : RatFunc k) ^ 2}) (RatFunc k) = 2 := by
    rw [show (RatFunc.X : RatFunc k) ^ 2 =
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ 2) by simp,
      RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
    simp
  intro hmem
  have htop : adjoin k {(RatFunc.X : RatFunc k) ^ 2} = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X]
    exact adjoin_simple_le_iff.mpr hmem
  rw [htop, IntermediateField.finrank_top] at hdegree
  exact (by decide : (1 : ℕ) ≠ 2) hdegree

private theorem adjoin_sq_lt_of_transcendental
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (ht : Transcendental k t) : adjoin k {t ^ 2} < adjoin k {t} := by
  let f : RatFunc k →ₐ[k] Ω :=
    (adjoin k {t}).val.comp (RatFunc.algEquivOfTranscendental t ht).toAlgHom
  have hfX : f RatFunc.X = t := by
    simp [f]
  have hmap : (adjoin k {(RatFunc.X : RatFunc k) ^ 2}).map f = adjoin k {t ^ 2} := by
    rw [adjoin_map, Set.image_singleton, map_pow, hfX]
  have hnot : t ∉ adjoin k {t ^ 2} := by
    rw [← hmap, ← hfX, map_mem_map]
    exact ratFunc_X_notMem_adjoin_sq k
  refine lt_of_le_of_ne (adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self k t) 2)) ?_
  intro heq
  rw [heq] at hnot
  exact hnot (mem_adjoin_simple_self k t)

/-- The endpoint field of a genuine finite-correspondence composite can be
strictly smaller than the joint field of its shared-middle chain. The example
`(t²,t)` followed by `(t,t²)` works in any characteristic, hence also in the
source's algebraically closed setting. -/
theorem exists_compositeBranchField_lt_chainField
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (ht : Transcendental k t) :
    ∃ (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source),
      (P.comp Q h).branchField < P.chainField Q := by
  have ht0 : t ∉ racl k (∅ : Set Ω) := notMem_racl_empty_of_transcendental ht
  have ht2 : t ^ 2 ∉ racl k (∅ : Set Ω) := by
    intro h
    exact ht0 (racl_le_of_subset_racl (Set.singleton_subset_iff.mpr h)
      (mem_racl_singleton_pow (k := k) (x := t) (by decide : 2 ≠ 0)))
  let P : FiniteCorrespondencePair k Ω :=
    { source := t ^ 2
      target := t
      source_generic := ht2
      target_mem_source := mem_racl_singleton_pow (by decide : 2 ≠ 0)
      source_mem_target := pow_mem (subset_racl k {t} rfl) 2 }
  refine ⟨P, P.swap, rfl, ?_⟩
  change adjoin k {t ^ 2, t ^ 2} < adjoin k {t ^ 2, t, t ^ 2}
  have hchain : adjoin k {t ^ 2, t, t ^ 2} = adjoin k {t} := by
    apply le_antisymm
    · refine adjoin_le_iff.mpr ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨pow_mem (mem_adjoin_simple_self k t) 2,
        mem_adjoin_simple_self k t, pow_mem (mem_adjoin_simple_self k t) 2⟩
    · exact adjoin_simple_le_iff.mpr (subset_adjoin k _ (by simp))
  simpa only [Set.insert_eq_of_mem (Set.mem_singleton _), hchain] using
    adjoin_sq_lt_of_transcendental ht

end AclGeom
