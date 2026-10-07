/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobLinkSemantic
import AclGeom.Transfer.JDescent

/-!
# The bridge relation forces a Frobenius twist

The forward implication of blueprint Lemma `frobeq-correct`. If `j(x, a)` and `j(y, a')` are related
by `FrobEq`, then `a' = a^{q^s}` or `a = a'^{q^s}`.

* The bridge tuple `w` of `FrobEq` is only geometric. Its semantic coordinates are an explicit
  obligation, as blueprint remark `frob-link-audit` requires. They enter as the local hypothesis
  `hJ : ∀ w, IsJTuple w → JSem w` (`FrobEq.frobenius_of_witnesses`).
* The canonical form discharges `hJ` through `jSem_of_jGeom_of_lift`, keeping its inputs visible:
  the closure `k̄ ⊆ K̄`, `PerfectField K`, rank at least five, and `JCompletenessACF` over
  `k̄ ⊆ K̄`. That arrow needs no `Infinite k`.
* The two direct-link twists compose by `frobenius_twist_trans`, which needs only injectivity of
  Frobenius powers in a field. No perfection or inverse Frobenius is used.

**Status:** the two-link implication is proved under the explicit semantic-bridge hypothesis
or its canonical ACF-completeness form. Unconditional completeness remains open (#23).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

section Twist

variable {K : Type*} [Field K] (q : ℕ) [ExpChar K q]

/-- **Frobenius twists compose.**  If `b` is a Frobenius twist of `a` and `c` one of `b`, each in
either direction, then `c` is a Frobenius twist of `a`.  Mixed directions reduce through
injectivity of `x ↦ x ^ q ^ m`; no inverse Frobenius is needed. -/
theorem frobenius_twist_trans {a b c : K}
    (hab : ∃ s : ℕ, b = a ^ q ^ s ∨ a = b ^ q ^ s)
    (hbc : ∃ t : ℕ, c = b ^ q ^ t ∨ b = c ^ q ^ t) :
    ∃ n : ℕ, c = a ^ q ^ n ∨ a = c ^ q ^ n := by
  have inj : ∀ {m : ℕ} {x y : K}, x ^ q ^ m = y ^ q ^ m → x = y := fun {m x y} h ↦
    iterateFrobenius_inj K q m (by simpa only [iterateFrobenius_def] using h)
  have comp : ∀ (x : K) (i j : ℕ), (x ^ q ^ i) ^ q ^ j = x ^ q ^ (i + j) := fun x i j ↦ by
    rw [← pow_mul, ← pow_add]
  obtain ⟨s, hs | hs⟩ := hab <;> obtain ⟨t, ht | ht⟩ := hbc
  · exact ⟨s + t, Or.inl (by rw [ht, hs, comp])⟩
  · rcases le_total s t with hst | hts
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
      refine ⟨d, Or.inr (inj (m := s) ?_)⟩
      rw [← hs, ht, comp, add_comm]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hts
      refine ⟨d, Or.inl (inj (m := t) ?_)⟩
      rw [← ht, hs, comp, add_comm]
  · rcases le_total s t with hst | hts
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
      exact ⟨d, Or.inl (by rw [ht, hs, comp])⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hts
      exact ⟨d, Or.inr (by rw [hs, ht, comp])⟩
  · exact ⟨t + s, Or.inr (by rw [hs, ht, comp])⟩

end Twist

section Bridge

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The bridge relation forces a Frobenius twist**, given semantic coordinates for geometric
`j`-tuples (`hJ`, the explicit completeness obligation of blueprint remark `frob-link-audit`).
The coordinate hypotheses are the conjunctions inside `JSem`. -/
theorem FrobEq.frobenius_of_witnesses (q : ℕ) [ExpChar k q]
    (hJ : ∀ w : Fin 5 → Point k K, IsJTuple w → JSem w)
    {u v : Fin 5 → Point k K} (h : FrobEq u v) {x a y a' : K}
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s := by
  have : ExpChar K q := expChar_of_injective_algebraMap (algebraMap k K).injective q
  obtain ⟨w, hw, huw, hwv⟩ := h
  obtain ⟨z, b, -, hwb⟩ := hJ w hw
  exact frobenius_twist_trans q (huw.frobenius_of_witnesses q hu hwb)
    (hwv.frobenius_of_witnesses q hwb hv)

/-- **The bridge relation forces a Frobenius twist over a perfect field of rank at least five**,
given completeness of geometric `J` over the algebraically closed pair `k̄ ⊆ K̄`
(`JCompletenessACF`).  The bridge tuple is made semantic by `jSem_of_jGeom_of_lift`. -/
theorem FrobEq.frobenius_of_witnesses_of_completeness [PerfectField K] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {u v : Fin 5 → Point k K} (h : FrobEq u v) {x a y a' : K}
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s :=
  h.frobenius_of_witnesses q
    (fun _ hw ↦ jSem_of_jGeom_of_lift (fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz)
      (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) q htr hcomp hw) hu hv

end Bridge

end AclGeom
