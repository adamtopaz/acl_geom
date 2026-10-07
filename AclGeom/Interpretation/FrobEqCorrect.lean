/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.FrobeniusPowers
import AclGeom.Interpretation.FrobEqForward
import AclGeom.Interpretation.FrobLinkSoundness

/-!
# Semantic correctness of the Frobenius link and the fixed class (conditional)

Blueprint Lemma `frobeq-correct`: for semantic `j`-tuples `u = j(x, a)` and `v = j(y, a')`,
`FrobEq u v` holds exactly when `a'` is a Frobenius twist of `a`.  The two directions have
different inputs, and both stay visible in the statements.

* `FrobEq ⇒` twist (`FrobEq.frobenius_of_witnesses_of_completeness`) needs `K` perfect of rank
  at least five, and completeness of geometric `J` over the algebraically closed pair `k̄ ⊆ K̄`
  (`hcomp`, still open).  The bridge tuple of `FrobEq` is only geometric, and `hcomp` makes it
  semantic.
* twist `⇒ FrobEq` (`frobEq_of_frobenius_twist`) needs only soundness: rank at least five.

`frobEq_iff_frobenius_twist` states the twist with natural exponents in either direction, and
`frobEq_iff_exists_frobeniusZPow` is the blueprint's literal form `∃ n ∈ ℤ, a' = Frob^n a`.

The fixed class (blueprint §genericops): under the same inputs, the `FrobEq` class of `j(x₀, a)`
consists exactly of the tuples `j(x, a)` with the *same* parameter `a`
(`frobEq_jTupleOf_iff`).  A class member `j(y, Frob^n a)` is normalized by applying `Frob^{-n}`
to all of its coordinates, which does not move points (`point_frobeniusZPow`); this uses the
perfection of `K`.

**Status:** the semantic equivalences and fixed-class description are proved under the explicit
ACF J-completeness hypothesis `hcomp` (#23). Unconditional completeness, the class coordinate
bijection, fixed-class operations, ratio semantics and totalization remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Semantic correctness of the Frobenius link** (blueprint Lemma `frobeq-correct`), with natural
Frobenius exponents.  The forward direction uses `PerfectField K`, `htr` and the completeness
hypothesis `hcomp`; the converse uses only `htr`. -/
theorem frobEq_iff_frobenius_twist [PerfectField K] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {u v : Fin 5 → Point k K} {x a y a' : K}
    (hxa : AlgebraicIndependent k ![x, a]) (hya : AlgebraicIndependent k ![y, a'])
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    FrobEq u v ↔ ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s :=
  ⟨fun h ↦ h.frobenius_of_witnesses_of_completeness q htr hcomp hu hv,
    frobEq_of_frobenius_twist htr q hxa hya hu hv⟩

/-- **Semantic correctness of the Frobenius link**, in the blueprint's form
`FrobEq (j x a) (j y a') ↔ ∃ n ∈ ℤ, a' = Frob^n a`, under the same visible inputs as
`frobEq_iff_frobenius_twist`. -/
theorem frobEq_iff_exists_frobeniusZPow [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {u v : Fin 5 → Point k K} {x a y a' : K}
    (hxa : AlgebraicIndependent k ![x, a]) (hya : AlgebraicIndependent k ![y, a'])
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    FrobEq u v ↔ ∃ n : ℤ, a' = frobeniusZPow K q n a := by
  have : ExpChar k q := (algebraMap k K).expChar (algebraMap k K).injective q
  rw [frobEq_iff_frobenius_twist q htr hcomp hxa hya hu hv, exists_frobeniusZPow_iff]

/-- **The fixed Frobenius class** (blueprint §genericops: `J₁ = [j(x₀, a)]_FrobEq` consists of the
`j(x, a)` with `x ∉ acl(a)`), conditional on `hcomp`.  Every tuple Frobenius-equivalent to
`j(x₀, a)` is `j(x, a)` for some `x` independent from the same parameter `a`, and conversely. -/
theorem frobEq_jTupleOf_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {w : Fin 5 → Point k K} :
    FrobEq (jTupleOf x₀ a h₀) w ↔
      ∃ (x : K) (hx : AlgebraicIndependent k ![x, a]), w = jTupleOf x a hx := by
  have : ExpChar k q := (algebraMap k K).expChar (algebraMap k K).injective q
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The other endpoint is semantic, `j(y, b)` with `b = Frob^n a`.
    obtain ⟨y, b, hyb, hw⟩ := jSem_of_jGeom_of_lift
      (fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz)
      (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) q htr hcomp h.target_mem
    obtain ⟨n, hn⟩ := (frobEq_iff_exists_frobeniusZPow q htr hcomp h₀ hyb
      ⟨rfl, rfl, rfl, rfl, rfl⟩ hw).1 h
    -- Normalize by `F = Frob^{-n}`, which fixes every point and sends `b` to `a`.
    obtain ⟨F, hF⟩ : ∃ F : RingAut K, F = frobeniusZPow K q (-n) := ⟨_, rfl⟩
    have hpt : ∀ z : K, point k (F z) = point k z := fun z ↦ by
      rw [hF]
      exact point_frobeniusZPow q (-n) z
    have hFb : F b = a := by
      rw [hF, hn, ← RingAut.mul_apply, frobeniusZPow, frobeniusZPow, ← zpow_add,
        neg_add_cancel, zpow_zero]
      rfl
    have hr : ∀ z : K, racl k ({F z} : Set K) = racl k {z} := fun z ↦
      congrArg Subtype.val (hpt z)
    have hab : racl k ({a} : Set K) = racl k {b} := by
      rw [← hFb]
      exact hr b
    have hind : AlgebraicIndependent k ![F y, a] :=
      (algebraicIndependent_congr_racl fun i ↦ by
        fin_cases i
        · exact (hr y).symm
        · exact hab.symm).1 hyb
    obtain ⟨h0, h1, h2, h3, h4⟩ := hw
    refine ⟨F y, hind, eq_jTupleOf hind ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [h0, hpt]
    · rw [h1, ← hpt (y + b), map_add, hFb]
    · rw [h2, ← hpt (y * b), map_mul, hFb]
    · rw [h3, ← hpt (y + y * b), map_add, map_mul, hFb]
    · rw [h4, ← hFb, hpt]
  · rintro ⟨x, hx, rfl⟩
    exact frobEq_jTupleOf_of_common htr h₀ hx

end AclGeom
