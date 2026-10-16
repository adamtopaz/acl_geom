/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Main
import AclGeom.Test.RationalFunctionField
import AclGeom.Reconstruct.Kernel
import AclGeom.Transfer.Transcendence

/-!
# Validation: Frobenius iterates and rational function fields

Two items of the blueprint's validation suite that need new statements:

* TEST-2: in positive characteristic, distinct integral Frobenius iterates are distinct
  automorphisms of a chosen perfection as soon as the transcendence degree is positive
  (`Perfection.frobZPow_injective`). That every iterate induces the identity of the
  closed-subfield lattice when the base is relatively algebraically closed is
  `Perfection.inducedIso_frobZPow`.
* TEST-8: the reconstruction theorem for rational function fields over an arbitrary base
  (`reconstruction_ratFn`). The base `k` is relatively algebraically closed in
  `k(t₁, …, tₙ)` (`isRAC_bot_ratFn`), and `trdeg_k k(t₁, …, tₙ) = n` (`trdeg_ratFn`). Any
  chosen perfections may be used.

**Status:** proved.
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **TEST-2**: in positive characteristic and positive transcendence degree, distinct integral
Frobenius iterates of a chosen perfection are distinct. -/
theorem frobZPow_injective (π : Perfection K) (hp : π.p ≠ 1)
    (htr : 0 < Algebra.trdeg k K) : Function.Injective π.frobZPow := by
  have hpos : 0 < Algebra.trdeg (π.basePerf k) π.carrier :=
    Cardinal.lift_lt.1 ((Cardinal.lift_lt.2 htr).trans_le
      (lift_trdeg_le_of_orderIso (π.latticeIso k)))
  obtain ⟨z, hz⟩ := exists_notMem_racl_of_mk_lt_trdeg (k := π.basePerf k)
    (∅ : Set π.carrier) (by simpa using hpos)
  exact fun m n h ↦ frobeniusZPow_injective (k := π.basePerf k) π.p hp hz h

end Perfection

namespace Test

variable (k : Type*) [Field k] (n : ℕ)

/-- The base is relatively algebraically closed in the rational function field. -/
theorem isRAC_bot_ratFn : IsRAC (⊥ : IntermediateField k (RatFn k n)) := by
  have hbot : (⊥ : ClosedIF k (RatFn k n)).1 = ⊥ := by
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    have hxalg : IsAlgebraic k x := ClosedIF.mem_bot_iff.1 (ClosedIF.mem_val.1 hx)
    obtain ⟨c, hc⟩ :=
      mem_range_algebraMap_of_isAlgebraic_fractionRing (F := k) (σ := Fin n) hxalg
    exact IntermediateField.mem_bot.2 ⟨c, hc⟩
  rw [← hbot]
  exact (⊥ : ClosedIF k (RatFn k n)).2

/-- The rational function field in `n` variables has transcendence degree `n`. -/
theorem trdeg_ratFn : Algebra.trdeg k (RatFn k n) = n := by
  have hb := (isTranscendenceBasis_iff_racl_range_eq_top (algebraicIndependent_t k n)).2
    (racl_range_t k n)
  simpa using hb.lift_cardinalMk_eq_trdeg.symm

end Test

/-- **TEST-8**: the reconstruction theorem for rational function fields. For `n ≥ 5`, an order
isomorphism of the closed-subfield lattices of `k(t₁, …, tₙ)/k` and `l(s₁, …, s_m)/l`, over
arbitrary fields `k` and `l`, forces `m = n`. It is induced by a compatible isomorphism of any
chosen perfections, unique up to integral Frobenius twists. -/
theorem reconstruction_ratFn {k l : Type*} [Field k] [Field l] {n m : ℕ} (hn : 5 ≤ n)
    (π : Perfection (Test.RatFn k n)) (ρ : Perfection (Test.RatFn l m))
    (φ : ClosedIF k (Test.RatFn k n) ≃o ClosedIF l (Test.RatFn l m)) :
    n = m ∧ ∃ Φ : π.carrier ≃+* ρ.carrier,
      CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ ∧ Reconstructs π ρ φ Φ ∧
        ∀ Ψ : π.carrier ≃+* ρ.carrier,
          Reconstructs π ρ φ Ψ ↔ ∃ n : ℤ, Ψ = Φ.trans (ρ.frobZPow n) := by
  have htr : (5 : Cardinal) ≤ Algebra.trdeg k (Test.RatFn k n) := by
    rw [Test.trdeg_ratFn]
    exact_mod_cast hn
  obtain ⟨hrank, Φ, hΦ, h, -, hfib, -⟩ :=
    reconstruction_target π ρ (Test.isRAC_bot_ratFn k n) (Test.isRAC_bot_ratFn l m) htr φ
  refine ⟨?_, Φ, hΦ, h, hfib⟩
  rw [Test.trdeg_ratFn, Test.trdeg_ratFn] at hrank
  simpa using hrank

end

end AclGeom
