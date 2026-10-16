/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Config.Completeness
import AclGeom.Transfer.JDescent

/-!
# Correctness of `J` over arbitrary perfect fields

Blueprint Thm `j-descent` (T4). Let `K` be perfect with `trdeg_k K ≥ 5`, let `ι : K →ₐ[k] Ω`
embed `K` into an algebraically closed field, and let `k̄ = algebraicClosure k Ω`. For a
five-tuple of points of `K/k` the following are equivalent (`jDescent_tfae`):

1. it is semantically `j(x, a)` in `K`;
2. its lift (`liftTuple`) is semantically `j(x, a)` in `Ω/k̄`;
3. its lift satisfies the geometric `J` predicate over `Ω/k̄`;
4. it satisfies the geometric `J` predicate over `K/k`.

The arrow `(3) ⇒ (2)` is `jCompletenessACF`, at the rank-five bound transported to `k̄ ⊆ Ω`
(`five_le_trdeg_algebraicClosure_of_algHom`). The other arrows are those of
`Transfer.JDescent`. Consequently geometric and semantic `J` agree over `K/k`
(`jGeom_iff_jSem_of_perfectField`).

The blueprint also assumes `k` relatively algebraically closed in `K`; the Lean statements do
not need it.

**Status:** proved.
-/

namespace AclGeom

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]

/-- The algebraic closure `k̄` of `k` in an algebraically closed field `Ω` containing `K` has
codimension at least five when `K/k` has transcendence degree at least five. -/
theorem five_le_trdeg_algebraicClosure_of_algHom (ι : K →ₐ[k] Ω)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    (5 : Cardinal) ≤ Algebra.trdeg (↥(algebraicClosure k Ω)) Ω := by
  have hΩ := five_le_trdeg_of_algHom ι htr
  have hadd := lift_trdeg_add_eq k (↥(algebraicClosure k Ω)) Ω
  rw [trdeg_eq_zero, Cardinal.lift_zero, zero_add, Cardinal.lift_inj] at hadd
  rwa [hadd]

/-- The lift of a five-tuple of points of `K/k` to `Ω/k̄`, where `k̄` is the algebraic closure of
`k` in `Ω`. -/
noncomputable def liftTuple (ι : K →ₐ[k] Ω) (X : Fin 5 → Point k K) :
    Fin 5 → Point (↥(algebraicClosure k Ω)) Ω :=
  liftPoint (fun _ hz ↦ (mem_algebraicClosure_iff).1 hz) ι ∘ X

/-- **Descent and arbitrary-field correctness of `J`** (blueprint Thm `j-descent`): for perfect
`K` of transcendence degree at least five over `k`, an embedding into an algebraically closed
`Ω` and the algebraic closure `k̄` of `k` in `Ω`, the four conditions are equivalent. -/
theorem jDescent_tfae [IsAlgClosed Ω] [PerfectField K] (ι : K →ₐ[k] Ω)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (X : Fin 5 → Point k K) :
    List.TFAE [JSem X, JSem (liftTuple ι X),
      JGeom (liftTuple ι X 0) (liftTuple ι X 1) (liftTuple ι X 2) (liftTuple ι X 3)
        (liftTuple ι X 4),
      JGeom (X 0) (X 1) (X 2) (X 3) (X 4)] := by
  have halg : ∀ y ∈ algebraicClosure k Ω, IsAlgebraic k y := fun _ hz ↦
    (mem_algebraicClosure_iff).1 hz
  have : IsAlgClosed ↥(algebraicClosure k Ω) := IsAlgClosure.isAlgClosed k
  have hcomp : JCompletenessACF (↥(algebraicClosure k Ω)) Ω :=
    jCompletenessACF (five_le_trdeg_algebraicClosure_of_algHom ι htr)
  tfae_have 1 → 2 := jSem_lift_of_jSem halg ι
  tfae_have 2 → 1 := jSem_of_jSem_lift halg ι (ringExpChar k) htr
  tfae_have 3 → 2 := hcomp _
  tfae_have 4 → 3 := jGeom_lift_of_jGeom halg ι
  tfae_have 1 → 4 := jGeom_of_jSem_of_five_le_trdeg htr
  tfae_finish

/-- **Geometric and semantic `J` agree over every perfect field of transcendence degree at
least five** (blueprint Thm `j-descent`, consequence). -/
theorem jGeom_iff_jSem_of_perfectField [PerfectField K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X : Fin 5 → Point k K} :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) ↔ JSem X :=
  (jDescent_tfae (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) htr X).out 4 1

end AclGeom
