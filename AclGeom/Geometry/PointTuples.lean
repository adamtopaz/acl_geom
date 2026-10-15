/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Rank

/-!
# Point representatives and finite tuple ranks

These identities translate between representatives, joins of closed fields and tuple rank.
The rank-two Ψ input and rank-one partial-quadrangle input use the same translations.

**Status:** proved (#12).
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The one-element tuple representing a point has that point as its relative closure. -/
theorem Point.racl_repTuple (P : Point k K) :
    racl k (range (fun _ : Fin 1 ↦ P.rep)) = P.1.1 := by
  rw [range_const]
  exact congrArg Subtype.val P.point_rep

/-- Joining closed fields corresponds to taking the closure of the union of generators. -/
theorem ClosedIF.racl_union_eq_sup {S T : Set K} {E F : ClosedIF k K}
    (hS : racl k S = E.1) (hT : racl k T = F.1) : racl k (S ∪ T) = (E ⊔ F).1 := by
  rw [ClosedIF.coe_sup]
  change racl k (S ∪ T) = racl k ((E.1 : Set K) ∪ (F.1 : Set K))
  rw [← hS, ← hT, racl_union_left, racl_union_right]

/-- A tuple spanning a closed field of rank `n` has tuple rank `n`. -/
theorem ClosedIF.erk_eq_of_racl_eq {S : Set K} {E : ClosedIF k K} {n : ℕ}
    (hS : racl k S = E.1) (hE : RankEq n E) : erk k ∅ S = n := by
  rw [← erk_racl k ∅ S, empty_union, hS]
  change erk k ∅ (E : Set K) = n
  rw [erk_empty_eq, rankEq_iff_eRk.1 hE]

end

end AclGeom
