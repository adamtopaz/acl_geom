/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.AtomClause

/-!
# The soundness witness satisfies Ψ

The assembly of blueprint Theorem q-correct, soundness direction, at the
witness level: for any five algebraically independent elements
`a, b, c, d, x` of `K` over an infinite base `k`, the table-7.1 witness
`qWitness` satisfies all seven clauses of `Ψ`. Consequently the semantic
quadruple `([b], [ax], [ax+b], [ax/b])` — that is,
`([u], [v], [u+v], [u/v])` for `u = b`, `v = ax` — is in the geometric
relation `QGeom`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness assembly).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/-- **The witness satisfies Ψ** (blueprint Thm q-correct, soundness
direction, witness verification): all seven clauses hold at the
table-7.1 points. -/
theorem qWitness_psi [Infinite k] : (qWitness hind).Psi where
  rank_ABC := qWitness_rank_ABC hind
  rank_AB := qWitness_rank_AB hind
  rank_BC := qWitness_rank_BC hind
  rank_AC := qWitness_rank_AC hind
  X_le := qWitness_X_le hind
  Z_le := qWitness_Z_le hind
  X_notLe := qWitness_X_notLe hind
  Y_notLe := qWitness_Y_notLe hind
  Z_notLe := qWitness_Z_notLe hind
  X_free := qWitness_X_free hind
  Z_freeB := qWitness_Z_freeB hind
  Z_freeC := qWitness_Z_freeC hind
  S_le := qWitness_S_le hind
  T_le := qWitness_T_le hind
  U_le := qWitness_U_le hind
  rank_STU := qWitness_rank_STU hind
  quad := qWitness_quad hind
  meet_D := qWitness_meet_D hind
  meet_E := qWitness_meet_E hind
  meet_F := qWitness_meet_F hind
  meet_G := qWitness_meet_G hind
  meet_I := qWitness_meet_I hind
  meet_H := qWitness_meet_H hind
  meet_R := qWitness_meet_R hind

/-- The geometric `Q` holds at the four free outputs of the witness:
`([b], [ax], [ax+b], [ax/b])`. -/
theorem qGeom_of_table [Infinite k] :
    QGeom (Point.mk' k b (qtable_b_notMem_bot hind))
      (Point.mk' k (a * x) (qtable_mul_ax_notMem_bot hind))
      (Point.mk' k (a * x + b) (qtable_Y_notMem_bot hind))
      (Point.mk' k (a * x / b) (qtable_axb_notMem_bot hind)) :=
  ⟨qWitness hind, qWitness_psi hind, rfl, rfl, rfl, rfl⟩

end

end AclGeom
