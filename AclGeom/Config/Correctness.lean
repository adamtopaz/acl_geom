/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.AffineGrid
import AclGeom.Config.MulDiagramCheck
import AclGeom.Correspondence.JRigidity
import AclGeom.Transfer.OneQuantifier
import AclGeom.Transfer.Transcendence

/-!
# Correctness of the geometric configurations

Rank-five assembly of the configuration layer (blueprint Thms q-correct,
qp-correct, j-acf-correct, j-descent).  Proved here: the soundness arrows
`QSem → QGeom`, `Q'Sem → Q'Geom` and `JSem → JGeom` under `trdeg ≥ 5` over an
infinite base, and, over algebraically closed fields, the `Q` equivalence
conditional on the open witness-level completeness `QCompletenessACF` (see
`Config/AffineGrid.lean`, issue #22).

Not yet formalized: ACF completeness of `Q′` (converse of Lemma mul-diagram)
and `J`, the geometric projection identities, the removal of `[Infinite k]`,
and the full four-way J descent theorem (issue #7). The arbitrary-field Q/Q′ equivalence
consequences have been refuted mathematically (issue #25); their Lean
refutations remain open.

**Status:** in progress (M4–M5).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Rank-five soundness of `Q`: the blueprint's transcendence-degree
hypothesis supplies the fresh elements needed by the explicit table. -/
theorem qGeom_of_qSem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {P D Y I : Point k K} (h : QSem P D Y I) :
    QGeom P D Y I :=
  qGeom_of_qSem (fresh_four_of_five_le_trdeg htr) h

/-- Rank-five soundness of `Q′`. -/
theorem q'Geom_of_q'Sem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X Y Z W : Point k K} (h : Q'Sem X Y Z W) :
    Q'Geom X Y Z W :=
  q'Geom_of_q'Sem (fresh_four_of_five_le_trdeg htr) h

/-- **The `(1) ⇒ (4)` soundness arrow of blueprint Theorem
`j-descent`**: a semantic j-tuple is geometric under the stated rank-five
hypothesis, with no fresh-element oracle left in the public statement. -/
theorem jGeom_of_jSem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X : Fin 5 → Point k K} (h : JSem X) :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) :=
  jGeom_of_jSem (fresh_four_of_five_le_trdeg htr) h

/-- Conditional rank-five correctness of `Q` over algebraically closed
fields, given the open witness-level completeness `QCompletenessACF` (the
acceptance boundary for the corrected blueprint Lemma 8.5). No arbitrary-field
equivalence follows: the blueprint's proposed Q/Q′ consequences are refuted
mathematically in issue #25. -/
theorem qGeom_iff_qSem_of_five_le_trdeg [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcompl : QCompletenessACF k K)
    {P D Y I : Point k K} :
    QGeom P D Y I ↔ QSem P D Y I :=
  qGeom_iff_qSem hcompl (fresh_four_of_five_le_trdeg htr)

end

end AclGeom
