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

The equivalence of geometric and semantic Q, Q′, J: over algebraically closed
fields (blueprint Thms q-correct, qp-correct, j-acf-correct, using the witness
table 7.1 and the affine grid extraction), then over arbitrary perfect
relatively algebraically closed extensions by the one-quantifier transfer and
descent (Thm j-descent). Also the projection identities.

**Status:** in progress (M4–M5): rank-five soundness is assembled; the
completeness direction is conditional on `AffineGridExtraction`.

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

/-- Conditional rank-five correctness of `Q` at the exact remaining M4
boundary.  A proof of affine-grid extraction turns the assembled soundness
and completeness implications into the desired equivalence. -/
theorem qGeom_iff_qSem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hextract : AffineGridExtraction k K)
    {P D Y I : Point k K} :
    QGeom P D Y I ↔ QSem P D Y I :=
  qGeom_iff_qSem hextract (fresh_four_of_five_le_trdeg htr)

end

end AclGeom
