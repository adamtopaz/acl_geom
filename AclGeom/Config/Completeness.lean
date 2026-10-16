/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Config.GuardedAffineGrid
import AclGeom.Config.Correctness

/-!
# Correctness of geometric configurations over algebraically closed pairs

The guarded Q extraction supplies the remaining input of the established Q′ and J
assembly. Together with soundness, this proves corrected `q-correct`, `qp-correct` and
`j-acf-correct` for every ACF pair of transcendence degree at least five.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Geometric J is complete over every algebraically closed pair of transcendence degree
at least five. The guarded Q chart and multiplication converse are proved internally;
no completeness or chart hypothesis is supplied by the caller. -/
theorem jCompletenessACF [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) : JCompletenessACF k K :=
  jCompletenessACF_of_guardedQCompleteness (ringExpChar k) htr guardedQCompletenessACF

/-- Guarded geometric Q is exactly semantic Q over an algebraically closed pair of
transcendence degree at least five (corrected blueprint `q-correct`). -/
theorem qGeom_and_ne_iff_qSem_of_isAlgClosed [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {P D Y I : Point k K} :
    QGeom P D Y I ∧ I ≠ D ∧ I ≠ P ↔ QSem P D Y I :=
  qGeom_and_ne_iff_qSem_of_five_le_trdeg htr guardedQCompletenessACF

/-- Geometric Q′ is exactly semantic Q′ over an algebraically closed pair of
transcendence degree at least five (blueprint `qp-correct`). -/
theorem q'Geom_iff_q'Sem_of_isAlgClosed [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X Y S E : Point k K} :
    Q'Geom X Y S E ↔ Q'Sem X Y S E :=
  ⟨q'Sem_of_q'Geom_of_guardedQCompleteness htr guardedQCompletenessACF,
    q'Geom_of_q'Sem_of_five_le_trdeg htr⟩

/-- Geometric J is exactly semantic J over an algebraically closed pair of
transcendence degree at least five (blueprint `j-acf-correct`). -/
theorem jGeom_iff_jSem_of_isAlgClosed [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X : Fin 5 → Point k K} :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) ↔ JSem X :=
  ⟨jCompletenessACF htr X, jGeom_of_jSem_of_five_le_trdeg htr⟩

end AclGeom
