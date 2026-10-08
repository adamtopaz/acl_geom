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

Rank-five soundness `QSem → QGeom`, `Q'Sem → Q'Geom` and `JSem → JGeom` holds over any
base field. Over algebraically closed fields, guarded `Q` correctness and its guarded
geometric projection to `J` are conditional on `GuardedQCompletenessACF` (#27).

Unguarded `QCompletenessACF`, `AffineGridExtraction` and geometric `Q` projection are refuted
by the actual degenerate `Psi` witness in Counterexamples.QDegenerate, even for ACF pairs
with five independent elements. ACF `Q′` completeness (multiplication-diagram converse),
`J` completeness and unconditional four-way `J` descent remain open. The existing conditional
public target still uses the unchanged `JCompletenessACF`. Counterexamples.QRefutation retains
the characteristic-zero arbitrary-field `Q′` refutation and the earlier `Q` example (#25).

**Status:** in progress (M4–M5).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Rank-five soundness of `Q`: the blueprint's transcendence-degree
hypothesis supplies the fresh elements needed by the explicit table. -/
theorem qGeom_of_qSem_of_five_le_trdeg
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {P D Y I : Point k K} (h : QSem P D Y I) :
    QGeom P D Y I :=
  qGeom_of_qSem (fresh_four_of_five_le_trdeg htr) h

/-- Rank-five soundness of `Q′`. -/
theorem q'Geom_of_q'Sem_of_five_le_trdeg
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X Y Z W : Point k K} (h : Q'Sem X Y Z W) :
    Q'Geom X Y Z W :=
  q'Geom_of_q'Sem (fresh_four_of_five_le_trdeg htr) h

/-- **The `(1) ⇒ (4)` soundness arrow of blueprint Theorem
`j-descent`**: a semantic j-tuple is geometric under the stated rank-five
hypothesis, with no fresh-element oracle left in the public statement. -/
theorem jGeom_of_jSem_of_five_le_trdeg
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X : Fin 5 → Point k K} (h : JSem X) :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) :=
  jGeom_of_jSem (fresh_four_of_five_le_trdeg htr) h

/-- Conditional rank-five **guarded** correctness of `Q` over ACF pairs (#27).
`GuardedQCompletenessACF` is open; the former unguarded wrapper is superseded because its
completeness input is refuted even for ACF pairs with five independent elements. -/
theorem qGeom_and_ne_iff_qSem_of_five_le_trdeg [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcompl : GuardedQCompletenessACF k K)
    {P D Y I : Point k K} :
    QGeom P D Y I ∧ I ≠ D ∧ I ≠ P ↔ QSem P D Y I :=
  qGeom_and_ne_iff_qSem hcompl (fresh_four_of_five_le_trdeg htr)

/-- Conditional **guarded** geometric projection identity (#27): semantic projection and
proved soundness supply `J`; the reverse guard comes from actual multiplication distinctness.
The unguarded projection is refuted by `not_forall_qGeom_imp_exists_jGeom_of_five_indep`. -/
theorem qGeom_and_ne_iff_exists_jGeom [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcompl : GuardedQCompletenessACF k K)
    {X Q R A : Point k K} :
    QGeom X Q R A ∧ A ≠ Q ∧ A ≠ X ↔ ∃ P : Point k K, JGeom X P Q R A := by
  constructor
  · intro h
    obtain ⟨P, hP⟩ := qSem_iff_exists_jSem.1 (qSem_of_qGeom_of_ne hcompl h.1 h.2.1 h.2.2)
    exact ⟨P, jGeom_of_jSem_of_five_le_trdeg htr hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨hP.1, hP.2.1.ne.symm, hP.2.1.snd_ne_fst⟩

end

end AclGeom
