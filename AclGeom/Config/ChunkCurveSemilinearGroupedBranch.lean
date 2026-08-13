/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedBranchE
import AclGeom.Config.ChunkCurveSemilinearGroupedBranchA
import AclGeom.Config.ChunkCurveSemilinearGroupedBranchB
import AclGeom.Config.ChunkCurveSemilinearGroupedBranchC

/-!
# Selected branches in the grouped finite triangles

The four branch-specific modules elaborate independently.  This compatibility
aggregator exposes all four APIs and records their simultaneous coherence.
-/

namespace AclGeom

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- Simultaneously, all four grouped right arrows preserve their complete
selected branches. -/
theorem fourGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.SeGroupedSelectedRightBranchCoherence L hind ∧
      R.SAaGroupedSelectedRightBranchCoherence L hind ∧
      R.SbGroupedSelectedRightBranchCoherence L hind ∧
      R.SAcGroupedSelectedRightBranchCoherence L hind := by
  exact ⟨R.seGrouped_right_comp_selectedRightBranch L hind,
    R.sAaGrouped_right_comp_selectedRightBranch L hind,
    R.sbGrouped_right_comp_selectedRightBranch L hind,
    R.sAcGrouped_right_comp_selectedRightBranch L hind⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
