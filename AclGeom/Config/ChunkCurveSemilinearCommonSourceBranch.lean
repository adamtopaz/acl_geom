/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchE
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchA
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchB
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchC

/-!
# Selected branches in the four inverse-oriented common-source triangles

The complete selected right branches embed in the four extended middle and
target fields, and each extended right arrow preserves its branch by an
exact ring-hom square.
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

/-- Simultaneously, all four inverse-oriented common-source extensions
preserve their entire selected complete right branches. -/
theorem fourSemilinearCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
          (R.seSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
        R.seSelectedRightBranchToSemilinearCommonTargetRingHom L hind ∧
      (R.sAaRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
          (R.sAaSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
        R.sAaSelectedRightBranchToSemilinearCommonTargetRingHom L hind ∧
      (R.sbRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
          (R.sbSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
        R.sbSelectedRightBranchToSemilinearCommonTargetRingHom L hind ∧
      (R.sAcRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
          (R.sAcSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
        R.sAcSelectedRightBranchToSemilinearCommonTargetRingHom L hind := by
  exact ⟨R.seSemilinearCommon_right_comp_selectedRightBranch L hind,
    R.sAaSemilinearCommon_right_comp_selectedRightBranch L hind,
    R.sbSemilinearCommon_right_comp_selectedRightBranch L hind,
    R.sAcSemilinearCommon_right_comp_selectedRightBranch L hind⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
