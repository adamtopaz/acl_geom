/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedRestriction

/-!
# The selected b-branch in the grouped finite triangle

The complete selected `b` right branch embeds in the grouped middle and target
fields, and the grouped right arrow preserves it exactly.
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

/-- Include the complete selected `b` branch in the grouped middle field. -/
noncomputable def sbSelectedRightBranchToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbGroupedSourceField L hind)).comp
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- Include the image of the complete selected `b` branch in the grouped
target field. -/
noncomputable def sbSelectedRightBranchToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbGroupedSourceField L hind)).comp
    ((R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sbSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The proposition that the grouped `b` right arrow preserves its complete
selected branch.  Naming this expanded equality keeps downstream theorem
types compact in serialized artifacts. -/
def SbGroupedSelectedRightBranchCoherence
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Prop :=
    (R.sbGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sbSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sbSelectedRightBranchToGroupedTargetRingHom L hind

/-- The grouped `b` right arrow preserves its complete selected branch. -/
theorem sbGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.SbGroupedSelectedRightBranchCoherence L hind := by
  exact (R.sbRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
      (R.sbGroupedSourceField L hind)
      (R.sbSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom

/-- The grouped `b` middle anchor factors through the selected branch. -/
theorem sbSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbSelectedRightBranchToGroupedMiddleRingHom L hind
        (R.sbBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sbBGermCoefficientToGroupedMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sbSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbGroupedSourceField L hind)) h

/-- The grouped `b` target anchor factors through the selected branch. -/
theorem sbSelectedRightBranchToGroupedTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbSelectedRightBranchToGroupedTargetRingHom L hind
        (R.sbBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sbBGermCoefficientToGroupedTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sbSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbGroupedSourceField L hind)).comp
      (R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom) h

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
