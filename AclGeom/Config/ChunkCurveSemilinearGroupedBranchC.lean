/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedRestriction

/-!
# The selected c-branch in the grouped finite triangle

The complete genuine-`c` right branch embeds in the grouped middle and target
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

/-- Include the complete genuine-`c` branch in the grouped middle field. -/
noncomputable def sAcSelectedRightBranchToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcGroupedSourceField L hind)).comp
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
      L hind).toAlgHom.toRingHom

/-- Include the image of the complete genuine-`c` branch in the grouped
target field. -/
noncomputable def sAcSelectedRightBranchToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcGroupedSourceField L hind)).comp
    ((R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The proposition that the grouped `c` right arrow preserves its complete
selected branch.  Naming this expanded equality keeps downstream theorem
types compact in serialized artifacts. -/
def SAcGroupedSelectedRightBranchCoherence
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Prop :=
    (R.sAcGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sAcSelectedRightBranchToGroupedTargetRingHom L hind

/-- The grouped `c` right arrow preserves its complete selected branch. -/
theorem sAcGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.SAcGroupedSelectedRightBranchCoherence L hind := by
  exact (R.sAcRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
      (R.sAcGroupedSourceField L hind)
      (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom

/-- The grouped `c` middle anchor factors through the selected branch. -/
theorem sAcSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcSelectedRightBranchToGroupedMiddleRingHom L hind
        (R.sAcBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAcBGermCoefficientToGroupedMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAcSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcGroupedSourceField L hind)) h

/-- The grouped `c` target anchor factors through the selected branch. -/
theorem sAcSelectedRightBranchToGroupedTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcSelectedRightBranchToGroupedTargetRingHom L hind
        (R.sAcBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAcBGermCoefficientToGroupedTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAcSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcGroupedSourceField L hind)).comp
      (R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom) h

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
