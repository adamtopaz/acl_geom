/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedRestriction

/-!
# The selected a-branch in the grouped finite triangle

The complete selected `a` right branch embeds in the grouped middle and target
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

/-- Include the complete selected `a` branch in the grouped middle field. -/
noncomputable def sAaSelectedRightBranchToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaGroupedSourceField L hind)).comp
    (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
      L hind).toAlgHom.toRingHom

/-- Include the image of the complete selected `a` branch in the grouped
target field. -/
noncomputable def sAaSelectedRightBranchToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaGroupedSourceField L hind)).comp
    ((R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The proposition that the grouped `a` right arrow preserves its complete
selected branch.  Naming this expanded equality keeps downstream theorem
types compact in serialized artifacts. -/
def SAaGroupedSelectedRightBranchCoherence
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Prop :=
    (R.sAaGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sAaSelectedRightBranchToGroupedTargetRingHom L hind

/-- The grouped `a` right arrow preserves its complete selected branch. -/
theorem sAaGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.SAaGroupedSelectedRightBranchCoherence L hind := by
  exact (R.sAaRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
      (R.sAaGroupedSourceField L hind)
      (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom

/-- The grouped `a` middle anchor factors through the selected branch. -/
theorem sAaSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaSelectedRightBranchToGroupedMiddleRingHom L hind
        (R.sAaBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAaBGermCoefficientToGroupedMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAaSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaGroupedSourceField L hind)) h

/-- The grouped `a` target anchor factors through the selected branch. -/
theorem sAaSelectedRightBranchToGroupedTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaSelectedRightBranchToGroupedTargetRingHom L hind
        (R.sAaBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAaBGermCoefficientToGroupedTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAaSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaGroupedSourceField L hind)).comp
      (R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom) h

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
