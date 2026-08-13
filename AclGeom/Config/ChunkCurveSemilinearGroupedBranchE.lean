/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedRestriction

/-!
# The selected e-branch in the grouped finite triangle

The complete selected `e` right branch embeds in the grouped middle and target
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

/-- Include the complete selected `e` branch in the grouped middle field. -/
noncomputable def seSelectedRightBranchToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.seGroupedSourceField L hind)).comp
    (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- Include the image of the complete selected `e` branch in the grouped
target field. -/
noncomputable def seSelectedRightBranchToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.seGroupedSourceField L hind)).comp
    ((R.seSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.seSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The proposition that the grouped `e` right arrow preserves its complete
selected branch.  Naming this expanded equality keeps downstream theorem
types compact in serialized artifacts. -/
def SeGroupedSelectedRightBranchCoherence
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Prop :=
    (R.seGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.seSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.seSelectedRightBranchToGroupedTargetRingHom L hind

/-- The grouped `e` right arrow preserves its complete selected branch. -/
theorem seGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.SeGroupedSelectedRightBranchCoherence L hind := by
  exact (R.seSelectedGraphRightCompositionTriangle L hind)
    |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
      (R.seGroupedSourceField L hind)
      (R.seSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom

/-- The grouped `e` middle anchor factors through the selected branch. -/
theorem seSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seSelectedRightBranchToGroupedMiddleRingHom L hind
        (R.seBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.seBGermCoefficientToGroupedMiddleRingHom L hind z := by
  rfl

/-- The grouped `e` target anchor factors through the selected branch. -/
theorem seSelectedRightBranchToGroupedTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seSelectedRightBranchToGroupedTargetRingHom L hind
        (R.seBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.seBGermCoefficientToGroupedTargetRingHom L hind z := by
  rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
