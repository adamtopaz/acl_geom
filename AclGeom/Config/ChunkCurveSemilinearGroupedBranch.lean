/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedRestriction

/-!
# Selected branches in the grouped finite triangles

The complete selected right branches embed in the grouped middle and target
fields.  Every grouped right arrow preserves its branch exactly, and the
intrinsic middle and target anchors factor pointwise through these branch
embeddings.  This connects the grouped source restrictions to the concrete
normalized branches that the final common charts must retain.
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

/-- The grouped `e` right arrow preserves its complete selected branch. -/
theorem seGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.seSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.seSelectedRightBranchToGroupedTargetRingHom L hind := by
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

/-- The grouped `a` right arrow preserves its complete selected branch. -/
theorem sAaGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sAaSelectedRightBranchToGroupedTargetRingHom L hind := by
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

/-- The grouped `b` right arrow preserves its complete selected branch. -/
theorem sbGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sbSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sbSelectedRightBranchToGroupedTargetRingHom L hind := by
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

/-- The grouped `c` right arrow preserves its complete selected branch. -/
theorem sAcGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcSelectedRightBranchToGroupedMiddleRingHom L hind) =
      R.sAcSelectedRightBranchToGroupedTargetRingHom L hind := by
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

/-- Simultaneously, all four grouped right arrows preserve their complete
selected branches. -/
theorem fourGrouped_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seGroupedCompositionTriangle L hind).right.toRingHom.comp
          (R.seSelectedRightBranchToGroupedMiddleRingHom L hind) =
        R.seSelectedRightBranchToGroupedTargetRingHom L hind ∧
      (R.sAaGroupedCompositionTriangle L hind).right.toRingHom.comp
          (R.sAaSelectedRightBranchToGroupedMiddleRingHom L hind) =
        R.sAaSelectedRightBranchToGroupedTargetRingHom L hind ∧
      (R.sbGroupedCompositionTriangle L hind).right.toRingHom.comp
          (R.sbSelectedRightBranchToGroupedMiddleRingHom L hind) =
        R.sbSelectedRightBranchToGroupedTargetRingHom L hind ∧
      (R.sAcGroupedCompositionTriangle L hind).right.toRingHom.comp
          (R.sAcSelectedRightBranchToGroupedMiddleRingHom L hind) =
        R.sAcSelectedRightBranchToGroupedTargetRingHom L hind := by
  exact ⟨R.seGrouped_right_comp_selectedRightBranch L hind,
    R.sAaGrouped_right_comp_selectedRightBranch L hind,
    R.sbGrouped_right_comp_selectedRightBranch L hind,
    R.sAcGrouped_right_comp_selectedRightBranch L hind⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
