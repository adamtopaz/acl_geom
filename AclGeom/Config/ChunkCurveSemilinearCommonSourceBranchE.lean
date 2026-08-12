/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceE
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranchE

/-! # The selected `e` branch in the inverse-oriented common-source triangle -/

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

/-- Carry the whole selected `e` branch into the middle field of the
inverse-oriented common-source extension. -/
noncomputable def seSelectedRightBranchToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightSemilinearCommonSourceField L hind)).comp
    (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching selected `e` branch map in the extended target field. -/
noncomputable def seSelectedRightBranchToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightSemilinearCommonSourceField L hind)).comp
    ((R.seRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.seSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The extended inverse-oriented `e` right arrow preserves the entire
selected complete branch. -/
theorem seSemilinearCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.seSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
      R.seSelectedRightBranchToSemilinearCommonTargetRingHom L hind := by
  exact
    (R.seRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
        (R.rightSemilinearCommonSourceField L hind)
        (R.seSelectedRightBranchInSelectedGraphRightMiddle
          L hind).toAlgHom.toRingHom

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
