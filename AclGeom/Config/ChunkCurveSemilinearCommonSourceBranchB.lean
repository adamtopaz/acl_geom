/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceB
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranchB

/-! # The selected `b` branch in the inverse-oriented common-source triangle -/

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

/-- Carry the whole selected `b` branch into the middle field of the
inverse-oriented common-source extension. -/
noncomputable def sbSelectedRightBranchToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbRightSemilinearCommonSourceField L hind)).comp
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching selected `b` branch map in the extended target field. -/
noncomputable def sbSelectedRightBranchToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbRightSemilinearCommonSourceField L hind)).comp
    ((R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sbSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The extended inverse-oriented `b` right arrow preserves the entire
selected complete branch. -/
theorem sbSemilinearCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sbSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
      R.sbSelectedRightBranchToSemilinearCommonTargetRingHom L hind := by
  exact
    (R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
        (R.sbRightSemilinearCommonSourceField L hind)
        (R.sbSelectedRightBranchInSelectedGraphRightMiddle
          L hind).toAlgHom.toRingHom

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
