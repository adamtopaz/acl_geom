/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceC
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranchC

/-! # The selected `c` branch in the inverse-oriented common-source triangle -/

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

/-- Carry the whole selected `c` branch into the middle field of the
inverse-oriented common-source extension. -/
noncomputable def sAcSelectedRightBranchToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)).comp
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching selected `c` branch map in the extended target field. -/
noncomputable def sAcSelectedRightBranchToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)).comp
    ((R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The extended inverse-oriented `c` right arrow preserves the entire
selected complete branch. -/
theorem sAcSemilinearCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
      R.sAcSelectedRightBranchToSemilinearCommonTargetRingHom L hind := by
  exact
    (R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
        (R.sAcRightSemilinearCommonSourceField L hind)
        (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
          L hind).toAlgHom.toRingHom

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
