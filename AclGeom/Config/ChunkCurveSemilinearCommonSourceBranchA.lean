/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceA
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranchA

/-! # The selected `a` branch in the inverse-oriented common-source triangle -/

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

/-- Carry the whole selected `a` branch into the middle field of the
inverse-oriented common-source extension. -/
noncomputable def sAaSelectedRightBranchToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)).comp
    (R.sAaSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching selected `a` branch map in the extended target field. -/
noncomputable def sAaSelectedRightBranchToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)).comp
    ((R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom)

/-- The extended inverse-oriented `a` right arrow preserves the entire
selected complete branch. -/
theorem sAaSemilinearCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaSelectedRightBranchToSemilinearCommonMiddleRingHom L hind) =
      R.sAaSelectedRightBranchToSemilinearCommonTargetRingHom L hind := by
  exact
    (R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
        (R.sAaRightSemilinearCommonSourceField L hind)
        (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
          L hind).toAlgHom.toRingHom

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
