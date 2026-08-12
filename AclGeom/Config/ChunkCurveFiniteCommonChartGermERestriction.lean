/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-!
# Whole-germ restriction of the finite common `e` chart
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested selected-cover types require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
/-- The finite `e` chart restricts on the whole intrinsic germ to the
selected `e` target map. -/
theorem rightEFiniteCommonChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.rightEFiniteCommonChart L hind
        ((R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
          |>.pullbackBaseRingHom
            (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x)) =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) := by
  let old := R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  let src := R.seBGermCoefficientToSemanticSourceAlgHom L hind x
  calc
    R.rightEFiniteCommonChart L hind
          ((R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
            |>.pullbackBaseRingHom old) =
        R.selectedGraphRightSourceToRightEJointRingHom L hind old :=
      (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
        |>.pullbackBaseEquiv_pullbackBaseRingHom old
    _ = R.selectedGraphRightSourceToRightEJointRingHom L hind
          (R.semanticSourceToSelectedGraphRightSourceRingHom L hind src) :=
      congrArg (R.selectedGraphRightSourceToRightEJointRingHom L hind)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply L hind x)
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint src) :=
      R.selectedGraphRightSourceToRightEJointRingHom_algebraMap L hind src
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint
            (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) :=
      rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
