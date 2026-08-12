/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-!
# The finite common chart on the intrinsic `b` germ
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
/-- The finite `b` chart carries the one intrinsic source germ to the
selected `b` target map. -/
theorem rightBFiniteCommonChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.rightBFiniteCommonChart L hind
        ((R.selectedGraphRightSourceToRightBJointClosureExtension L hind)
          |>.pullbackBaseRingHom
            (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x)) =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.sbBGermCoefficientToSemanticSourceAlgHom L hind x)) := by
  let old := R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  let srcE := R.seBGermCoefficientToSemanticSourceAlgHom L hind x
  let srcB := R.sbBGermCoefficientToSemanticSourceAlgHom L hind x
  have hbase : R.rightBToJointBaseRingHom hind srcE =
      R.semanticSourceToRightSourceJoint srcB := by
    change R.semanticSourceToRightSourceJoint
        (R.commonSourceRightBAut hind srcE) =
      R.semanticSourceToRightSourceJoint srcB
    exact congrArg R.semanticSourceToRightSourceJoint
      (R.commonSourceRightBAut_comp_seBGermCoefficient L hind x)
  calc
    R.rightBFiniteCommonChart L hind
          ((R.selectedGraphRightSourceToRightBJointClosureExtension L hind)
            |>.pullbackBaseRingHom old) =
        R.selectedGraphRightSourceToRightBJointRingHom L hind old :=
      (R.selectedGraphRightSourceToRightBJointClosureExtension L hind)
        |>.pullbackBaseEquiv_pullbackBaseRingHom old
    _ = R.selectedGraphRightSourceToRightBJointRingHom L hind
          (R.semanticSourceToSelectedGraphRightSourceRingHom L hind srcE) :=
      congrArg (R.selectedGraphRightSourceToRightBJointRingHom L hind)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply L hind x)
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.rightBToJointBaseRingHom hind srcE) :=
      R.selectedGraphRightSourceToRightBJointRingHom_algebraMap L hind srcE
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint srcB) := congrArg _ hbase
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint
            (R.sbBGermCoefficientToSemanticSourceAlgHom L hind x)) :=
      rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
