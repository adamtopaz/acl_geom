/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-!
# The finite common chart on the intrinsic algebraic-output `c` germ
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
/-- The finite genuine `c` chart carries the one intrinsic source germ to
the selected algebraic-output target map. -/
theorem rightCFiniteCommonChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.rightCFiniteCommonChart L hind
        ((R.selectedGraphRightSourceToRightCJointClosureExtension L hind)
          |>.pullbackBaseRingHom
            (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x)) =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightCSourceToRightSourceJoint
          (R.sAcBGermCoefficientToRightCSourceAlgHom L hind x)) := by
  let old := R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  let srcE := R.seBGermCoefficientToSemanticSourceAlgHom L hind x
  let srcC := R.sAcBGermCoefficientToRightCSourceAlgHom L hind x
  have hbase : R.rightCToJointBaseRingHom hind srcE =
      R.rightCSourceToRightSourceJoint srcC := by
    change R.rightCSourceToRightSourceJoint
        (R.commonSourceToRightCSourceEquiv hind srcE) =
      R.rightCSourceToRightSourceJoint srcC
    exact congrArg R.rightCSourceToRightSourceJoint
      (R.commonSourceToRightCSourceEquiv_comp_seBGermCoefficient L hind x)
  calc
    R.rightCFiniteCommonChart L hind
          ((R.selectedGraphRightSourceToRightCJointClosureExtension L hind)
            |>.pullbackBaseRingHom old) =
        R.selectedGraphRightSourceToRightCJointRingHom L hind old :=
      (R.selectedGraphRightSourceToRightCJointClosureExtension L hind)
        |>.pullbackBaseEquiv_pullbackBaseRingHom old
    _ = R.selectedGraphRightSourceToRightCJointRingHom L hind
          (R.semanticSourceToSelectedGraphRightSourceRingHom L hind srcE) :=
      congrArg (R.selectedGraphRightSourceToRightCJointRingHom L hind)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply L hind x)
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.rightCToJointBaseRingHom hind srcE) :=
      R.selectedGraphRightSourceToRightCJointRingHom_algebraMap L hind srcE
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.rightCSourceToRightSourceJoint srcC) := congrArg _ hbase
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.rightCSourceToRightSourceJoint
            (R.sAcBGermCoefficientToRightCSourceAlgHom L hind x)) :=
      rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
