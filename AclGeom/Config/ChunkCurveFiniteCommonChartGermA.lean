/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-!
# The finite common chart on the intrinsic `a` germ
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
/-- The finite `a` chart carries the one intrinsic source germ to the
selected `a` target map. -/
theorem rightAFiniteCommonChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.rightAFiniteCommonChart L hind
        ((R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
          |>.pullbackBaseRingHom
            (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x)) =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x)) := by
  let old := R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  let srcE := R.seBGermCoefficientToSemanticSourceAlgHom L hind x
  let srcA := R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x
  have hbase : R.rightAToJointBaseRingHom hind srcE =
      R.semanticSourceToRightSourceJoint srcA := by
    change R.semanticSourceToRightSourceJoint
        (R.commonSourceRightAAut hind srcE) =
      R.semanticSourceToRightSourceJoint srcA
    exact congrArg R.semanticSourceToRightSourceJoint
      (R.commonSourceRightAAut_comp_seBGermCoefficient L hind x)
  calc
    R.rightAFiniteCommonChart L hind
          ((R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
            |>.pullbackBaseRingHom old) =
        R.selectedGraphRightSourceToRightAJointRingHom L hind old :=
      (R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
        |>.pullbackBaseEquiv_pullbackBaseRingHom old
    _ = R.selectedGraphRightSourceToRightAJointRingHom L hind
          (R.semanticSourceToSelectedGraphRightSourceRingHom L hind srcE) :=
      congrArg (R.selectedGraphRightSourceToRightAJointRingHom L hind)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply L hind x)
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.rightAToJointBaseRingHom hind srcE) :=
      R.selectedGraphRightSourceToRightAJointRingHom_algebraMap L hind srcE
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint srcA) := congrArg _ hbase
    _ = algebraMap (↥R.rightSourceJointField)
          (↥(R.fourSelectedGraphJointCover L hind).field)
          (R.semanticSourceToRightSourceJoint
            (R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x)) :=
      rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
