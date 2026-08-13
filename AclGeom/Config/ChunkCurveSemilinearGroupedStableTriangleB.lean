/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableSource

/-!
# The b triangle on the stable grouped source
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

/-- Pull back the stable grouped cover through the reoriented selected `b`
closure comparison. -/
noncomputable def sbGroupedStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedSourceClosureExtension L hind)
    |>.pullbackField (R.groupedStableSourceField L hind)

/-- The inverse-oriented `b` triangle extended across its stable pullback. -/
noncomputable def sbGroupedStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sbGroupedStableSourceField L hind)

/-- The `b` source chart to the literal stable grouped cover. -/
noncomputable def sbGroupedStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedSourceClosureExtension L hind)
    |>.pullbackEquiv (R.groupedStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback intermediate field hides its source algebra instance.
/-- The intrinsic germ included in the stable `b` pullback source. -/
noncomputable def bGermCoefficientToSbGroupedStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (R.rightBSelectedGraphRightSourceCover L hind).field
      (R.sbGroupedStableSourceField L hind)).comp
    (R.bGermCoefficientToRightBSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback chart and stable normal cover carry nested algebra towers.
set_option maxHeartbeats 800000 in
-- The exact restriction also reduces the inverse `b` source chart.
/-- The stable `b` chart carries its intrinsic germ to the same repeated-`s`
embedding as the `e` face. -/
theorem sbGroupedStableSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbGroupedStableSourceChart L hind
        (R.bGermCoefficientToSbGroupedStableSource L hind z) =
      R.groupedStableSourceS L hind z := by
  let C := R.sbGroupedSourceClosureExtension L hind
  change C.pullbackEquiv (R.groupedStableSourceField L hind)
      (algebraMap _ _ (R.bGermCoefficientToRightBSourceRingHom L hind z)) =
    R.groupedJointCoverToStableSourceRingHom L hind
      (R.selectedGraphRightSourceToRightEJointRingHom L hind
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z))
  rw [C.pullbackEquiv_algebraMap]
  exact congrArg (R.groupedJointCoverToStableSourceRingHom L hind)
    (congrArg (R.selectedGraphRightSourceToRightEJointRingHom L hind)
      (DFunLike.congr_fun
        (R.rightBSourceChart_comp_bGermCoefficient L hind) z))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
