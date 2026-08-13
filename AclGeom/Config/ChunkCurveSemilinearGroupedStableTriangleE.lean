/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableSource

/-!
# The e triangle on the stable grouped source
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

/-- Pull back the stable grouped cover through the selected `e` closure
comparison. -/
noncomputable def seGroupedStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackField (R.groupedStableSourceField L hind)

/-- The `e` triangle extended across its stable grouped pullback source. -/
noncomputable def seGroupedStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.seGroupedStableSourceField L hind)

/-- The `e` source chart to the literal stable grouped cover. -/
noncomputable def seGroupedStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackEquiv (R.groupedStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback intermediate field hides its source algebra instance.
/-- The intrinsic germ included in the stable `e` pullback source. -/
noncomputable def bGermCoefficientToSeGroupedStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (R.selectedGraphRightSourceCover L hind).field
      (R.seGroupedStableSourceField L hind)).comp
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback chart and stable normal cover carry nested algebra towers.
set_option maxHeartbeats 800000 in
-- The exact restriction unfolds the selected joint-cover embedding once.
/-- The stable `e` chart carries its intrinsic germ to the common repeated-`s`
embedding. -/
theorem seGroupedStableSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seGroupedStableSourceChart L hind
        (R.bGermCoefficientToSeGroupedStableSource L hind z) =
      R.groupedStableSourceS L hind z := by
  exact (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackEquiv_algebraMap (R.groupedStableSourceField L hind)
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
