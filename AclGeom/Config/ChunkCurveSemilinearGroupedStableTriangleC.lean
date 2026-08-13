/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableSource

/-!
# The c triangle on the stable grouped source
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

/-- Pull back the stable grouped cover through the reoriented genuine `c`
closure comparison. -/
noncomputable def sAcGroupedStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedSourceClosureExtension L hind)
    |>.pullbackField (R.groupedStableSourceField L hind)

/-- The inverse-oriented `c` triangle extended across its stable pullback. -/
noncomputable def sAcGroupedStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sAcGroupedStableSourceField L hind)

/-- The genuine `c` source chart to the literal stable grouped cover. -/
noncomputable def sAcGroupedStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedSourceClosureExtension L hind)
    |>.pullbackEquiv (R.groupedStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback intermediate field hides its source algebra instance.
/-- The intrinsic germ included in the stable `c` pullback source. -/
noncomputable def bGermCoefficientToSAcGroupedStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (R.rightCSelectedGraphRightSourceCover L hind).field
      (R.sAcGroupedStableSourceField L hind)).comp
    (R.bGermCoefficientToRightCSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback chart and stable normal cover carry nested algebra towers.
set_option maxHeartbeats 800000 in
-- The exact restriction also reduces the inverse genuine-`c` source chart.
/-- The stable `c` chart carries its intrinsic germ to the same repeated-`sA`
embedding as the `a` face. -/
theorem sAcGroupedStableSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcGroupedStableSourceChart L hind
        (R.bGermCoefficientToSAcGroupedStableSource L hind z) =
      R.groupedStableSourceSA L hind z := by
  let C := R.sAcGroupedSourceClosureExtension L hind
  change C.pullbackEquiv (R.groupedStableSourceField L hind)
      (algebraMap _ _ (R.bGermCoefficientToRightCSourceRingHom L hind z)) =
    R.groupedJointCoverToStableSourceRingHom L hind
      (R.selectedGraphRightSourceToRightAJointRingHom L hind
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z))
  rw [C.pullbackEquiv_algebraMap]
  exact congrArg (R.groupedJointCoverToStableSourceRingHom L hind)
    (congrArg (R.selectedGraphRightSourceToRightAJointRingHom L hind)
      (DFunLike.congr_fun
        (R.rightCSourceChart_comp_bGermCoefficient L hind) z))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
