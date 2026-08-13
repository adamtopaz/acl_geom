/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableSource

/-!
# The a triangle on the stable grouped source
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

/-- Pull back the stable grouped cover through the reoriented selected `a`
closure comparison. -/
noncomputable def sAaGroupedStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedSourceClosureExtension L hind)
    |>.pullbackField (R.groupedStableSourceField L hind)

/-- The inverse-oriented `a` triangle extended across its stable pullback. -/
noncomputable def sAaGroupedStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sAaGroupedStableSourceField L hind)

/-- The `a` source chart to the literal stable grouped cover. -/
noncomputable def sAaGroupedStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedSourceClosureExtension L hind)
    |>.pullbackEquiv (R.groupedStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback intermediate field hides its source algebra instance.
/-- The intrinsic germ included in the stable `a` pullback source. -/
noncomputable def bGermCoefficientToSAaGroupedStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (R.rightASelectedGraphRightSourceCover L hind).field
      (R.sAaGroupedStableSourceField L hind)).comp
    (R.bGermCoefficientToRightASourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback chart and stable normal cover carry nested algebra towers.
set_option maxHeartbeats 800000 in
-- The exact restriction also reduces the inverse `a` source chart.
/-- The stable `a` chart carries its intrinsic germ to the common
repeated-`sA` embedding. -/
theorem sAaGroupedStableSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaGroupedStableSourceChart L hind
        (R.bGermCoefficientToSAaGroupedStableSource L hind z) =
      R.groupedStableSourceSA L hind z := by
  let C := R.sAaGroupedSourceClosureExtension L hind
  change C.pullbackEquiv (R.groupedStableSourceField L hind)
      (algebraMap _ _ (R.bGermCoefficientToRightASourceRingHom L hind z)) =
    R.groupedJointCoverToStableSourceRingHom L hind
      (R.selectedGraphRightSourceToRightAJointRingHom L hind
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z))
  rw [C.pullbackEquiv_algebraMap]
  exact congrArg (R.groupedJointCoverToStableSourceRingHom L hind)
    (congrArg (R.selectedGraphRightSourceToRightAJointRingHom L hind)
      (DFunLike.congr_fun
        (R.rightASourceChart_comp_bGermCoefficient L hind) z))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
