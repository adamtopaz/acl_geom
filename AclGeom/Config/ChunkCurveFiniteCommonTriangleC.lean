/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChart
import AclGeom.Correspondence.CompositionTriangleExtension

/-! # The strict `sA·c=uB` triangle on its finite semilinear source -/

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

/-- The strict `sA·c=uB` triangle extended across the genuine finite `c`
pullback source chart. -/
noncomputable def sAcFiniteCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.rightCFiniteCommonChartSourceField L hind)

/-- The selected source chart for the genuine finite `c` face. -/
noncomputable def sAcFiniteCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.rightCFiniteCommonChart L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The nested pullback field exposes a deep canonical algebra structure.
set_option maxHeartbeats 800000 in
-- Elaborating the selected whole-source equality unfolds the same tower.
/-- On the old graph/right source, the extended `c` triangle begins with
the originally selected genuine `c` embedding into the joint cover. -/
theorem sAcFiniteCommonSourceChart_on_oldSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.sAcFiniteCommonSourceChart L hind
        (algebraMap _ (↥(R.rightCFiniteCommonChartSourceField L hind)) x) =
      R.selectedGraphRightSourceToRightCJointRingHom L hind x :=
  (R.selectedGraphRightSourceToRightCJointClosureExtension L hind)
    |>.pullbackBaseEquiv_algebraMap x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
