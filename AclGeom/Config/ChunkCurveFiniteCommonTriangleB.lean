/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChart
import AclGeom.Correspondence.CompositionTriangleExtension

/-! # The strict `s·b=uB` triangle on its finite semilinear source -/

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

/-- The strict `s·b=uB` triangle extended across the finite `b` pullback
source chart. -/
noncomputable def sbFiniteCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.rightBFiniteCommonChartSourceField L hind)

/-- The selected source chart for the finite `b` face. -/
noncomputable def sbFiniteCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.rightBFiniteCommonChart L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The nested pullback field exposes a deep canonical algebra structure.
set_option maxHeartbeats 800000 in
-- Elaborating the selected whole-source equality unfolds the same tower.
/-- On the old graph/right source, the extended `b` triangle begins with
the originally selected `b` embedding into the joint cover. -/
theorem sbFiniteCommonSourceChart_on_oldSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.sbFiniteCommonSourceChart L hind
        (algebraMap _ (↥(R.rightBFiniteCommonChartSourceField L hind)) x) =
      R.selectedGraphRightSourceToRightBJointRingHom L hind x :=
  (R.selectedGraphRightSourceToRightBJointClosureExtension L hind)
    |>.pullbackBaseEquiv_algebraMap x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
