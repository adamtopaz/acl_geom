/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChart
import AclGeom.Correspondence.CompositionTriangleExtension

/-! # The strict `s·e=u` triangle on its finite semilinear source -/

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

/-- The strict `s·e=u` triangle extended across the finite `e` pullback
source chart. -/
noncomputable def seFiniteCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.rightEFiniteCommonChartSourceField L hind)

/-- The source chart of the extended `e` triangle is the selected finite
semilinear chart to the literal joint cover. -/
noncomputable def seFiniteCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.rightEFiniteCommonChart L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The nested pullback field exposes a deep canonical algebra structure.
set_option maxHeartbeats 800000 in
-- Elaborating the selected whole-source equality unfolds the same tower.
/-- On the old graph/right source, the extended `e` triangle begins with
the originally selected `e` embedding into the joint cover. -/
theorem seFiniteCommonSourceChart_on_oldSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.seFiniteCommonSourceChart L hind
        (algebraMap _ (↥(R.rightEFiniteCommonChartSourceField L hind)) x) =
      R.selectedGraphRightSourceToRightEJointRingHom L hind x :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackBaseEquiv_algebraMap x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
