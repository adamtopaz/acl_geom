/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChart
import AclGeom.Correspondence.CompositionTriangleExtension

/-! # The strict `sA·a=u` triangle on its finite semilinear source -/

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

/-- The strict `sA·a=u` triangle extended across the finite `a` pullback
source chart. -/
noncomputable def sAaFiniteCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.rightAFiniteCommonChartSourceField L hind)

/-- The selected source chart for the finite `a` face. -/
noncomputable def sAaFiniteCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.rightAFiniteCommonChart L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The nested pullback field exposes a deep canonical algebra structure.
set_option maxHeartbeats 800000 in
-- Elaborating the selected whole-source equality unfolds the same tower.
/-- On the old graph/right source, the extended `a` triangle begins with
the originally selected `a` embedding into the joint cover. -/
theorem sAaFiniteCommonSourceChart_on_oldSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.sAaFiniteCommonSourceChart L hind
        (algebraMap _ (↥(R.rightAFiniteCommonChartSourceField L hind)) x) =
      R.selectedGraphRightSourceToRightAJointRingHom L hind x :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
    |>.pullbackBaseEquiv_algebraMap x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
