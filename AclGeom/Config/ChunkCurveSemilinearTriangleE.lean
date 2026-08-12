/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranch
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-! # The common `e` source orientation -/

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

/-- The `s·e=u` triangle already uses the selected graph/right source in the
common orientation. -/
noncomputable def seRightSemilinearCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.seSelectedGraphRightCompositionTriangle L hind

/-- The source chart of the common `e` presentation is the identity. -/
noncomputable def seRightSemilinearSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
  RingEquiv.refl _

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
