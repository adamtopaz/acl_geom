/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearTriangleE
import AclGeom.Correspondence.CompositionTriangleCommonSource

/-!
# The common finite source for inverse-oriented semantic triangles

The finite `e` pullback field is used as the one literal source chart.  The
`e` triangle extends directly across it, and the intrinsic germ enters by
the algebra map from the established graph/right source.
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

/-- The finite source field used literally by all four inverse-oriented
semantic triangles. -/
noncomputable def rightSemilinearCommonSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.rightEFiniteCommonChartSourceField L hind

/-- The inverse-oriented `e` triangle extended across the common finite
source field. -/
noncomputable def seRightSemilinearCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.rightSemilinearCommonSourceField L hind)

/-- The `e` source already is the common presentation, so its common chart is
the identity. -/
noncomputable def seRightSemilinearCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightSemilinearCommonSourceField L hind)) ≃+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  RingEquiv.refl _

set_option synthInstance.maxHeartbeats 100000 in
-- The nested intermediate-field algebra tower needs extra synthesis time.
/-- The one intrinsic germ embedding in the common finite source. -/
noncomputable def bGermCoefficientToRightSemilinearCommonSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  (algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightSemilinearCommonSourceField L hind))).comp
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The nested intermediate-field algebra tower needs extra synthesis time.
/-- The intrinsic germ included in the extended `e` source. -/
noncomputable def bGermCoefficientToSeRightSemilinearExtendedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The nested intermediate-field algebra tower needs extra synthesis time.
/-- The common `e` chart fixes the whole intrinsic germ embedding. -/
theorem seRightSemilinearCommonSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSeRightSemilinearExtendedSourceRingHom L hind) =
      R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind := by
  rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
