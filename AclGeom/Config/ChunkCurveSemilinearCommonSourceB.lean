/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceE
import AclGeom.Config.ChunkCurveSemilinearTriangleB

/-! # The inverse-oriented `b` triangle on the common finite source -/

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

/-- Pull back the common finite source through the inverse `b` source
chart. -/
noncomputable def sbRightSemilinearCommonSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sbRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

/-- Extend the inverse-oriented `b` triangle across its pullback of the
common finite source. -/
noncomputable def sbRightSemilinearCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sbRightSemilinearSourceChart L hind)
      (R.rightSemilinearCommonSourceField L hind)

/-- The restricted inverse `b` source chart with literal common codomain. -/
noncomputable def sbRightSemilinearCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sbRightSemilinearCommonSourceField L hind)) ≃+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackChart
    (R.sbRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- The intrinsic `b` germ included in the pullback source of the extended
triangle. -/
noncomputable def bGermCoefficientToSbRightSemilinearExtendedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sbRightSemilinearCommonSourceField L hind)) :=
  (algebraMap (↥(R.rightBSelectedGraphRightSourceCover L hind).field)
      (↥(R.sbRightSemilinearCommonSourceField L hind))).comp
    (R.bGermCoefficientToRightBSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- After the finite pullback, the inverse `b` chart still carries the
entire intrinsic germ to the one common finite-source embedding. -/
theorem sbRightSemilinearCommonSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCommonSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSbRightSemilinearExtendedSourceRingHom
          L hind) =
      R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind := by
  unfold bGermCoefficientToSbRightSemilinearExtendedSourceRingHom
    bGermCoefficientToRightSemilinearCommonSourceRingHom
  exact
    (FieldEquiv.CompositionTriangle.commonSourcePullbackChart_comp_algebraMap_comp
        (R.sbRightSemilinearSourceChart L hind)
        (R.rightSemilinearCommonSourceField L hind)
        (R.bGermCoefficientToRightBSourceRingHom L hind)).trans
      (congrArg
        (fun f ↦
          (algebraMap
            (↥(R.selectedGraphRightSourceCover L hind).field)
            (↥(R.rightSemilinearCommonSourceField L hind))).comp f)
        (R.rightBSourceChart_comp_bGermCoefficient L hind))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
