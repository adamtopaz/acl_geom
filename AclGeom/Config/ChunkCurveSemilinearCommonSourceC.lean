/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceE
import AclGeom.Config.ChunkCurveSemilinearTriangleC

/-! # The inverse-oriented `c` triangle on the common finite source -/

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

/-- Pull back the common finite source through the inverse `c` source
chart. -/
noncomputable def sAcRightSemilinearCommonSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sAcRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

/-- Extend the inverse-oriented `c` triangle across its pullback of the
common finite source. -/
noncomputable def sAcRightSemilinearCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sAcRightSemilinearSourceChart L hind)
      (R.rightSemilinearCommonSourceField L hind)

/-- The restricted inverse `c` source chart with literal common codomain. -/
noncomputable def sAcRightSemilinearCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sAcRightSemilinearCommonSourceField L hind)) ≃+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackChart
    (R.sAcRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- The intrinsic algebraic-output `c` germ included in the pullback source
of the extended triangle. -/
noncomputable def bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAcRightSemilinearCommonSourceField L hind)) :=
  (algebraMap (↥(R.rightCSelectedGraphRightSourceCover L hind).field)
      (↥(R.sAcRightSemilinearCommonSourceField L hind))).comp
    (R.bGermCoefficientToRightCSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- After the finite pullback, the inverse `c` chart still carries the
entire intrinsic germ to the one common finite-source embedding. -/
theorem sAcRightSemilinearCommonSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCommonSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom
          L hind) =
      R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind := by
  unfold bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom
    bGermCoefficientToRightSemilinearCommonSourceRingHom
  exact
    (FieldEquiv.CompositionTriangle.commonSourcePullbackChart_comp_algebraMap_comp
        (R.sAcRightSemilinearSourceChart L hind)
        (R.rightSemilinearCommonSourceField L hind)
        (R.bGermCoefficientToRightCSourceRingHom L hind)).trans
      (congrArg
        (fun f ↦
          (algebraMap
            (↥(R.selectedGraphRightSourceCover L hind).field)
            (↥(R.rightSemilinearCommonSourceField L hind))).comp f)
        (R.rightCSourceChart_comp_bGermCoefficient L hind))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
