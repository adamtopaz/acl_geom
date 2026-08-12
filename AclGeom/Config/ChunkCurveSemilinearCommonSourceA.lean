/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceE
import AclGeom.Config.ChunkCurveSemilinearTriangleA

/-! # The inverse-oriented `a` triangle on the common finite source -/

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

/-- Pull back the common finite source through the inverse `a` source
chart. -/
noncomputable def sAaRightSemilinearCommonSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sAaRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

/-- Extend the inverse-oriented `a` triangle across its pullback of the
common finite source. -/
noncomputable def sAaRightSemilinearCommonCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sAaRightSemilinearSourceChart L hind)
      (R.rightSemilinearCommonSourceField L hind)

/-- The restricted inverse `a` source chart with literal common codomain. -/
noncomputable def sAaRightSemilinearCommonSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sAaRightSemilinearCommonSourceField L hind)) ≃+*
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackChart
    (R.sAaRightSemilinearSourceChart L hind)
    (R.rightSemilinearCommonSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- The intrinsic `a` germ included in the pullback source of the extended
triangle. -/
noncomputable def bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAaRightSemilinearCommonSourceField L hind)) :=
  (algebraMap (↥(R.rightASelectedGraphRightSourceCover L hind).field)
      (↥(R.sAaRightSemilinearCommonSourceField L hind))).comp
    (R.bGermCoefficientToRightASourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source adds another intermediate-field algebra tower.
/-- After the finite pullback, the inverse `a` chart still carries the
entire intrinsic germ to the one common finite-source embedding. -/
theorem sAaRightSemilinearCommonSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCommonSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom
          L hind) =
      R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind := by
  unfold bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom
    bGermCoefficientToRightSemilinearCommonSourceRingHom
  exact
    (FieldEquiv.CompositionTriangle.commonSourcePullbackChart_comp_algebraMap_comp
        (R.sAaRightSemilinearSourceChart L hind)
        (R.rightSemilinearCommonSourceField L hind)
        (R.bGermCoefficientToRightASourceRingHom L hind)).trans
      (congrArg
        (fun f ↦
          (algebraMap
            (↥(R.selectedGraphRightSourceCover L hind).field)
            (↥(R.rightSemilinearCommonSourceField L hind))).comp f)
        (R.rightASourceChart_comp_bGermCoefficient L hind))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
