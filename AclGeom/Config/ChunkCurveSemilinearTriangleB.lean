/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranch
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-! # Inverse semilinear source normalization for the `b` triangle -/

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

/-- The intrinsic `b` germ embedded in the transported finite normal source
cover for the `b` presentation. -/
noncomputable def bGermCoefficientToRightBSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightBSelectedGraphRightSourceCover L hind).field) :=
  (algebraMap (↥R.semanticCommonSourceField)
      (↥(R.rightBSelectedGraphRightSourceCover L hind).field)).comp
    (R.sbBGermCoefficientToSemanticSourceAlgHom L hind).toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- The cover algebra maps are hidden behind the selected graph/right sup.
set_option maxHeartbeats 800000 in
/-- Forward semilinear transport carries the entire intrinsic `e` germ to
the intrinsic `b` germ in the transported source cover. -/
theorem selectedGraphRightSourceToRightB_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightBRingEquiv L hind).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.bGermCoefficientToRightBSourceRingHom L hind := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply,
    R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply]
  apply Subtype.ext
  change (R.rightBCommonSourceClosureTransport hind).closureEquiv
      (algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) =
    algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField))
      (R.sbBGermCoefficientToSemanticSourceAlgHom L hind x)
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)))
    (R.commonSourceRightBAut_comp_seBGermCoefficient L hind x)

/-- The inverse `b` source chart sends the entire intrinsic `b` germ back to
the common selected `e` germ. -/
theorem rightBSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightBRingEquiv L hind).symm.toRingHom.comp
        (R.bGermCoefficientToRightBSourceRingHom L hind) =
      R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind := by
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun
    (R.selectedGraphRightSourceToRightB_comp_bGermCoefficient L hind) x
  change R.selectedGraphRightSourceToRightBRingEquiv L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x) =
    R.bGermCoefficientToRightBSourceRingHom L hind x at hx
  change (R.selectedGraphRightSourceToRightBRingEquiv L hind).symm
      (R.bGermCoefficientToRightBSourceRingHom L hind x) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  apply (R.selectedGraphRightSourceToRightBRingEquiv L hind).injective
  simpa using hx.symm

/-- The strict `s·b=uB` triangle re-presented on the transported `b` source
cover. -/
noncomputable def sbRightSemilinearCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbSelectedGraphRightCompositionTriangle L hind).conjugate
    (R.selectedGraphRightSourceToRightBRingEquiv L hind)
    (RingEquiv.refl _)
    (RingEquiv.refl _)

/-- The inverse finite-cover chart from the transported `b` source to the
one common selected graph/right source. -/
noncomputable def sbRightSemilinearSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightBRingEquiv L hind).symm

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
