/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranch
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-! # Inverse semilinear source normalization for the `c` triangle -/

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

/-- The intrinsic algebraic-output `c` germ embedded in its genuinely
different transported source cover. -/
noncomputable def bGermCoefficientToRightCSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightCSelectedGraphRightSourceCover L hind).field) :=
  (algebraMap (↥R.rightCSourceField)
      (↥(R.rightCSelectedGraphRightSourceCover L hind).field)).comp
    (R.sAcBGermCoefficientToRightCSourceAlgHom L hind).toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- The source and target covers have different displayed base fields.
set_option maxHeartbeats 800000 in
/-- Forward semilinear transport carries the entire intrinsic `e` germ to
the intrinsic algebraic-output `c` germ in the transported source cover. -/
theorem selectedGraphRightSourceToRightC_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightCRingEquiv L hind).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.bGermCoefficientToRightCSourceRingHom L hind := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply,
    R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply]
  apply Subtype.ext
  change (R.rightCSourceClosureTransport hind).closureEquiv
      (algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) =
    algebraMap (↥R.rightCSourceField)
      (AlgebraicClosure (↥R.rightCSourceField))
      (R.sAcBGermCoefficientToRightCSourceAlgHom L hind x)
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.rightCSourceField)
      (AlgebraicClosure (↥R.rightCSourceField)))
    (R.commonSourceToRightCSourceEquiv_comp_seBGermCoefficient L hind x)

/-- The inverse genuine-`c` source chart sends its entire intrinsic germ
back to the common selected `e` germ. -/
theorem rightCSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightCRingEquiv L hind).symm.toRingHom.comp
        (R.bGermCoefficientToRightCSourceRingHom L hind) =
      R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind := by
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun
    (R.selectedGraphRightSourceToRightC_comp_bGermCoefficient L hind) x
  change R.selectedGraphRightSourceToRightCRingEquiv L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x) =
    R.bGermCoefficientToRightCSourceRingHom L hind x at hx
  change (R.selectedGraphRightSourceToRightCRingEquiv L hind).symm
      (R.bGermCoefficientToRightCSourceRingHom L hind x) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  apply (R.selectedGraphRightSourceToRightCRingEquiv L hind).injective
  simpa using hx.symm

/-- The strict `sA·c=uB` triangle re-presented on the transported genuine
`c` source cover. -/
noncomputable def sAcRightSemilinearCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcSelectedGraphRightCompositionTriangle L hind).conjugate
    (R.selectedGraphRightSourceToRightCRingEquiv L hind)
    (RingEquiv.refl _)
    (RingEquiv.refl _)

/-- The inverse finite-cover chart from the transported `c` source to the
one common selected graph/right source. -/
noncomputable def sAcRightSemilinearSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightCRingEquiv L hind).symm

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
