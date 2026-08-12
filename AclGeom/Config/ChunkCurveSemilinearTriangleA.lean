/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleBranch
import AclGeom.Config.ChunkCurveFiniteCommonChartGermAnchor

/-!
# Inverse semilinear source normalization for the `a` triangle

The forward finite-cover chart carries the distinguished `e` source
presentation to the `a` presentation.  For a common middle chart the useful
orientation is the inverse one: first regard the `sA·a=u` triangle as a
triangle on the transported `a` source cover, then chart that source back to
the original selected graph/right cover.  The whole intrinsic germ is sent
back exactly, not merely its displayed generators.
-/

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

/-- The intrinsic `a` germ embedded in the transported finite normal source
cover for the `a` presentation. -/
noncomputable def bGermCoefficientToRightASourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightASelectedGraphRightSourceCover L hind).field) :=
  (algebraMap (↥R.semanticCommonSourceField)
      (↥(R.rightASelectedGraphRightSourceCover L hind).field)).comp
    (R.sAaBGermCoefficientToSemanticSourceAlgHom L hind).toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- The cover algebra maps are hidden behind the selected graph/right sup.
set_option maxHeartbeats 800000 in
/-- Forward semilinear transport carries the entire intrinsic `e` germ in
the selected graph/right source to the intrinsic `a` germ in the transported
source cover. -/
theorem selectedGraphRightSourceToRightA_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightARingEquiv L hind).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.bGermCoefficientToRightASourceRingHom L hind := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply,
    R.bGermCoefficientToSelectedGraphRightSourceRingHom_apply]
  apply Subtype.ext
  change (R.rightACommonSourceClosureTransport hind).closureEquiv
      (algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) =
    algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField))
      (R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x)
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)))
    (R.commonSourceRightAAut_comp_seBGermCoefficient L hind x)

/-- In the inverse orientation used as a common source chart, the whole
intrinsic `a` germ returns to the one selected `e` germ. -/
theorem rightASourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightARingEquiv L hind).symm.toRingHom.comp
        (R.bGermCoefficientToRightASourceRingHom L hind) =
      R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind := by
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun
    (R.selectedGraphRightSourceToRightA_comp_bGermCoefficient L hind) x
  change R.selectedGraphRightSourceToRightARingEquiv L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x) =
    R.bGermCoefficientToRightASourceRingHom L hind x at hx
  change (R.selectedGraphRightSourceToRightARingEquiv L hind).symm
      (R.bGermCoefficientToRightASourceRingHom L hind x) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x
  apply (R.selectedGraphRightSourceToRightARingEquiv L hind).injective
  simpa using hx.symm

/-- The strict `sA·a=u` triangle re-presented on the transported `a` source
cover.  Its middle and target fields are unchanged. -/
noncomputable def sAaRightSemilinearCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaSelectedGraphRightCompositionTriangle L hind).conjugate
    (R.selectedGraphRightSourceToRightARingEquiv L hind)
    (RingEquiv.refl _)
    (RingEquiv.refl _)

/-- The inverse finite-cover chart from the transported `a` source to the
one selected graph/right source. -/
noncomputable def sAaRightSemilinearSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightARingEquiv L hind).symm

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
