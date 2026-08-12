/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonMiddleA
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchB

/-! # The based germ through the direct `b` face

The `b` source chart sends its intrinsic source germ back to the based `e`
germ.  Consequently its left square lands in the based coefficient anchor
inside the `b` middle cover.  This is the exact `b` analogue of the
inverse-oriented `a` face.
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

/-- The based intrinsic germ embedded by the common coefficient field into
the middle cover of the unextended `b` triangle. -/
noncomputable def
    sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (↥R.sbCommonBaseData.coefficientField)
    (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sb) R.sbCommonBaseData hψ)
      (R.selectedGraphRightSourceCover L hind)).field)).comp
    (R.seBGermCoefficientToCommonCoefficientRingHom L)

set_option synthInstance.maxHeartbeats 100000 in
-- The selected source and middle fields are nested finite-cover transports.
/-- The original `b` left arrow carries the based source anchor to the
matching common-coefficient anchor in its middle field. -/
theorem sbSelectedGraphRight_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbSelectedGraphRightCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  let P :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  let h :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ
  let N := R.selectedGraphRightSourceCover L hind
  change
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
      P Q h N).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind
  calc
    _ = (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp
        ((algebraMap (↥R.sbCommonBaseData.coefficientField)
          (↥N.field)).comp
            (R.seBGermCoefficientToCommonCoefficientRingHom L)) :=
      congrArg
        ((FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_eq_commonCoefficient
          L hind)
    _ = (algebraMap (↥R.sbCommonBaseData.coefficientField)
          (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
            P Q h N).field)).comp
        (R.seBGermCoefficientToCommonCoefficientRingHom L) :=
      finiteCoverTriangle_left_comp_algebraMap_comp P Q h N
        (R.seBGermCoefficientToCommonCoefficientRingHom L)
    _ = R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the source conjugation exposes several nested cover aliases.
/-- After source normalization, the `b` left arrow sends the intrinsic `b`
source germ to the based middle anchor. -/
theorem sbRightSemilinear_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToRightBSourceRingHom L hind) =
      R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  have hsource := DFunLike.congr_fun
    (R.rightBSourceChart_comp_bGermCoefficient L hind) z
  have hleft := DFunLike.congr_fun
    (R.sbSelectedGraphRight_left_comp_bGermCoefficient L hind) z
  change (R.selectedGraphRightSourceToRightBRingEquiv L hind).symm
      (R.bGermCoefficientToRightBSourceRingHom L hind z) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z at hsource
  change (R.sbSelectedGraphRightCompositionTriangle L hind).left
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z) =
    R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind z at hleft
  change (R.sbSelectedGraphRightCompositionTriangle L hind).left
      ((R.selectedGraphRightSourceToRightBRingEquiv L hind).symm
        (R.bGermCoefficientToRightBSourceRingHom L hind z)) = _
  exact (congrArg
    (R.sbSelectedGraphRightCompositionTriangle L hind).left hsource).trans hleft

/-- The based middle anchor included in the middle field of the extended
`b` triangle. -/
noncomputable def sbBGermCoefficientToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbRightSemilinearCommonSourceField L hind)).comp
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source and transported middle form nested algebra towers.
/-- The common-source `b` left arrow carries its intrinsic source germ to
the based middle anchor. -/
theorem sbSemilinearCommon_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCommonCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSbRightSemilinearExtendedSourceRingHom L hind) =
      R.sbBGermCoefficientToSemilinearCommonMiddleRingHom L hind := by
  let T := R.sbRightSemilinearCompositionTriangle L hind
  let X := R.sbRightSemilinearCommonSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightBSourceRingHom L hind)
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sbRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The corresponding based target anchor in the extended `b` target
field. -/
noncomputable def sbBGermCoefficientToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbRightSemilinearCommonSourceField L hind)).comp
    ((R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

/-- The extended `b` right arrow restricts on the based middle anchor to
the named target map. -/
theorem sbSemilinearCommon_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sbBGermCoefficientToSemilinearCommonMiddleRingHom L hind) =
      R.sbBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sbRightSemilinearCompositionTriangle L hind
  let X := R.sbRightSemilinearCommonSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The strict direct `uB` arrow on the common-source `b` face carries the
intrinsic source germ to the same based target map. -/
theorem sbSemilinearCommon_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearCommonCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSbRightSemilinearExtendedSourceRingHom L hind) =
      R.sbBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sbRightSemilinearCommonCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSbRightSemilinearExtendedSourceRingHom L hind)
    (R.sbBGermCoefficientToSemilinearCommonMiddleRingHom L hind)
    (R.sbBGermCoefficientToSemilinearCommonTargetRingHom L hind)
    (R.sbSemilinearCommon_left_comp_bGermCoefficient L hind)
    (R.sbSemilinearCommon_right_comp_bGermCoefficient L hind)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
