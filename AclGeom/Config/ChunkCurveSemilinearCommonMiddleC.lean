/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonMiddleB
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchC

/-! # The based germ through the inverse-oriented `c` face

The inverse `c` source chart sends its intrinsic source germ back to the
based `e` germ.  Consequently its left square lands in the based coefficient
anchor inside the `c` middle cover.  This completes the four separately
typed common-source faces before their middle charts are aligned.
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
the middle cover of the unextended `c` triangle. -/
noncomputable def
    sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (↥R.sAcCommonBaseData.coefficientField)
    (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (R.selectedGraphRightSourceCover L hind)).field)).comp
    (R.seBGermCoefficientToCommonCoefficientRingHom L)

set_option synthInstance.maxHeartbeats 100000 in
-- The selected source and middle fields are nested finite-cover transports.
/-- The original `c` left arrow carries the based source anchor to the
matching common-coefficient anchor in its middle field. -/
theorem sAcSelectedGraphRight_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcSelectedGraphRightCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  let P :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  let h :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ
  let N := R.selectedGraphRightSourceCover L hind
  change
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
      P Q h N).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind
  calc
    _ = (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp
        ((algebraMap (↥R.sAcCommonBaseData.coefficientField)
          (↥N.field)).comp
            (R.seBGermCoefficientToCommonCoefficientRingHom L)) :=
      congrArg
        ((FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_eq_commonCoefficient
          L hind)
    _ = (algebraMap (↥R.sAcCommonBaseData.coefficientField)
          (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
            P Q h N).field)).comp
        (R.seBGermCoefficientToCommonCoefficientRingHom L) :=
      finiteCoverTriangle_left_comp_algebraMap_comp P Q h N
        (R.seBGermCoefficientToCommonCoefficientRingHom L)
    _ = R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the source conjugation exposes several nested cover aliases.
/-- After inverse source normalization, the `c` left arrow sends the
intrinsic `c` source germ to the based middle anchor. -/
theorem sAcRightSemilinear_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToRightCSourceRingHom L hind) =
      R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  have hsource := DFunLike.congr_fun
    (R.rightCSourceChart_comp_bGermCoefficient L hind) z
  have hleft := DFunLike.congr_fun
    (R.sAcSelectedGraphRight_left_comp_bGermCoefficient L hind) z
  change (R.selectedGraphRightSourceToRightCRingEquiv L hind).symm
      (R.bGermCoefficientToRightCSourceRingHom L hind z) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z at hsource
  change (R.sAcSelectedGraphRightCompositionTriangle L hind).left
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z) =
    R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind z at hleft
  change (R.sAcSelectedGraphRightCompositionTriangle L hind).left
      ((R.selectedGraphRightSourceToRightCRingEquiv L hind).symm
        (R.bGermCoefficientToRightCSourceRingHom L hind z)) = _
  exact (congrArg
    (R.sAcSelectedGraphRightCompositionTriangle L hind).left hsource).trans hleft

/-- The based middle anchor included in the middle field of the extended
`c` triangle. -/
noncomputable def sAcBGermCoefficientToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)).comp
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source and transported middle form nested algebra towers.
/-- The common-source `c` left arrow carries its intrinsic source germ to
the based middle anchor. -/
theorem sAcSemilinearCommon_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCommonCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom L hind) =
      R.sAcBGermCoefficientToSemilinearCommonMiddleRingHom L hind := by
  let T := R.sAcRightSemilinearCompositionTriangle L hind
  let X := R.sAcRightSemilinearCommonSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightCSourceRingHom L hind)
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sAcRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The corresponding based target anchor in the extended `c` target
field. -/
noncomputable def sAcBGermCoefficientToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)).comp
    ((R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

/-- The extended `c` right arrow restricts on the based middle anchor to
the named target map. -/
theorem sAcSemilinearCommon_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcBGermCoefficientToSemilinearCommonMiddleRingHom L hind) =
      R.sAcBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sAcRightSemilinearCompositionTriangle L hind
  let X := R.sAcRightSemilinearCommonSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The strict direct arrow on the common-source `c` face carries the
intrinsic source germ to the same based target map. -/
theorem sAcSemilinearCommon_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearCommonCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom L hind) =
      R.sAcBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sAcRightSemilinearCommonCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom L hind)
    (R.sAcBGermCoefficientToSemilinearCommonMiddleRingHom L hind)
    (R.sAcBGermCoefficientToSemilinearCommonTargetRingHom L hind)
    (R.sAcSemilinearCommon_left_comp_bGermCoefficient L hind)
    (R.sAcSemilinearCommon_right_comp_bGermCoefficient L hind)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
