/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonMiddleC

/-! # The common-coefficient anchors lie in the selected branches

The separately typed middle and target anchors constructed for the four
common-source faces factor through the already preserved complete right
branches.  These are the compatibility equations that a common middle and
target chart must retain.
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

/-- The common-source `e` middle anchor is the restriction of the preserved
selected complete branch. -/
theorem seSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seSelectedRightBranchToSemilinearCommonMiddleRingHom L hind
        (R.seBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.seBGermCoefficientToSemilinearCommonMiddleRingHom L hind z := by
  rfl

/-- The common-source `e` target anchor is the restriction of the preserved
selected complete branch. -/
theorem seSelectedRightBranchToSemilinearCommonTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seSelectedRightBranchToSemilinearCommonTargetRingHom L hind
        (R.seBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.seBGermCoefficientToSemilinearCommonTargetRingHom L hind z := by
  rfl

/-- The based intrinsic germ included in the selected semantic `a` branch. -/
noncomputable def sAaBGermCoefficientToSemanticRightBranchRingHom :=
  (algebraMap
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource)).comp
    ((algebraMap (↥R.sAaCommonBaseData.coefficientField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).sourceField)).comp
      (R.seBGermCoefficientToCommonCoefficientRingHom L))

set_option synthInstance.maxHeartbeats 100000 in
-- The selected branch embedding is linear over its complete source field.
/-- In the old `a` middle cover, the route through the selected branch is
the named common-coefficient anchor. -/
theorem sAaSelectedRightBranchMiddle_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom.comp
      (R.sAaBGermCoefficientToSemanticRightBranchRingHom L) =
        R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  unfold sAaBGermCoefficientToSemanticRightBranchRingHom
    sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  let c := R.seBGermCoefficientToCommonCoefficientRingHom L z
  have hcomm :=
    (R.sAaSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.commutes
      (algebraMap (↥R.sAaCommonBaseData.coefficientField)
        (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAa) R.sAaCommonBaseData hψ).sourceField) c)
  apply Subtype.ext
  exact congrArg Subtype.val hcomm

/-- The common-source `a` middle anchor factors through the preserved
selected complete branch. -/
theorem sAaSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaSelectedRightBranchToSemilinearCommonMiddleRingHom L hind
        (R.sAaBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAaBGermCoefficientToSemilinearCommonMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAaSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)) h

/-- The common-source `a` target anchor factors through the preserved
selected complete branch. -/
theorem sAaSelectedRightBranchToSemilinearCommonTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaSelectedRightBranchToSemilinearCommonTargetRingHom L hind
        (R.sAaBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAaBGermCoefficientToSemilinearCommonTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAaSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)).comp
      (R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom) h

/-- The based intrinsic germ included in the selected semantic `b` branch. -/
noncomputable def sbBGermCoefficientToSemanticRightBranchRingHom :=
  (algebraMap
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).branchOverSource)).comp
    ((algebraMap (↥R.sbCommonBaseData.coefficientField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).sourceField)).comp
      (R.seBGermCoefficientToCommonCoefficientRingHom L))

set_option synthInstance.maxHeartbeats 100000 in
-- The selected branch embedding is linear over its complete source field.
/-- In the old `b` middle cover, the route through the selected branch is
the named common-coefficient anchor. -/
theorem sbSelectedRightBranchMiddle_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom.comp
      (R.sbBGermCoefficientToSemanticRightBranchRingHom L) =
        R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  unfold sbBGermCoefficientToSemanticRightBranchRingHom
    sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  let c := R.seBGermCoefficientToCommonCoefficientRingHom L z
  have hcomm :=
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.commutes
      (algebraMap (↥R.sbCommonBaseData.coefficientField)
        (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ).sourceField) c)
  apply Subtype.ext
  exact congrArg Subtype.val hcomm

/-- The common-source `b` middle anchor factors through the preserved
selected complete branch. -/
theorem sbSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbSelectedRightBranchToSemilinearCommonMiddleRingHom L hind
        (R.sbBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sbBGermCoefficientToSemilinearCommonMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sbSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbRightSemilinearCommonSourceField L hind)) h

/-- The common-source `b` target anchor factors through the preserved
selected complete branch. -/
theorem sbSelectedRightBranchToSemilinearCommonTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbSelectedRightBranchToSemilinearCommonTargetRingHom L hind
        (R.sbBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sbBGermCoefficientToSemilinearCommonTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sbSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbRightSemilinearCommonSourceField L hind)).comp
      (R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom) h

/-- The based intrinsic germ included in the selected semantic `c` branch. -/
noncomputable def sAcBGermCoefficientToSemanticRightBranchRingHom :=
  (algebraMap
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource)).comp
    ((algebraMap (↥R.sAcCommonBaseData.coefficientField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).sourceField)).comp
      (R.seBGermCoefficientToCommonCoefficientRingHom L))

set_option synthInstance.maxHeartbeats 100000 in
-- The selected branch embedding is linear over its complete source field.
/-- In the old `c` middle cover, the route through the selected branch is
the named common-coefficient anchor. -/
theorem sAcSelectedRightBranchMiddle_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle
        L hind).toAlgHom.toRingHom.comp
      (R.sAcBGermCoefficientToSemanticRightBranchRingHom L) =
        R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  unfold sAcBGermCoefficientToSemanticRightBranchRingHom
    sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  let c := R.seBGermCoefficientToCommonCoefficientRingHom L z
  have hcomm :=
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.commutes
      (algebraMap (↥R.sAcCommonBaseData.coefficientField)
        (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAc) R.sAcCommonBaseData hψ).sourceField) c)
  apply Subtype.ext
  exact congrArg Subtype.val hcomm

/-- The common-source `c` middle anchor factors through the preserved
selected complete branch. -/
theorem sAcSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcSelectedRightBranchToSemilinearCommonMiddleRingHom L hind
        (R.sAcBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAcBGermCoefficientToSemilinearCommonMiddleRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAcSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)) h

/-- The common-source `c` target anchor factors through the preserved
selected complete branch. -/
theorem sAcSelectedRightBranchToSemilinearCommonTarget_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcSelectedRightBranchToSemilinearCommonTargetRingHom L hind
        (R.sAcBGermCoefficientToSemanticRightBranchRingHom L z) =
      R.sAcBGermCoefficientToSemilinearCommonTargetRingHom L hind z := by
  have h := DFunLike.congr_fun
    (R.sAcSelectedRightBranchMiddle_comp_bGermCoefficient L hind) z
  exact congrArg
    (((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcRightSemilinearCommonSourceField L hind)).comp
      (R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom) h

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
