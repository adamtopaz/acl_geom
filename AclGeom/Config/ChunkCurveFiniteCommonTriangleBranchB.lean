/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleB

/-! # The selected right branch in the extended finite `b` triangle -/

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

/-- The original `b` composition cover is contained in the established
graph/right source. -/
theorem sbFiniteSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbFiniteSourceCover).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  (R.sbFiniteSourceCover_le_branchComparisonSourceCover hind).trans
    ((R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind).trans
      (R.selectedGraphSourceCover_le_selectedGraphRightSourceCover L hind))

/-- The selected complete `b` branch in the middle cover of the established
graph/right triangle. -/
noncomputable def sbSelectedRightBranchInSelectedGraphRightMiddle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)
    (R.sbFiniteSourceCover_le_selectedGraphRightSourceCover L hind)

/-- The whole selected `b` branch carried into the middle field of the
finite source-extended triangle. -/
noncomputable def sbSelectedRightBranchToFiniteCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightBFiniteCommonChartSourceField L hind)).comp
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching whole-branch map in the target field of the extended `b`
triangle. -/
noncomputable def sbSelectedRightBranchToFiniteCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightBFiniteCommonChartSourceField L hind)).comp
    ((R.sbSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom)

set_option synthInstance.maxHeartbeats 100000 in
-- The statement unfolds the nested selected source and transported fields.
set_option maxHeartbeats 2000000 in
/-- The extended semantic right arrow restricts on the entire selected
complete `b` branch to the named target map above. -/
theorem sbFiniteCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbFiniteCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sbSelectedRightBranchToFiniteCommonMiddleRingHom L hind) =
      R.sbSelectedRightBranchToFiniteCommonTargetRingHom L hind := by
  let T := R.sbSelectedGraphRightCompositionTriangle L hind
  let X := R.rightBFiniteCommonChartSourceField L hind
  let branch :=
    (R.sbSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom
  have h := T.sourceExtensionRightEquiv_comp_middleRingHom X
  have hc := congrArg (fun f ↦ f.comp branch) h
  simpa only [T, X, branch, sbFiniteCommonCompositionTriangle,
    FieldEquiv.CompositionTriangle.sourceExtension,
    sbSelectedRightBranchToFiniteCommonMiddleRingHom,
    sbSelectedRightBranchToFiniteCommonTargetRingHom, RingHom.comp_assoc]
    using hc

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
