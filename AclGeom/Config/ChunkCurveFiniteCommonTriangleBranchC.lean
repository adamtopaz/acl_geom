/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleC

/-! # The selected right branch in the extended finite `c` triangle -/

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

/-- The original `c` composition cover is contained in the established
graph/right source. -/
theorem sAcFiniteSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcFiniteSourceCover).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  (R.sAcFiniteSourceCover_le_branchComparisonSourceCover hind).trans
    ((R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind).trans
      (R.selectedGraphSourceCover_le_selectedGraphRightSourceCover L hind))

/-- The selected complete `c` branch in the middle cover of the established
graph/right triangle. -/
noncomputable def sAcSelectedRightBranchInSelectedGraphRightMiddle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)
    (R.sAcFiniteSourceCover_le_selectedGraphRightSourceCover L hind)

/-- The whole selected `c` branch carried into the middle field of the
finite source-extended triangle. -/
noncomputable def sAcSelectedRightBranchToFiniteCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightCFiniteCommonChartSourceField L hind)).comp
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching whole-branch map in the target field of the extended `c`
triangle. -/
noncomputable def sAcSelectedRightBranchToFiniteCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightCFiniteCommonChartSourceField L hind)).comp
    ((R.sAcSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.sAcSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom)

set_option synthInstance.maxHeartbeats 100000 in
-- The statement unfolds the nested selected source and transported fields.
set_option maxHeartbeats 2000000 in
/-- The extended semantic right arrow restricts on the entire selected
complete `c` branch to the named target map above. -/
theorem sAcFiniteCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcFiniteCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcSelectedRightBranchToFiniteCommonMiddleRingHom L hind) =
      R.sAcSelectedRightBranchToFiniteCommonTargetRingHom L hind := by
  let T := R.sAcSelectedGraphRightCompositionTriangle L hind
  let X := R.rightCFiniteCommonChartSourceField L hind
  let branch :=
    (R.sAcSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom
  have h := T.sourceExtensionRightEquiv_comp_middleRingHom X
  have hc := congrArg (fun f ↦ f.comp branch) h
  simpa only [T, X, branch, sAcFiniteCommonCompositionTriangle,
    FieldEquiv.CompositionTriangle.sourceExtension,
    sAcSelectedRightBranchToFiniteCommonMiddleRingHom,
    sAcSelectedRightBranchToFiniteCommonTargetRingHom, RingHom.comp_assoc]
    using hc

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
