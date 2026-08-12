/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleE

/-!
# The selected right branch in the extended finite `e` triangle

The selected complete `e` branch already lies in the middle cover obtained
from the established graph/right source.  The old-middle inclusion of a
source-extended triangle carries that whole branch into the new finite
middle field, and the extended right arrow carries it through an exact
commuting square to the new target field.
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

/-- The original `e` composition cover is contained in the established
graph/right source. -/
theorem seFiniteSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seFiniteSourceCover).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  (R.seFiniteSourceCover_le_branchComparisonSourceCover hind).trans
    ((R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind).trans
      (R.selectedGraphSourceCover_le_selectedGraphRightSourceCover L hind))

/-- The selected complete `e` branch in the middle cover of the established
graph/right triangle. -/
noncomputable def seSelectedRightBranchInSelectedGraphRightMiddle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)
    (R.seFiniteSourceCover_le_selectedGraphRightSourceCover L hind)

/-- The whole selected `e` branch carried into the middle field of the
finite source-extended triangle. -/
noncomputable def seSelectedRightBranchToFiniteCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightEFiniteCommonChartSourceField L hind)).comp
    (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching whole-branch map in the target field of the extended `e`
triangle. -/
noncomputable def seSelectedRightBranchToFiniteCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightEFiniteCommonChartSourceField L hind)).comp
    ((R.seSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom)

set_option synthInstance.maxHeartbeats 100000 in
-- The statement unfolds the nested selected source and transported fields.
set_option maxHeartbeats 2000000 in
/-- The extended semantic right arrow restricts on the entire selected
complete `e` branch to the named target map above. -/
theorem seFiniteCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seFiniteCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.seSelectedRightBranchToFiniteCommonMiddleRingHom L hind) =
      R.seSelectedRightBranchToFiniteCommonTargetRingHom L hind := by
  let T := R.seSelectedGraphRightCompositionTriangle L hind
  let X := R.rightEFiniteCommonChartSourceField L hind
  let branch :=
    (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom
  have h := T.sourceExtensionRightEquiv_comp_middleRingHom X
  have hc := congrArg (fun f ↦ f.comp branch) h
  simpa only [T, X, branch, seFiniteCommonCompositionTriangle,
    FieldEquiv.CompositionTriangle.sourceExtension,
    seSelectedRightBranchToFiniteCommonMiddleRingHom,
    seSelectedRightBranchToFiniteCommonTargetRingHom, RingHom.comp_assoc]
    using hc

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
