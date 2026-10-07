/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleA
import AclGeom.Correspondence.CompositionTriangleCommonSource

/-! # The selected right branch in the extended finite `a` triangle -/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

/- The finite common-chart and triangle fields are transparent aliases.
Lean 4.34 needs to unfold them when synthesizing scalar structures; this
scoped setting affects elaboration only, while the kernel checks all terms. -/
section FiniteTriangleAliases
set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The original `a` composition cover is contained in the established
graph/right source. -/
theorem sAaFiniteSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaFiniteSourceCover).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  (R.sAaFiniteSourceCover_le_branchComparisonSourceCover hind).trans
    ((R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind).trans
      (R.selectedGraphSourceCover_le_selectedGraphRightSourceCover L hind))

/-- The selected complete `a` branch in the middle cover of the established
graph/right triangle. -/
noncomputable def sAaSelectedRightBranchInSelectedGraphRightMiddle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)
    (R.sAaFiniteSourceCover_le_selectedGraphRightSourceCover L hind)

/-- The whole selected `a` branch carried into the middle field of the
finite source-extended triangle. -/
noncomputable def sAaSelectedRightBranchToFiniteCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightAFiniteCommonChartSourceField L hind)).comp
    (R.sAaSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

/-- The matching whole-branch map in the target field of the extended `a`
triangle. -/
noncomputable def sAaSelectedRightBranchToFiniteCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightAFiniteCommonChartSourceField L hind)).comp
    ((R.sAaSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.sAaSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom)

set_option synthInstance.maxHeartbeats 100000 in
-- The statement unfolds the nested selected source and transported fields.
set_option maxHeartbeats 2000000 in
/-- The extended semantic right arrow restricts on the entire selected
complete `a` branch to the named target map above. -/
theorem sAaFiniteCommon_right_comp_selectedRightBranch
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaFiniteCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaSelectedRightBranchToFiniteCommonMiddleRingHom L hind) =
      R.sAaSelectedRightBranchToFiniteCommonTargetRingHom L hind := by
  unfold sAaFiniteCommonCompositionTriangle
    sAaSelectedRightBranchToFiniteCommonMiddleRingHom
    sAaSelectedRightBranchToFiniteCommonTargetRingHom
  exact (R.sAaSelectedGraphRightCompositionTriangle L hind)
    |>.sourceExtensionRightEquiv_comp_middleRingHom_comp
      (R.rightAFiniteCommonChartSourceField L hind)
      (R.sAaSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom

end FiniteTriangleAliases

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
