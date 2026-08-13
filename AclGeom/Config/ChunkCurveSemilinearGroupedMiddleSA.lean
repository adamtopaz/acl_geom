/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge

/-!
# The repeated-sA anchors on the enlarged grouped source

The two selected occurrences of `sA` already map coherently into one
pairwise total-field anchor inside the comparison source cover.  This file
extends both anchor-aligning deck transformations through the selected graph
source and its right-cover enlargement.  Exact restriction equations are
retained at each finite-cover boundary.

This is the sibling of `ChunkCurveSemilinearGroupedMiddleS`; keeping the two
families separate allows their normal-cover extension proofs to serialize in
parallel.
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

/-- A local short name for the literal common curve-source field. -/
private abbrev groupedSemanticCommonSourceType
    (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D) :=
  ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra tower is hidden behind the selected graph source supremum.
/-- Extend the first `sA` total-anchor alignment from the comparison cover to
the selected graph source. -/
noncomputable def sAaRepeatedSASelectedGraphSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphSourceCover L hind).field := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.sAaRepeatedSATotalAnchorAlignmentAut hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra tower is hidden behind the selected graph source supremum.
/-- Extend the second `sA` total-anchor alignment to the same selected graph
source. -/
noncomputable def sAcRepeatedSASelectedGraphSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphSourceCover L hind).field := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.sAcRepeatedSATotalAnchorAlignmentAut hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the selected-source normal-cover tower.
/-- The first selected-graph extension has exactly its original action on the
whole comparison source cover. -/
@[simp] theorem sAaRepeatedSASelectedGraphSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.sAaRepeatedSASelectedGraphSourceAlignmentAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.sAaRepeatedSATotalAnchorAlignmentAut hind x) := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the selected-source normal-cover tower.
/-- The second selected-graph extension likewise has its original action on
the whole comparison source cover. -/
@[simp] theorem sAcRepeatedSASelectedGraphSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.sAcRepeatedSASelectedGraphSourceAlignmentAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.sAcRepeatedSATotalAnchorAlignmentAut hind x) := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- Extend the first `sA` anchor alignment to the right-enlarged selected
graph source. -/
noncomputable def sAaRepeatedSASelectedGraphRightSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphRightSourceCover L hind).field :=
  R.selectedGraphRightSourceChartAut L hind
    (R.sAaRepeatedSASelectedGraphSourceAlignmentAut L hind)

/-- Extend the second `sA` anchor alignment to the right-enlarged selected
graph source. -/
noncomputable def sAcRepeatedSASelectedGraphRightSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphRightSourceCover L hind).field :=
  R.selectedGraphRightSourceChartAut L hind
    (R.sAcRepeatedSASelectedGraphSourceAlignmentAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the right-enlarged normal-cover tower.
/-- The first right-enlarged extension restricts exactly to its selected-graph
predecessor. -/
@[simp] theorem sAaRepeatedSASelectedGraphRightSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphSourceCover L hind).field) :
    R.sAaRepeatedSASelectedGraphRightSourceAlignmentAut L hind
        (R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind x) =
      R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind
        (R.sAaRepeatedSASelectedGraphSourceAlignmentAut L hind x) :=
  R.selectedGraphRightSourceChartAut_apply L hind
    (R.sAaRepeatedSASelectedGraphSourceAlignmentAut L hind) x

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the right-enlarged normal-cover tower.
/-- The second right-enlarged extension restricts exactly to its selected-graph
predecessor. -/
@[simp] theorem sAcRepeatedSASelectedGraphRightSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphSourceCover L hind).field) :
    R.sAcRepeatedSASelectedGraphRightSourceAlignmentAut L hind
        (R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind x) =
      R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind
        (R.sAcRepeatedSASelectedGraphSourceAlignmentAut L hind x) :=
  R.selectedGraphRightSourceChartAut_apply L hind
    (R.sAcRepeatedSASelectedGraphSourceAlignmentAut L hind) x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
