/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge

/-!
# The repeated-s alignment on the enlarged grouped source

The semantic common-source cover already contains a deck transformation that
aligns the two selected occurrences of the repeated `s` branch.  This file
extends that transformation first to the selected graph source and then to the
right-enlarged selected graph source.  Both extensions retain exact pointwise
restriction equations on their entire predecessor covers.

Keeping this lift in its own leaf lets the repeated-`s` and repeated-`sA`
middle-chart constructions elaborate independently.
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
/-- Extend the established repeated-`s` alignment from the comparison source
cover to the selected graph source. -/
noncomputable def repeatedSSelectedGraphSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphSourceCover L hind).field := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.repeatedSBranchAlignmentAut hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the same hidden normal-cover tower.
/-- The selected-graph extension acts by the original repeated-`s` alignment
on the entire comparison source cover. -/
@[simp] theorem repeatedSSelectedGraphSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.repeatedSSelectedGraphSourceAlignmentAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.repeatedSBranchAlignmentAut hind x) := by
  letI : Normal (groupedSemanticCommonSourceType R)
      (R.selectedGraphSourceCover L hind).field :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- Extend the repeated-`s` alignment once more to the right-enlarged selected
graph source. -/
noncomputable def repeatedSSelectedGraphRightSourceAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceCover L hind).field
        ≃ₐ[groupedSemanticCommonSourceType R]
      (R.selectedGraphRightSourceCover L hind).field :=
  R.selectedGraphRightSourceChartAut L hind
    (R.repeatedSSelectedGraphSourceAlignmentAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the right-enlarged normal-cover tower.
/-- The second extension restricts exactly to the first extension on the
entire selected graph source.  Together with
`repeatedSSelectedGraphSourceAlignmentAut_apply`, this gives the original
alignment's action without forcing Lean to normalize two nested inclusions in
one declaration. -/
@[simp] theorem repeatedSSelectedGraphRightSourceAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphSourceCover L hind).field) :
    R.repeatedSSelectedGraphRightSourceAlignmentAut L hind
        (R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind x) =
      R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind
        (R.repeatedSSelectedGraphSourceAlignmentAut L hind x) :=
  R.selectedGraphRightSourceChartAut_apply L hind
    (R.repeatedSSelectedGraphSourceAlignmentAut L hind) x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
