/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedMiddleSA
import AclGeom.Config.ChunkCurveSemilinearGroupedStableAlignment

/-!
# The repeated-sA anchors on the stable grouped cover

Both coherent `sA` total-anchor corrections extend to the finite semantic
normal closure of the grouped joint cover.  They remain separate so their
later relative alignment can be oriented without losing either selected
whole-branch restriction.
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

/-- The first coherent `sA` total-anchor correction on the stable grouped
cover. -/
noncomputable def sAaRepeatedSAGroupedStableAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableSourceChartAut L hind
    (R.sAaRepeatedSASelectedGraphRightSourceAlignmentAut L hind)

/-- The second coherent `sA` total-anchor correction on the same stable
grouped cover. -/
noncomputable def sAcRepeatedSAGroupedStableAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableSourceChartAut L hind
    (R.sAcRepeatedSASelectedGraphRightSourceAlignmentAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The exact restriction traverses both finite source enlargements.
set_option maxHeartbeats 800000 in
-- The stable normal-cover extension retains the selected source embedding.
/-- The first stable `sA` correction restricts to its established action on
the complete selected graph/right source. -/
@[simp] theorem sAaRepeatedSAGroupedStableAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.sAaRepeatedSAGroupedStableAlignmentAut L hind
        (R.selectedGraphRightSourceToGroupedStableSource L hind x) =
      R.selectedGraphRightSourceToGroupedStableSource L hind
        (R.sAaRepeatedSASelectedGraphRightSourceAlignmentAut L hind x) :=
  R.groupedStableSourceChartAut_apply L hind
    (R.sAaRepeatedSASelectedGraphRightSourceAlignmentAut L hind) x

set_option synthInstance.maxHeartbeats 100000 in
-- The exact restriction traverses both finite source enlargements.
set_option maxHeartbeats 800000 in
-- The stable normal-cover extension retains the selected source embedding.
/-- The second stable `sA` correction restricts to its established action on
the complete selected graph/right source. -/
@[simp] theorem sAcRepeatedSAGroupedStableAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.sAcRepeatedSAGroupedStableAlignmentAut L hind
        (R.selectedGraphRightSourceToGroupedStableSource L hind x) =
      R.selectedGraphRightSourceToGroupedStableSource L hind
        (R.sAcRepeatedSASelectedGraphRightSourceAlignmentAut L hind x) :=
  R.groupedStableSourceChartAut_apply L hind
    (R.sAcRepeatedSASelectedGraphRightSourceAlignmentAut L hind) x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
