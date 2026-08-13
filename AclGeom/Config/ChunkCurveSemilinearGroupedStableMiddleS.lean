/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedMiddleS
import AclGeom.Config.ChunkCurveSemilinearGroupedStableAlignment

/-!
# The repeated-s alignment on the stable grouped cover

The repeated-`s` alignment now extends from the complete selected graph/right
source to the finite semantic normal closure of the joint cover.  Its exact
restriction remains available on the whole predecessor cover.
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

/-- The repeated-`s` deck transformation on the finite stable grouped cover. -/
noncomputable def repeatedSGroupedStableAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableSourceChartAut L hind
    (R.repeatedSSelectedGraphRightSourceAlignmentAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The exact restriction traverses both finite source enlargements.
set_option maxHeartbeats 800000 in
-- The stable normal-cover extension retains the selected source embedding.
/-- The stable repeated-`s` alignment restricts to its established action on
the whole selected graph/right source. -/
@[simp] theorem repeatedSGroupedStableAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.repeatedSGroupedStableAlignmentAut L hind
        (R.selectedGraphRightSourceToGroupedStableSource L hind x) =
      R.selectedGraphRightSourceToGroupedStableSource L hind
        (R.repeatedSSelectedGraphRightSourceAlignmentAut L hind x) :=
  R.groupedStableSourceChartAut_apply L hind
    (R.repeatedSSelectedGraphRightSourceAlignmentAut L hind) x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
