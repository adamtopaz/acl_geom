/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableCover

/-!
# The two intrinsic source embeddings in the stable grouped cover

The stable grouped cover contains the earlier four-face joint cover
literally.  Composing that inclusion with the two grouped intrinsic source
maps gives the repeated-`s` and repeated-`sA` embeddings used by all four
stable pullback charts.
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

/-- The literal inclusion of the four-face joint cover into its stable
semantic normal closure. -/
noncomputable def groupedJointCoverToStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.fourSelectedGraphJointCover L hind).field →+*
      (R.groupedStableSourceField L hind) :=
  algebraMap _ _

/-- The repeated-`s` intrinsic germ embedding in the stable grouped cover. -/
noncomputable def groupedStableSourceS
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToStableSourceRingHom L hind).comp
    (R.groupedSourceS L hind)

/-- The repeated-`sA` intrinsic germ embedding in the same stable cover. -/
noncomputable def groupedStableSourceSA
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToStableSourceRingHom L hind).comp
    (R.groupedSourceSA L hind)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
