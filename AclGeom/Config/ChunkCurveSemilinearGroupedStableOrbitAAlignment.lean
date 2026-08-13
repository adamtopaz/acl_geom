/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitA
import AclGeom.Config.ChunkCurveSemilinearGroupedStableMiddle

/-!
# Repeated-arrow alignments on the e/a-stable grouped source

The canonical two-orbit source contains the previous stable grouped source.
Normality therefore extends each established source-linear alignment once
more, without changing its action on the complete previous cover.
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

private abbrev groupedStableOrbitAlignmentSourceType :=
  ↥R.semanticCommonSourceField

set_option synthInstance.maxHeartbeats 100000 in
-- The normal extension crosses the canonical-closure comparison and a sup.
set_option maxHeartbeats 800000 in
-- The preceding stable source is included as the first orbit summand.
/-- Extend a source-linear automorphism of the preceding stable source to the
`e/a`-stable two-orbit source. -/
noncomputable def groupedStableAOrbitSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (R.groupedStableSourceField L hind) ≃ₐ[groupedStableOrbitAlignmentSourceType R]
      (R.groupedStableSourceField L hind)) :
    (R.groupedStableAOrbitSourceCover L hind).field ≃ₐ[
      groupedStableOrbitAlignmentSourceType R]
      (R.groupedStableAOrbitSourceCover L hind).field := by
  letI : Normal (groupedStableOrbitAlignmentSourceType R)
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.groupedStableAOrbitSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.groupedStableSourceToAOrbitSourceAlgHom L hind) σ

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction unfolds the same canonical comparison and orbit inclusion.
set_option maxHeartbeats 800000 in
-- This is the defining equation of normal extension along that inclusion.
/-- The extended automorphism retains its exact action on the whole preceding
stable grouped source. -/
@[simp] theorem groupedStableAOrbitSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (R.groupedStableSourceField L hind) ≃ₐ[groupedStableOrbitAlignmentSourceType R]
      (R.groupedStableSourceField L hind))
    (x : R.groupedStableSourceField L hind) :
    R.groupedStableAOrbitSourceChartAut L hind σ
        (R.groupedStableSourceToAOrbitSourceAlgHom L hind x) =
      R.groupedStableSourceToAOrbitSourceAlgHom L hind (σ x) := by
  letI : Normal (groupedStableOrbitAlignmentSourceType R)
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.groupedStableAOrbitSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- The repeated-`s` correction on the `e/a`-stable source. -/
noncomputable def repeatedSGroupedStableAOrbitAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableAOrbitSourceChartAut L hind
    (R.repeatedSGroupedStableAlignmentAut L hind)

/-- The first coherent repeated-`sA` anchor correction on the `e/a`-stable
source. -/
noncomputable def sAaRepeatedSAGroupedStableAOrbitAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableAOrbitSourceChartAut L hind
    (R.sAaRepeatedSAGroupedStableAlignmentAut L hind)

/-- The second coherent repeated-`sA` anchor correction on the same source. -/
noncomputable def sAcRepeatedSAGroupedStableAOrbitAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.groupedStableAOrbitSourceChartAut L hind
    (R.sAcRepeatedSAGroupedStableAlignmentAut L hind)

/-- The final repeated-`s` correction restricts to the preceding stable
correction. -/
@[simp] theorem repeatedSGroupedStableAOrbitAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.groupedStableSourceField L hind) :
    R.repeatedSGroupedStableAOrbitAlignmentAut L hind
        (R.groupedStableSourceToAOrbitSourceAlgHom L hind x) =
      R.groupedStableSourceToAOrbitSourceAlgHom L hind
        (R.repeatedSGroupedStableAlignmentAut L hind x) :=
  R.groupedStableAOrbitSourceChartAut_apply L hind _ x

/-- The first final repeated-`sA` correction restricts to its preceding
stable correction. -/
@[simp] theorem sAaRepeatedSAGroupedStableAOrbitAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.groupedStableSourceField L hind) :
    R.sAaRepeatedSAGroupedStableAOrbitAlignmentAut L hind
        (R.groupedStableSourceToAOrbitSourceAlgHom L hind x) =
      R.groupedStableSourceToAOrbitSourceAlgHom L hind
        (R.sAaRepeatedSAGroupedStableAlignmentAut L hind x) :=
  R.groupedStableAOrbitSourceChartAut_apply L hind _ x

/-- The second final repeated-`sA` correction restricts to its preceding
stable correction. -/
@[simp] theorem sAcRepeatedSAGroupedStableAOrbitAlignmentAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.groupedStableSourceField L hind) :
    R.sAcRepeatedSAGroupedStableAOrbitAlignmentAut L hind
        (R.groupedStableSourceToAOrbitSourceAlgHom L hind x) =
      R.groupedStableSourceToAOrbitSourceAlgHom L hind
        (R.sAcRepeatedSAGroupedStableAlignmentAut L hind x) :=
  R.groupedStableAOrbitSourceChartAut_apply L hind _ x

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
