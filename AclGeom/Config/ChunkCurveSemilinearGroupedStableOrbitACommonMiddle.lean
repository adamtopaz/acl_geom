/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitAAlignment

/-!
# Candidate middle orientations on the final grouped source

The repeated-`s` correction identifies its two complete selected left
branches.  The relative correction between the two repeated-`sA` anchors
does the same for the other pair.  These corrections are linear over the
semantic source and hence fix both intrinsic source embeddings pointwise.

After the repeated-`s` correction, the finite semilinear `e → a` chart
moves the repeated-`s` intrinsic source to the repeated-`sA` source.  Thus
the two candidate orientations have one literal codomain and one literal
whole-germ coefficient restriction.

These equations do not yet identify the face-specific selected left-branch
embeddings.  Since a common postcomposition is injective, that identification
must first be built into face-specific source charts, simultaneously with the
selected direct branches, before these orientations can supply the common
middle chart of the final non-induced four-triangle reference.
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

private abbrev groupedAOrbitCommonMiddleSourceType
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ↥(R.groupedStableAOrbitSourceCover L hind).field

/-- The candidate repeated-`s` left orientation: first apply the exact whole-branch
`e/b` correction, then cross to the `sA` intrinsic presentation. -/
noncomputable def groupedStableAOrbitLeftSChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    groupedAOrbitCommonMiddleSourceType R L hind ≃+*
      groupedAOrbitCommonMiddleSourceType R L hind :=
  (R.repeatedSGroupedStableAOrbitAlignmentAut L hind).toRingEquiv.trans
    (R.groupedStableASourceChartRingEquiv L hind)

/-- The candidate repeated-`sA` left orientation is the relative correction from the
first selected `sA` branch to the second through their common total-field
anchor. -/
noncomputable def groupedStableAOrbitLeftSAChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    groupedAOrbitCommonMiddleSourceType R L hind ≃+*
      groupedAOrbitCommonMiddleSourceType R L hind :=
  (R.sAaRepeatedSAGroupedStableAOrbitAlignmentAut L hind).toRingEquiv.trans
    (R.sAcRepeatedSAGroupedStableAOrbitAlignmentAut L hind).symm.toRingEquiv

/-- The repeated-`s` candidate orientation carries the complete intrinsic
source to the chosen common coefficient embedding. -/
theorem groupedStableAOrbitLeftSChart_comp_sourceS
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableAOrbitLeftSChart L hind).toRingHom.comp
        (R.groupedStableAOrbitSourceS L hind) =
      R.groupedStableAOrbitSourceSA L hind := by
  apply RingHom.ext
  intro x
  change R.groupedStableASourceChartRingEquiv L hind
      (R.repeatedSGroupedStableAOrbitAlignmentAut L hind
        (R.groupedStableAOrbitSourceS L hind x)) = _
  rw [R.groupedStableAOrbitSourceS_apply L hind,
    (R.repeatedSGroupedStableAOrbitAlignmentAut L hind).commutes,
    R.groupedStableASourceChartRingEquiv_algebraMap L hind,
    R.groupedStableAOrbitSourceSA_apply L hind]
  exact congrArg
    (algebraMap (↥R.semanticCommonSourceField)
      (↥(R.groupedStableAOrbitSourceCover L hind).field))
    (R.commonSourceRightAAut_comp_seBGermCoefficient L hind x)

/-- The relative repeated-`sA` correction fixes the same intrinsic middle
embedding because both constituent branch corrections are source-linear. -/
theorem groupedStableAOrbitLeftSAChart_comp_sourceSA
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableAOrbitLeftSAChart L hind).toRingHom.comp
        (R.groupedStableAOrbitSourceSA L hind) =
      R.groupedStableAOrbitSourceSA L hind := by
  apply RingHom.ext
  intro x
  change (R.sAcRepeatedSAGroupedStableAOrbitAlignmentAut L hind).symm
      (R.sAaRepeatedSAGroupedStableAOrbitAlignmentAut L hind
        (R.groupedStableAOrbitSourceSA L hind x)) = _
  rw [R.groupedStableAOrbitSourceSA_apply L hind,
    (R.sAaRepeatedSAGroupedStableAOrbitAlignmentAut L hind).commutes,
    (R.sAcRepeatedSAGroupedStableAOrbitAlignmentAut L hind).symm.commutes]

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
