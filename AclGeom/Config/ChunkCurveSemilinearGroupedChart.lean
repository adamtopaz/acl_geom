/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedBranch

/-!
# The finite common-chart interface for the grouped four-arrow triangles

The four grouped triangles already have one literal source-chart codomain and
retain their complete selected right branches.  This file isolates the six
cross-face squares still required from common middle and target charts.  Any
inhabitant of `GroupedCommonChartData` produces the non-induced four-triangle
reference, its faithful four-arrow diagram, and the intrinsic
`RightRestriction` in one step.

This interface is deliberately downstream of the four branch-specific sibling
modules.  Constructing the common middle and target covers can therefore be
split into independent leaves without making their large selected-branch
proofs elaborate serially again.
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

/-- Six exact whole-germ squares for independently chosen common left and
direct arrows on the grouped joint source.  The first two squares give one
literal middle embedding.  The remaining four retain the normalized
`e/a/b/c` target embeddings through the repeated `u` and `uB` arrows. -/
structure GroupedCommonChartData
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (Y Z : Type u) [Field Y] [Field Z] where
  /-- Common realization of the repeated left arrow `s`. -/
  leftS : (R.fourSelectedGraphJointCover L hind).field ≃+* Y
  /-- Common realization of the repeated left arrow `sA`. -/
  leftSA : (R.fourSelectedGraphJointCover L hind).field ≃+* Y
  /-- Common realization of the repeated direct arrow `u`. -/
  directU : (R.fourSelectedGraphJointCover L hind).field ≃+* Z
  /-- Common realization of the repeated direct arrow `uB`. -/
  directUB : (R.fourSelectedGraphJointCover L hind).field ≃+* Z
  /-- The one intrinsic coefficient embedding in the common middle chart. -/
  middle : (w.bGermCoefficientField hψ) →+* Y
  /-- The normalized `e` embedding in the common target chart. -/
  mapE : (w.bGermCoefficientField hψ) →+* Z
  /-- The normalized `a` embedding in the common target chart. -/
  mapA : (w.bGermCoefficientField hψ) →+* Z
  /-- The normalized `b` embedding in the common target chart. -/
  mapB : (w.bGermCoefficientField hψ) →+* Z
  /-- The normalized algebraic-output `c` embedding in the common target
  chart. -/
  mapC : (w.bGermCoefficientField hψ) →+* Z
  /-- The `s` arrow carries its grouped source embedding to `middle`. -/
  leftS_source : leftS.toRingHom.comp (R.groupedSourceS L hind) = middle
  /-- The `sA` arrow carries its grouped source embedding to the same
  `middle`. -/
  leftSA_source : leftSA.toRingHom.comp (R.groupedSourceSA L hind) = middle
  /-- The first restriction of the repeated direct `u` arrow. -/
  directU_sourceS : directU.toRingHom.comp (R.groupedSourceS L hind) = mapE
  /-- The second restriction of the repeated direct `u` arrow. -/
  directU_sourceSA : directU.toRingHom.comp (R.groupedSourceSA L hind) = mapA
  /-- The first restriction of the repeated direct `uB` arrow. -/
  directUB_sourceS : directUB.toRingHom.comp (R.groupedSourceS L hind) = mapB
  /-- The second restriction of the repeated direct `uB` arrow. -/
  directUB_sourceSA :
    directUB.toRingHom.comp (R.groupedSourceSA L hind) = mapC

set_option synthInstance.maxHeartbeats 100000 in
-- Resolving the four nested algebraic-closure chart instances together is
-- substantially harder than checking any branch-specific source chart.
set_option maxHeartbeats 1000000 in
-- Comparing the four instantiated triangle types crosses the ordinary
-- deterministic elaboration budget when the declaration is serialized.
/-- The non-induced four-triangle reference supplied by a grouped common
chart.  Its middle and target charts are independently prescribed by the
four arrows in `C`, rather than being gauge-normalized from source charts
alone. -/
noncomputable def groupedFourTriangleReference
    {Y Z : Type u} [Field Y] [Field Z]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (C : R.GroupedCommonChartData L hind Y Z) :=
  FieldEquiv.FourTriangleReference.ofCommonLeftDirect
    (R.seGroupedCompositionTriangle L hind)
    (R.sAaGroupedCompositionTriangle L hind)
    (R.sbGroupedCompositionTriangle L hind)
    (R.sAcGroupedCompositionTriangle L hind)
    (R.seGroupedSourceChart L hind)
    (R.sAaGroupedSourceChart L hind)
    (R.sbGroupedSourceChart L hind)
    (R.sAcGroupedSourceChart L hind)
    C.leftS C.leftSA C.directU C.directUB

/-- The faithful semantic four-arrow diagram obtained from a grouped common
chart. -/
noncomputable def groupedFourArrowDiagram
    {Y Z : Type u} [Field Y] [Field Z]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (C : R.GroupedCommonChartData L hind Y Z) :=
  (R.groupedFourTriangleReference L hind C).toFourArrowDiagram

set_option maxHeartbeats 1000000 in
-- The result compares eight projections of a deeply instantiated reference;
-- package serialization needs more reduction steps than a direct source check.
/-- The grouped semantic diagram retains the four independently prescribed
left and direct arrows, and its right arrows are their nontrivial quotients. -/
theorem groupedFourArrowDiagram_arrows
    {Y Z : Type u} [Field Y] [Field Z]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (C : R.GroupedCommonChartData L hind Y Z) :
    (R.groupedFourArrowDiagram L hind C).leftS = C.leftS ∧
      (R.groupedFourArrowDiagram L hind C).leftSA = C.leftSA ∧
      (R.groupedFourArrowDiagram L hind C).rightE =
        C.leftS.symm.trans C.directU ∧
      (R.groupedFourArrowDiagram L hind C).rightA =
        C.leftSA.symm.trans C.directU ∧
      (R.groupedFourArrowDiagram L hind C).rightB =
        C.leftS.symm.trans C.directUB ∧
      (R.groupedFourArrowDiagram L hind C).rightC =
        C.leftSA.symm.trans C.directUB ∧
      (R.groupedFourArrowDiagram L hind C).compositeU = C.directU ∧
      (R.groupedFourArrowDiagram L hind C).compositeUB = C.directUB := by
  exact FieldEquiv.FourTriangleReference.ofCommonLeftDirect_toFourArrowDiagram
    (R.seGroupedCompositionTriangle L hind)
    (R.sAaGroupedCompositionTriangle L hind)
    (R.sbGroupedCompositionTriangle L hind)
    (R.sAcGroupedCompositionTriangle L hind)
    (R.seGroupedSourceChart L hind)
    (R.sAaGroupedSourceChart L hind)
    (R.sbGroupedSourceChart L hind)
    (R.sAcGroupedSourceChart L hind)
    C.leftS C.leftSA C.directU C.directUB

/-- The six grouped source squares instantiate the non-vacuous intrinsic
right restriction of the resulting semantic four-arrow diagram. -/
noncomputable def groupedRightRestriction
    {Y Z : Type u} [Field Y] [Field Z]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (C : R.GroupedCommonChartData L hind Y Z) :
    (R.groupedFourArrowDiagram L hind C).RightRestriction
      (w.bGermCoefficientField hψ) := by
  let A := R.groupedFourArrowDiagram L hind C
  apply FieldEquiv.FourArrowDiagram.RightRestriction.ofSourceRestrictions
    (D := A)
    C.middle
    (R.groupedSourceS L hind)
    (R.groupedSourceSA L hind)
    C.mapE C.mapA C.mapB C.mapC
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).1]
    exact C.leftS_source
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).2.1]
    exact C.leftSA_source
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).2.2.2.2.2.2.1]
    exact C.directU_sourceS
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).2.2.2.2.2.2.1]
    exact C.directU_sourceSA
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).2.2.2.2.2.2.2]
    exact C.directUB_sourceS
  · rw [(R.groupedFourArrowDiagram_arrows L hind C).2.2.2.2.2.2.2]
    exact C.directUB_sourceSA

/-- Faithful cancellation on any completed grouped common chart, restricted
to the one whole intrinsic germ field. -/
theorem groupedRightRestriction_mapC_factorization
    {Y Z : Type u} [Field Y] [Field Z]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (C : R.GroupedCommonChartData L hind Y Z) :
    C.mapC =
      (R.groupedFourArrowDiagram L hind C).rightB.toRingHom.comp
        ((R.groupedFourArrowDiagram L hind C).rightE.symm.toRingHom.comp
          C.mapA) := by
  change (R.groupedRightRestriction L hind C).mapC =
    (R.groupedFourArrowDiagram L hind C).rightB.toRingHom.comp
      ((R.groupedFourArrowDiagram L hind C).rightE.symm.toRingHom.comp
        (R.groupedRightRestriction L hind C).mapA)
  exact (R.groupedRightRestriction L hind C).mapC_factorization

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
