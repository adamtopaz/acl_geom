/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearStableSource

/-!
# The four semantic triangles on the stable common source

The `e` triangle extends directly across the stable source.  The `a`, `b`,
and genuine `c` triangles extend across its pullbacks through their inverse
semilinear source charts.  Postcomposing the restricted pullback charts with
the four stable selected-source automorphisms gives four nontrivial source
charts with one literal codomain.
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

private abbrev stableTriangleSemanticSourceType :=
  ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField

/-! ### The four stable source triangles and charts -/

/-- The `e` triangle extended directly across the stable source. -/
noncomputable def seRightSemilinearStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.rightSemilinearStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal-cover chart carries a nested algebra tower.
/-- The graph-faithful `e` source chart on the stable source. -/
noncomputable def seRightSemilinearStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightSemilinearStableSourceField L hind)) ≃+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (R.seSemilinearStableSourceChartAut L hind).toRingEquiv

/-- Pull the stable source back through the inverse `a` source chart. -/
noncomputable def sAaRightSemilinearStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sAaRightSemilinearSourceChart L hind)
    (R.rightSemilinearStableSourceField L hind)

/-- The inverse-oriented `a` triangle extended across its stable pullback. -/
noncomputable def sAaRightSemilinearStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sAaRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal-cover chart carries a nested algebra tower.
/-- The stable `a` source chart followed by its selected graph correction. -/
noncomputable def sAaRightSemilinearStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sAaRightSemilinearStableSourceField L hind)) ≃+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (FieldEquiv.CompositionTriangle.commonSourcePullbackChart
      (R.sAaRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)).trans
    (R.sAaSemilinearStableSourceChartAut L hind).toRingEquiv

/-- Pull the stable source back through the inverse `b` source chart. -/
noncomputable def sbRightSemilinearStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sbRightSemilinearSourceChart L hind)
    (R.rightSemilinearStableSourceField L hind)

/-- The inverse-oriented `b` triangle extended across its stable pullback. -/
noncomputable def sbRightSemilinearStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sbRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal-cover chart carries a nested algebra tower.
/-- The stable `b` source chart followed by its selected graph correction. -/
noncomputable def sbRightSemilinearStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sbRightSemilinearStableSourceField L hind)) ≃+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (FieldEquiv.CompositionTriangle.commonSourcePullbackChart
      (R.sbRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)).trans
    (R.sbSemilinearStableSourceChartAut L hind).toRingEquiv

/-- Pull the stable source back through the inverse genuine `c` chart. -/
noncomputable def sAcRightSemilinearStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.CompositionTriangle.commonSourcePullbackField
    (R.sAcRightSemilinearSourceChart L hind)
    (R.rightSemilinearStableSourceField L hind)

/-- The inverse-oriented `c` triangle extended across its stable pullback. -/
noncomputable def sAcRightSemilinearStableCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcRightSemilinearCompositionTriangle L hind)
    |>.sourceExtensionAlongChart
      (R.sAcRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal-cover chart carries a nested algebra tower.
/-- The stable genuine-`c` source chart followed by its selected graph
correction. -/
noncomputable def sAcRightSemilinearStableSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.sAcRightSemilinearStableSourceField L hind)) ≃+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (FieldEquiv.CompositionTriangle.commonSourcePullbackChart
      (R.sAcRightSemilinearSourceChart L hind)
      (R.rightSemilinearStableSourceField L hind)).trans
    (R.sAcSemilinearStableSourceChartAut L hind).toRingEquiv

/-! ### Exact intrinsic source restrictions -/

set_option synthInstance.maxHeartbeats 100000 in
-- The stable intermediate-field tower requires an enlarged search budget.
/-- The intrinsic germ embedded in the stable common source before applying a
selected graph chart. -/
noncomputable def bGermCoefficientToRightSemilinearStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (R.selectedGraphRightSourceToSemilinearStableSource L hind).toRingHom.comp
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable intermediate-field tower requires an enlarged search budget.
/-- The intrinsic `a` germ included in the source of the stable pulled-back
triangle. -/
noncomputable def bGermCoefficientToSAaRightSemilinearStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAaRightSemilinearStableSourceField L hind)) :=
  (algebraMap (↥(R.rightASelectedGraphRightSourceCover L hind).field)
      (↥(R.sAaRightSemilinearStableSourceField L hind))).comp
    (R.bGermCoefficientToRightASourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable intermediate-field tower requires an enlarged search budget.
/-- The intrinsic `b` germ included in the source of the stable pulled-back
triangle. -/
noncomputable def bGermCoefficientToSbRightSemilinearStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sbRightSemilinearStableSourceField L hind)) :=
  (algebraMap (↥(R.rightBSelectedGraphRightSourceCover L hind).field)
      (↥(R.sbRightSemilinearStableSourceField L hind))).comp
    (R.bGermCoefficientToRightBSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable intermediate-field tower requires an enlarged search budget.
/-- The intrinsic algebraic-output `c` germ included in the source of the
stable pulled-back triangle. -/
noncomputable def bGermCoefficientToSAcRightSemilinearStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAcRightSemilinearStableSourceField L hind)) :=
  (algebraMap (↥(R.rightCSelectedGraphRightSourceCover L hind).field)
      (↥(R.sAcRightSemilinearStableSourceField L hind))).comp
    (R.bGermCoefficientToRightCSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable intermediate-field tower requires an enlarged search budget.
/-- The intrinsic germ after applying a selected graph/right source chart and
then including it in the stable source. -/
noncomputable def chartedBGermCoefficientToRightSemilinearStableSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ :
      (↥(R.selectedGraphRightSourceCover L hind).field)
        ≃ₐ[stableTriangleSemanticSourceType R]
        (↥(R.selectedGraphRightSourceCover L hind).field)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  (R.selectedGraphRightSourceToSemilinearStableSource L hind).toRingHom.comp
    (σ.toRingHom.comp
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal-cover extension carries a nested algebra tower.
set_option maxHeartbeats 800000 in
-- The pointwise restriction proof needs a larger heartbeat budget.
/-- Applying a stable extended chart to the uncharted intrinsic germ gives
the selected charted intrinsic embedding. -/
theorem semilinearStableSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ :
      (↥(R.selectedGraphRightSourceCover L hind).field)
        ≃ₐ[stableTriangleSemanticSourceType R]
        (↥(R.selectedGraphRightSourceCover L hind).field)) :
    (R.semilinearStableSourceChartAut L hind σ).toRingEquiv.toRingHom.comp
        (R.bGermCoefficientToRightSemilinearStableSourceRingHom L hind) =
      R.chartedBGermCoefficientToRightSemilinearStableSourceRingHom
        L hind σ := by
  apply RingHom.ext
  intro z
  exact R.semilinearStableSourceChartAut_apply L hind σ
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable pullback and normal-cover extension carry nested algebra towers.
set_option maxHeartbeats 800000 in
-- The generic source restriction proof needs a larger heartbeat budget.
/-- A pulled-back source chart followed by a stable selected correction has
the expected intrinsic restriction whenever the old inverse chart does. -/
theorem semilinearStablePullbackSourceChart_comp
    {X W : Type u} [Field X] [Semiring W]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (sourceChart : X ≃+*
      (↥(R.selectedGraphRightSourceCover L hind).field))
    (σ :
      (↥(R.selectedGraphRightSourceCover L hind).field)
        ≃ₐ[stableTriangleSemanticSourceType R]
        (↥(R.selectedGraphRightSourceCover L hind).field))
    (gX : W →+* X)
    (gN : W →+* (↥(R.selectedGraphRightSourceCover L hind).field))
    (h : sourceChart.toRingHom.comp gX = gN) :
    ((FieldEquiv.CompositionTriangle.commonSourcePullbackChart sourceChart
        (R.rightSemilinearStableSourceField L hind)).trans
      (R.semilinearStableSourceChartAut L hind σ).toRingEquiv).toRingHom.comp
        ((algebraMap X
          (↥(FieldEquiv.CompositionTriangle.commonSourcePullbackField
            sourceChart (R.rightSemilinearStableSourceField L hind)))).comp gX) =
      (R.selectedGraphRightSourceToSemilinearStableSource L hind).toRingHom.comp
        (σ.toRingHom.comp gN) := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply]
  calc
    R.semilinearStableSourceChartAut L hind σ
        (FieldEquiv.CompositionTriangle.commonSourcePullbackChart sourceChart
          (R.rightSemilinearStableSourceField L hind)
          (algebraMap X
            (↥(FieldEquiv.CompositionTriangle.commonSourcePullbackField
              sourceChart (R.rightSemilinearStableSourceField L hind)))
            (gX z))) =
      R.semilinearStableSourceChartAut L hind σ
        (algebraMap _ _ (sourceChart (gX z))) :=
          congrArg (R.semilinearStableSourceChartAut L hind σ)
            (FieldEquiv.CompositionTriangle.commonSourcePullbackChart_algebraMap
              sourceChart (R.rightSemilinearStableSourceField L hind) (gX z))
    _ = R.selectedGraphRightSourceToSemilinearStableSource L hind
        (σ (sourceChart (gX z))) :=
      R.semilinearStableSourceChartAut_apply L hind σ (sourceChart (gX z))
    _ = R.selectedGraphRightSourceToSemilinearStableSource L hind
        (σ (gN z)) :=
      congrArg
        (fun y ↦ R.selectedGraphRightSourceToSemilinearStableSource L hind
          (σ y))
        (DFunLike.congr_fun h z)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable source chart contains a nested normal-cover extension.
/-- Exact intrinsic source restriction for the stable `e` face. -/
theorem seRightSemilinearStableSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearStableSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToRightSemilinearStableSourceRingHom L hind) =
      R.chartedBGermCoefficientToRightSemilinearStableSourceRingHom L hind
        (R.seSelectedGraphRightSourceChartAut L hind) := by
  simpa only [seRightSemilinearStableSourceChart,
      seSemilinearStableSourceChartAut] using
    R.semilinearStableSourceChart_comp_bGermCoefficient L hind
      (R.seSelectedGraphRightSourceChartAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The stable source chart contains nested pullback and normal-cover towers.
/-- Exact intrinsic source restriction for the stable `a` face. -/
theorem sAaRightSemilinearStableSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearStableSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSAaRightSemilinearStableSourceRingHom L hind) =
      R.chartedBGermCoefficientToRightSemilinearStableSourceRingHom L hind
        (R.sAaSelectedGraphRightSourceChartAut L hind) := by
  apply RingHom.ext
  intro z
  exact DFunLike.congr_fun (R.semilinearStablePullbackSourceChart_comp L hind
      (R.sAaRightSemilinearSourceChart L hind)
      (R.sAaSelectedGraphRightSourceChartAut L hind)
      (R.bGermCoefficientToRightASourceRingHom L hind)
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)
      (R.rightASourceChart_comp_bGermCoefficient L hind)) z

set_option synthInstance.maxHeartbeats 100000 in
-- The stable source chart contains nested pullback and normal-cover towers.
/-- Exact intrinsic source restriction for the stable `b` face. -/
theorem sbRightSemilinearStableSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRightSemilinearStableSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSbRightSemilinearStableSourceRingHom L hind) =
      R.chartedBGermCoefficientToRightSemilinearStableSourceRingHom L hind
        (R.sbSelectedGraphRightSourceChartAut L hind) := by
  apply RingHom.ext
  intro z
  exact DFunLike.congr_fun (R.semilinearStablePullbackSourceChart_comp L hind
      (R.sbRightSemilinearSourceChart L hind)
      (R.sbSelectedGraphRightSourceChartAut L hind)
      (R.bGermCoefficientToRightBSourceRingHom L hind)
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)
      (R.rightBSourceChart_comp_bGermCoefficient L hind)) z

set_option synthInstance.maxHeartbeats 100000 in
-- The genuine-c chart contains nested pullback and normal-cover towers.
/-- Exact intrinsic source restriction for the stable genuine `c` face. -/
theorem sAcRightSemilinearStableSourceChart_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRightSemilinearStableSourceChart L hind).toRingHom.comp
        (R.bGermCoefficientToSAcRightSemilinearStableSourceRingHom L hind) =
      R.chartedBGermCoefficientToRightSemilinearStableSourceRingHom L hind
        (R.sAcSelectedGraphRightSourceChartAut L hind) := by
  apply RingHom.ext
  intro z
  exact DFunLike.congr_fun (R.semilinearStablePullbackSourceChart_comp L hind
      (R.sAcRightSemilinearSourceChart L hind)
      (R.sAcSelectedGraphRightSourceChartAut L hind)
      (R.bGermCoefficientToRightCSourceRingHom L hind)
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)
      (R.rightCSourceChart_comp_bGermCoefficient L hind)) z

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
