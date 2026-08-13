/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearStableTriangle
import AclGeom.Correspondence.EmbeddingClosureEquivComposition

/-!
# Semilinear source charts grouped by the repeated left arrows

The earlier inverse source charts carry all four intrinsic right-parameter
germs back to the selected `e` embedding.  That orientation preserves a
single based anchor, but it cannot support a faithful four-arrow restriction:
the two repeated left labels need two source embeddings.

Here the `e` and `b` sources are charted to the selected `e` embedding in the
joint cover, while the `a` and genuine `c` sources are charted to the selected
`a` embedding.  The construction precomposes the selected `e` or `a`
algebraic-closure comparison with the inverse semilinear source equivalence,
then pulls the literal joint cover back along that composite.  Thus all four
charts have one literal codomain, retain the selected whole-source maps, and
have exactly the two intrinsic source restrictions required by the repeated
`s` and `sA` arrows.
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

/-! ### Grouped closure comparisons and finite sources -/

/-- The `a` source closure chart, reoriented so that the transported `a`
germ remains the `a` embedding in the joint target. -/
noncomputable def sAaGroupedSourceClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
    |>.precompRingEquiv
      (R.selectedGraphRightSourceToRightARingEquiv L hind).symm

/-- The `b` source closure chart, reoriented back to the selected `e`
embedding for the repeated-`s` pair. -/
noncomputable def sbGroupedSourceClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.precompRingEquiv
      (R.selectedGraphRightSourceToRightBRingEquiv L hind).symm

/-- The genuine `c` source closure chart, reoriented to the selected `a`
embedding for the repeated-`sA` pair. -/
noncomputable def sAcGroupedSourceClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
    |>.precompRingEquiv
      (R.selectedGraphRightSourceToRightCRingEquiv L hind).symm

/-- Finite `e` pullback source for the grouped repeated-left charts. -/
noncomputable def seGroupedSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackField ⊥

/-- Finite `a` pullback source for the grouped repeated-left charts. -/
noncomputable def sAaGroupedSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedSourceClosureExtension L hind).pullbackField ⊥

/-- Finite `b` pullback source for the grouped repeated-left charts. -/
noncomputable def sbGroupedSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedSourceClosureExtension L hind).pullbackField ⊥

/-- Finite `c` pullback source for the grouped repeated-left charts. -/
noncomputable def sAcGroupedSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedSourceClosureExtension L hind).pullbackField ⊥

/-- The `e` source chart to the literal joint selected graph cover. -/
noncomputable def seGroupedSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackBaseEquiv

/-- The `a` source chart to the literal joint selected graph cover. -/
noncomputable def sAaGroupedSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedSourceClosureExtension L hind).pullbackBaseEquiv

/-- The `b` source chart to the literal joint selected graph cover. -/
noncomputable def sbGroupedSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedSourceClosureExtension L hind).pullbackBaseEquiv

/-- The `c` source chart to the literal joint selected graph cover. -/
noncomputable def sAcGroupedSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedSourceClosureExtension L hind).pullbackBaseEquiv

/-! ### Strict triangles on the grouped sources -/

/-- The strict `s·e=u` triangle extended to the grouped finite source. -/
noncomputable def seGroupedCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seSelectedGraphRightCompositionTriangle L hind).sourceExtension
    (R.seGroupedSourceField L hind)

/-- The inverse-oriented `sA·a=u` triangle extended to the grouped finite
source. -/
noncomputable def sAaGroupedCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sAaGroupedSourceField L hind)

/-- The inverse-oriented `s·b=uB` triangle extended to the grouped finite
source. -/
noncomputable def sbGroupedCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sbGroupedSourceField L hind)

/-- The inverse-oriented `sA·c=uB` triangle extended to the grouped finite
source. -/
noncomputable def sAcGroupedCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcRightSemilinearCompositionTriangle L hind).sourceExtension
    (R.sAcGroupedSourceField L hind)

/-! ### Exact intrinsic source restrictions -/

/-- The common selected `e` source embedding used by both repeated-`s`
faces. -/
noncomputable def groupedSourceS
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointRingHom L hind).comp
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

/-- The common selected `a` source embedding used by both repeated-`sA`
faces. -/
noncomputable def groupedSourceSA
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightAJointRingHom L hind).comp
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

/-- The intrinsic germ included in the grouped `e` source. -/
noncomputable def bGermCoefficientToSeGroupedSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackBaseRingHom.comp
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)

/-- The intrinsic germ included in the grouped `a` source. -/
noncomputable def bGermCoefficientToSAaGroupedSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedSourceClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToRightASourceRingHom L hind)

/-- The intrinsic germ included in the grouped `b` source. -/
noncomputable def bGermCoefficientToSbGroupedSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedSourceClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToRightBSourceRingHom L hind)

/-- The intrinsic germ included in the grouped `c` source. -/
noncomputable def bGermCoefficientToSAcGroupedSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedSourceClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToRightCSourceRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
/-- The grouped `e` chart carries its intrinsic germ to the common
repeated-`s` source embedding. -/
theorem seGroupedSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seGroupedSourceChart L hind
        (R.bGermCoefficientToSeGroupedSource L hind z) =
      R.groupedSourceS L hind z := by
  exact (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackBaseEquiv_pullbackBaseRingHom
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `a` chart carries its intrinsic germ to the common
repeated-`sA` source embedding. -/
theorem sAaGroupedSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaGroupedSourceChart L hind
        (R.bGermCoefficientToSAaGroupedSource L hind z) =
      R.groupedSourceSA L hind z := by
  let C := R.sAaGroupedSourceClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToRightASourceRingHom L hind z)) =
    R.selectedGraphRightSourceToRightAJointRingHom L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.selectedGraphRightSourceToRightAJointRingHom L hind)
    (DFunLike.congr_fun
      (R.rightASourceChart_comp_bGermCoefficient L hind) z)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `b` chart carries its intrinsic germ to the same
repeated-`s` source embedding as the `e` face. -/
theorem sbGroupedSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbGroupedSourceChart L hind
        (R.bGermCoefficientToSbGroupedSource L hind z) =
      R.groupedSourceS L hind z := by
  let C := R.sbGroupedSourceClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToRightBSourceRingHom L hind z)) =
    R.selectedGraphRightSourceToRightEJointRingHom L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.selectedGraphRightSourceToRightEJointRingHom L hind)
    (DFunLike.congr_fun
      (R.rightBSourceChart_comp_bGermCoefficient L hind) z)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `c` chart carries its intrinsic germ to the same
repeated-`sA` source embedding as the `a` face. -/
theorem sAcGroupedSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcGroupedSourceChart L hind
        (R.bGermCoefficientToSAcGroupedSource L hind z) =
      R.groupedSourceSA L hind z := by
  let C := R.sAcGroupedSourceClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToRightCSourceRingHom L hind z)) =
    R.selectedGraphRightSourceToRightAJointRingHom L hind
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.selectedGraphRightSourceToRightAJointRingHom L hind)
    (DFunLike.congr_fun
      (R.rightCSourceChart_comp_bGermCoefficient L hind) z)

/-- Pointwise, the four grouped charts have exactly the two source
restrictions required by the repeated left labels. -/
theorem groupedSourceCharts_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seGroupedSourceChart L hind
          (R.bGermCoefficientToSeGroupedSource L hind z) =
        R.groupedSourceS L hind z ∧
      R.sAaGroupedSourceChart L hind
          (R.bGermCoefficientToSAaGroupedSource L hind z) =
        R.groupedSourceSA L hind z ∧
      R.sbGroupedSourceChart L hind
          (R.bGermCoefficientToSbGroupedSource L hind z) =
        R.groupedSourceS L hind z ∧
      R.sAcGroupedSourceChart L hind
          (R.bGermCoefficientToSAcGroupedSource L hind z) =
        R.groupedSourceSA L hind z :=
  ⟨R.seGroupedSourceChart_bGermCoefficient_apply L hind z,
    R.sAaGroupedSourceChart_bGermCoefficient_apply L hind z,
    R.sbGroupedSourceChart_bGermCoefficient_apply L hind z,
    R.sAcGroupedSourceChart_bGermCoefficient_apply L hind z⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end


end AclGeom
