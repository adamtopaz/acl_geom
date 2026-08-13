/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitA

/-!
# The e triangle on the e/a-stable grouped source
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

set_option synthInstance.maxHeartbeats 100000 in
-- Inferring the deeply nested pullback source field needs extra synthesis time.
/-- Embed the grouped `e` source in the final orbit cover through its joint
source chart. -/
noncomputable def seGroupedAOrbitSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.seGroupedSourceChart L hind).toRingHom

/-- The final orbit cover is finite over the grouped `e` source through the
displayed chart. -/
theorem seGroupedAOrbitSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥(R.seGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
      (R.seGroupedAOrbitSourceRingHom L hind).toAlgebra
    FiniteDimensional (↥(R.seGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
  R.groupedStableAOrbitSource_finite_over_chartSource L hind
    (R.seGroupedSourceChart L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra structure is the explicit composite through the joint chart.
/-- Extend the grouped `e` source embedding to an equivalence of algebraic
closures. -/
noncomputable def seGroupedAOrbitClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.seGroupedAOrbitSourceRingHom L hind) := by
  let seAlg : Algebra (↥(R.seGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.seGroupedAOrbitSourceRingHom L hind).toAlgebra
  let seModule : Module
      (↥(R.seGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) := seAlg.toModule
  let seFinite : @Module.Finite
      (↥(R.seGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) _ _ seModule := by
    letI : Algebra (↥(R.seGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) := seAlg
    exact R.seGroupedAOrbitSource_finiteDimensional L hind
  exact @AlgebraicClosureTransport.EmbeddingClosureEquiv.ofFinite
    _ _ _ _ (R.seGroupedAOrbitSourceRingHom L hind) seAlg seFinite rfl

/-- Pull back the final orbit cover to a source for the grouped `e` triangle. -/
noncomputable def seGroupedAOrbitSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seGroupedAOrbitClosureExtension L hind).pullbackField ⊥

/-- Extend the grouped `e` triangle across its final pullback source. -/
noncomputable def seGroupedAOrbitCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seGroupedCompositionTriangle L hind).sourceExtension
    (R.seGroupedAOrbitSourceField L hind)

/-- The final `e` source chart to the literal orbit cover. -/
noncomputable def seGroupedAOrbitSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seGroupedAOrbitClosureExtension L hind).pullbackBaseEquiv

/-- The intrinsic germ included in the final grouped `e` source. -/
noncomputable def bGermCoefficientToSeGroupedAOrbitSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seGroupedAOrbitClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToSeGroupedSource L hind)

/-- The final `e` source chart carries its intrinsic germ to the repeated-`s`
embedding in the orbit cover. -/
theorem seGroupedAOrbitSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seGroupedAOrbitSourceChart L hind
        (R.bGermCoefficientToSeGroupedAOrbitSource L hind z) =
      R.groupedStableAOrbitSourceS L hind z := by
  let C := R.seGroupedAOrbitClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToSeGroupedSource L hind z)) =
    R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.groupedSourceS L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.groupedJointCoverToAOrbitSourceRingHom L hind)
    (R.seGroupedSourceChart_bGermCoefficient_apply L hind z)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
