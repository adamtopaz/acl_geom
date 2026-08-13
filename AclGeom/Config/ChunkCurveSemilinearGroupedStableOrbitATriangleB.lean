/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitA

/-!
# The b triangle on the e/a-stable grouped source
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
/-- Embed the grouped `b` source in the final orbit cover through its joint
source chart. -/
noncomputable def sbGroupedAOrbitSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.sbGroupedSourceChart L hind).toRingHom

/-- The final orbit cover is finite over the grouped `b` source. -/
theorem sbGroupedAOrbitSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥(R.sbGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
      (R.sbGroupedAOrbitSourceRingHom L hind).toAlgebra
    FiniteDimensional (↥(R.sbGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
  R.groupedStableAOrbitSource_finite_over_chartSource L hind
    (R.sbGroupedSourceChart L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra structure is the explicit composite through the joint chart.
/-- Extend the grouped `b` source embedding to algebraic closures. -/
noncomputable def sbGroupedAOrbitClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.sbGroupedAOrbitSourceRingHom L hind) := by
  let sourceAlgebra : Algebra (↥(R.sbGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.sbGroupedAOrbitSourceRingHom L hind).toAlgebra
  let sourceModule : Module (↥(R.sbGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    sourceAlgebra.toModule
  let sourceFinite : @Module.Finite
      (↥(R.sbGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) _ _ sourceModule := by
    letI : Algebra (↥(R.sbGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) := sourceAlgebra
    exact R.sbGroupedAOrbitSource_finiteDimensional L hind
  exact @AlgebraicClosureTransport.EmbeddingClosureEquiv.ofFinite
    _ _ _ _ (R.sbGroupedAOrbitSourceRingHom L hind)
      sourceAlgebra sourceFinite rfl

/-- Pull back the final orbit cover to a source for the grouped `b` triangle. -/
noncomputable def sbGroupedAOrbitSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedAOrbitClosureExtension L hind).pullbackField ⊥

/-- Extend the grouped `b` triangle across its final pullback source. -/
noncomputable def sbGroupedAOrbitCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedCompositionTriangle L hind).sourceExtension
    (R.sbGroupedAOrbitSourceField L hind)

/-- The final `b` source chart to the literal orbit cover. -/
noncomputable def sbGroupedAOrbitSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedAOrbitClosureExtension L hind).pullbackBaseEquiv

/-- The intrinsic germ included in the final grouped `b` source. -/
noncomputable def bGermCoefficientToSbGroupedAOrbitSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sbGroupedAOrbitClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToSbGroupedSource L hind)

/-- The final `b` source chart carries its intrinsic germ to the repeated-`s`
embedding in the orbit cover. -/
theorem sbGroupedAOrbitSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbGroupedAOrbitSourceChart L hind
        (R.bGermCoefficientToSbGroupedAOrbitSource L hind z) =
      R.groupedStableAOrbitSourceS L hind z := by
  let C := R.sbGroupedAOrbitClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToSbGroupedSource L hind z)) =
    R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.groupedSourceS L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.groupedJointCoverToAOrbitSourceRingHom L hind)
    (R.sbGroupedSourceChart_bGermCoefficient_apply L hind z)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
