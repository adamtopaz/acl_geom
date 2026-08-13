/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitA

/-!
# The a triangle on the e/a-stable grouped source
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
/-- Embed the grouped `a` source in the final orbit cover through its joint
source chart. -/
noncomputable def sAaGroupedAOrbitSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.sAaGroupedSourceChart L hind).toRingHom

/-- The final orbit cover is finite over the grouped `a` source. -/
theorem sAaGroupedAOrbitSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥(R.sAaGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
      (R.sAaGroupedAOrbitSourceRingHom L hind).toAlgebra
    FiniteDimensional (↥(R.sAaGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
  R.groupedStableAOrbitSource_finite_over_chartSource L hind
    (R.sAaGroupedSourceChart L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra structure is the explicit composite through the joint chart.
/-- Extend the grouped `a` source embedding to algebraic closures. -/
noncomputable def sAaGroupedAOrbitClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.sAaGroupedAOrbitSourceRingHom L hind) := by
  let sourceAlgebra : Algebra (↥(R.sAaGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.sAaGroupedAOrbitSourceRingHom L hind).toAlgebra
  let sourceModule : Module (↥(R.sAaGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    sourceAlgebra.toModule
  let sourceFinite : @Module.Finite
      (↥(R.sAaGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) _ _ sourceModule := by
    letI : Algebra (↥(R.sAaGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) := sourceAlgebra
    exact R.sAaGroupedAOrbitSource_finiteDimensional L hind
  exact @AlgebraicClosureTransport.EmbeddingClosureEquiv.ofFinite
    _ _ _ _ (R.sAaGroupedAOrbitSourceRingHom L hind)
      sourceAlgebra sourceFinite rfl

/-- Pull back the final orbit cover to a source for the grouped `a` triangle. -/
noncomputable def sAaGroupedAOrbitSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedAOrbitClosureExtension L hind).pullbackField ⊥

/-- Extend the grouped `a` triangle across its final pullback source. -/
noncomputable def sAaGroupedAOrbitCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedCompositionTriangle L hind).sourceExtension
    (R.sAaGroupedAOrbitSourceField L hind)

/-- The final `a` source chart to the literal orbit cover. -/
noncomputable def sAaGroupedAOrbitSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedAOrbitClosureExtension L hind).pullbackBaseEquiv

/-- The intrinsic germ included in the final grouped `a` source. -/
noncomputable def bGermCoefficientToSAaGroupedAOrbitSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAaGroupedAOrbitClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToSAaGroupedSource L hind)

/-- The final `a` source chart carries its intrinsic germ to the
repeated-`sA` embedding in the orbit cover. -/
theorem sAaGroupedAOrbitSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaGroupedAOrbitSourceChart L hind
        (R.bGermCoefficientToSAaGroupedAOrbitSource L hind z) =
      R.groupedStableAOrbitSourceSA L hind z := by
  let C := R.sAaGroupedAOrbitClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToSAaGroupedSource L hind z)) =
    R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.groupedSourceSA L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.groupedJointCoverToAOrbitSourceRingHom L hind)
    (R.sAaGroupedSourceChart_bGermCoefficient_apply L hind z)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
