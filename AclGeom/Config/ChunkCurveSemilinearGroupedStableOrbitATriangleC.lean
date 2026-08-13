/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableOrbitA

/-!
# The c triangle on the e/a-stable grouped source
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
/-- Embed the grouped `c` source in the final orbit cover through its joint
source chart. -/
noncomputable def sAcGroupedAOrbitSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.sAcGroupedSourceChart L hind).toRingHom

/-- The final orbit cover is finite over the grouped `c` source. -/
theorem sAcGroupedAOrbitSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥(R.sAcGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
      (R.sAcGroupedAOrbitSourceRingHom L hind).toAlgebra
    FiniteDimensional (↥(R.sAcGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
  R.groupedStableAOrbitSource_finite_over_chartSource L hind
    (R.sAcGroupedSourceChart L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The algebra structure is the explicit composite through the joint chart.
/-- Extend the grouped `c` source embedding to algebraic closures. -/
noncomputable def sAcGroupedAOrbitClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.sAcGroupedAOrbitSourceRingHom L hind) := by
  let sourceAlgebra : Algebra (↥(R.sAcGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    (R.sAcGroupedAOrbitSourceRingHom L hind).toAlgebra
  let sourceModule : Module (↥(R.sAcGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
    sourceAlgebra.toModule
  let sourceFinite : @Module.Finite
      (↥(R.sAcGroupedSourceField L hind))
      (↥(R.groupedStableAOrbitSourceCover L hind).field) _ _ sourceModule := by
    letI : Algebra (↥(R.sAcGroupedSourceField L hind))
        (↥(R.groupedStableAOrbitSourceCover L hind).field) := sourceAlgebra
    exact R.sAcGroupedAOrbitSource_finiteDimensional L hind
  exact @AlgebraicClosureTransport.EmbeddingClosureEquiv.ofFinite
    _ _ _ _ (R.sAcGroupedAOrbitSourceRingHom L hind)
      sourceAlgebra sourceFinite rfl

/-- Pull back the final orbit cover to a source for the grouped `c` triangle. -/
noncomputable def sAcGroupedAOrbitSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedAOrbitClosureExtension L hind).pullbackField ⊥

/-- Extend the grouped `c` triangle across its final pullback source. -/
noncomputable def sAcGroupedAOrbitCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedCompositionTriangle L hind).sourceExtension
    (R.sAcGroupedAOrbitSourceField L hind)

/-- The final `c` source chart to the literal orbit cover. -/
noncomputable def sAcGroupedAOrbitSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedAOrbitClosureExtension L hind).pullbackBaseEquiv

/-- The intrinsic germ included in the final grouped `c` source. -/
noncomputable def bGermCoefficientToSAcGroupedAOrbitSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.sAcGroupedAOrbitClosureExtension L hind).pullbackBaseRingHom.comp
    (R.bGermCoefficientToSAcGroupedSource L hind)

/-- The final `c` source chart carries its intrinsic germ to the
repeated-`sA` embedding in the orbit cover. -/
theorem sAcGroupedAOrbitSourceChart_bGermCoefficient_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcGroupedAOrbitSourceChart L hind
        (R.bGermCoefficientToSAcGroupedAOrbitSource L hind z) =
      R.groupedStableAOrbitSourceSA L hind z := by
  let C := R.sAcGroupedAOrbitClosureExtension L hind
  change C.pullbackBaseEquiv
      (C.pullbackBaseRingHom
        (R.bGermCoefficientToSAcGroupedSource L hind z)) =
    R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.groupedSourceSA L hind z)
  rw [C.pullbackBaseEquiv_pullbackBaseRingHom]
  exact congrArg (R.groupedJointCoverToAOrbitSourceRingHom L hind)
    (R.sAcGroupedSourceChart_bGermCoefficient_apply L hind z)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
