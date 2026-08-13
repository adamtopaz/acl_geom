/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonMiddleBranch
import AclGeom.Config.ChunkCurveFiniteCommonChartFiniteness

/-!
# A stable normal source for the four semantic charts

The literal finite common source need not itself be stable under the four
selected graph/right source charts.  We take its normal closure over the
semantic common source inside the algebraic closure of the established
graph/right source.  The resulting field is finite and normal over the
semantic source, contains both the old graph/right source and the finite
common source, and therefore supports extensions of all four selected source
automorphisms.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

private abbrev stableSemanticSourceType :=
  ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- Normal-closure elaboration needs more than the default heartbeat budget.
/-- The normal closure of the finite literal common source over the semantic
source, formed in the algebraic closure of the selected graph/right source. -/
noncomputable def rightSemilinearStableNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.normalClosure (stableSemanticSourceType R)
    (↥(R.rightSemilinearCommonSourceField L hind))
    (AlgebraicClosure
      (↥(R.selectedGraphRightSourceCover L hind).field))

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- Normal-closure membership elaboration needs a larger heartbeat budget.
/-- The old selected graph/right source lies in the stable normal field. -/
theorem selectedGraphRightSource_algebraMap_mem_stableNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
        (AlgebraicClosure
          (↥(R.selectedGraphRightSourceCover L hind).field)) x ∈
      R.rightSemilinearStableNormalField L hind := by
  let X := R.rightSemilinearCommonSourceField L hind
  let φ : (↥X) →ₐ[stableSemanticSourceType R]
      (AlgebraicClosure
        (↥(R.selectedGraphRightSourceCover L hind).field)) :=
    { algebraMap (↥X)
        (AlgebraicClosure
          (↥(R.selectedGraphRightSourceCover L hind).field)) with
      commutes' := fun y ↦ by rfl }
  apply AlgHom.fieldRange_le_normalClosure φ
  refine ⟨algebraMap _ (↥X) x, ?_⟩
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The carrier re-presentation needs a larger heartbeat budget.
/-- The same stable field, now viewed as an intermediate extension of the
selected graph/right source.  This is the presentation consumed by source
extension of the four strict triangles. -/
noncomputable def rightSemilinearStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (↥(R.selectedGraphRightSourceCover L hind).field)
      (AlgebraicClosure
        (↥(R.selectedGraphRightSourceCover L hind).field)) where
  __ := (R.rightSemilinearStableNormalField L hind).toSubfield
  algebraMap_mem' :=
    R.selectedGraphRightSource_algebraMap_mem_stableNormalField L hind

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- Normal-closure containment needs a larger heartbeat budget.
/-- The original finite common source is literally contained in the stable
source. -/
theorem rightSemilinearCommonSourceField_le_stableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.rightSemilinearCommonSourceField L hind ≤
      R.rightSemilinearStableSourceField L hind := by
  intro x hx
  let X := R.rightSemilinearCommonSourceField L hind
  let φ : (↥X) →ₐ[stableSemanticSourceType R]
      (AlgebraicClosure
        (↥(R.selectedGraphRightSourceCover L hind).field)) :=
    { algebraMap (↥X)
        (AlgebraicClosure
          (↥(R.selectedGraphRightSourceCover L hind).field)) with
      commutes' := fun y ↦ by rfl }
  change x ∈ R.rightSemilinearStableNormalField L hind
  apply AlgHom.fieldRange_le_normalClosure φ
  exact ⟨⟨x, hx⟩, rfl⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The finite tower proof needs a larger heartbeat budget.
/-- The finite common source is finite already over the semantic common
source. -/
theorem rightSemilinearCommonSourceField_finite_over_semantic
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (stableSemanticSourceType R)
      (↥(R.rightSemilinearCommonSourceField L hind)) := by
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let X := ↥(R.rightSemilinearCommonSourceField L hind)
  letI : FiniteDimensional (stableSemanticSourceType R) N :=
    (R.selectedGraphRightSourceCover L hind).finiteDimensional
  letI : FiniteDimensional N X :=
    R.rightEFiniteCommonChartSourceField_finiteDimensional L hind
  letI : IsScalarTower (stableSemanticSourceType R) N X :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact FiniteDimensional.trans (stableSemanticSourceType R) N X

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The normal tower proof needs a larger heartbeat budget.
/-- The ambient algebraic closure of the graph/right source is normal over
the semantic source. -/
theorem selectedGraphRightAlgebraicClosure_normal_over_semantic
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal (stableSemanticSourceType R)
      (AlgebraicClosure
        (↥(R.selectedGraphRightSourceCover L hind).field)) := by
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let Ω := AlgebraicClosure N
  letI : Normal (stableSemanticSourceType R) N :=
    (R.selectedGraphRightSourceCover L hind).normal
  letI : Algebra.IsAlgebraic (stableSemanticSourceType R) N :=
    Normal.toIsAlgebraic
  letI : IsScalarTower (stableSemanticSourceType R) N Ω :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra.IsAlgebraic (stableSemanticSourceType R) Ω :=
    Algebra.IsAlgebraic.trans (stableSemanticSourceType R) N Ω
  rw [normal_iff]
  intro x
  exact ⟨(Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    IsAlgClosed.splits _⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The normal-closure instance proof needs a larger heartbeat budget.
/-- The stable source is normal over the full semantic source, which is the
base fixed by all four selected source charts. -/
theorem rightSemilinearStableSourceField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal (stableSemanticSourceType R)
      (↥(R.rightSemilinearStableSourceField L hind)) := by
  change Normal (stableSemanticSourceType R)
    (↥(R.rightSemilinearStableNormalField L hind))
  letI : FiniteDimensional (stableSemanticSourceType R)
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
    R.rightSemilinearCommonSourceField_finite_over_semantic L hind
  letI : Normal (stableSemanticSourceType R)
      (AlgebraicClosure
        (↥(R.selectedGraphRightSourceCover L hind).field)) :=
    R.selectedGraphRightAlgebraicClosure_normal_over_semantic L hind
  exact normalClosure.normal _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The normal-closure finiteness proof needs a larger heartbeat budget.
/-- The stable source remains finite over the semantic source. -/
theorem rightSemilinearStableSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (stableSemanticSourceType R)
      (↥(R.rightSemilinearStableSourceField L hind)) := by
  change FiniteDimensional (stableSemanticSourceType R)
    (↥(R.rightSemilinearStableNormalField L hind))
  letI : FiniteDimensional (stableSemanticSourceType R)
      (↥(R.rightSemilinearCommonSourceField L hind)) :=
    R.rightSemilinearCommonSourceField_finite_over_semantic L hind
  exact normalClosure.is_finiteDimensional _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The finite tower proof needs a larger heartbeat budget.
/-- The stable source is finite over the established selected graph/right
source as well. -/
theorem rightSemilinearStableSourceField_finite_over_selectedGraphRight
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightSemilinearStableSourceField L hind)) := by
  let S := stableSemanticSourceType R
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let T := ↥(R.rightSemilinearStableSourceField L hind)
  letI : FiniteDimensional S T :=
    R.rightSemilinearStableSourceField_finiteDimensional L hind
  letI : IsScalarTower S N T :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact FiniteDimensional.right S N T

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The explicit semantic-linear inclusion needs a larger heartbeat budget.
/-- Inclusion of the entire selected graph/right source in the stable source,
linear over the semantic common source. -/
noncomputable def selectedGraphRightSourceToSemilinearStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) →ₐ[
      stableSemanticSourceType R]
      (↥(R.rightSemilinearStableSourceField L hind)) :=
  { algebraMap _ _ with
    commutes' := fun _ ↦ rfl }

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- Extending the chart across the normal closure needs a larger heartbeat budget.
/-- Extend any selected graph/right source chart to the stable source. -/
noncomputable def semilinearStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ :
      (↥(R.selectedGraphRightSourceCover L hind).field) ≃ₐ[stableSemanticSourceType R]
        (↥(R.selectedGraphRightSourceCover L hind).field)) :
    (↥(R.rightSemilinearStableSourceField L hind)) ≃ₐ[
      stableSemanticSourceType R]
      (↥(R.rightSemilinearStableSourceField L hind)) := by
  letI : Normal (stableSemanticSourceType R)
      (↥(R.rightSemilinearStableSourceField L hind)) :=
    R.rightSemilinearStableSourceField_normal L hind
  exact NormalBranchEmbedding.extendAlong
    (R.selectedGraphRightSourceToSemilinearStableSource L hind) σ

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- The exact restriction proof needs a larger heartbeat budget.
/-- The extended stable chart has the prescribed action on the complete old
graph/right source. -/
@[simp] theorem semilinearStableSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ :
      (↥(R.selectedGraphRightSourceCover L hind).field) ≃ₐ[stableSemanticSourceType R]
        (↥(R.selectedGraphRightSourceCover L hind).field))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.semilinearStableSourceChartAut L hind σ
        (R.selectedGraphRightSourceToSemilinearStableSource L hind x) =
      R.selectedGraphRightSourceToSemilinearStableSource L hind (σ x) := by
  letI : Normal (stableSemanticSourceType R)
      (↥(R.rightSemilinearStableSourceField L hind)) :=
    R.rightSemilinearStableSourceField_normal L hind
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The nested stable-source type requires an enlarged instance-search budget.
/-- Stable extension of the selected `e` source chart. -/
noncomputable def seSemilinearStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.semilinearStableSourceChartAut L hind
    (R.seSelectedGraphRightSourceChartAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The nested stable-source type requires an enlarged instance-search budget.
/-- Stable extension of the selected `a` source chart. -/
noncomputable def sAaSemilinearStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.semilinearStableSourceChartAut L hind
    (R.sAaSelectedGraphRightSourceChartAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The nested stable-source type requires an enlarged instance-search budget.
/-- Stable extension of the selected `b` source chart. -/
noncomputable def sbSemilinearStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.semilinearStableSourceChartAut L hind
    (R.sbSelectedGraphRightSourceChartAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The nested stable-source type requires an enlarged instance-search budget.
/-- Stable extension of the selected `c` source chart. -/
noncomputable def sAcSemilinearStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.semilinearStableSourceChartAut L hind
    (R.sAcSelectedGraphRightSourceChartAut L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate-field towers require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
-- Combining the four restriction proofs needs a larger heartbeat budget.
/-- All four stable charts retain their exact, generally nontrivial action on
the whole selected graph/right source. -/
theorem semilinearStableSourceCharts_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.seSemilinearStableSourceChartAut L hind
        (R.selectedGraphRightSourceToSemilinearStableSource L hind x) =
        R.selectedGraphRightSourceToSemilinearStableSource L hind
          (R.seSelectedGraphRightSourceChartAut L hind x) ∧
    R.sAaSemilinearStableSourceChartAut L hind
        (R.selectedGraphRightSourceToSemilinearStableSource L hind x) =
        R.selectedGraphRightSourceToSemilinearStableSource L hind
          (R.sAaSelectedGraphRightSourceChartAut L hind x) ∧
    R.sbSemilinearStableSourceChartAut L hind
        (R.selectedGraphRightSourceToSemilinearStableSource L hind x) =
        R.selectedGraphRightSourceToSemilinearStableSource L hind
          (R.sbSelectedGraphRightSourceChartAut L hind x) ∧
    R.sAcSemilinearStableSourceChartAut L hind
        (R.selectedGraphRightSourceToSemilinearStableSource L hind x) =
        R.selectedGraphRightSourceToSemilinearStableSource L hind
          (R.sAcSelectedGraphRightSourceChartAut L hind x) := by
  exact ⟨R.semilinearStableSourceChartAut_apply L hind _ x,
    R.semilinearStableSourceChartAut_apply L hind _ x,
    R.semilinearStableSourceChartAut_apply L hind _ x,
    R.semilinearStableSourceChartAut_apply L hind _ x⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
