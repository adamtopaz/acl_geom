/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableCover

/-!
# Extending semantic-source alignments to the stable grouped cover

The selected `e` embedding carries the complete graph/right source into the
joint cover and hence into its semantic normal closure.  Normality over the
semantic source then extends every established source-linear deck
transformation to the stable grouped cover, with an exact restriction on the
whole old cover.
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

private abbrev groupedAlignmentSemanticSourceType :=
  ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField

/-- Use the source-field presentation carried by the selected graph cover for
the semantic algebra structure on the stable grouped field. -/
noncomputable local instance groupedAlignmentStableSourceAlgebra
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Algebra (groupedAlignmentSemanticSourceType R)
      (R.groupedStableSourceField L hind) :=
  R.groupedStableSourceFieldAlgebra L hind

set_option synthInstance.maxHeartbeats 100000 in
-- The selected map crosses the rebased joint cover and its semantic closure.
set_option maxHeartbeats 800000 in
-- Its semantic-linearity uses the exact whole-source square of the `e` leg.
/-- Include the whole selected graph/right source in the stable grouped cover,
linearly over the original semantic source. -/
noncomputable def selectedGraphRightSourceToGroupedStableSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceCover L hind).field →ₐ[
      groupedAlignmentSemanticSourceType R]
      (R.groupedStableSourceField L hind) :=
  { (algebraMap (R.fourSelectedGraphJointCover L hind).field
        (R.groupedStableSourceField L hind)).comp
      (R.selectedGraphRightSourceToRightEJointRingHom L hind) with
    commutes' := fun x ↦ by
      change algebraMap (R.fourSelectedGraphJointCover L hind).field
          (R.groupedStableSourceField L hind)
          (R.selectedGraphRightSourceToRightEJointRingHom L hind
            ⟨algebraMap (↥R.semanticCommonSourceField)
                (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
              (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩) =
        algebraMap (↥R.semanticCommonSourceField)
          (R.groupedStableSourceField L hind) x
      rw [R.selectedGraphRightSourceToRightEJointRingHom_algebraMap]
      rfl }

set_option synthInstance.maxHeartbeats 100000 in
-- The stable normal field is presented over the joint cover but normal over S.
set_option maxHeartbeats 800000 in
-- Extending along the selected joint embedding unfolds both presentations.
/-- Extend any semantic-source-linear automorphism of the selected graph/right
source to the stable grouped cover. -/
noncomputable def groupedStableSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (R.selectedGraphRightSourceCover L hind).field
      ≃ₐ[groupedAlignmentSemanticSourceType R]
      (R.selectedGraphRightSourceCover L hind).field) :
    (R.groupedStableSourceField L hind)
      ≃ₐ[groupedAlignmentSemanticSourceType R]
      (R.groupedStableSourceField L hind) := by
  letI : Normal (groupedAlignmentSemanticSourceType R)
      (R.groupedStableSourceField L hind) :=
    R.groupedStableSourceField_normal L hind
  exact NormalBranchEmbedding.extendAlong
    (R.selectedGraphRightSourceToGroupedStableSource L hind) σ

set_option synthInstance.maxHeartbeats 100000 in
-- The exact restriction traverses the stable field's two algebra structures.
set_option maxHeartbeats 800000 in
-- It is the defining equation of normal-cover extension along the selected map.
/-- The stable extension has exactly the prescribed action on the complete
selected graph/right source. -/
@[simp] theorem groupedStableSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (R.selectedGraphRightSourceCover L hind).field
      ≃ₐ[groupedAlignmentSemanticSourceType R]
      (R.selectedGraphRightSourceCover L hind).field)
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.groupedStableSourceChartAut L hind σ
        (R.selectedGraphRightSourceToGroupedStableSource L hind x) =
      R.selectedGraphRightSourceToGroupedStableSource L hind (σ x) := by
  letI : Normal (groupedAlignmentSemanticSourceType R)
      (R.groupedStableSourceField L hind) :=
    R.groupedStableSourceField_normal L hind
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
