/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge

/-!
# Intrinsic coefficient restrictions of the semilinear source charts

The four selected relocated coefficient embeddings are restrictions of one
intrinsic germ map acted on by the semilinear e/a/b/c source charts.  These
whole-field identities are the coefficient-faithful input to the finite
common-chart descent.
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

/-! ### Intrinsic coefficient restrictions of the semilinear source charts -/

/-- The common eight-input coefficient field enters the semantic source
through its literal coefficient algebra map. -/
theorem commonCoefficientField_le_semanticCommonSourceField :
    R.seCommonBaseData.coefficientField ≤ R.semanticCommonSourceField := by
  intro z hz
  change z ∈
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField
  exact
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.algebraMap_mem
        ⟨z, hz⟩

/-- The relocated `e` parameter field is already contained in the literal
semantic source, before any normal-cover canonicalization. -/
theorem seRelocatedParameterField_le_semanticCommonSourceField
    (L : w.PsiChunkFourArrowEdgeLifts hψ D)
    (_hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.semanticCommonSourceField := by
  apply (show
    (R.se.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.mappedReferenceInputField L by
      rw [R.mappedReferenceInputField_eq_commonCoefficientField L]
      unfold FiniteCorrespondenceFamilyMember.parameterField
      apply adjoin_le_iff.2
      rintro _ ⟨i, rfl⟩
      change commonCurveEmbedding (k := k) (K := K) (e i) ∈
        adjoin k (Set.range R.commonInputTuple)
      fin_cases i
      · exact subset_adjoin k _ ⟨2, rfl⟩
      · exact subset_adjoin k _ ⟨3, rfl⟩).trans
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

/-- The relocated `a` parameter field is likewise a literal subfield of
the original semantic source presentation. -/
theorem sAaRelocatedParameterField_le_semanticCommonSourceField
    (L : w.PsiChunkFourArrowEdgeLifts hψ D)
    (_hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.semanticCommonSourceField := by
  apply (show
    (R.sAa.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.mappedReferenceInputField L by
      rw [R.mappedReferenceInputField_eq_commonCoefficientField L]
      unfold FiniteCorrespondenceFamilyMember.parameterField
      apply adjoin_le_iff.2
      rintro _ ⟨i, rfl⟩
      change commonCurveEmbedding (k := k) (K := K) (a i) ∈
        adjoin k (Set.range R.commonInputTuple)
      fin_cases i
      · exact subset_adjoin k _ ⟨4, rfl⟩
      · exact subset_adjoin k _ ⟨5, rfl⟩).trans
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

/-- The relocated `b` parameter field is a literal subfield of the same
semantic source presentation. -/
theorem sbRelocatedParameterField_le_semanticCommonSourceField
    (L : w.PsiChunkFourArrowEdgeLifts hψ D)
    (_hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.semanticCommonSourceField := by
  apply (show
    (R.sb.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.mappedReferenceInputField L by
      rw [R.mappedReferenceInputField_eq_commonCoefficientField L]
      unfold FiniteCorrespondenceFamilyMember.parameterField
      apply adjoin_le_iff.2
      rintro _ ⟨i, rfl⟩
      change commonCurveEmbedding (k := k) (K := K) (b i) ∈
        adjoin k (Set.range R.commonInputTuple)
      fin_cases i
      · exact subset_adjoin k _ ⟨6, rfl⟩
      · exact subset_adjoin k _ ⟨7, rfl⟩).trans
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

/-- The relocated `c` parameter field lies literally in the independent
algebraic-output source presentation. -/
theorem sAcRelocatedParameterField_le_rightCSourceField
    (_L : w.PsiChunkFourArrowEdgeLifts hψ D)
    (_hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.rightCSourceField := by
  unfold FiniteCorrespondenceFamilyMember.parameterField rightCSourceField
  apply adjoin_le_iff.2
  rintro _ ⟨i, rfl⟩
  change commonCurveEmbedding (k := k) (K := K) (D.c i) ∈
    adjoin k (Set.range R.rightCSourceTuple)
  fin_cases i
  · exact subset_adjoin k _ ⟨2, rfl⟩
  · exact subset_adjoin k _ ⟨3, rfl⟩

/-- The intrinsic selected-`B` germ embedded in the `e` parameter field and
then literally in the semantic source.  This is the common input whose
semilinear images will supply all four selected right restrictions. -/
noncomputable def seBGermCoefficientToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.seRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (R.seBGermCoefficientToRelocatedBParameterAlgHom L)

/-- The intrinsic germ in the relocated `a` parameter field, included in
the same literal semantic source. -/
noncomputable def sAaBGermCoefficientToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.sAaRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (R.sAaBGermCoefficientToRelocatedBParameterAlgHom L)

/-- The intrinsic germ in the relocated `b` parameter field, included in
the literal semantic source. -/
noncomputable def sbBGermCoefficientToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.sbRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (R.sbBGermCoefficientToRelocatedBParameterAlgHom L)

/-- The intrinsic output germ in the genuine `c` source presentation. -/
noncomputable def sAcBGermCoefficientToRightCSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥R.rightCSourceField) :=
  (IntermediateField.inclusion
      (R.sAcRelocatedParameterField_le_rightCSourceField L hind)).comp
    (R.sAcBGermCoefficientToRelocatedBParameterAlgHom L)

private noncomputable def seSelectedBParameterToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥w.bField) →ₐ[k] (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.seRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (selectedBToRelocatedBParameterEquiv
      (w := w) (hψ := hψ)
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq).toAlgHom

private noncomputable def sAaSelectedBParameterToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥w.bField) →ₐ[k] (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.sAaRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (selectedBToRelocatedBParameterEquiv
      (w := w) (hψ := hψ)
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq).toAlgHom

private noncomputable def sbSelectedBParameterToSemanticSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥w.bField) →ₐ[k] (↥R.semanticCommonSourceField) :=
  (IntermediateField.inclusion
      (R.sbRelocatedParameterField_le_semanticCommonSourceField L hind)).comp
    (selectedBToRelocatedBParameterEquiv
      (w := w) (hψ := hψ)
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq).toAlgHom

private noncomputable def sAcSelectedBParameterToRightCSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥w.bField) →ₐ[k] (↥R.rightCSourceField) :=
  (IntermediateField.inclusion
      (R.sAcRelocatedParameterField_le_rightCSourceField L hind)).comp
    (selectedBToRelocatedBParameterEquiv
      (w := w) (hψ := hψ)
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq).toAlgHom

private theorem seSelectedBParameterToSemanticSourceAlgHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 2) :
    R.seSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      R.rightESemanticSourceCoordinate (rightParameterIndex i) := by
  unfold seSelectedBParameterToSemanticSourceAlgHom
  change
    (IntermediateField.inclusion
      (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.se.bCorrespondenceFamilyMember hψ)
          R.seMappedSelectedBFamily_ideal_eq
          ⟨w.bReps i, IntermediateField.subset_adjoin k _
            (Set.mem_range_self i)⟩) = _
  rw [selectedBToRelocatedBParameterEquiv_apply]
  apply Subtype.ext
  simp [rightESemanticSourceCoordinate,
    R.relocatedBFamily_parameters.1]

private theorem sAaSelectedBParameterToSemanticSourceAlgHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 2) :
    R.sAaSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      R.rightASemanticSourceCoordinate (rightParameterIndex i) := by
  unfold sAaSelectedBParameterToSemanticSourceAlgHom
  change
    (IntermediateField.inclusion
      (R.sAaRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.sAa.bCorrespondenceFamilyMember hψ)
          R.sAaMappedSelectedBFamily_ideal_eq
          ⟨w.bReps i, IntermediateField.subset_adjoin k _
            (Set.mem_range_self i)⟩) = _
  rw [selectedBToRelocatedBParameterEquiv_apply]
  apply Subtype.ext
  simp [rightASemanticSourceCoordinate,
    R.relocatedBFamily_parameters.2.1]

private theorem sbSelectedBParameterToSemanticSourceAlgHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 2) :
    R.sbSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      R.rightBSemanticSourceCoordinate (rightParameterIndex i) := by
  unfold sbSelectedBParameterToSemanticSourceAlgHom
  change
    (IntermediateField.inclusion
      (R.sbRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.sb.bCorrespondenceFamilyMember hψ)
          R.sbMappedSelectedBFamily_ideal_eq
          ⟨w.bReps i, IntermediateField.subset_adjoin k _
            (Set.mem_range_self i)⟩) = _
  rw [selectedBToRelocatedBParameterEquiv_apply]
  apply Subtype.ext
  simp [rightBSemanticSourceCoordinate,
    R.relocatedBFamily_parameters.2.2.1]

private theorem sAcSelectedBParameterToRightCSourceAlgHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 2) :
    R.sAcSelectedBParameterToRightCSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      R.rightCSourceCoordinate (rightParameterIndex i) := by
  unfold sAcSelectedBParameterToRightCSourceAlgHom
  change
    (IntermediateField.inclusion
      (R.sAcRelocatedParameterField_le_rightCSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.sAc.bCorrespondenceFamilyMember hψ)
          R.sAcMappedSelectedBFamily_ideal_eq
          ⟨w.bReps i, IntermediateField.subset_adjoin k _
            (Set.mem_range_self i)⟩) = _
  rw [selectedBToRelocatedBParameterEquiv_apply]
  apply Subtype.ext
  simp [rightCSourceCoordinate,
    R.relocatedBFamily_parameters.2.2.2]

private theorem commonSourceRightAAut_comp_selectedBParameter
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.commonSourceRightAAut hind).toAlgHom.comp
        (R.seSelectedBParameterToSemanticSourceAlgHom L hind) =
      R.sAaSelectedBParameterToSemanticSourceAlgHom L hind := by
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  change R.commonSourceRightAAut hind
      (R.seSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩) =
    R.sAaSelectedBParameterToSemanticSourceAlgHom L hind
      ⟨w.bReps i, IntermediateField.subset_adjoin k _
        (Set.mem_range_self i)⟩
  rw [R.seSelectedBParameterToSemanticSourceAlgHom_apply L hind,
    R.sAaSelectedBParameterToSemanticSourceAlgHom_apply L hind]
  exact R.commonSourceRightAAut_apply hind (rightParameterIndex i)

private theorem commonSourceRightBAut_comp_selectedBParameter
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.commonSourceRightBAut hind).toAlgHom.comp
        (R.seSelectedBParameterToSemanticSourceAlgHom L hind) =
      R.sbSelectedBParameterToSemanticSourceAlgHom L hind := by
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  change R.commonSourceRightBAut hind
      (R.seSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩) =
    R.sbSelectedBParameterToSemanticSourceAlgHom L hind
      ⟨w.bReps i, IntermediateField.subset_adjoin k _
        (Set.mem_range_self i)⟩
  rw [R.seSelectedBParameterToSemanticSourceAlgHom_apply L hind,
    R.sbSelectedBParameterToSemanticSourceAlgHom_apply L hind]
  exact R.commonSourceRightBAut_apply hind (rightParameterIndex i)

private theorem commonSourceToRightCSourceEquiv_comp_selectedBParameter
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.commonSourceToRightCSourceEquiv hind).toAlgHom.comp
        (R.seSelectedBParameterToSemanticSourceAlgHom L hind) =
      R.sAcSelectedBParameterToRightCSourceAlgHom L hind := by
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  change R.commonSourceToRightCSourceEquiv hind
      (R.seSelectedBParameterToSemanticSourceAlgHom L hind
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩) =
    R.sAcSelectedBParameterToRightCSourceAlgHom L hind
      ⟨w.bReps i, IntermediateField.subset_adjoin k _
        (Set.mem_range_self i)⟩
  rw [R.seSelectedBParameterToSemanticSourceAlgHom_apply L hind,
    R.sAcSelectedBParameterToRightCSourceAlgHom_apply L hind]
  simpa only [rightESemanticSourceCoordinate, rightCSourceCoordinate] using
    R.commonSourceToRightCSourceEquiv_apply hind (rightParameterIndex i)

set_option maxHeartbeats 800000 in
-- Dependent intermediate-field transport needs extra elaboration heartbeats.
/-- On the entire intrinsic germ field, the semantic `e→a` source chart
carries the selected `e` coefficient embedding to the selected `a`
embedding.  This is stronger than a coordinate-generator formula. -/
theorem commonSourceRightAAut_comp_seBGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.commonSourceRightAAut hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x) =
      R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x := by
  have hxE := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.1)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.seBGermCoefficientToRelocatedBParameterAlgHom L x at hxE
  have hxA := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.1)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L x at hxA
  have hxSource := DFunLike.congr_fun
    (R.commonSourceRightAAut_comp_selectedBParameter L hind)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change R.commonSourceRightAAut hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.se.bCorrespondenceFamilyMember hψ)
          R.seMappedSelectedBFamily_ideal_eq
          (bGermCoefficientToSelectedBParameterAlgHom
            (w := w) (hψ := hψ) x))) =
    (IntermediateField.inclusion
      (R.sAaRelocatedParameterField_le_semanticCommonSourceField L hind))
      (selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x)) at hxSource
  change R.commonSourceRightAAut hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (R.seBGermCoefficientToRelocatedBParameterAlgHom L x)) =
    (IntermediateField.inclusion
      (R.sAaRelocatedParameterField_le_semanticCommonSourceField L hind))
      (R.sAaBGermCoefficientToRelocatedBParameterAlgHom L x)
  rw [← hxE, ← hxA]
  exact hxSource

set_option maxHeartbeats 800000 in
-- Dependent intermediate-field transport needs extra elaboration heartbeats.
/-- The semantic `e→b` source chart carries the whole intrinsic selected
coefficient field to its relocated `b` embedding. -/
theorem commonSourceRightBAut_comp_seBGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.commonSourceRightBAut hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x) =
      R.sbBGermCoefficientToSemanticSourceAlgHom L hind x := by
  have hxE := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.1)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.seBGermCoefficientToRelocatedBParameterAlgHom L x at hxE
  have hxB := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.1)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L x at hxB
  have hxSource := DFunLike.congr_fun
    (R.commonSourceRightBAut_comp_selectedBParameter L hind)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change R.commonSourceRightBAut hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.se.bCorrespondenceFamilyMember hψ)
          R.seMappedSelectedBFamily_ideal_eq
          (bGermCoefficientToSelectedBParameterAlgHom
            (w := w) (hψ := hψ) x))) =
    (IntermediateField.inclusion
      (R.sbRelocatedParameterField_le_semanticCommonSourceField L hind))
      (selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x)) at hxSource
  change R.commonSourceRightBAut hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (R.seBGermCoefficientToRelocatedBParameterAlgHom L x)) =
    (IntermediateField.inclusion
      (R.sbRelocatedParameterField_le_semanticCommonSourceField L hind))
      (R.sbBGermCoefficientToRelocatedBParameterAlgHom L x)
  rw [← hxE, ← hxB]
  exact hxSource

set_option maxHeartbeats 800000 in
-- Dependent intermediate-field transport needs extra elaboration heartbeats.
/-- The genuine `e→c` source equivalence carries the entire intrinsic germ
embedding to the selected algebraic-output embedding in the independent
`c` source. -/
theorem commonSourceToRightCSourceEquiv_comp_seBGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.commonSourceToRightCSourceEquiv hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x) =
      R.sAcBGermCoefficientToRightCSourceAlgHom L hind x := by
  have hxE := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.1)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.seBGermCoefficientToRelocatedBParameterAlgHom L x at hxE
  have hxC := DFunLike.congr_fun
    (selectedBToRelocatedBParameterEquiv_eq_projection
      (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.2)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x) =
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L x at hxC
  have hxSource := DFunLike.congr_fun
    (R.commonSourceToRightCSourceEquiv_comp_selectedBParameter L hind)
    (bGermCoefficientToSelectedBParameterAlgHom
      (w := w) (hψ := hψ) x)
  change R.commonSourceToRightCSourceEquiv hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ)
          (R.se.bCorrespondenceFamilyMember hψ)
          R.seMappedSelectedBFamily_ideal_eq
          (bGermCoefficientToSelectedBParameterAlgHom
            (w := w) (hψ := hψ) x))) =
    (IntermediateField.inclusion
      (R.sAcRelocatedParameterField_le_rightCSourceField L hind))
      (selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) x)) at hxSource
  change R.commonSourceToRightCSourceEquiv hind
      ((IntermediateField.inclusion
        (R.seRelocatedParameterField_le_semanticCommonSourceField L hind))
        (R.seBGermCoefficientToRelocatedBParameterAlgHom L x)) =
    (IntermediateField.inclusion
      (R.sAcRelocatedParameterField_le_rightCSourceField L hind))
      (R.sAcBGermCoefficientToRelocatedBParameterAlgHom L x)
  rw [← hxE, ← hxC]
  exact hxSource


end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
