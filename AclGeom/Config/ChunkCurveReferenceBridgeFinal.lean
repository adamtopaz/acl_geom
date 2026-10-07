/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge
import AclGeom.Config.ChunkCurveReferenceBridgeBGermComplete
import AclGeom.Config.ChunkCurveReferenceBridgeSelectedBScalar

/-!
# Agreement of the B-germ reference comparisons

The `B`-germ coefficient comparison into the selected graph agrees with the reference
comparison. Split from `AclGeom.Config.ChunkCurveReferenceBridge` (#18).
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

/- These chart types use named intermediate-field and normal-cover aliases.
Lean 4.34's default backward transparency does not unfold those aliases in
rewrites or instance comparisons. This setting is scoped to this bridge;
it affects elaboration only, and the resulting terms are kernel-checked. -/
section ReferenceFieldAliases
set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-! ### One finite normal codomain for the four semilinear source charts -/

/-- Simultaneously, all four whole parameter transports factor through the
intrinsic coefficient fields of their relocated canonical curves. -/
theorem fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients :
    R.seBGermCoefficientToRelocatedBParameterAlgHom L =
        (IntermediateField.inclusion
          ((R.se.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField_le k
              (R.se.bCorrespondenceFamilyMember hψ).parameterField)).comp
          (R.seBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toAlgHom ∧
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L =
        (IntermediateField.inclusion
          ((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField_le k
              (R.sAa.bCorrespondenceFamilyMember hψ).parameterField)).comp
          (R.sAaBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toAlgHom ∧
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L =
        (IntermediateField.inclusion
          ((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField_le k
              (R.sb.bCorrespondenceFamilyMember hψ).parameterField)).comp
          (R.sbBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toAlgHom ∧
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L =
        (IntermediateField.inclusion
          ((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField_le k
              (R.sAc.bCorrespondenceFamilyMember hψ).parameterField)).comp
          (R.sAcBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toAlgHom := by
  exact ⟨bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.1,
    bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.1,
    bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.1,
    bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.2⟩

/-- The selected relocated intrinsic `e` embedding and the promoted
normalized reference embedding are equal on every intrinsic coefficient in
the selected graph source. -/
theorem seBGermCoefficientToSelectedGraph_eq_reference_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.seBGermCoefficientToSelectedGraphSourceRingHom L hind z =
      R.seBGermCoefficientToReferenceInSelectedGraphRingHom L hind z := by
  unfold seBGermCoefficientToSelectedGraphSourceRingHom
    seBGermCoefficientToSelectedSourceRingHom
    seBGermCoefficientToCompleteRightBranchRingHom
    seBGermCoefficientToReferenceInSelectedGraphRingHom
    selectedBScalarExtensionToReferenceEInSelectedGraphRingHom
    bGermCoefficientToSelectedBScalarExtensionAlgHom
    seRelocatedRightBranchToSelectedSourceRingHom
    seRelocatedRightBranchToSelectedNormalRingHom
    relocatedBCoefficientToCompleteRightBranchRingHom
    referenceNormalCoverToSelectedGraphSource
    referenceNormalCoverToSelectedSource
    referenceNormalCoverToSelectedNormal
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  apply congrArg
  apply congrArg
  apply Subtype.ext
  calc
    _ = ((R.seBGermCoefficientToRelocatedBParameterAlgHom L z :
          (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
            CommonCurveAmbient K) := by
      have hz := DFunLike.congr_fun
        (R.fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
          L).1 z
      exact (congrArg Subtype.val hz).symm
    _ = commonCurveEmbedding (k := k) (K := K)
        (((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) L.eProjectionRelation.symm).totalEquiv
            ((IntermediateField.inclusion
              (rankTwoParameterField_le_rankTwoScalarField
                (k := k) w.bReps w.T.rep))
              (bGermCoefficientToSelectedBParameterAlgHom
                (w := w) (hψ := hψ) z)) :
                  rankTwoScalarExtension (k := k) e L.se_e) : K) := by
      unfold seBGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToProjectionParameterAlgHom
      simp only [AlgHom.comp_apply]
      rw [FiniteCover.ExtensionEquiv.commutes_apply]
      rfl

/-- The selected relocated intrinsic `a` embedding is the promoted
inverse-input reference embedding on the whole coefficient field. -/
theorem sAaBGermCoefficientToSelectedGraph_eq_reference_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAaBGermCoefficientToSelectedGraphSourceRingHom L hind z =
      R.sAaBGermCoefficientToReferenceInSelectedGraphRingHom L hind z := by
  unfold sAaBGermCoefficientToSelectedGraphSourceRingHom
    sAaBGermCoefficientToSelectedSourceRingHom
    sAaBGermCoefficientToCompleteRightBranchRingHom
    sAaBGermCoefficientToReferenceInSelectedGraphRingHom
    selectedBScalarExtensionToReferenceAInSelectedGraphRingHom
    bGermCoefficientToSelectedBScalarExtensionAlgHom
    sAaRelocatedRightBranchToSelectedSourceRingHom
    sAaRelocatedRightBranchToSelectedNormalRingHom
    relocatedBCoefficientToCompleteRightBranchRingHom
    referenceNormalCoverToSelectedGraphSource
    referenceNormalCoverToSelectedSource
    referenceNormalCoverToSelectedNormal
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  apply congrArg
  apply congrArg
  apply Subtype.ext
  calc
    _ = ((R.sAaBGermCoefficientToRelocatedBParameterAlgHom L z :
          (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
            CommonCurveAmbient K) := by
      have hz := DFunLike.congr_fun
        (R.fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
          L).2.1 z
      exact (congrArg Subtype.val hz).symm
    _ = commonCurveEmbedding (k := k) (K := K)
        (((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) L.aProjectionRelation.symm).totalEquiv
            ((IntermediateField.inclusion
              (rankTwoParameterField_le_rankTwoScalarField
                (k := k) w.bReps w.T.rep))
              (bGermCoefficientToSelectedBParameterAlgHom
                (w := w) (hψ := hψ) z)) :
                  rankTwoScalarExtension (k := k) a L.sA_a_a) : K) := by
      unfold sAaBGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToProjectionParameterAlgHom
      simp only [AlgHom.comp_apply]
      rw [FiniteCover.ExtensionEquiv.commutes_apply]
      rfl

/-- The selected relocated intrinsic `b` embedding is the promoted
second-input reference embedding on the whole coefficient field. -/
theorem sbBGermCoefficientToSelectedGraph_eq_reference_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sbBGermCoefficientToSelectedGraphSourceRingHom L hind z =
      R.sbBGermCoefficientToReferenceInSelectedGraphRingHom L hind z := by
  unfold sbBGermCoefficientToSelectedGraphSourceRingHom
    sbBGermCoefficientToSelectedSourceRingHom
    sbBGermCoefficientToCompleteRightBranchRingHom
    sbBGermCoefficientToReferenceInSelectedGraphRingHom
    selectedBScalarExtensionToReferenceBInSelectedGraphRingHom
    bGermCoefficientToSelectedBScalarExtensionAlgHom
    sbRelocatedRightBranchToSelectedSourceRingHom
    sbRelocatedRightBranchToSelectedNormalRingHom
    relocatedBCoefficientToCompleteRightBranchRingHom
    referenceNormalCoverToSelectedGraphSource
    referenceNormalCoverToSelectedSource
    referenceNormalCoverToSelectedNormal
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  apply congrArg
  apply congrArg
  apply Subtype.ext
  calc
    _ = ((R.sbBGermCoefficientToRelocatedBParameterAlgHom L z :
          (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
            CommonCurveAmbient K) := by
      have hz := DFunLike.congr_fun
        (R.fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
          L).2.2.1 z
      exact (congrArg Subtype.val hz).symm
    _ = commonCurveEmbedding (k := k) (K := K)
        (((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) L.bProjectionRelation.symm).totalEquiv
            ((IntermediateField.inclusion
              (rankTwoParameterField_le_rankTwoScalarField
                (k := k) w.bReps w.T.rep))
              (bGermCoefficientToSelectedBParameterAlgHom
                (w := w) (hψ := hψ) z)) :
                  rankTwoScalarExtension (k := k) b L.s_b_b) : K) := by
      unfold sbBGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToProjectionParameterAlgHom
      simp only [AlgHom.comp_apply]
      rw [FiniteCover.ExtensionEquiv.commutes_apply]
      rfl

/-- The selected relocated intrinsic algebraic `c` embedding is the
promoted output reference embedding on the whole coefficient field. -/
theorem sAcBGermCoefficientToSelectedGraph_eq_reference_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.sAcBGermCoefficientToSelectedGraphSourceRingHom L hind z =
      R.sAcBGermCoefficientToReferenceInSelectedGraphRingHom L hind z := by
  unfold sAcBGermCoefficientToSelectedGraphSourceRingHom
    sAcBGermCoefficientToSelectedSourceRingHom
    sAcBGermCoefficientToCompleteRightBranchRingHom
    sAcBGermCoefficientToReferenceInSelectedGraphRingHom
    selectedBScalarExtensionToReferenceCInSelectedGraphRingHom
    bGermCoefficientToSelectedBScalarExtensionAlgHom
    sAcRelocatedRightBranchToSelectedSourceRingHom
    sAcRelocatedRightBranchToSelectedNormalRingHom
    relocatedBCoefficientToCompleteRightBranchRingHom
    referenceNormalCoverToSelectedGraphSource
    referenceNormalCoverToSelectedSource
    referenceNormalCoverToSelectedNormal
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  apply congrArg
  apply congrArg
  apply Subtype.ext
  calc
    _ = ((R.sAcBGermCoefficientToRelocatedBParameterAlgHom L z :
          (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
            CommonCurveAmbient K) := by
      have hz := DFunLike.congr_fun
        (R.fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
          L).2.2.2 z
      exact (congrArg Subtype.val hz).symm
    _ = commonCurveEmbedding (k := k) (K := K)
        (((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) L.cProjectionRelation.symm).totalEquiv
            ((IntermediateField.inclusion
              (rankTwoParameterField_le_rankTwoScalarField
                (k := k) w.bReps w.T.rep))
              (bGermCoefficientToSelectedBParameterAlgHom
                (w := w) (hψ := hψ) z)) :
                  rankTwoScalarExtension (k := k) D.c L.sA_c_c) : K) := by
      unfold sAcBGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToRelocatedBParameterAlgHom
        bGermCoefficientToProjectionParameterAlgHom
      simp only [AlgHom.comp_apply]
      rw [FiniteCover.ExtensionEquiv.commutes_apply]
      rfl

/-- Simultaneously, the four named selected intrinsic coefficient maps are
exactly the four promoted normalized-reference restrictions in the unified
selected graph source.  This is an equality on the whole intrinsic field,
not only on its canonical coefficient generators. -/
theorem fourBGermCoefficientToSelectedGraph_eq_reference
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seBGermCoefficientToSelectedGraphSourceRingHom L hind =
        R.seBGermCoefficientToReferenceInSelectedGraphRingHom L hind ∧
      R.sAaBGermCoefficientToSelectedGraphSourceRingHom L hind =
        R.sAaBGermCoefficientToReferenceInSelectedGraphRingHom L hind ∧
      R.sbBGermCoefficientToSelectedGraphSourceRingHom L hind =
        R.sbBGermCoefficientToReferenceInSelectedGraphRingHom L hind ∧
      R.sAcBGermCoefficientToSelectedGraphSourceRingHom L hind =
        R.sAcBGermCoefficientToReferenceInSelectedGraphRingHom L hind := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    exact R.seBGermCoefficientToSelectedGraph_eq_reference_apply L hind
  · apply RingHom.ext
    exact R.sAaBGermCoefficientToSelectedGraph_eq_reference_apply L hind
  · apply RingHom.ext
    exact R.sbBGermCoefficientToSelectedGraph_eq_reference_apply L hind
  · apply RingHom.ext
    exact R.sAcBGermCoefficientToSelectedGraph_eq_reference_apply L hind

end ReferenceFieldAliases

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
