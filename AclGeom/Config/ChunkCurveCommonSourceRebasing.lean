/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource

/-!
# Repeated-branch rebasing over the common source

Rebased canonical covers, branch embeddings and closure-alignment automorphisms for the
repeated `s`, `sA`, `u` and `uB` branches. Split from
`AclGeom.Config.ChunkCurveCommonSource` (#18). No other library module uses these
results; the book documents them.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

variable {k K Ω : Type u} [Field k] [Field K] [Algebra k K]
  [Field Ω] [Algebra k Ω]

namespace QWitness

variable (w : QWitness k K)

namespace PsiCurveCompositionBaseChangeRealization

variable {w : QWitness k K} {ι : K →ₐ[k] Ω}
  {a b c : Fin 2 → Ω}
  (R : w.PsiCurveCompositionBaseChangeRealization ι a b c)

namespace CommonBaseData

variable {n : ℕ} {base : Fin n → Ω}
  (H : R.CommonBaseData base)

end CommonBaseData

end PsiCurveCompositionBaseChangeRealization

namespace PsiCurveFourArrowCommonSourceRealizations

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)

/-- The alternative `sA` coefficient field is contained in the common
finite normal coefficient field. -/
theorem repeatedSAAlternativeInputField_le_normalField :
    R.repeatedSAAlternativeInputField ≤
      R.commonCoefficientNormalField.restrictScalars k :=
  R.repeatedSAAlternativeInputField_le_extended.trans
    R.commonCoefficientExtendedField_le_normalField

/-- The alternative `u` coefficient field is contained in the common
finite normal coefficient field. -/
theorem repeatedUAlternativeInputField_le_normalField :
    R.repeatedUAlternativeInputField ≤
      R.commonCoefficientNormalField.restrictScalars k :=
  R.repeatedUAlternativeInputField_le_extended.trans
    R.commonCoefficientExtendedField_le_normalField

/-- The alternative `uB` coefficient field is contained in the common
finite normal coefficient field. -/
theorem repeatedUBAlternativeInputField_le_normalField :
    R.repeatedUBAlternativeInputField ≤
      R.commonCoefficientNormalField.restrictScalars k :=
  R.repeatedUBAlternativeInputField_le_extended.trans
    R.commonCoefficientExtendedField_le_normalField

/-- The two independently relocated occurrences of the `sA`-family branch
have the same complete parameter/source/target locus. -/
theorem sAaAFamily_ideal_eq_sAcAFamily :
    (R.sAa.aCorrespondenceFamilyMember hψ).ideal =
      (R.sAc.aCorrespondenceFamilyMember hψ).ideal := by
  change idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.sA)
        R.sAa.source) R.sAa.middle) =
    idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.sA)
        R.sAc.source) R.sAc.middle)
  exact (R.sAa.aFamilyLocus hψ).trans (R.sAc.aFamilyLocus hψ).symm

/-- The two independently relocated direct branches labelled by `u` have
the same complete family locus. -/
theorem seCFamily_ideal_eq_sAaCFamily :
    (R.se.cCorrespondenceFamilyMember hψ).ideal =
      (R.sAa.cCorrespondenceFamilyMember hψ).ideal := by
  change idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.u)
        R.se.source) R.se.target) =
    idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.u)
        R.sAa.source) R.sAa.target)
  exact (R.se.cFamilyLocus hψ).trans (R.sAa.cFamilyLocus hψ).symm

/-- The two independently relocated direct branches labelled by `uB` have
the same complete family locus. -/
theorem sbCFamily_ideal_eq_sAcCFamily :
    (R.sb.cCorrespondenceFamilyMember hψ).ideal =
      (R.sAc.cCorrespondenceFamilyMember hψ).ideal := by
  change idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.uB)
        R.sb.source) R.sb.target) =
    idealOf k
      (Fin.snoc (Fin.snoc
        (commonCurveEmbedding (k := k) (K := K) ∘ D.uB)
        R.sAc.source) R.sAc.target)
  exact (R.sb.cFamilyLocus hψ).trans (R.sAc.cFamilyLocus hψ).symm

/-- The two selected `sA` branches have the same endpoint-pair ideal over
the literal rank-two `sA` parameter field. -/
theorem repeatedSAPairIdeal_eq_over_parameterField :
    idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.sA))))
        ![R.sAa.source, R.sAa.middle] =
      idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.sA))))
        ![R.sAc.source, R.sAc.middle] := by
  apply pairIdeal_eq_over_commonParameter_of_familyIdeal_eq
  exact R.sAaAFamily_ideal_eq_sAcAFamily

/-- The two selected direct `u` branches have the same endpoint-pair ideal
over the literal rank-two `u` parameter field. -/
theorem repeatedUPairIdeal_eq_over_parameterField :
    idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.u))))
        ![R.se.source, R.se.target] =
      idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.u))))
        ![R.sAa.source, R.sAa.target] := by
  apply pairIdeal_eq_over_commonParameter_of_familyIdeal_eq
  exact R.seCFamily_ideal_eq_sAaCFamily

/-- The two selected direct `uB` branches have the same endpoint-pair ideal
over the literal rank-two `uB` parameter field. -/
theorem repeatedUBPairIdeal_eq_over_parameterField :
    idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.uB))))
        ![R.sb.source, R.sb.target] =
      idealOf
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.uB))))
        ![R.sAc.source, R.sAc.target] := by
  apply pairIdeal_eq_over_commonParameter_of_familyIdeal_eq
  exact R.sbCFamily_ideal_eq_sAcCFamily

section SourceFieldAliases

/-!
### Source-field aliases

From here on, branch fields of different correspondence pairs are compared
over source fields that agree only definitionally: for instance
`repeatedSCommonCorrespondencePair_source_eq` is `rfl`, so the source field of
the `s·e = u` pair is the source field of the `s·b = uB` pair after unfolding.
Statements such as `repeatedSCommonBranchEquiv` need the induced instances
`Algebra ↥P.sourceField ↥P'.branchOverSource` across these aliases.  Since
Lean v4.34 instance search no longer unfolds such definitions under the
default transparency, so this section restores the earlier elaboration
behaviour with `backward.isDefEq.respectTransparency false`.  The setting
affects elaboration only; the kernel still checks every declaration.  See
issues #20 (version upgrade) and #18 (build performance) for the plan to
replace these aliases with explicit presentations.
-/

set_option backward.isDefEq.respectTransparency false

/-- The common-base branch equivalence carries the first displayed `s`
target to the second displayed `s` target. -/
@[simp] theorem repeatedSCommonBranchEquiv_target
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSCommonBranchEquiv hind
        ⟨R.se.middle, by
          change
            (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).target ∈
                (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
                  (R := R.se) R.seCommonBaseData hψ).branchField
          exact subset_adjoin _ _ (by simp)⟩ =
      ⟨R.sb.middle, by
        change
          (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.sb) R.sbCommonBaseData hψ).target ∈
              (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
                (R := R.sb) R.sbCommonBaseData hψ).branchField
        exact subset_adjoin _ _ (by simp)⟩ := by
  exact FiniteCoefficientBranchCompositum.branchEquivOfIdealEq_target
    R.seCommonBaseData.coefficientField
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    R.repeatedSCommonCorrespondencePair_source_eq
    (R.repeatedSCommonCorrespondencePair_ideal_eq hind)

/-- The common-input comparison of the repeated `s` relation is corrected
to preserve the literal selected branch.  This is the first faithful
anchor for the eventual four-triangle reference alignment. -/
noncomputable def repeatedSCommonBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).basedBranchEquivOfIdealEq
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.repeatedSCommonCorrespondencePair_ideal_eq hind)

/-- The faithful common-input `s` comparison sends the selected branch to
the selected branch. -/
@[simp] theorem repeatedSCommonBasedBranchEquiv_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedSCommonBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ).sourceField_le_branchField) =
      finiteCoverSelectedBranch
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ).sourceField_le_branchField :=
  (R.repeatedSCommonBasedBranchEquiv hind).map_selected

/-- The nested scalar-extension presentation for `sA` is exactly its named
alternative eight-input coefficient field. -/
theorem repeatedSAIndependentInputField_eq_alternative :
    (adjoin
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.sA))))
        (Set.range R.repeatedSAAuxiliaryInput)).restrictScalars k =
      R.repeatedSAAlternativeInputField := by
  unfold repeatedSAAlternativeInputField
  rw [adjoin_adjoin_left]

/-- The nested scalar-extension presentation for `u` is exactly its named
alternative eight-input coefficient field. -/
theorem repeatedUIndependentInputField_eq_alternative :
    (adjoin
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.u))))
        (Set.range R.repeatedUAuxiliaryInput)).restrictScalars k =
      R.repeatedUAlternativeInputField := by
  unfold repeatedUAlternativeInputField
  rw [adjoin_adjoin_left]

/-- The nested scalar-extension presentation for `uB` is exactly its named
alternative eight-input coefficient field. -/
theorem repeatedUBIndependentInputField_eq_alternative :
    (adjoin
        (↥(adjoin k (Set.range
          (commonCurveEmbedding (k := k) (K := K) ∘ D.uB))))
        (Set.range R.repeatedUBAuxiliaryInput)).restrictScalars k =
      R.repeatedUBAlternativeInputField := by
  unfold repeatedUBAlternativeInputField
  rw [adjoin_adjoin_left]

/-- The repeated `sA` curve relation remains equal after adjoining its six
complementary independent inputs. -/
theorem repeatedSAPairIdeal_eq_over_independentInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.sA))))
          (Set.range R.repeatedSAAuxiliaryInput)).restrictScalars k))
        ![R.sAa.source, R.sAa.middle] =
      idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.sA))))
          (Set.range R.repeatedSAAuxiliaryInput)).restrictScalars k))
        ![R.sAc.source, R.sAc.middle] := by
  apply pairIdeal_eq_over_independentExtension_of_pairIdeal_eq
    R.repeatedSAPairIdeal_eq_over_parameterField
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.sAa_source] using
        R.repeatedSA_auxiliary_parameter_source_independent hind
    · exact (R.sAa.aCorrespondenceFamilyMember hψ).target_mem_parameter_source
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.sAc_source] using
        R.repeatedSA_auxiliary_parameter_source_independent hind
    · exact (R.sAc.aCorrespondenceFamilyMember hψ).target_mem_parameter_source

/-- The repeated `sA` relation over its named alternative full input
field. -/
theorem repeatedSAPairIdeal_eq_over_alternativeInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf (↥R.repeatedSAAlternativeInputField)
        ![R.sAa.source, R.sAa.middle] =
      idealOf (↥R.repeatedSAAlternativeInputField)
        ![R.sAc.source, R.sAc.middle] := by
  rw [← R.repeatedSAIndependentInputField_eq_alternative]
  exact R.repeatedSAPairIdeal_eq_over_independentInputField hind

/-- The repeated direct `u` curve relation remains equal after adjoining
its six complementary independent inputs. -/
theorem repeatedUPairIdeal_eq_over_independentInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.u))))
          (Set.range R.repeatedUAuxiliaryInput)).restrictScalars k))
        ![R.se.source, R.se.target] =
      idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.u))))
          (Set.range R.repeatedUAuxiliaryInput)).restrictScalars k))
        ![R.sAa.source, R.sAa.target] := by
  apply pairIdeal_eq_over_independentExtension_of_pairIdeal_eq
    R.repeatedUPairIdeal_eq_over_parameterField
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.se_source] using
        R.repeatedU_auxiliary_parameter_source_independent hind
    · exact (R.se.cCorrespondenceFamilyMember hψ).target_mem_parameter_source
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.sAa_source] using
        R.repeatedU_auxiliary_parameter_source_independent hind
    · exact (R.sAa.cCorrespondenceFamilyMember hψ).target_mem_parameter_source

/-- The repeated direct `u` relation over its named alternative full input
field. -/
theorem repeatedUPairIdeal_eq_over_alternativeInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf (↥R.repeatedUAlternativeInputField)
        ![R.se.source, R.se.target] =
      idealOf (↥R.repeatedUAlternativeInputField)
        ![R.sAa.source, R.sAa.target] := by
  rw [← R.repeatedUIndependentInputField_eq_alternative]
  exact R.repeatedUPairIdeal_eq_over_independentInputField hind

/-- The repeated direct `uB` curve relation remains equal after adjoining
its six complementary independent inputs. -/
theorem repeatedUBPairIdeal_eq_over_independentInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.uB))))
          (Set.range R.repeatedUBAuxiliaryInput)).restrictScalars k))
        ![R.sb.source, R.sb.target] =
      idealOf
        (↥((adjoin
          (↥(adjoin k (Set.range
            (commonCurveEmbedding (k := k) (K := K) ∘ D.uB))))
          (Set.range R.repeatedUBAuxiliaryInput)).restrictScalars k))
        ![R.sAc.source, R.sAc.target] := by
  apply pairIdeal_eq_over_independentExtension_of_pairIdeal_eq
    R.repeatedUBPairIdeal_eq_over_parameterField
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.sb_source] using
        R.repeatedUB_auxiliary_parameter_source_independent hind
    · exact (R.sb.cCorrespondenceFamilyMember hψ).target_mem_parameter_source
  · apply auxiliary_independent_over_parameterPairField
    · simpa only [R.sAc_source] using
        R.repeatedUB_auxiliary_parameter_source_independent hind
    · exact (R.sAc.cCorrespondenceFamilyMember hψ).target_mem_parameter_source

/-- The repeated direct `uB` relation over its named alternative full input
field. -/
theorem repeatedUBPairIdeal_eq_over_alternativeInputField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    idealOf (↥R.repeatedUBAlternativeInputField)
        ![R.sb.source, R.sb.target] =
      idealOf (↥R.repeatedUBAlternativeInputField)
        ![R.sAc.source, R.sAc.target] := by
  rw [← R.repeatedUBIndependentInputField_eq_alternative]
  exact R.repeatedUBPairIdeal_eq_over_independentInputField hind

/-- The two alternative-field `sA` pairs have the same selected curve
ideal. -/
theorem repeatedSAAlternativePair_ideal_eq
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedSAFirstAlternativePair hind).ideal =
      (R.repeatedSASecondAlternativePair hind).ideal := by
  change idealOf (↥R.repeatedSAAlternativeInputField)
      ![R.sAa.source, R.sAa.middle] =
    idealOf (↥R.repeatedSAAlternativeInputField)
      ![R.sAc.source, R.sAc.middle]
  exact R.repeatedSAPairIdeal_eq_over_alternativeInputField hind

/-- The two alternative-field direct `u` pairs have the same selected
curve ideal. -/
theorem repeatedUAlternativePair_ideal_eq
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedUFirstAlternativePair hind).ideal =
      (R.repeatedUSecondAlternativePair hind).ideal := by
  change idealOf (↥R.repeatedUAlternativeInputField)
      ![R.se.source, R.se.target] =
    idealOf (↥R.repeatedUAlternativeInputField)
      ![R.sAa.source, R.sAa.target]
  exact R.repeatedUPairIdeal_eq_over_alternativeInputField hind

/-- The two alternative-field direct `uB` pairs have the same selected
curve ideal. -/
theorem repeatedUBAlternativePair_ideal_eq
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedUBFirstAlternativePair hind).ideal =
      (R.repeatedUBSecondAlternativePair hind).ideal := by
  change idealOf (↥R.repeatedUBAlternativeInputField)
      ![R.sb.source, R.sb.target] =
    idealOf (↥R.repeatedUBAlternativeInputField)
      ![R.sAc.source, R.sAc.target]
  exact R.repeatedUBPairIdeal_eq_over_alternativeInputField hind

/-- The repeated `sA` relation has a selected-branch-preserving comparison
over its full alternative input field. -/
noncomputable def repeatedSAAlternativeBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedSAFirstAlternativePair hind).basedBranchEquivOfIdealEq
    (R.repeatedSASecondAlternativePair hind)
    (R.repeatedSAAlternativePair_ideal_eq hind)

/-- The repeated direct `u` relation has a selected-branch-preserving
comparison over its full alternative input field. -/
noncomputable def repeatedUAlternativeBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedUFirstAlternativePair hind).basedBranchEquivOfIdealEq
    (R.repeatedUSecondAlternativePair hind)
    (R.repeatedUAlternativePair_ideal_eq hind)

/-- The repeated direct `uB` relation has a selected-branch-preserving
comparison over its full alternative input field. -/
noncomputable def repeatedUBAlternativeBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedUBFirstAlternativePair hind).basedBranchEquivOfIdealEq
    (R.repeatedUBSecondAlternativePair hind)
    (R.repeatedUBAlternativePair_ideal_eq hind)

/-- All three alternative-field comparisons preserve their literal
selected branches. -/
theorem repeatedAlternativeBasedBranchEquiv_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedSAAlternativeBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.repeatedSAFirstAlternativePair hind).sourceField_le_branchField) =
        finiteCoverSelectedBranch
          (R.repeatedSASecondAlternativePair hind).sourceField_le_branchField ∧
      (R.repeatedUAlternativeBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.repeatedUFirstAlternativePair hind).sourceField_le_branchField) =
        finiteCoverSelectedBranch
          (R.repeatedUSecondAlternativePair hind).sourceField_le_branchField ∧
      (R.repeatedUBAlternativeBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.repeatedUBFirstAlternativePair hind).sourceField_le_branchField) =
        finiteCoverSelectedBranch
          (R.repeatedUBSecondAlternativePair hind).sourceField_le_branchField :=
  ⟨(R.repeatedSAAlternativeBasedBranchEquiv hind).map_selected,
    (R.repeatedUAlternativeBasedBranchEquiv hind).map_selected,
    (R.repeatedUBAlternativeBasedBranchEquiv hind).map_selected⟩

/-- The joint `sA` coefficient-and-branch normal field is finite over its
alternative source-coordinate field. -/
theorem repeatedSACoefficientBranchNormalField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedSAAlternativeInputField
        (R.repeatedSAFirstAlternativePair hind)))
      (↥(R.repeatedSACoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedSA_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_finiteDimensional
    R.repeatedSAAlternativeInputField
    (R.repeatedSAFirstAlternativePair hind)
    (R.repeatedSASecondAlternativePair hind)
    (R.repeatedSAAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedSA

/-- The joint `sA` field is normal over its alternative source-coordinate
field. -/
theorem repeatedSACoefficientBranchNormalField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedSAAlternativeInputField
        (R.repeatedSAFirstAlternativePair hind)))
      (↥(R.repeatedSACoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedSA_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_normal
    R.repeatedSAAlternativeInputField
    (R.repeatedSAFirstAlternativePair hind)
    (R.repeatedSASecondAlternativePair hind)
    (R.repeatedSAAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedSA

/-- The pairwise `sA` normal source field contains the common coefficient
normalization and both selected branches. -/
theorem repeatedSACoefficientBranchNormalField_contains
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.commonCoefficientNormalOverRepeatedSA.restrictScalars k ≤
        (R.repeatedSACoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.firstBranchOverSource
          R.repeatedSAAlternativeInputField
          (R.repeatedSAFirstAlternativePair hind)).restrictScalars k ≤
        (R.repeatedSACoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.secondBranchOverSource
          R.repeatedSAAlternativeInputField
          (R.repeatedSAFirstAlternativePair hind)
          (R.repeatedSASecondAlternativePair hind)
          (R.repeatedSAAlternativePair_source_eq hind)).restrictScalars k ≤
        (R.repeatedSACoefficientBranchNormalField hind).restrictScalars k := by
  letI := R.commonCoefficientNormalOverRepeatedSA_finiteDimensional
  exact ⟨FiniteCoefficientBranchCompositum.coefficientExtension_le_normalField
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind)
      (R.repeatedSASecondAlternativePair hind)
      (R.repeatedSAAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedSA,
    FiniteCoefficientBranchCompositum.firstBranch_le_normalField
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind)
      (R.repeatedSASecondAlternativePair hind)
      (R.repeatedSAAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedSA,
    FiniteCoefficientBranchCompositum.secondBranch_le_normalField
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind)
      (R.repeatedSASecondAlternativePair hind)
      (R.repeatedSAAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedSA⟩

/-- The joint direct-`u` coefficient-and-branch normal field is finite
over its alternative source-coordinate field. -/
theorem repeatedUCoefficientBranchNormalField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUAlternativeInputField
        (R.repeatedUFirstAlternativePair hind)))
      (↥(R.repeatedUCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedU_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_finiteDimensional
    R.repeatedUAlternativeInputField
    (R.repeatedUFirstAlternativePair hind)
    (R.repeatedUSecondAlternativePair hind)
    (R.repeatedUAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedU

/-- The joint direct-`u` field is normal over its alternative
source-coordinate field. -/
theorem repeatedUCoefficientBranchNormalField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUAlternativeInputField
        (R.repeatedUFirstAlternativePair hind)))
      (↥(R.repeatedUCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedU_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_normal
    R.repeatedUAlternativeInputField
    (R.repeatedUFirstAlternativePair hind)
    (R.repeatedUSecondAlternativePair hind)
    (R.repeatedUAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedU

/-- The pairwise direct-`u` normal source field contains the common
coefficient normalization and both selected branches. -/
theorem repeatedUCoefficientBranchNormalField_contains
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.commonCoefficientNormalOverRepeatedU.restrictScalars k ≤
        (R.repeatedUCoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.firstBranchOverSource
          R.repeatedUAlternativeInputField
          (R.repeatedUFirstAlternativePair hind)).restrictScalars k ≤
        (R.repeatedUCoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.secondBranchOverSource
          R.repeatedUAlternativeInputField
          (R.repeatedUFirstAlternativePair hind)
          (R.repeatedUSecondAlternativePair hind)
          (R.repeatedUAlternativePair_source_eq hind)).restrictScalars k ≤
        (R.repeatedUCoefficientBranchNormalField hind).restrictScalars k := by
  letI := R.commonCoefficientNormalOverRepeatedU_finiteDimensional
  exact ⟨FiniteCoefficientBranchCompositum.coefficientExtension_le_normalField
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind)
      (R.repeatedUSecondAlternativePair hind)
      (R.repeatedUAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedU,
    FiniteCoefficientBranchCompositum.firstBranch_le_normalField
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind)
      (R.repeatedUSecondAlternativePair hind)
      (R.repeatedUAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedU,
    FiniteCoefficientBranchCompositum.secondBranch_le_normalField
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind)
      (R.repeatedUSecondAlternativePair hind)
      (R.repeatedUAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedU⟩

/-- The joint direct-`uB` coefficient-and-branch normal field is finite
over its alternative source-coordinate field. -/
theorem repeatedUBCoefficientBranchNormalField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUBAlternativeInputField
        (R.repeatedUBFirstAlternativePair hind)))
      (↥(R.repeatedUBCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedUB_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_finiteDimensional
    R.repeatedUBAlternativeInputField
    (R.repeatedUBFirstAlternativePair hind)
    (R.repeatedUBSecondAlternativePair hind)
    (R.repeatedUBAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedUB

/-- The joint direct-`uB` field is normal over its alternative
source-coordinate field. -/
theorem repeatedUBCoefficientBranchNormalField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal
      (↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUBAlternativeInputField
        (R.repeatedUBFirstAlternativePair hind)))
      (↥(R.repeatedUBCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedUB_finiteDimensional
  exact FiniteCoefficientBranchCompositum.normalField_normal
    R.repeatedUBAlternativeInputField
    (R.repeatedUBFirstAlternativePair hind)
    (R.repeatedUBSecondAlternativePair hind)
    (R.repeatedUBAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedUB

/-- The pairwise direct-`uB` normal source field contains the common
coefficient normalization and both selected branches. -/
theorem repeatedUBCoefficientBranchNormalField_contains
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.commonCoefficientNormalOverRepeatedUB.restrictScalars k ≤
        (R.repeatedUBCoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.firstBranchOverSource
          R.repeatedUBAlternativeInputField
          (R.repeatedUBFirstAlternativePair hind)).restrictScalars k ≤
        (R.repeatedUBCoefficientBranchNormalField hind).restrictScalars k ∧
      (FiniteCoefficientBranchCompositum.secondBranchOverSource
          R.repeatedUBAlternativeInputField
          (R.repeatedUBFirstAlternativePair hind)
          (R.repeatedUBSecondAlternativePair hind)
          (R.repeatedUBAlternativePair_source_eq hind)).restrictScalars k ≤
        (R.repeatedUBCoefficientBranchNormalField hind).restrictScalars k := by
  letI := R.commonCoefficientNormalOverRepeatedUB_finiteDimensional
  exact ⟨FiniteCoefficientBranchCompositum.coefficientExtension_le_normalField
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind)
      (R.repeatedUBSecondAlternativePair hind)
      (R.repeatedUBAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedUB,
    FiniteCoefficientBranchCompositum.firstBranch_le_normalField
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind)
      (R.repeatedUBSecondAlternativePair hind)
      (R.repeatedUBAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedUB,
    FiniteCoefficientBranchCompositum.secondBranch_le_normalField
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind)
      (R.repeatedUBSecondAlternativePair hind)
      (R.repeatedUBAlternativePair_source_eq hind)
      R.commonCoefficientNormalOverRepeatedUB⟩

/-- A deck transformation of the joint `sA` normal field that carries the
first literal selected branch to the second. -/
noncomputable def repeatedSABranchAutomorphism
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.repeatedSACoefficientBranchNormalField hind)) ≃ₐ[
      ↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedSAAlternativeInputField
        (R.repeatedSAFirstAlternativePair hind))]
      (↥(R.repeatedSACoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedSA_finiteDimensional
  exact FiniteCoefficientBranchCompositum.branchAutomorphismOfIdealEq
    R.repeatedSAAlternativeInputField
    (R.repeatedSAFirstAlternativePair hind)
    (R.repeatedSASecondAlternativePair hind)
    (R.repeatedSAAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedSA
    (R.repeatedSAAlternativePair_ideal_eq hind)

/-- A deck transformation of the joint direct-`u` normal field that carries
the first literal selected branch to the second. -/
noncomputable def repeatedUBranchAutomorphism
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.repeatedUCoefficientBranchNormalField hind)) ≃ₐ[
      ↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUAlternativeInputField
        (R.repeatedUFirstAlternativePair hind))]
      (↥(R.repeatedUCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedU_finiteDimensional
  exact FiniteCoefficientBranchCompositum.branchAutomorphismOfIdealEq
    R.repeatedUAlternativeInputField
    (R.repeatedUFirstAlternativePair hind)
    (R.repeatedUSecondAlternativePair hind)
    (R.repeatedUAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedU
    (R.repeatedUAlternativePair_ideal_eq hind)

/-- A deck transformation of the joint direct-`uB` normal field that carries
the first literal selected branch to the second. -/
noncomputable def repeatedUBBranchAutomorphism
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.repeatedUBCoefficientBranchNormalField hind)) ≃ₐ[
      ↥(FiniteCoefficientBranchCompositum.sourceField
        R.repeatedUBAlternativeInputField
        (R.repeatedUBFirstAlternativePair hind))]
      (↥(R.repeatedUBCoefficientBranchNormalField hind)) := by
  letI := R.commonCoefficientNormalOverRepeatedUB_finiteDimensional
  exact FiniteCoefficientBranchCompositum.branchAutomorphismOfIdealEq
    R.repeatedUBAlternativeInputField
    (R.repeatedUBFirstAlternativePair hind)
    (R.repeatedUBSecondAlternativePair hind)
    (R.repeatedUBAlternativePair_source_eq hind)
    R.commonCoefficientNormalOverRepeatedUB
    (R.repeatedUBAlternativePair_ideal_eq hind)

/-- The common source presentation after applying the alternative-base
`sA` branch comparison.  It is recorded as an image field because the
comparison is only linear over the alternative coefficient presentation. -/
def repeatedSACommonSourceImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField k (↥(R.repeatedSACoefficientBranchNormalField hind)) :=
  IntermediateField.imageUnderAutomorphism
    (R.repeatedSACommonSourceEmbedding hind)
    ((R.repeatedSABranchAutomorphism hind).restrictScalars k)

/-- The common source presentation after applying the alternative-base
direct-`u` branch comparison. -/
def repeatedUCommonSourceImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField k (↥(R.repeatedUCoefficientBranchNormalField hind)) :=
  IntermediateField.imageUnderAutomorphism
    (R.repeatedUCommonSourceEmbedding hind)
    ((R.repeatedUBranchAutomorphism hind).restrictScalars k)

/-- The common source presentation after applying the alternative-base
direct-`uB` branch comparison. -/
def repeatedUBCommonSourceImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField k (↥(R.repeatedUBCoefficientBranchNormalField hind)) :=
  IntermediateField.imageUnderAutomorphism
    (R.repeatedUBCommonSourceEmbedding hind)
    ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)

/-- The coefficient-faithful semilinear source chart induced by the `sA`
alternative-base comparison. -/
noncomputable def repeatedSACommonSourceImageEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.equivImageUnderAutomorphism
    (R.repeatedSACommonSourceEmbedding hind)
    ((R.repeatedSABranchAutomorphism hind).restrictScalars k)

/-- The coefficient-faithful semilinear source chart induced by the direct-`u`
alternative-base comparison. -/
noncomputable def repeatedUCommonSourceImageEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.equivImageUnderAutomorphism
    (R.repeatedUCommonSourceEmbedding hind)
    ((R.repeatedUBranchAutomorphism hind).restrictScalars k)

/-- The coefficient-faithful semilinear source chart induced by the direct-`uB`
alternative-base comparison. -/
noncomputable def repeatedUBCommonSourceImageEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.equivImageUnderAutomorphism
    (R.repeatedUBCommonSourceEmbedding hind)
    ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)

/-- The formal curve coordinate as an element of the literal common source
field. -/
def commonSourceGenerator :
    ↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k) :=
  ⟨commonCurveSource (K := K), by
    change commonCurveSource (K := K) ∈
      adjoin (↑R.seCommonBaseData.coefficientField)
        {commonCurveSource (K := K)}
    exact subset_adjoin _ _ (by simp)⟩

/-- The semilinear `sA` source chart fixes the formal curve coordinate even
though it may move coefficients of the literal common source presentation. -/
theorem repeatedSACommonSourceImageEquiv_generator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (((R.repeatedSACommonSourceImageEquiv hind)
      R.commonSourceGenerator : R.repeatedSACommonSourceImage hind) :
        R.repeatedSACoefficientBranchNormalField hind) =
      R.repeatedSACommonSourceEmbedding hind R.commonSourceGenerator := by
  unfold repeatedSACommonSourceImageEquiv
  rw [IntermediateField.equivImageUnderAutomorphism_apply]
  change (R.repeatedSABranchAutomorphism hind)
      (R.repeatedSACommonSourceEmbedding hind R.commonSourceGenerator) =
    R.repeatedSACommonSourceEmbedding hind R.commonSourceGenerator
  let y : FiniteCoefficientBranchCompositum.sourceField
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind) :=
    ⟨commonCurveSource (K := K), by
      change commonCurveSource (K := K) ∈
        adjoin R.repeatedSAAlternativeInputField
          {(R.repeatedSAFirstAlternativePair hind).source}
      apply subset_adjoin
      change commonCurveSource (K := K) = R.sAa.source
      exact R.sAa_source.symm⟩
  have hy : R.repeatedSACommonSourceEmbedding hind R.commonSourceGenerator =
      algebraMap _ (↥(R.repeatedSACoefficientBranchNormalField hind)) y := by
    ext
    rfl
  rw [hy]
  exact (R.repeatedSABranchAutomorphism hind).commutes y

/-- The semilinear direct-`u` source chart fixes the formal curve coordinate
while retaining its potentially moved coefficient presentation. -/
theorem repeatedUCommonSourceImageEquiv_generator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (((R.repeatedUCommonSourceImageEquiv hind)
      R.commonSourceGenerator : R.repeatedUCommonSourceImage hind) :
        R.repeatedUCoefficientBranchNormalField hind) =
      R.repeatedUCommonSourceEmbedding hind R.commonSourceGenerator := by
  unfold repeatedUCommonSourceImageEquiv
  rw [IntermediateField.equivImageUnderAutomorphism_apply]
  change (R.repeatedUBranchAutomorphism hind)
      (R.repeatedUCommonSourceEmbedding hind R.commonSourceGenerator) =
    R.repeatedUCommonSourceEmbedding hind R.commonSourceGenerator
  let y : FiniteCoefficientBranchCompositum.sourceField
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind) :=
    ⟨commonCurveSource (K := K), by
      change commonCurveSource (K := K) ∈
        adjoin R.repeatedUAlternativeInputField
          {(R.repeatedUFirstAlternativePair hind).source}
      apply subset_adjoin
      change commonCurveSource (K := K) = R.se.source
      exact R.se_source.symm⟩
  have hy : R.repeatedUCommonSourceEmbedding hind R.commonSourceGenerator =
      algebraMap _ (↥(R.repeatedUCoefficientBranchNormalField hind)) y := by
    ext
    rfl
  rw [hy]
  exact (R.repeatedUBranchAutomorphism hind).commutes y

/-- The semilinear direct-`uB` source chart fixes the formal curve coordinate
while retaining its potentially moved coefficient presentation. -/
theorem repeatedUBCommonSourceImageEquiv_generator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (((R.repeatedUBCommonSourceImageEquiv hind)
      R.commonSourceGenerator : R.repeatedUBCommonSourceImage hind) :
        R.repeatedUBCoefficientBranchNormalField hind) =
      R.repeatedUBCommonSourceEmbedding hind R.commonSourceGenerator := by
  unfold repeatedUBCommonSourceImageEquiv
  rw [IntermediateField.equivImageUnderAutomorphism_apply]
  change (R.repeatedUBBranchAutomorphism hind)
      (R.repeatedUBCommonSourceEmbedding hind R.commonSourceGenerator) =
    R.repeatedUBCommonSourceEmbedding hind R.commonSourceGenerator
  let y : FiniteCoefficientBranchCompositum.sourceField
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind) :=
    ⟨commonCurveSource (K := K), by
      change commonCurveSource (K := K) ∈
        adjoin R.repeatedUBAlternativeInputField
          {(R.repeatedUBFirstAlternativePair hind).source}
      apply subset_adjoin
      change commonCurveSource (K := K) = R.sb.source
      exact R.sb_source.symm⟩
  have hy : R.repeatedUBCommonSourceEmbedding hind R.commonSourceGenerator =
      algebraMap _ (↥(R.repeatedUBCoefficientBranchNormalField hind)) y := by
    ext
    rfl
  rw [hy]
  exact (R.repeatedUBBranchAutomorphism hind).commutes y

/-- Extend the semilinear `sA` source chart to the chosen algebraic
closures.  Its restriction to any finite common-source cover will provide
the corresponding coefficient-faithful source chart. -/
noncomputable def repeatedSACommonSourceImageClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  AlgebraicClosureTransport.lift
    (R.repeatedSACommonSourceImageEquiv hind).toRingEquiv

/-- Extend the semilinear direct-`u` source chart to the chosen algebraic
closures. -/
noncomputable def repeatedUCommonSourceImageClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  AlgebraicClosureTransport.lift
    (R.repeatedUCommonSourceImageEquiv hind).toRingEquiv

/-- Extend the semilinear direct-`uB` source chart to the chosen algebraic
closures. -/
noncomputable def repeatedUBCommonSourceImageClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  AlgebraicClosureTransport.lift
    (R.repeatedUBCommonSourceImageEquiv hind).toRingEquiv

/-- The semilinear `sA` source image, now viewed back in the common curve
ambient field alongside the original pairwise normal field. -/
def repeatedSACommonSourceAmbientImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.ambientImageUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedSACoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedSACoefficientBranchNormalField hind)
    ((R.repeatedSABranchAutomorphism hind).restrictScalars k)

/-- The semilinear direct-`u` source image in the common curve ambient. -/
def repeatedUCommonSourceAmbientImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.ambientImageUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUCoefficientBranchNormalField hind)
    ((R.repeatedUBranchAutomorphism hind).restrictScalars k)

/-- The semilinear direct-`uB` source image in the common curve ambient. -/
def repeatedUBCommonSourceAmbientImage
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.ambientImageUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUBCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUBCoefficientBranchNormalField hind)
    ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)

/-- The nested-extension equivalence coupling the moved `sA` common-source
presentation to the actual alternative-base branch automorphism on the
entire pairwise normal field. -/
noncomputable def repeatedSACommonSourceExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.extensionEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedSACoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedSACoefficientBranchNormalField hind)
    ((R.repeatedSABranchAutomorphism hind).restrictScalars k)

/-- The nested-extension equivalence coupling the moved direct-`u` source
presentation to its actual branch automorphism. -/
noncomputable def repeatedUCommonSourceExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.extensionEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUCoefficientBranchNormalField hind)
    ((R.repeatedUBranchAutomorphism hind).restrictScalars k)

/-- The nested-extension equivalence coupling the moved direct-`uB` source
presentation to its actual branch automorphism. -/
noncomputable def repeatedUBCommonSourceExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  IntermediateField.extensionEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUBCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUBCoefficientBranchNormalField hind)
    ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)

/-- Lift the full `sA` nested-extension comparison to its two canonical
normal closures.  Unlike a lift of the source equivalence alone, this datum
retains the branch automorphism on the total pairwise normal field. -/
noncomputable def repeatedSACommonSourceNormalExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedSACommonSourceExtensionEquiv hind).normalLift

/-- Lift the full direct-`u` nested-extension comparison to canonical normal
closures. -/
noncomputable def repeatedUCommonSourceNormalExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedUCommonSourceExtensionEquiv hind).normalLift

/-- Lift the full direct-`uB` nested-extension comparison to canonical normal
closures. -/
noncomputable def repeatedUBCommonSourceNormalExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.repeatedUBCommonSourceExtensionEquiv hind).normalLift

/- The canonical covers and total-field embeddings below use the literal
common source over its coefficient field throughout. Mixing it with the
restriction to k caused costly kernel conversions under Lean 4.34 (#20).
The explicit carrier equivalences preserve the original finite extensions. -/

/-- Canonical-cover algebra equivalence with one native base presentation. -/
noncomputable def nativeSACanonicalCoverAlgEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.nativeSAExtensionEquiv hind).mappedNormalAlgEquiv
    (R.nativeSAClosureTransport hind) (R.nativeSACommonRawRoundtrip hind)

/-- The identity-on-ambient-values equivalence from the rebased `sA`
source presentation to the literal common source presentation. -/
def repeatedSARebasedSourceEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥((adjoin R.seCommonBaseData.coefficientField
      {(R.repeatedSAFirstAlternativePair hind).source}))) ≃+*
      (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)) :=
  (R.nativeSAExtensionEquiv hind).baseEquiv.toRingEquiv.symm

/-- The chosen algebraic-closure transport extending the rebased-to-common
`sA` source equivalence. -/
noncomputable def repeatedSARebasedClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeSAClosureTransport hind

/-- The `sA` pairwise comparison cover before transporting its equal
ambient source presentation to the named literal common source type. -/
noncomputable def repeatedSARawRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeSARawCanonicalCover hind

/-- The corresponding identity-on-ambient-values equivalence of first
`sA` branch fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedSAFirstRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.firstBranchOverRebasedSource
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedSAFirstRebasedBranch_carrier_eq hind)

/-- The identity-on-ambient-values equivalence of second `sA` branch
fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedSASecondRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.secondBranchOverRebasedSource
      R.repeatedSAAlternativeInputField
      (R.repeatedSAFirstAlternativePair hind)
      (R.repeatedSASecondAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedSASecondRebasedBranch_carrier_eq hind)

/-- Restrict the coherent total-field embedding to its second literal branch. -/
noncomputable def nativeSASecondBranchEmbedding
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource)
      (↥(R.nativeSARebasedCover hind).field) := by
  have := R.nativeSACommonTotal_finiteDimensional hind
  exact ⟨(R.nativeSASelectedTotalAlgHom hind (Algebra.IsAlgebraic.of_finite _ _)).comp
    (IntermediateField.inclusion (R.nativeSASecondBranch_le_total hind))⟩

/-- Embed the second literal `sA` branch by restricting the coherent
whole-total-field embedding into its rebased canonical cover. -/
noncomputable def repeatedSASecondBranchEmbeddingInRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource)
      (↥(R.repeatedSARebasedCanonicalCover hind).field) :=
  R.nativeSASecondBranchEmbedding hind

/-- Canonical-cover algebra equivalence with one native base presentation. -/
noncomputable def nativeUCanonicalCoverAlgEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.nativeUExtensionEquiv hind).mappedNormalAlgEquiv
    (R.nativeUClosureTransport hind) (R.nativeUCommonRawRoundtrip hind)

/-- The identity-on-ambient-values equivalence from the raw direct-`u`
source presentation to the literal common source. -/
def repeatedURebasedSourceEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥((adjoin R.seCommonBaseData.coefficientField
      {(R.repeatedUFirstAlternativePair hind).source}))) ≃+*
      (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)) :=
  (R.nativeUExtensionEquiv hind).baseEquiv.toRingEquiv.symm

/-- The algebraic-closure transport extending the raw-to-common direct-`u`
source equivalence. -/
noncomputable def repeatedURebasedClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUClosureTransport hind

/-- The direct-`u` comparison cover before transporting its raw source
presentation to the named common-source algebraic closure. -/
noncomputable def repeatedURawRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeURawCanonicalCover hind

/-- The identity-on-ambient-values equivalence of the first direct-`u`
branch fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedUFirstRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.firstBranchOverRebasedSource
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥R.seCommonDirectPair.branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedUFirstRebasedBranch_carrier_eq hind)

/-- Restrict the coherent total-field embedding to its first literal branch. -/
noncomputable def nativeUFirstBranchEmbedding
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.seCommonDirectPair.branchOverSource)
      (↥(R.nativeURebasedCover hind).field) := by
  have := R.nativeUCommonTotal_finiteDimensional hind
  exact ⟨(R.nativeUSelectedTotalAlgHom hind (Algebra.IsAlgebraic.of_finite _ _)).comp
    (IntermediateField.inclusion (R.nativeUFirstBranch_le_total hind))⟩

/-- Embed the first literal direct-`u` branch by restricting the coherent
whole-total-field embedding into its rebased canonical cover. -/
noncomputable def repeatedUFirstBranchEmbeddingInRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.seCommonDirectPair.branchOverSource)
      (↥(R.repeatedURebasedCanonicalCover hind).field) :=
  R.nativeUFirstBranchEmbedding hind

/-- The identity-on-ambient-values equivalence of the second direct-`u`
branch fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedUSecondRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.secondBranchOverRebasedSource
      R.repeatedUAlternativeInputField
      (R.repeatedUFirstAlternativePair hind)
      (R.repeatedUSecondAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥R.sAaCommonDirectPair.branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedUSecondRebasedBranch_carrier_eq hind)

/-- Restrict the coherent total-field embedding to its second literal branch. -/
noncomputable def nativeUSecondBranchEmbedding
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAaCommonDirectPair.branchOverSource)
      (↥(R.nativeURebasedCover hind).field) := by
  have := R.nativeUCommonTotal_finiteDimensional hind
  exact ⟨(R.nativeUSelectedTotalAlgHom hind (Algebra.IsAlgebraic.of_finite _ _)).comp
    (IntermediateField.inclusion (R.nativeUSecondBranch_le_total hind))⟩

/-- Embed the second literal direct-`u` branch by restricting the coherent
whole-total-field embedding into its rebased canonical cover. -/
noncomputable def repeatedUSecondBranchEmbeddingInRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAaCommonDirectPair.branchOverSource)
      (↥(R.repeatedURebasedCanonicalCover hind).field) :=
  R.nativeUSecondBranchEmbedding hind

/-- Canonical-cover algebra equivalence with one native base presentation. -/
noncomputable def nativeUBCanonicalCoverAlgEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.nativeUBExtensionEquiv hind).mappedNormalAlgEquiv
    (R.nativeUBClosureTransport hind) (R.nativeUBCommonRawRoundtrip hind)

/-- Regard the literal-common-source `sA` extension as the raw rebased
extension used to construct the canonical comparison cover. The base
equality is taken over the native coefficient field; the total field stays
fixed. Both maps preserve ambient values. -/
noncomputable def repeatedSACommonToRawRebasedExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeSAExtensionEquiv hind

/-- The same equality-based comparison for the repeated direct-`u`
extension. -/
noncomputable def repeatedUCommonToRawRebasedExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUExtensionEquiv hind

/-- The equality-based comparison from the literal common-source
direct-`uB` extension to its raw rebased presentation. -/
noncomputable def repeatedUBCommonToRawRebasedExtensionEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUBExtensionEquiv hind

/-- The equality-based common-to-raw source change followed by the
raw-to-common semilinear source change is the identity. The projections use
the native definitions directly; the public map aliases denote the same maps
but converting through those aliases is costly under Lean 4.34 (#20). -/
theorem repeatedSACommonRawBaseRoundtrip
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : ↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField)) :
    (R.nativeSAClosureTransport hind).baseEquiv
        ((R.nativeSAExtensionEquiv hind).baseEquiv x) = x :=
  R.nativeSACommonRawRoundtrip hind x

/-- The corresponding common-to-raw-to-common source change for the
direct-`u` comparison is the identity. -/
theorem repeatedUCommonRawBaseRoundtrip
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : ↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField)) :
    (R.nativeUClosureTransport hind).baseEquiv
        ((R.nativeUExtensionEquiv hind).baseEquiv x) = x :=
  R.nativeUCommonRawRoundtrip hind x

/-- Compare the canonical normal closure of the pairwise `sA` total field
over the literal common source with the rebased canonical cover already
adjoined to `branchComparisonSourceCover`. -/
noncomputable def repeatedSACommonCanonicalCoverEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.canonicalNormalClosure
      (R.nativeSACommonSource_le_total hind))) ≃+*
      (↥(R.repeatedSARebasedCanonicalCover hind).field) :=
  (R.nativeSACanonicalCoverAlgEquiv hind).toRingEquiv

/-- The canonical `sA` cover comparison is an equivalence over the literal
common source, not merely an equivalence of its underlying fields. -/
noncomputable def repeatedSACommonCanonicalCoverAlgEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeSACanonicalCoverAlgEquiv hind

/-- Compare the direct-`u` common-source canonical normal closure with its
named rebased comparison cover. -/
noncomputable def repeatedUCommonCanonicalCoverEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.canonicalNormalClosure
      (R.nativeUCommonSource_le_total hind))) ≃+*
      (↥(R.repeatedURebasedCanonicalCover hind).field) :=
  (R.nativeUCanonicalCoverAlgEquiv hind).toRingEquiv

/-- The canonical direct-`u` cover comparison is an equivalence over the
literal common source. -/
noncomputable def repeatedUCommonCanonicalCoverAlgEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUCanonicalCoverAlgEquiv hind

/-- The deck-corrected semilinear `sA` normal-cover comparison preserves
the literal selected copy of the entire pairwise total field. -/
noncomputable def repeatedSACommonSourceBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCover.basedBranchEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedSACoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedSACoefficientBranchNormalField hind)
    ((R.repeatedSABranchAutomorphism hind).restrictScalars k)
    (R.repeatedSACoefficientBranchNormalField_finiteDimensional_overCommonSource
      hind)

/-- The deck-corrected semilinear direct-`u` normal-cover comparison
preserves the literal selected pairwise total field. -/
noncomputable def repeatedUCommonSourceBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCover.basedBranchEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUCoefficientBranchNormalField hind)
    ((R.repeatedUBranchAutomorphism hind).restrictScalars k)
    (R.repeatedUCoefficientBranchNormalField_finiteDimensional_overCommonSource
      hind)

/-- The deck-corrected semilinear direct-`uB` normal-cover comparison
preserves the literal selected pairwise total field. -/
noncomputable def repeatedUBCommonSourceBasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCover.basedBranchEquivUnderAutomorphism
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
    (R.repeatedUBCoefficientBranchNormalField hind)
    (R.commonSourceField_le_repeatedUBCoefficientBranchNormalField hind)
    ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)
    (R.repeatedUBCoefficientBranchNormalField_finiteDimensional_overCommonSource
      hind)

/-- All three deck-corrected semilinear comparisons preserve their literal
selected total-field branches. -/
theorem repeatedCommonSourceBasedBranchEquiv_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.repeatedSACommonSourceBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.commonSourceField_le_repeatedSACoefficientBranchNormalField hind)) =
        finiteCoverSelectedBranch
          (IntermediateField.ambientImageUnderAutomorphism_le
            ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
            (R.repeatedSACoefficientBranchNormalField hind)
            (R.commonSourceField_le_repeatedSACoefficientBranchNormalField hind)
            ((R.repeatedSABranchAutomorphism hind).restrictScalars k)) ∧
      (R.repeatedUCommonSourceBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.commonSourceField_le_repeatedUCoefficientBranchNormalField hind)) =
        finiteCoverSelectedBranch
          (IntermediateField.ambientImageUnderAutomorphism_le
            ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
            (R.repeatedUCoefficientBranchNormalField hind)
            (R.commonSourceField_le_repeatedUCoefficientBranchNormalField hind)
            ((R.repeatedUBranchAutomorphism hind).restrictScalars k)) ∧
      (R.repeatedUBCommonSourceBasedBranchEquiv hind).branchEquiv
        (finiteCoverSelectedBranch
          (R.commonSourceField_le_repeatedUBCoefficientBranchNormalField hind)) =
        finiteCoverSelectedBranch
          (IntermediateField.ambientImageUnderAutomorphism_le
            ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)
            (R.repeatedUBCoefficientBranchNormalField hind)
            (R.commonSourceField_le_repeatedUBCoefficientBranchNormalField hind)
            ((R.repeatedUBBranchAutomorphism hind).restrictScalars k)) :=
  ⟨FiniteCover.basedBranchEquivUnderAutomorphism_selected _ _ _ _ _,
    FiniteCover.basedBranchEquivUnderAutomorphism_selected _ _ _ _ _,
    FiniteCover.basedBranchEquivUnderAutomorphism_selected _ _ _ _ _⟩

/-- The identity-on-ambient-values equivalence from the raw direct-`uB`
source presentation to the literal common source. -/
def repeatedUBRebasedSourceEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥((adjoin R.seCommonBaseData.coefficientField
      {(R.repeatedUBFirstAlternativePair hind).source}))) ≃+*
      (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)) :=
  (R.nativeUBExtensionEquiv hind).baseEquiv.toRingEquiv.symm

/-- The algebraic-closure transport extending the raw-to-common direct-
`uB` source equivalence. -/
noncomputable def repeatedUBRebasedClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUBClosureTransport hind

/-- The direct-`uB` comparison cover before transporting its raw source
presentation to the named common-source algebraic closure. -/
noncomputable def repeatedUBRawRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUBRawCanonicalCover hind

/-- Compare the direct-`uB` common-source canonical normal closure with its
named rebased comparison cover. -/
noncomputable def repeatedUBCommonCanonicalCoverEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.canonicalNormalClosure
      (R.nativeUBCommonSource_le_total hind))) ≃+*
      (↥(R.repeatedUBRebasedCanonicalCover hind).field) :=
  (R.nativeUBCanonicalCoverAlgEquiv hind).toRingEquiv

/-- The common-to-raw-to-common source change for the direct-`uB`
comparison is the identity. -/
theorem repeatedUBCommonRawBaseRoundtrip
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : ↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField)) :
    (R.nativeUBClosureTransport hind).baseEquiv
        ((R.nativeUBExtensionEquiv hind).baseEquiv x) = x :=
  R.nativeUBCommonRawRoundtrip hind x

/-- The canonical direct-`uB` cover comparison is an equivalence over the
literal common source. -/
noncomputable def repeatedUBCommonCanonicalCoverAlgEquivRebased
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.nativeUBCanonicalCoverAlgEquiv hind

/-- The identity-on-ambient-values equivalence of the first direct-`uB`
branch fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedUBFirstRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.firstBranchOverRebasedSource
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥R.sbCommonDirectPair.branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedUBFirstRebasedBranch_carrier_eq hind)

/-- Restrict the coherent total-field embedding to its first literal branch. -/
noncomputable def nativeUBFirstBranchEmbedding
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sbCommonDirectPair.branchOverSource)
      (↥(R.nativeUBRebasedCover hind).field) := by
  have := R.nativeUBCommonTotal_finiteDimensional hind
  exact ⟨(R.nativeUBSelectedTotalAlgHom hind (Algebra.IsAlgebraic.of_finite _ _)).comp
    (IntermediateField.inclusion (R.nativeUBFirstBranch_le_total hind))⟩

/-- Embed the first literal direct-`uB` branch by restricting the coherent
whole-total-field embedding into its rebased canonical cover. -/
noncomputable def repeatedUBFirstBranchEmbeddingInRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sbCommonDirectPair.branchOverSource)
      (↥(R.repeatedUBRebasedCanonicalCover hind).field) :=
  R.nativeUBFirstBranchEmbedding hind

/-- The identity-on-ambient-values equivalence of the second direct-`uB`
branch fields.

Retained as a compatibility API for the raw restricted-source presentation
(issue #20); the canonical branch embeddings use whole-total restrictions. -/
def repeatedUBSecondRebasedBranchEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCoefficientBranchCompositum.secondBranchOverRebasedSource
      R.repeatedUBAlternativeInputField
      (R.repeatedUBFirstAlternativePair hind)
      (R.repeatedUBSecondAlternativePair hind)
      R.seCommonBaseData.coefficientField)) ≃+*
      (↥R.sAcCommonDirectPair.branchOverSource) :=
  IntermediateField.ringEquivOfCarrierEq _ _
    (R.repeatedUBSecondRebasedBranch_carrier_eq hind)

/-- Restrict the coherent total-field embedding to its second literal branch. -/
noncomputable def nativeUBSecondBranchEmbedding
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAcCommonDirectPair.branchOverSource)
      (↥(R.nativeUBRebasedCover hind).field) := by
  have := R.nativeUBCommonTotal_finiteDimensional hind
  exact ⟨(R.nativeUBSelectedTotalAlgHom hind (Algebra.IsAlgebraic.of_finite _ _)).comp
    (IntermediateField.inclusion (R.nativeUBSecondBranch_le_total hind))⟩

/-- Embed the second literal direct-`uB` branch by restricting the coherent
whole-total-field embedding into its rebased canonical cover. -/
noncomputable def repeatedUBSecondBranchEmbeddingInRebasedCanonicalCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAcCommonDirectPair.branchOverSource)
      (↥(R.repeatedUBRebasedCanonicalCover hind).field) :=
  R.nativeUBSecondBranchEmbedding hind

/-- The coefficient-aware normal-cover comparison for the repeated
`s` branch.  It retains the displayed `s` parameter and source coordinates;
the based comparison below additionally corrects it to the selected
branch. -/
noncomputable def repeatedSNormalExtensionEquiv :=
  (R.se.aCorrespondenceFamilyMember hψ).normalExtensionEquivOfIdealEq
    (R.sb.aCorrespondenceFamilyMember hψ)
    R.seAFamily_ideal_eq_sbAFamily

/-- The coefficient-aware normal-cover comparison for the repeated
`sA` branch. -/
noncomputable def repeatedSANormalExtensionEquiv :=
  (R.sAa.aCorrespondenceFamilyMember hψ).normalExtensionEquivOfIdealEq
    (R.sAc.aCorrespondenceFamilyMember hψ)
    R.sAaAFamily_ideal_eq_sAcAFamily

/-- The coefficient-aware normal-cover comparison for the repeated direct
branch labelled by `u`. -/
noncomputable def repeatedUNormalExtensionEquiv :=
  (R.se.cCorrespondenceFamilyMember hψ).normalExtensionEquivOfIdealEq
    (R.sAa.cCorrespondenceFamilyMember hψ)
    R.seCFamily_ideal_eq_sAaCFamily

/-- The coefficient-aware normal-cover comparison for the repeated direct
branch labelled by `uB`. -/
noncomputable def repeatedUBNormalExtensionEquiv :=
  (R.sb.cCorrespondenceFamilyMember hψ).normalExtensionEquivOfIdealEq
    (R.sAc.cCorrespondenceFamilyMember hψ)
    R.sbCFamily_ideal_eq_sAcCFamily

/-- The repeated `s` comparison corrected equivariantly so that the
literal selected middle branch is preserved. -/
noncomputable def repeatedSBasedBranchEquiv :=
  (R.se.aCorrespondenceFamilyMember hψ).basedBranchEquivOfIdealEq
    (R.sb.aCorrespondenceFamilyMember hψ)
    R.seAFamily_ideal_eq_sbAFamily

/-- The repeated `sA` comparison corrected equivariantly so that the
literal selected middle branch is preserved. -/
noncomputable def repeatedSABasedBranchEquiv :=
  (R.sAa.aCorrespondenceFamilyMember hψ).basedBranchEquivOfIdealEq
    (R.sAc.aCorrespondenceFamilyMember hψ)
    R.sAaAFamily_ideal_eq_sAcAFamily

/-- The repeated `u` comparison corrected equivariantly so that the
literal selected target branch is preserved. -/
noncomputable def repeatedUBasedBranchEquiv :=
  (R.se.cCorrespondenceFamilyMember hψ).basedBranchEquivOfIdealEq
    (R.sAa.cCorrespondenceFamilyMember hψ)
    R.seCFamily_ideal_eq_sAaCFamily

/-- The repeated `uB` comparison corrected equivariantly so that the
literal selected target branch is preserved. -/
noncomputable def repeatedUBBasedBranchEquiv :=
  (R.sb.cCorrespondenceFamilyMember hψ).basedBranchEquivOfIdealEq
    (R.sAc.cCorrespondenceFamilyMember hψ)
    R.sbCFamily_ideal_eq_sAcCFamily

/-- The enlarged common source cover transported along the semilinear `sA`
source chart. -/
noncomputable def repeatedSAImageBranchComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).map
    (R.repeatedSACommonSourceImageClosureTransport hind)

/-- The enlarged common source cover transported along the semilinear
direct-`u` source chart. -/
noncomputable def repeatedUImageBranchComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).map
    (R.repeatedUCommonSourceImageClosureTransport hind)

/-- The enlarged common source cover transported along the semilinear
direct-`uB` source chart. -/
noncomputable def repeatedUBImageBranchComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).map
    (R.repeatedUBCommonSourceImageClosureTransport hind)

/-- The finite-cover source chart induced by the alternative-base `sA`
comparison. -/
noncomputable def repeatedSAImageSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).mapEquiv
    (R.repeatedSACommonSourceImageClosureTransport hind)

/-- The finite-cover source chart induced by the alternative-base direct-`u`
comparison. -/
noncomputable def repeatedUImageSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).mapEquiv
    (R.repeatedUCommonSourceImageClosureTransport hind)

/-- The finite-cover source chart induced by the alternative-base
direct-`uB` comparison. -/
noncomputable def repeatedUBImageSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).mapEquiv
    (R.repeatedUBCommonSourceImageClosureTransport hind)

/-- On the formal curve generator, the finite-cover `sA` chart is exactly
the algebra map induced by the semilinear source-image equivalence. -/
theorem repeatedSAImageSourceChart_commonSourceGenerator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSAImageSourceChart hind
        ⟨algebraMap
          (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k))
          (AlgebraicClosure
            (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)))
          R.commonSourceGenerator,
          (R.branchComparisonSourceCover hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥(R.repeatedSACommonSourceImage hind))
          (AlgebraicClosure (↥(R.repeatedSACommonSourceImage hind)))
          (R.repeatedSACommonSourceImageEquiv hind R.commonSourceGenerator),
        (R.repeatedSAImageBranchComparisonSourceCover hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact (R.repeatedSACommonSourceImageClosureTransport hind).commutes_apply
    R.commonSourceGenerator

/-- On the formal curve generator, the finite-cover direct-`u` chart is the
algebra map induced by its semilinear source-image equivalence. -/
theorem repeatedUImageSourceChart_commonSourceGenerator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUImageSourceChart hind
        ⟨algebraMap
          (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k))
          (AlgebraicClosure
            (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)))
          R.commonSourceGenerator,
          (R.branchComparisonSourceCover hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥(R.repeatedUCommonSourceImage hind))
          (AlgebraicClosure (↥(R.repeatedUCommonSourceImage hind)))
          (R.repeatedUCommonSourceImageEquiv hind R.commonSourceGenerator),
        (R.repeatedUImageBranchComparisonSourceCover hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact (R.repeatedUCommonSourceImageClosureTransport hind).commutes_apply
    R.commonSourceGenerator

/-- On the formal curve generator, the finite-cover direct-`uB` chart is the
algebra map induced by its semilinear source-image equivalence. -/
theorem repeatedUBImageSourceChart_commonSourceGenerator
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUBImageSourceChart hind
        ⟨algebraMap
          (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k))
          (AlgebraicClosure
            (↥((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k)))
          R.commonSourceGenerator,
          (R.branchComparisonSourceCover hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥(R.repeatedUBCommonSourceImage hind))
          (AlgebraicClosure (↥(R.repeatedUBCommonSourceImage hind)))
          (R.repeatedUBCommonSourceImageEquiv hind R.commonSourceGenerator),
        (R.repeatedUBImageBranchComparisonSourceCover hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact (R.repeatedUBCommonSourceImageClosureTransport hind).commutes_apply
    R.commonSourceGenerator

/-- The second coefficient-comparison `sA` branch in the same enlarged
common source cover. -/
noncomputable def repeatedSASecondBranchEmbeddingInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) :=
  ⟨(IntermediateField.inclusion
      (R.repeatedSARebasedCanonicalCover_le_branchComparisonSourceCover hind)).comp
    (R.repeatedSASecondBranchEmbeddingInRebasedCanonicalCover hind).toAlgHom⟩

/-- A common-base deck transformation removes the normal-closure choice
between the `sA·a=u` face branch and its first coefficient-comparison copy. -/
noncomputable def repeatedSAFirstClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind)
    (R.repeatedSAFirstBranchEmbeddingInComparisonSourceCover hind)

/-- The first closure alignment has the prescribed effect on the selected
`sA` branch embedding. -/
theorem repeatedSAFirstClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSAFirstClosureAlignmentAut hind •
        R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind =
      R.repeatedSAFirstBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- A common-base deck transformation likewise removes the closure choice
between the `sA·c=uB` face branch and its second comparison copy. -/
noncomputable def repeatedSASecondClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind)
    (R.repeatedSASecondBranchEmbeddingInComparisonSourceCover hind)

/-- The second closure alignment has the prescribed effect on the selected
`sA` branch embedding. -/
theorem repeatedSASecondClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSASecondClosureAlignmentAut hind •
        R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind =
      R.repeatedSASecondBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The first coefficient-comparison direct-`u` branch, included in the
enlarged common source cover. -/
noncomputable def repeatedUFirstBranchEmbeddingInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.seCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) :=
  ⟨(IntermediateField.inclusion
      (R.repeatedURebasedCanonicalCover_le_branchComparisonSourceCover hind)).comp
    (R.repeatedUFirstBranchEmbeddingInRebasedCanonicalCover hind).toAlgHom⟩

/-- The second coefficient-comparison direct-`u` branch in the same
enlarged common source cover. -/
noncomputable def repeatedUSecondBranchEmbeddingInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAaCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) :=
  ⟨(IntermediateField.inclusion
      (R.repeatedURebasedCanonicalCover_le_branchComparisonSourceCover hind)).comp
    (R.repeatedUSecondBranchEmbeddingInRebasedCanonicalCover hind).toAlgHom⟩

/-- Regard the selected direct branch of the `s·e=u` face over the named
canonical common-source presentation. -/
noncomputable def seSelectedDirectBranchRebasedInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.seCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) := by
  exact R.seSelectedDirectBranchInComparisonSourceCover hind

/-- Regard the selected direct branch of the `sA·a=u` face over the same
canonical common-source presentation. -/
noncomputable def sAaSelectedDirectBranchRebasedInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAaCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) := by
  exact R.sAaSelectedDirectBranchInComparisonSourceCover hind

/-- A common-base deck transformation aligns the selected direct `u`
branch of the `s·e=u` face with its first coefficient-comparison copy. -/
noncomputable def repeatedUFirstClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.seSelectedDirectBranchRebasedInComparisonSourceCover hind)
    (R.repeatedUFirstBranchEmbeddingInComparisonSourceCover hind)

/-- The first direct-`u` closure alignment has the prescribed action on
the selected branch embedding. -/
theorem repeatedUFirstClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUFirstClosureAlignmentAut hind •
        R.seSelectedDirectBranchRebasedInComparisonSourceCover hind =
      R.repeatedUFirstBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- A common-base deck transformation aligns the selected direct `u`
branch of the `sA·a=u` face with its second comparison copy. -/
noncomputable def repeatedUSecondClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.sAaSelectedDirectBranchRebasedInComparisonSourceCover hind)
    (R.repeatedUSecondBranchEmbeddingInComparisonSourceCover hind)

/-- The second direct-`u` closure alignment likewise has the prescribed
action on the selected branch embedding. -/
theorem repeatedUSecondClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUSecondClosureAlignmentAut hind •
        R.sAaSelectedDirectBranchRebasedInComparisonSourceCover hind =
      R.repeatedUSecondBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The first coefficient-comparison direct-`uB` branch, included in the
enlarged common source cover. -/
noncomputable def repeatedUBFirstBranchEmbeddingInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sbCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) :=
  ⟨(IntermediateField.inclusion
      (R.repeatedUBRebasedCanonicalCover_le_branchComparisonSourceCover hind)).comp
    (R.repeatedUBFirstBranchEmbeddingInRebasedCanonicalCover hind).toAlgHom⟩

/-- The second coefficient-comparison direct-`uB` branch in the same
enlarged common source cover. -/
noncomputable def repeatedUBSecondBranchEmbeddingInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAcCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) :=
  ⟨(IntermediateField.inclusion
      (R.repeatedUBRebasedCanonicalCover_le_branchComparisonSourceCover hind)).comp
    (R.repeatedUBSecondBranchEmbeddingInRebasedCanonicalCover hind).toAlgHom⟩

/-- Regard the selected direct branch of the `s·b=uB` face over the named
canonical common-source presentation. -/
noncomputable def sbSelectedDirectBranchRebasedInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sbCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) := by
  exact R.sbSelectedDirectBranchInComparisonSourceCover hind

/-- Regard the selected direct branch of the `sA·c=uB` face over the same
canonical common-source presentation. -/
noncomputable def sAcSelectedDirectBranchRebasedInComparisonSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    NormalBranchEmbedding
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥R.sAcCommonDirectPair.branchOverSource)
      (↥(R.branchComparisonSourceCover hind).field) := by
  exact R.sAcSelectedDirectBranchInComparisonSourceCover hind

/-- A common-base deck transformation aligns the selected direct `uB`
branch of the `s·b=uB` face with its first coefficient-comparison copy. -/
noncomputable def repeatedUBFirstClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.sbSelectedDirectBranchRebasedInComparisonSourceCover hind)
    (R.repeatedUBFirstBranchEmbeddingInComparisonSourceCover hind)

/-- The first direct-`uB` closure alignment has the prescribed action on
the selected branch embedding. -/
theorem repeatedUBFirstClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUBFirstClosureAlignmentAut hind •
        R.sbSelectedDirectBranchRebasedInComparisonSourceCover hind =
      R.repeatedUBFirstBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- A common-base deck transformation aligns the selected direct `uB`
branch of the `sA·c=uB` face with its second comparison copy. -/
noncomputable def repeatedUBSecondClosureAlignmentAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.branchComparisonSourceCover hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut
    (R.sAcSelectedDirectBranchRebasedInComparisonSourceCover hind)
    (R.repeatedUBSecondBranchEmbeddingInComparisonSourceCover hind)

/-- The second direct-`uB` closure alignment likewise has the prescribed
action on the selected branch embedding. -/
theorem repeatedUBSecondClosureAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedUBSecondClosureAlignmentAut hind •
        R.sAcSelectedDirectBranchRebasedInComparisonSourceCover hind =
      R.repeatedUBSecondBranchEmbeddingInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The common-source alignment automorphism carries the first selected
`s` embedding to the reparametrized second selected `s` embedding. -/
theorem repeatedSBranchAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSBranchAlignmentAut hind •
        R.seSelectedLeftBranchInComparisonSourceCover hind =
      R.sbSelectedLeftBranchReparametrizedInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul
    (R.seSelectedLeftBranchInComparisonSourceCover hind)
    (R.sbSelectedLeftBranchReparametrizedInComparisonSourceCover hind)

/-- Pointwise, the common-source alignment carries the actual first
displayed middle coordinate of the repeated `s` branch to the actual
second displayed middle coordinate. -/
theorem repeatedSBranchAlignmentAut_selectedTarget
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.repeatedSBranchAlignmentAut hind
        ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom
          ⟨R.se.middle, by
            change
              (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
                (R := R.se) R.seCommonBaseData hψ).target ∈
              (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
                (R := R.se) R.seCommonBaseData hψ).branchField
            exact subset_adjoin _ _ (by simp)⟩) =
      (R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom
        ⟨R.sb.middle, by
          change
            (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.sb) R.sbCommonBaseData hψ).target ∈
            (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
              (R := R.sb) R.sbCommonBaseData hψ).branchField
          exact subset_adjoin _ _ (by simp)⟩ := by
  let x :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).branchOverSource :=
    ⟨R.se.middle, by
      change
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).target ∈
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).branchField
      exact subset_adjoin _ _ (by simp)⟩
  let y :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).branchOverSource :=
    ⟨R.sb.middle, by
      change
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ).target ∈
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ).branchField
      exact subset_adjoin _ _ (by simp)⟩
  have hmap := congrArg (fun f ↦ f.toAlgHom x)
    (R.repeatedSBranchAlignmentAut_smul hind)
  change R.repeatedSBranchAlignmentAut hind
      ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x) =
    (R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom
      (R.repeatedSCommonBranchEquiv hind x) at hmap
  have hxy : R.repeatedSCommonBranchEquiv hind x = y := by
    simpa only [x, y] using R.repeatedSCommonBranchEquiv_target hind
  have htarget := congrArg
    (R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom hxy
  simpa only [x, y] using hmap.trans htarget

end SourceFieldAliases

end PsiCurveFourArrowCommonSourceRealizations

end QWitness

end

end AclGeom
