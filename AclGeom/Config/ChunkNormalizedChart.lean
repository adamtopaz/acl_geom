/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkRelationCover

/-!
# A reference-normalized chart for the joint chunk cover

The complete joint chunk locus is positive-dimensional, while the branch
ambiguity above each of its points is finite.  A reference edge trivializes
that finite branch/deck local system without collapsing the joint locus to
the deck group.  This module packages the resulting product decomposition
and transports every based branch action to one fixed normal-cover field.

The base of the bundles below remains `PsiChunkRelationRealization`, hence
retains all nine coordinates and the complete joint multiplication locus.
Only the finite conjugate-branch direction is normalized.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable (w : QWitness k K)

/-- The total finite branch bundle over all realizations of the complete
joint chunk locus. -/
abbrev PsiChunkBranchBundle :=
  Σ R : w.PsiChunkRelationRealization,
    FiniteCoverBranch R.ambientField_le_jointField

/-- The total deck-transformation bundle over all realizations of the
complete joint chunk locus. -/
abbrev PsiChunkDeckBundle :=
  Σ R : w.PsiChunkRelationRealization,
    FiniteCoverDeck R.ambientField_le_jointField

namespace PsiChunkRelationRealization

variable {w : QWitness k K}

/-- Normalize the branch fiber of `R` into the branch fiber of one fixed
reference edge. -/
noncomputable def normalizeBranch [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization) :
    FiniteCoverBranch R.ambientField_le_jointField ≃
      FiniteCoverBranch reference.ambientField_le_jointField :=
  (branchTrivialization hψ reference R).branchEquiv.symm

/-- Normalize the deck group of `R` into the deck group of one fixed
reference edge. -/
noncomputable def normalizeDeck [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization) :
    FiniteCoverDeck R.ambientField_le_jointField ≃*
      FiniteCoverDeck reference.ambientField_le_jointField :=
  (branchTrivialization hψ reference R).deckEquiv.symm

/-- Reference normalization preserves the literal selected branch. -/
@[simp] theorem normalizeBranch_selected [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization) :
    normalizeBranch hψ reference R
        (finiteCoverSelectedBranch R.ambientField_le_jointField) =
      finiteCoverSelectedBranch reference.ambientField_le_jointField := by
  exact (branchTrivialization hψ reference R).symm.map_selected

/-- Reference normalization remains equivariant for the deck action. -/
@[simp] theorem normalizeBranch_smul [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization)
    (σ : FiniteCoverDeck R.ambientField_le_jointField)
    (b : FiniteCoverBranch R.ambientField_le_jointField) :
    normalizeBranch hψ reference R (σ • b) =
      normalizeDeck hψ reference R σ •
        normalizeBranch hψ reference R b := by
  exact (branchTrivialization hψ reference R).symm.map_smul σ b

/-- A joint realization equipped with its literal selected branch. -/
def selectedBranchPoint (R : w.PsiChunkRelationRealization) :
    w.PsiChunkBranchBundle :=
  ⟨R, finiteCoverSelectedBranch R.ambientField_le_jointField⟩

/-- A reference edge globally trivializes the finite branch bundle while
leaving its positive-dimensional base realization unchanged. -/
noncomputable def branchBundleTrivialization [IsAlgClosed K] (hψ : w.Psi)
    (reference : w.PsiChunkRelationRealization) :
    w.PsiChunkBranchBundle ≃
      (w.PsiChunkRelationRealization ×
        FiniteCoverBranch reference.ambientField_le_jointField) where
  toFun z := ⟨z.1, normalizeBranch hψ reference z.1 z.2⟩
  invFun z := ⟨z.1, (normalizeBranch hψ reference z.1).symm z.2⟩
  left_inv z := by
    rcases z with ⟨R, b⟩
    simp
  right_inv z := by
    rcases z with ⟨R, b⟩
    simp

/-- Under the global trivialization, the selected branch section is the
constant selected branch in the reference fiber. -/
@[simp] theorem branchBundleTrivialization_selected [IsAlgClosed K]
    (hψ : w.Psi) (reference R : w.PsiChunkRelationRealization) :
    branchBundleTrivialization hψ reference (selectedBranchPoint R) =
      (R, finiteCoverSelectedBranch
        reference.ambientField_le_jointField) := by
  apply Prod.ext
  · rfl
  · exact normalizeBranch_selected hψ reference R

/-- The same reference edge globally trivializes the finite deck-group
bundle. -/
noncomputable def deckBundleTrivialization [IsAlgClosed K] (hψ : w.Psi)
    (reference : w.PsiChunkRelationRealization) :
    w.PsiChunkDeckBundle ≃
      (w.PsiChunkRelationRealization ×
        FiniteCoverDeck reference.ambientField_le_jointField) where
  toFun z := ⟨z.1, normalizeDeck hψ reference z.1 z.2⟩
  invFun z := ⟨z.1, (normalizeDeck hψ reference z.1).symm z.2⟩
  left_inv z := by
    rcases z with ⟨R, σ⟩
    simp
  right_inv z := by
    rcases z with ⟨R, σ⟩
    simp

/-- Normalize a based arrow family into the fixed reference branch
groupoid. -/
noncomputable def normalizedArrowEquiv [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization)
    (b : finiteCoverBranchGroupoid R.ambientField_le_jointField) :
    (finiteCoverSelectedObject R.ambientField_le_jointField ⟶ b) ≃
      (finiteCoverSelectedObject reference.ambientField_le_jointField ⟶
        (normalizeBranch hψ reference R b.back :
          finiteCoverBranchGroupoid
            reference.ambientField_le_jointField)) :=
  (branchTrivialization hψ reference R).symm.arrowEquiv b

/-- Arrow normalization sends the deck label through the normalized deck
equivalence. -/
@[simp] theorem normalizedArrowEquiv_label [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization)
    (b : finiteCoverBranchGroupoid R.ambientField_le_jointField)
    (a : finiteCoverSelectedObject R.ambientField_le_jointField ⟶ b) :
    actionCategoryLabel (normalizedArrowEquiv hψ reference R b a) =
      normalizeDeck hψ reference R (actionCategoryLabel a) := rfl

/-- Every based branch action above `R` can be represented on the one fixed
normal-cover field of `reference`.  The parameter type still belongs to
the original edge fiber; only its finite deck action has been descended. -/
noncomputable def normalizedTranslationChunk [IsAlgClosed K] (hψ : w.Psi)
    (reference R : w.PsiChunkRelationRealization)
    (b : finiteCoverBranchGroupoid R.ambientField_le_jointField) :
    TranslationGroupChunk (↥reference.ambientField)
      (↥(FiniteCover.normalClosureOver
        reference.ambientField_le_jointField))
      (finiteCoverSelectedObject R.ambientField_le_jointField ⟶ b) := by
  let e := normalizedArrowEquiv hψ reference R b
  let a₀ := finiteCoverSelectedArrow R.ambientField_le_jointField
    (R.jointExtension_finiteDimensional hψ) b
  exact (actionCategoryTranslationChunk (e a₀)).reindex e

/-- The common-field translation attached to an original fiber arrow is
the inverse normalized difference label in the reference deck group. -/
@[simp] theorem normalizedTranslationChunk_translation [IsAlgClosed K]
    (hψ : w.Psi) (reference R : w.PsiChunkRelationRealization)
    (b : finiteCoverBranchGroupoid R.ambientField_le_jointField)
    (a : finiteCoverSelectedObject R.ambientField_le_jointField ⟶ b) :
    (normalizedTranslationChunk hψ reference R b).translation a =
      ((normalizeDeck hψ reference R
          (actionCategoryLabel
            (finiteCoverSelectedArrow R.ambientField_le_jointField
              (R.jointExtension_finiteDimensional hψ) b)))⁻¹ *
        normalizeDeck hψ reference R (actionCategoryLabel a))⁻¹ := by
  simp [normalizedTranslationChunk]

end PsiChunkRelationRealization

end QWitness

end

end AclGeom
