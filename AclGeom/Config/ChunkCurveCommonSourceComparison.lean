/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource

/-!
# Coefficient-comparison charts over the common source

Branch-comparison covers, composition triangles and the final coefficient-chart
identities for the four semilinear faces. Split from
`AclGeom.Config.ChunkCurveCommonSource` (#18).
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

/-- The common finite normal middle cover of the larger-base triangle. -/
noncomputable def finiteMiddleCover (hψ : w.Psi) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.middleCover
    (aCorrespondencePair (R := R) H hψ)
    (bCorrespondencePair (R := R) H hψ)
    (aPair_target_eq_bPair_source (R := R) H hψ)

/-- The common finite normal target cover of the larger-base triangle. -/
noncomputable def finiteTargetCover (hψ : w.Psi) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.targetCover
    (aCorrespondencePair (R := R) H hψ)
    (bCorrespondencePair (R := R) H hψ)
    (aPair_target_eq_bPair_source (R := R) H hψ)

/-- The deck-corrected finite-cover action of the common-base triangle. -/
noncomputable def finiteCoverCompositionTriangle (hψ : w.Psi) :
    FieldEquiv.CompositionTriangle
      (↥(finiteSourceCover (R := R) H hψ).field)
      (↥(finiteMiddleCover (R := R) H hψ).field)
      (↥(finiteTargetCover (R := R) H hψ).field) where
  left := FiniteCorrespondencePair.FiniteCoverTriangle.leftEquiv
    (aCorrespondencePair (R := R) H hψ)
    (bCorrespondencePair (R := R) H hψ)
    (aPair_target_eq_bPair_source (R := R) H hψ)
  right := FiniteCorrespondencePair.FiniteCoverTriangle.rightEquiv
    (aCorrespondencePair (R := R) H hψ)
    (bCorrespondencePair (R := R) H hψ)
    (aPair_target_eq_bPair_source (R := R) H hψ)
  direct := FiniteCorrespondencePair.FiniteCoverTriangle.strictDirectEquiv
    (aCorrespondencePair (R := R) H hψ)
    (bCorrespondencePair (R := R) H hψ)
    (aPair_target_eq_bPair_source (R := R) H hψ)
  composition :=
    FiniteCorrespondencePair.FiniteCoverTriangle.strictComposition
      (aCorrespondencePair (R := R) H hψ)
      (bCorrespondencePair (R := R) H hψ)
      (aPair_target_eq_bPair_source (R := R) H hψ)

end CommonBaseData

end PsiCurveCompositionBaseChangeRealization

namespace PsiCurveFourArrowCommonSourceRealizations

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)

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

/- The canonical covers and total-field embeddings below use the literal
common source over its coefficient field throughout. Mixing it with the
restriction to k caused costly kernel conversions under Lean 4.34 (#20).
The explicit carrier equivalences preserve the original finite extensions. -/

/-- The strict finite-cover composition triangle for `s·e=u`, now over the
common eight-input coefficient field. -/
noncomputable def seFiniteCoverCompositionTriangle :=
  PsiCurveCompositionBaseChangeRealization.CommonBaseData.finiteCoverCompositionTriangle
    (R := R.se) R.seCommonBaseData hψ

/-- The strict finite-cover composition triangle for `sA·a=u`, over the
same common coefficient field. -/
noncomputable def sAaFiniteCoverCompositionTriangle :=
  PsiCurveCompositionBaseChangeRealization.CommonBaseData.finiteCoverCompositionTriangle
    (R := R.sAa) R.sAaCommonBaseData hψ

/-- The strict finite-cover composition triangle for `s·b=uB`, over the
same common coefficient field. -/
noncomputable def sbFiniteCoverCompositionTriangle :=
  PsiCurveCompositionBaseChangeRealization.CommonBaseData.finiteCoverCompositionTriangle
    (R := R.sb) R.sbCommonBaseData hψ

/-- The strict finite-cover composition triangle for `sA·c=uB`, over the
same common coefficient field. -/
noncomputable def sAcFiniteCoverCompositionTriangle :=
  PsiCurveCompositionBaseChangeRealization.CommonBaseData.finiteCoverCompositionTriangle
    (R := R.sAc) R.sAcCommonBaseData hψ

/-- The strict `s·e=u` action after enlarging its source to the
simultaneous four-face compositum. -/
noncomputable def seCommonCoverCompositionTriangle :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    R.commonFiniteSourceCover

/-- The strict `sA·a=u` action on the same simultaneous source
compositum. -/
noncomputable def sAaCommonCoverCompositionTriangle :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    R.commonFiniteSourceCover

/-- The strict `s·b=uB` action on the same simultaneous source
compositum. -/
noncomputable def sbCommonCoverCompositionTriangle :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    R.commonFiniteSourceCover

/-- The strict `sA·c=uB` action on the same simultaneous source
compositum. -/
noncomputable def sAcCommonCoverCompositionTriangle :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    R.commonFiniteSourceCover

/-- The strict `s·e=u` action on the enlarged source cover which also
contains all three rebased branch-comparison covers. -/
noncomputable def seBranchComparisonCoverCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)

/-- The strict `sA·a=u` action on the same enlarged branch-comparison
source cover. -/
noncomputable def sAaBranchComparisonCoverCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)

/-- The strict `s·b=uB` action on the same enlarged branch-comparison
source cover. -/
noncomputable def sbBranchComparisonCoverCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)

/-- The strict `sA·c=uB` action on the same enlarged branch-comparison
source cover. -/
noncomputable def sAcBranchComparisonCoverCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)

/-- The selected right `e` branch, embedded in the middle cover of the
enlarged `s·e=u` composition triangle. -/
noncomputable def seSelectedRightBranchInComparisonMiddleCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)
    (R.seFiniteSourceCover_le_branchComparisonSourceCover hind)

/-- The selected right `a` branch, embedded in the middle cover of the
enlarged `sA·a=u` composition triangle. -/
noncomputable def sAaSelectedRightBranchInComparisonMiddleCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)
    (R.sAaFiniteSourceCover_le_branchComparisonSourceCover hind)

/-- The selected right `b` branch, embedded in the middle cover of the
enlarged `s·b=uB` composition triangle. -/
noncomputable def sbSelectedRightBranchInComparisonMiddleCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)
    (R.sbFiniteSourceCover_le_branchComparisonSourceCover hind)

/-- The selected right `c` branch, embedded in the middle cover of the
enlarged `sA·c=uB` composition triangle. -/
noncomputable def sAcSelectedRightBranchInComparisonMiddleCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (R.branchComparisonSourceCover hind)
    (R.sAcFiniteSourceCover_le_branchComparisonSourceCover hind)

/-- The `sA·a=u` and canonical `s·e=u` source fields have the same
ambient carrier.  Keeping this equality explicit records the coefficient-
field presentation change needed before comparing their selected branches. -/
theorem sAaSourceField_carrier_eq :
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).sourceField :
        Set (CommonCurveAmbient K)) =
      ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField :
          Set (CommonCurveAmbient K)) := by
  change ((adjoin (↥R.sAaCommonBaseData.coefficientField)
      {R.sAaCommonBaseData.source}) : Set (CommonCurveAmbient K)) =
    ((adjoin (↥R.seCommonBaseData.coefficientField)
      {R.seCommonBaseData.source}) : Set (CommonCurveAmbient K))
  rfl

/-- The identity-on-ambient-values source equivalence from the
`sA·a=u` face to the canonical common-base presentation. -/
def sAaSourceFieldEquiv :
    (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).sourceField) ≃+*
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField) :=
  IntermediateField.ringEquivOfCarrierEq _ _ R.sAaSourceField_carrier_eq

/-- The `sA·c=uB` source field has the same ambient carrier as the
canonical common source field. -/
theorem sAcSourceField_carrier_eq :
    ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).sourceField :
        Set (CommonCurveAmbient K)) =
      ((PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField :
          Set (CommonCurveAmbient K)) := by
  change ((adjoin (↥R.sAcCommonBaseData.coefficientField)
      {R.sAcCommonBaseData.source}) : Set (CommonCurveAmbient K)) =
    ((adjoin (↥R.seCommonBaseData.coefficientField)
      {R.seCommonBaseData.source}) : Set (CommonCurveAmbient K))
  rfl

/-- The identity-on-ambient-values source equivalence from the
`sA·c=uB` face to the canonical common-base presentation. -/
def sAcSourceFieldEquiv :
    (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).sourceField) ≃+*
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField) :=
  IntermediateField.ringEquivOfCarrierEq _ _ R.sAcSourceField_carrier_eq

/-- The first coherent `sA` anchor alignment has the prescribed action on
the entire selected branch. -/
theorem sAaRepeatedSATotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAaRepeatedSATotalAnchorAlignmentAut hind •
        R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind =
      R.sAaSelectedLeftBranchViaRepeatedSATotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The second coherent `sA` anchor alignment has the prescribed action on
the entire selected branch. -/
theorem sAcRepeatedSATotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAcRepeatedSATotalAnchorAlignmentAut hind •
        R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind =
      R.sAcSelectedLeftBranchViaRepeatedSATotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The first coherent direct-`u` anchor alignment has the prescribed
action on the entire selected branch. -/
theorem seRepeatedUTotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seRepeatedUTotalAnchorAlignmentAut hind •
        R.seSelectedDirectBranchInComparisonSourceCover hind =
      R.seSelectedDirectBranchViaRepeatedUTotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The second coherent direct-`u` anchor alignment has the prescribed
action on the entire selected branch. -/
theorem sAaRepeatedUTotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAaRepeatedUTotalAnchorAlignmentAut hind •
        R.sAaSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind =
      R.sAaSelectedDirectBranchViaRepeatedUTotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The first coherent direct-`uB` anchor alignment has the prescribed
action on the entire selected branch. -/
theorem sbRepeatedUBTotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sbRepeatedUBTotalAnchorAlignmentAut hind •
        R.sbSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind =
      R.sbSelectedDirectBranchViaRepeatedUBTotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The second coherent direct-`uB` anchor alignment has the prescribed
action on the entire selected branch. -/
theorem sAcRepeatedUBTotalAnchorAlignmentAut_smul
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAcRepeatedUBTotalAnchorAlignmentAut hind •
        R.sAcSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind =
      R.sAcSelectedDirectBranchViaRepeatedUBTotalInComparisonSourceCover hind := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.branchComparisonSourceCover hind).field) :=
    (R.branchComparisonSourceCover hind).normal
  exact NormalBranchEmbedding.alignmentAut_smul _ _

/-- The source chart for the `s·e=u` face.  It fixes the literal common
coefficient/source field and sends the selected direct `u` branch to the
first coherent whole-total-field anchor. -/
noncomputable def seCoefficientSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃+*
      (↥(R.branchComparisonSourceCover hind).field) :=
  (R.seRepeatedUTotalAnchorAlignmentAut hind).toRingEquiv

/-- The source chart for the `sA·a=u` face, using the second coherent
direct-`u` anchor. -/
noncomputable def sAaCoefficientSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃+*
      (↥(R.branchComparisonSourceCover hind).field) :=
  (R.sAaRepeatedUTotalAnchorAlignmentAut hind).toRingEquiv

/-- The source chart for the `s·b=uB` face, using the first coherent
direct-`uB` anchor. -/
noncomputable def sbCoefficientSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃+*
      (↥(R.branchComparisonSourceCover hind).field) :=
  (R.sbRepeatedUBTotalAnchorAlignmentAut hind).toRingEquiv

/-- The source chart for the `sA·c=uB` face, using the second coherent
direct-`uB` anchor. -/
noncomputable def sAcCoefficientSourceChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) ≃+*
      (↥(R.branchComparisonSourceCover hind).field) :=
  (R.sAcRepeatedUBTotalAnchorAlignmentAut hind).toRingEquiv

/-- All four source charts fix the literal common coefficient/source field.
This is the coefficient-faithfulness condition needed when their induced
middle charts select a different conjugate of a left branch. -/
theorem coefficientSourceCharts_commute
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (∀ x :
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).sourceField,
      R.seCoefficientSourceChart hind
          (algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) =
        algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) ∧
    (∀ x :
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).sourceField,
      R.sAaCoefficientSourceChart hind
          (algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) =
        algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) ∧
    (∀ x :
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).sourceField,
      R.sbCoefficientSourceChart hind
          (algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) =
        algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) ∧
    (∀ x :
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).sourceField,
      R.sAcCoefficientSourceChart hind
          (algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) =
        algebraMap _ (↥(R.branchComparisonSourceCover hind).field) x) := by
  exact ⟨fun x ↦ (R.seRepeatedUTotalAnchorAlignmentAut hind).commutes x,
    fun x ↦ (R.sAaRepeatedUTotalAnchorAlignmentAut hind).commutes x,
    fun x ↦ (R.sbRepeatedUBTotalAnchorAlignmentAut hind).commutes x,
    fun x ↦ (R.sAcRepeatedUBTotalAnchorAlignmentAut hind).commutes x⟩

/-- The four enlarged strict triangles, charted against their literal
common source cover.  Middle and target charts are induced from the four
coefficient-fixing source charts above, so all four compatibility equations
are literal equalities while the selected direct branches retain the
coherent `u` and `uB` anchors. -/
noncomputable def coefficientFourTriangleReference
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FieldEquiv.FourTriangleReference.ofSourceCharts
    (R.seBranchComparisonCoverCompositionTriangle hind)
    (R.sAaBranchComparisonCoverCompositionTriangle hind)
    (R.sbBranchComparisonCoverCompositionTriangle hind)
    (R.sAcBranchComparisonCoverCompositionTriangle hind)
    (R.seCoefficientSourceChart hind)
    (R.sAaCoefficientSourceChart hind)
    (R.sbCoefficientSourceChart hind)
    (R.sAcCoefficientSourceChart hind)

/-- The source-gauge-normalized four-arrow diagram obtained from the four
coefficient/source charts on the enlarged common normal cover.  Its selected
graph embeddings remain useful, but its four abstract right arrows are
identities because the middle and target charts are induced from the source
charts. -/
noncomputable def coefficientFourArrowDiagram
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.coefficientFourTriangleReference hind).toFourArrowDiagram

/-- All four abstract right arrows in the source-induced coefficient diagram
are identities.  This theorem records that its cancellation law is a gauge
identity; parameter-dependent information must be read from the selected
branch embeddings until independently chosen common charts are supplied. -/
theorem coefficientFourArrow_right_arrows_eq_refl
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.coefficientFourArrowDiagram hind).rightE = RingEquiv.refl _ ∧
      (R.coefficientFourArrowDiagram hind).rightA = RingEquiv.refl _ ∧
      (R.coefficientFourArrowDiagram hind).rightB = RingEquiv.refl _ ∧
      (R.coefficientFourArrowDiagram hind).rightC = RingEquiv.refl _ := by
  exact FieldEquiv.FourTriangleReference.ofSourceCharts_right_arrows_eq_refl
    (R.seBranchComparisonCoverCompositionTriangle hind)
    (R.sAaBranchComparisonCoverCompositionTriangle hind)
    (R.sbBranchComparisonCoverCompositionTriangle hind)
    (R.sAcBranchComparisonCoverCompositionTriangle hind)
    (R.seCoefficientSourceChart hind)
    (R.sAaCoefficientSourceChart hind)
    (R.sbCoefficientSourceChart hind)
    (R.sAcCoefficientSourceChart hind)

/-- The induced middle chart on the `s·e=u` face fixes the original
common coefficient field. -/
theorem seCoefficientMiddleChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).seY
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.seBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
      (R.seCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.seBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_algebraMap (R.seCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.seRepeatedUTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.se) R.seCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced middle chart on the `sA·a=u` face fixes the same
coefficient field. -/
theorem sAaCoefficientMiddleChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sAaY
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sAaBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
      (R.sAaCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sAaBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_algebraMap (R.sAaCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sAaRepeatedUTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced middle chart on the `s·b=uB` face fixes the common
coefficient field. -/
theorem sbCoefficientMiddleChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sbY
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sbBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
      (R.sbCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sbBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_algebraMap (R.sbCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sbRepeatedUBTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sb) R.sbCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced middle chart on the `sA·c=uB` face fixes the common
coefficient field. -/
theorem sAcCoefficientMiddleChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sAcY
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sAcBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
      (R.sAcCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sAcBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_algebraMap (R.sAcCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sAcRepeatedUBTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced target chart on the `s·e=u` face fixes the original
common coefficient field. -/
theorem seCoefficientTargetChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).seZ
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.seBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
      (R.seCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.seBranchComparisonCoverCompositionTriangle hind)
    |>.inducedTargetChart_algebraMap (R.seCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.seRepeatedUTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.strictDirectEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.se) R.seCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced target chart on the `sA·a=u` face fixes the same
coefficient field. -/
theorem sAaCoefficientTargetChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sAaZ
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sAaBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
      (R.sAaCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sAaBranchComparisonCoverCompositionTriangle hind)
    |>.inducedTargetChart_algebraMap (R.sAaCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sAaRepeatedUTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.strictDirectEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sAa) R.sAaCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced target chart on the `s·b=uB` face fixes the common
coefficient field. -/
theorem sbCoefficientTargetChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sbZ
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sbBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
      (R.sbCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sbBranchComparisonCoverCompositionTriangle hind)
    |>.inducedTargetChart_algebraMap (R.sbCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sbRepeatedUBTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.strictDirectEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sb) R.sbCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sb) R.sbCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- The induced target chart on the `sA·c=uB` face fixes the common
coefficient field. -/
theorem sAcCoefficientTargetChart_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (c : ↥R.seCommonBaseData.coefficientField) :
    (R.coefficientFourTriangleReference hind).sAcZ
        (algebraMap _ _ c) =
      algebraMap _ (↥(R.branchComparisonSourceCover hind).field) c := by
  change (R.sAcBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
      (R.sAcCoefficientSourceChart hind) (algebraMap _ _ c) = _
  apply (R.sAcBranchComparisonCoverCompositionTriangle hind)
    |>.inducedTargetChart_algebraMap (R.sAcCoefficientSourceChart hind)
  · intro d
    exact algEquiv_coefficient_algebraMap
      (R.sAcRepeatedUBTotalAnchorAlignmentAut hind) d
  · exact
      FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.strictDirectEquiv_algebraMap
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
          (R := R.sAc) R.sAcCommonBaseData hψ)
        (R.branchComparisonSourceCover hind)

/-- After the coefficient chart, the selected right `e` branch still
satisfies its original canonical curve equation. -/
theorem seCoefficientMiddleChart_selectedRight_curveEquation
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    let Q :=
      PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ
    MvPolynomial.aeval
        ![(R.coefficientFourTriangleReference hind).seY
            ((R.seSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.sourceInBranchOverSource),
          (R.coefficientFourTriangleReference hind).seY
            ((R.seSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.targetInBranchOverSource)]
        Q.curveEquation = 0 := by
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle_curveEquation
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.se) R.seCommonBaseData hψ)
      (R.branchComparisonSourceCover hind)
      (R.seFiniteSourceCover_le_branchComparisonSourceCover hind)
      (R.coefficientFourTriangleReference hind).seY
      (R.seCoefficientMiddleChart_algebraMap hind)

/-- After the coefficient chart, the selected right `a` branch still
satisfies its original canonical curve equation. -/
theorem sAaCoefficientMiddleChart_selectedRight_curveEquation
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    let Q :=
      PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ
    MvPolynomial.aeval
        ![(R.coefficientFourTriangleReference hind).sAaY
            ((R.sAaSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.sourceInBranchOverSource),
          (R.coefficientFourTriangleReference hind).sAaY
            ((R.sAaSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.targetInBranchOverSource)]
        Q.curveEquation = 0 := by
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle_curveEquation
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (R.branchComparisonSourceCover hind)
      (R.sAaFiniteSourceCover_le_branchComparisonSourceCover hind)
      (R.coefficientFourTriangleReference hind).sAaY
      (R.sAaCoefficientMiddleChart_algebraMap hind)

/-- After the coefficient chart, the selected right `b` branch still
satisfies its original canonical curve equation. -/
theorem sbCoefficientMiddleChart_selectedRight_curveEquation
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    let Q :=
      PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ
    MvPolynomial.aeval
        ![(R.coefficientFourTriangleReference hind).sbY
            ((R.sbSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.sourceInBranchOverSource),
          (R.coefficientFourTriangleReference hind).sbY
            ((R.sbSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.targetInBranchOverSource)]
        Q.curveEquation = 0 := by
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle_curveEquation
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sb) R.sbCommonBaseData hψ)
      (R.branchComparisonSourceCover hind)
      (R.sbFiniteSourceCover_le_branchComparisonSourceCover hind)
      (R.coefficientFourTriangleReference hind).sbY
      (R.sbCoefficientMiddleChart_algebraMap hind)

/-- After the coefficient chart, the selected right `c` branch still
satisfies its original canonical curve equation. -/
theorem sAcCoefficientMiddleChart_selectedRight_curveEquation
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    let Q :=
      PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ
    MvPolynomial.aeval
        ![(R.coefficientFourTriangleReference hind).sAcY
            ((R.sAcSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.sourceInBranchOverSource),
          (R.coefficientFourTriangleReference hind).sAcY
            ((R.sAcSelectedRightBranchInComparisonMiddleCover hind).toAlgHom
              Q.targetInBranchOverSource)]
        Q.curveEquation = 0 := by
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle_curveEquation
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (R.branchComparisonSourceCover hind)
      (R.sAcFiniteSourceCover_le_branchComparisonSourceCover hind)
      (R.coefficientFourTriangleReference hind).sAcY
      (R.sAcCoefficientMiddleChart_algebraMap hind)

/-- On the first face, the induced middle chart is exactly the
coefficient-fixing source chart on the selected left branch. -/
theorem seCoefficientMiddleChart_selectedLeft
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).branchOverSource) :
    (R.coefficientFourTriangleReference hind).seY
        ((R.seBranchComparisonCoverCompositionTriangle hind).left
          ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)) =
      R.seCoefficientSourceChart hind
        ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x) := by
  change
    (R.seBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
        (R.seCoefficientSourceChart hind)
        ((R.seBranchComparisonCoverCompositionTriangle hind).left
          ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)) = _
  exact (R.seBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_left_apply (R.seCoefficientSourceChart hind)
      ((R.seSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)

/-- On the second face, the induced middle chart is the corresponding
coefficient-fixing source chart on the selected `sA` branch. -/
theorem sAaCoefficientMiddleChart_selectedLeft
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource) :
    (R.coefficientFourTriangleReference hind).sAaY
        ((R.sAaBranchComparisonCoverCompositionTriangle hind).left
          ((R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)) =
      R.sAaCoefficientSourceChart hind
        ((R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x) := by
  change
    (R.sAaBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
        (R.sAaCoefficientSourceChart hind)
        ((R.sAaBranchComparisonCoverCompositionTriangle hind).left
          ((R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)) = _
  exact (R.sAaBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_left_apply (R.sAaCoefficientSourceChart hind)
      ((R.sAaSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)

/-- On the third face, the induced middle chart is the coefficient-fixing
source chart on the selected `s` branch. -/
theorem sbCoefficientMiddleChart_selectedLeft
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).branchOverSource) :
    (R.coefficientFourTriangleReference hind).sbY
        ((R.sbBranchComparisonCoverCompositionTriangle hind).left
          ((R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)) =
      R.sbCoefficientSourceChart hind
        ((R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x) := by
  change
    (R.sbBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
        (R.sbCoefficientSourceChart hind)
        ((R.sbBranchComparisonCoverCompositionTriangle hind).left
          ((R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)) = _
  exact (R.sbBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_left_apply (R.sbCoefficientSourceChart hind)
      ((R.sbSelectedLeftBranchInComparisonSourceCover hind).toAlgHom x)

/-- On the fourth face, the induced middle chart is the coefficient-fixing
source chart on the selected `sA` branch. -/
theorem sAcCoefficientMiddleChart_selectedLeft
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource) :
    (R.coefficientFourTriangleReference hind).sAcY
        ((R.sAcBranchComparisonCoverCompositionTriangle hind).left
          ((R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)) =
      R.sAcCoefficientSourceChart hind
        ((R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x) := by
  change
    (R.sAcBranchComparisonCoverCompositionTriangle hind).inducedMiddleChart
        (R.sAcCoefficientSourceChart hind)
        ((R.sAcBranchComparisonCoverCompositionTriangle hind).left
          ((R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)) = _
  exact (R.sAcBranchComparisonCoverCompositionTriangle hind)
    |>.inducedMiddleChart_left_apply (R.sAcCoefficientSourceChart hind)
      ((R.sAcSelectedLeftBranchRebasedInComparisonSourceCover hind).toAlgHom x)

/-- The induced target chart of the first face carries its selected direct
branch to the first coherent `u` anchor, pointwise on the entire branch
field. -/
theorem seCoefficientTargetChart_selectedDirect
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.seCommonDirectPair.branchOverSource) :
    (R.coefficientFourTriangleReference hind).seZ
        ((R.seBranchComparisonCoverCompositionTriangle hind).direct
          ((R.seSelectedDirectBranchInComparisonSourceCover hind).toAlgHom x)) =
      (R.seSelectedDirectBranchViaRepeatedUTotalInComparisonSourceCover hind).toAlgHom x := by
  change
    (R.seBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
        (R.seCoefficientSourceChart hind)
        ((R.seBranchComparisonCoverCompositionTriangle hind).direct
          ((R.seSelectedDirectBranchInComparisonSourceCover hind).toAlgHom x)) = _
  rw [FieldEquiv.CompositionTriangle.inducedTargetChart_direct_apply]
  have hmap := congrArg (fun f ↦ f.toAlgHom x)
    (R.seRepeatedUTotalAnchorAlignmentAut_smul hind)
  exact hmap

/-- The induced target chart of the second face carries its selected direct
branch to the second coherent `u` anchor. -/
theorem sAaCoefficientTargetChart_selectedDirect
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.sAaCommonDirectPair.branchOverSource) :
    (R.coefficientFourTriangleReference hind).sAaZ
        ((R.sAaBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sAaSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) =
      (R.sAaSelectedDirectBranchViaRepeatedUTotalInComparisonSourceCover hind).toAlgHom x := by
  change
    (R.sAaBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
        (R.sAaCoefficientSourceChart hind)
        ((R.sAaBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sAaSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) = _
  rw [FieldEquiv.CompositionTriangle.inducedTargetChart_direct_apply]
  have hmap := congrArg (fun f ↦ f.toAlgHom x)
    (R.sAaRepeatedUTotalAnchorAlignmentAut_smul hind)
  exact hmap

/-- The induced target chart of the third face carries its selected direct
branch to the first coherent `uB` anchor. -/
theorem sbCoefficientTargetChart_selectedDirect
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.sbCommonDirectPair.branchOverSource) :
    (R.coefficientFourTriangleReference hind).sbZ
        ((R.sbBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sbSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) =
      (R.sbSelectedDirectBranchViaRepeatedUBTotalInComparisonSourceCover hind).toAlgHom x := by
  change
    (R.sbBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
        (R.sbCoefficientSourceChart hind)
        ((R.sbBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sbSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) = _
  rw [FieldEquiv.CompositionTriangle.inducedTargetChart_direct_apply]
  have hmap := congrArg (fun f ↦ f.toAlgHom x)
    (R.sbRepeatedUBTotalAnchorAlignmentAut_smul hind)
  exact hmap

/-- The induced target chart of the fourth face carries its selected direct
branch to the second coherent `uB` anchor. -/
theorem sAcCoefficientTargetChart_selectedDirect
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.sAcCommonDirectPair.branchOverSource) :
    (R.coefficientFourTriangleReference hind).sAcZ
        ((R.sAcBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sAcSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) =
      (R.sAcSelectedDirectBranchViaRepeatedUBTotalInComparisonSourceCover hind).toAlgHom x := by
  change
    (R.sAcBranchComparisonCoverCompositionTriangle hind).inducedTargetChart
        (R.sAcCoefficientSourceChart hind)
        ((R.sAcBranchComparisonCoverCompositionTriangle hind).direct
          ((R.sAcSelectedDirectBranchOverCommonSourceInComparisonSourceCover hind).toAlgHom x)) = _
  rw [FieldEquiv.CompositionTriangle.inducedTargetChart_direct_apply]
  have hmap := congrArg (fun f ↦ f.toAlgHom x)
    (R.sAcRepeatedUBTotalAnchorAlignmentAut_smul hind)
  exact hmap

/-- Literal four-arrow cancellation on the coefficient-charted common normal
cover.  With the current source-induced charts this is the identity gauge
law recorded above, rather than the eventual intrinsic parameter
factorization. -/
theorem coefficientFourArrow_right_cancellation
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.coefficientFourArrowDiagram hind).rightC =
      ((R.coefficientFourArrowDiagram hind).rightA.trans
        (R.coefficientFourArrowDiagram hind).rightE.symm).trans
          (R.coefficientFourArrowDiagram hind).rightB :=
  (R.coefficientFourArrowDiagram hind).right_cancellation

end SourceFieldAliases

end PsiCurveFourArrowCommonSourceRealizations

end QWitness

end

end AclGeom
