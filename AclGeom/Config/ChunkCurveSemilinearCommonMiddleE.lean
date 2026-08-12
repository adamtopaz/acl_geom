/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchE

/-! # The intrinsic germ in the common-source `e` middle field -/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

/-- Factored coefficient restriction for a finite triangle's left arrow.
Keeping the correspondence pair abstract prevents the concrete nested cover
types below from being duplicated in every elementwise proof. -/
private theorem onSourceCover_left_comp_algebraMap_comp
    {E Ω W : Type*} [Field E] [Field Ω] [Algebra E Ω] [Semiring W]
    (P Q : FiniteCorrespondencePair E Ω) (h : P.target = Q.source)
    (N : AlgebraicClosureTransport.FiniteNormalCover (↥P.sourceField))
    (g : W →+* E) :
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
        P Q h N).toRingHom.comp
          ((algebraMap E (↥N.field)).comp g) =
      (algebraMap E
        (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
          P Q h N).field)).comp g := by
  apply RingHom.ext
  intro x
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
      P Q h N (g x)

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The relocated `e` parameter field lies in the common eight-input
coefficient field. -/
theorem seRelocatedParameterField_le_commonCoefficientField :
    (R.se.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.seCommonBaseData.coefficientField := by
  unfold FiniteCorrespondenceFamilyMember.parameterField
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.coefficientField
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  change commonCurveEmbedding (k := k) (K := K) (e i) ∈
    Set.range R.commonInputTuple
  fin_cases i
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The intrinsic `e` germ written directly in the common eight-input
coefficient field. -/
noncomputable def seBGermCoefficientToCommonCoefficientRingHom :=
  (IntermediateField.inclusion
    (R.seRelocatedParameterField_le_commonCoefficientField)).toRingHom.comp
      (R.seBGermCoefficientToRelocatedBParameterAlgHom L).toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- The selected source cover is a nested supremum of canonical covers.
/-- The established graph/right-source germ map is the common-coefficient
map followed by the canonical coefficient algebra map. -/
theorem bGermCoefficientToSelectedGraphRightSourceRingHom_eq_commonCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind =
      (algebraMap (↥R.seCommonBaseData.coefficientField)
        (↥(R.selectedGraphRightSourceCover L hind).field)).comp
          (R.seBGermCoefficientToCommonCoefficientRingHom L) := by
  apply RingHom.ext
  intro z
  apply Subtype.ext
  rfl

/-- The intrinsic germ included in the selected common-base `e` branch.
Only the intrinsic coefficient map is needed here; the whole semantic branch
is already preserved by the common-source extension. -/
noncomputable def seBGermCoefficientToSemanticRightBranchRingHom :=
  (algebraMap
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).branchOverSource)).comp
    ((algebraMap (↥R.seCommonBaseData.coefficientField)
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)).comp
      (R.seBGermCoefficientToCommonCoefficientRingHom L))

/-- The same intrinsic germ after inclusion of the selected semantic branch
in the middle cover of the established graph/right triangle. -/
noncomputable def seBGermCoefficientToSelectedGraphRightMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.toRingHom.comp
    (R.seBGermCoefficientToSemanticRightBranchRingHom L)

set_option synthInstance.maxHeartbeats 100000 in
-- The selected branch embedding is linear over its complete source field.
/-- In the old middle cover, the selected-branch route is just the common
coefficient algebra map. -/
theorem seBGermCoefficientToSelectedGraphRightMiddleRingHom_eq_commonCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind =
      (algebraMap (↥R.seCommonBaseData.coefficientField)
        (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
          (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ)
          (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
            (R := R.se) R.seCommonBaseData hψ)
          (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
            (R := R.se) R.seCommonBaseData hψ)
          (R.selectedGraphRightSourceCover L hind)).field)).comp
        (R.seBGermCoefficientToCommonCoefficientRingHom L) := by
  apply RingHom.ext
  intro z
  unfold seBGermCoefficientToSelectedGraphRightMiddleRingHom
    seBGermCoefficientToSemanticRightBranchRingHom
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  let c := R.seBGermCoefficientToCommonCoefficientRingHom L z
  have hcomm :=
    (R.seSelectedRightBranchInSelectedGraphRightMiddle L hind).toAlgHom.commutes
      (algebraMap (↥R.seCommonBaseData.coefficientField)
        (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
          (R := R.se) R.seCommonBaseData hψ).sourceField) c)
  apply Subtype.ext
  exact congrArg Subtype.val hcomm

/-- The intrinsic selected-`B` germ carried through the complete `e` branch
into the middle field of the inverse-oriented common-source triangle. -/
noncomputable def seBGermCoefficientToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.rightSemilinearCommonSourceField L hind)).comp
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
/-- Before the common-source extension, the finite `e` left arrow carries
the intrinsic source germ to its embedding through the selected branch. -/
theorem seSelectedGraphRight_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seSelectedGraphRightCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind := by
  let P :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  let h :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ
  let N := R.selectedGraphRightSourceCover L hind
  change
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
      P Q h N).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind
  calc
    _ = (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp
        ((algebraMap (↥R.seCommonBaseData.coefficientField)
          (↥N.field)).comp
            (R.seBGermCoefficientToCommonCoefficientRingHom L)) :=
      congrArg
        ((FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_eq_commonCoefficient
          L hind)
    _ = (algebraMap (↥R.seCommonBaseData.coefficientField)
          (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
            P Q h N).field)).comp
        (R.seBGermCoefficientToCommonCoefficientRingHom L) :=
      onSourceCover_left_comp_algebraMap_comp P Q h N
        (R.seBGermCoefficientToCommonCoefficientRingHom L)
    _ = R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind :=
      (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom_eq_commonCoefficient
        L hind).symm

set_option synthInstance.maxHeartbeats 100000 in
/-- The common-source `e` left arrow carries the intrinsic source germ to
the germ embedded through the preserved complete right branch. -/
theorem seSemilinearCommon_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSeRightSemilinearExtendedSourceRingHom L hind) =
      R.seBGermCoefficientToSemilinearCommonMiddleRingHom L hind := by
  let T := R.seSelectedGraphRightCompositionTriangle L hind
  let X := R.rightSemilinearCommonSourceField L hind
  have h := T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)
    (R.seSelectedGraphRight_left_comp_bGermCoefficient L hind)
  exact h

/-- The intrinsic germ in the target field of the common-source `e`
triangle, obtained through the preserved complete right branch. -/
noncomputable def seBGermCoefficientToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.rightSemilinearCommonSourceField L hind)).comp
    ((R.seSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind))

/-- The extended semantic `e` arrow has the named intrinsic middle and
target maps as an exact restriction square. -/
theorem seSemilinearCommon_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.seBGermCoefficientToSemilinearCommonMiddleRingHom L hind) =
      R.seBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.seSelectedGraphRightCompositionTriangle L hind
  let X := R.rightSemilinearCommonSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)

/-- The strict direct `u` arrow on the common-source `e` face carries the
intrinsic source germ to the same target map. -/
theorem seSemilinearCommon_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSeRightSemilinearExtendedSourceRingHom L hind) =
      R.seBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.seRightSemilinearCommonCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSeRightSemilinearExtendedSourceRingHom L hind)
    (R.seBGermCoefficientToSemilinearCommonMiddleRingHom L hind)
    (R.seBGermCoefficientToSemilinearCommonTargetRingHom L hind)
    (R.seSemilinearCommon_left_comp_bGermCoefficient L hind)
    (R.seSemilinearCommon_right_comp_bGermCoefficient L hind)


end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
