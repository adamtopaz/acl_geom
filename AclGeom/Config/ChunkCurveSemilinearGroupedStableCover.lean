/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedSourceFiniteness

/-!
# A stable finite cover above the grouped joint source

The four-face joint cover is normal over the enlarged joint source, whereas
the repeated-arrow deck transformations fix the original semantic source.
Normality over the larger field does not by itself let those transformations
extend.  We therefore take the normal closure of the entire joint cover over
the semantic source.  It is still finite, contains the joint cover literally,
and is normal over precisely the field fixed by the established alignments.
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

private abbrev groupedStableSemanticSourceType :=
  ↥R.semanticCommonSourceField

private abbrev groupedStableJointSourceType :=
  ↥R.rightSourceJointField

private abbrev groupedStableJointCoverType
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ↥(R.fourSelectedGraphJointCover L hind).field

/-- The selected semantic-source embedding into the four-face joint cover,
factored through the literal joint base. -/
private noncomputable def groupedStableSemanticSourceToJointCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    groupedStableSemanticSourceType R →+*
      groupedStableJointCoverType R L hind :=
  (algebraMap (groupedStableJointSourceType R)
      (groupedStableJointCoverType R L hind)).comp
    R.rightEToJointBaseRingHom

/-- The selected `e`-leg composite supplies the semantic algebra structure on
the grouped joint cover. -/
noncomputable instance groupedStableJointCoverAlgebra
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Algebra (groupedStableSemanticSourceType R)
      (groupedStableJointCoverType R L hind) := by
  letI : Algebra (groupedStableSemanticSourceType R)
      (groupedStableJointSourceType R) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- The three-level joint cover hides its finite algebra tower.
set_option maxHeartbeats 800000 in
-- Installing the selected composite algebra map requires reducing that tower.
/-- The complete four-face joint cover is finite over the original semantic
source along the selected `e`-leg embedding. -/
theorem fourSelectedGraphJointCover_finite_over_semantic
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (groupedStableSemanticSourceType R)
      (groupedStableJointCoverType R L hind) := by
    letI : Algebra (groupedStableSemanticSourceType R)
        (groupedStableJointSourceType R) :=
      R.semanticSourceToRightSourceJoint.toAlgebra
    letI : IsScalarTower (groupedStableSemanticSourceType R)
        (groupedStableJointSourceType R)
        (groupedStableJointCoverType R L hind) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : FiniteDimensional (groupedStableSemanticSourceType R)
        (groupedStableJointSourceType R) := by
      change FiniteDimensional (↥R.semanticCommonSourceField)
        (↥R.rightSourceJointOverSemantic)
      exact R.rightSourceJointOverSemantic_finiteDimensional
    letI : FiniteDimensional (groupedStableJointSourceType R)
        (groupedStableJointCoverType R L hind) :=
      (R.fourSelectedGraphJointCover L hind).finiteDimensional
    exact FiniteDimensional.trans
      (groupedStableSemanticSourceType R)
      (groupedStableJointSourceType R)
      (groupedStableJointCoverType R L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The selected semantic algebra map is the composite through the joint base.
set_option maxHeartbeats 800000 in
-- Normal-closure elaboration needs the explicit finite tower above.
/-- The normal closure of the whole joint cover over the original semantic
source, formed inside the algebraic closure of the joint cover. -/
noncomputable def groupedStableNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) := by
  exact normalClosure (groupedStableSemanticSourceType R)
    (groupedStableJointCoverType R L hind)
    (AlgebraicClosure (groupedStableJointCoverType R L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The normal closure and selected composite algebra map form a deep tower.
set_option maxHeartbeats 800000 in
-- The field-range inclusion unfolds the normal-closure presentation.
/-- Every element of the grouped joint cover lies in its semantic normal
closure. -/
theorem fourSelectedGraphJointCover_algebraMap_mem_groupedStableNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : groupedStableJointCoverType R L hind) :
    algebraMap (groupedStableJointCoverType R L hind)
        (AlgebraicClosure (groupedStableJointCoverType R L hind)) x ∈
      R.groupedStableNormalField L hind := by
  let φ : groupedStableJointCoverType R L hind →ₐ[
      groupedStableSemanticSourceType R]
      AlgebraicClosure (groupedStableJointCoverType R L hind) :=
    { algebraMap _ _ with
      commutes' := fun _ ↦ rfl }
  apply AlgHom.fieldRange_le_normalClosure φ
  exact ⟨x, rfl⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Re-presenting the semantic normal closure over the joint cover is instance-heavy.
set_option maxHeartbeats 800000 in
-- Its carrier is intentionally shared with `groupedStableNormalField`.
/-- The stable field re-presented as an intermediate extension of the grouped
joint cover.  This is the form consumed by finite pullback charts. -/
noncomputable def groupedStableSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (groupedStableJointCoverType R L hind)
      (AlgebraicClosure (groupedStableJointCoverType R L hind)) where
  __ := (R.groupedStableNormalField L hind).toSubfield
  algebraMap_mem' :=
    R.fourSelectedGraphJointCover_algebraMap_mem_groupedStableNormalField
      L hind

/-- The semantic algebra structure inherited by the stable field through the
literal joint-cover inclusion. -/
noncomputable instance groupedStableSourceFieldAlgebra
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Algebra (groupedStableSemanticSourceType R)
      (↥(R.groupedStableSourceField L hind)) := by
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- The ambient closure is algebraic through the selected finite joint cover.
set_option maxHeartbeats 800000 in
-- Normality is proved over the smaller semantic source, not the joint base.
/-- The ambient algebraic closure of the joint cover is normal over the
original semantic source. -/
theorem groupedJointCoverAlgebraicClosure_normal_over_semantic
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal (groupedStableSemanticSourceType R)
      (AlgebraicClosure (groupedStableJointCoverType R L hind)) := by
  let S := groupedStableSemanticSourceType R
  let P := groupedStableJointCoverType R L hind
  let Ω := AlgebraicClosure P
  letI : FiniteDimensional S P :=
    R.fourSelectedGraphJointCover_finite_over_semantic L hind
  letI : Algebra.IsAlgebraic S P := Algebra.IsAlgebraic.of_finite S P
  letI : Algebra.IsAlgebraic S Ω :=
    Algebra.IsAlgebraic.trans S P Ω
  rw [normal_iff]
  intro x
  exact ⟨(Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    IsAlgClosed.splits _⟩

set_option synthInstance.maxHeartbeats 100000 in
-- The stable field has two compatible intermediate-field presentations.
set_option maxHeartbeats 800000 in
-- Normal-closure normality uses the selected semantic algebra map.
/-- The stable grouped source is normal over the original semantic source. -/
theorem groupedStableSourceField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal (groupedStableSemanticSourceType R)
      (↥(R.groupedStableSourceField L hind)) := by
  change Normal (groupedStableSemanticSourceType R)
    (↥(R.groupedStableNormalField L hind))
  letI : FiniteDimensional (groupedStableSemanticSourceType R)
      (groupedStableJointCoverType R L hind) :=
    R.fourSelectedGraphJointCover_finite_over_semantic L hind
  letI : Normal (groupedStableSemanticSourceType R)
      (AlgebraicClosure (groupedStableJointCoverType R L hind)) :=
    R.groupedJointCoverAlgebraicClosure_normal_over_semantic L hind
  exact normalClosure.normal _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The stable field has two compatible intermediate-field presentations.
set_option maxHeartbeats 800000 in
-- Normal-closure finiteness uses the selected semantic algebra map.
/-- The stable grouped source remains finite over the semantic source. -/
theorem groupedStableSourceField_finite_over_semantic
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (groupedStableSemanticSourceType R)
      (↥(R.groupedStableSourceField L hind)) := by
  change FiniteDimensional (groupedStableSemanticSourceType R)
    (↥(R.groupedStableNormalField L hind))
  letI : FiniteDimensional (groupedStableSemanticSourceType R)
      (groupedStableJointCoverType R L hind) :=
    R.fourSelectedGraphJointCover_finite_over_semantic L hind
  exact normalClosure.is_finiteDimensional _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The right-dimension argument crosses both presentations of the stable field.
set_option maxHeartbeats 800000 in
-- The scalar tower is installed explicitly to retain the selected source map.
/-- The stable grouped source is finite over the original grouped joint cover,
so all four closure comparisons admit finite pullbacks to it. -/
theorem groupedStableSourceField_finite_over_jointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (groupedStableJointCoverType R L hind)
      (↥(R.groupedStableSourceField L hind)) := by
  let S := groupedStableSemanticSourceType R
  let P := groupedStableJointCoverType R L hind
  let Q := ↥(R.groupedStableSourceField L hind)
  letI : FiniteDimensional S Q :=
    R.groupedStableSourceField_finite_over_semantic L hind
  letI : IsScalarTower S P Q :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact FiniteDimensional.right S P Q

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
