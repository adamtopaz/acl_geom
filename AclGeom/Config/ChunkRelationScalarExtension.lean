/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkFourArrowReference
import AclGeom.Config.ChunkRelationCover

/-!
# Scalar extension of the four complete chunk edges

The four complete nine-coordinate chunk edges are initially finite over
four different six-coordinate ambient fields.  This file extends each
selected edge to the common sixteen-coordinate coefficient field of the
four-arrow diagram.  The resulting four finite fields remain literal
subfields of the twenty-eight-coordinate joint field and hence of the final
reference normal cover.

This is the coefficient-field bridge needed before the corrected edge
normal-cover transports can be compared with the common formal-source curve
charts.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiChunkFourArrowEdgeLifts

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- One complete edge together with its literal inclusions in the common
sixteen-coordinate coefficient field and the common twenty-eight-coordinate
selected field. -/
structure TotalBaseChangedEdge where
  /-- The complete nine-coordinate edge. -/
  realization : w.PsiChunkRelationRealization
  /-- Its six ambient coordinates lie in the common coefficient field. -/
  ambient_le_totalField : realization.ambientField ≤ D.totalField
  /-- Its nine selected coordinates lie in the common selected field. -/
  joint_le_jointField : realization.jointField ≤ L.jointField

namespace TotalBaseChangedEdge

variable {L : w.PsiChunkFourArrowEdgeLifts hψ D}
  (E : L.TotalBaseChangedEdge)

/-- The scalar extension of the complete edge from its six-coordinate
ambient field to the common sixteen-coordinate coefficient field. -/
def field : IntermediateField k K := by
  letI := E.realization.jointExtension_finiteDimensional hψ
  exact FiniteExtensionCompositum.field E.realization.ambientField
    D.totalField E.realization.jointExtension

/-- The common coefficient field lies in the scalar-extended edge. -/
theorem totalField_le_field : D.totalField ≤ E.field := by
  letI := E.realization.jointExtension_finiteDimensional hψ
  exact FiniteExtensionCompositum.le_field E.realization.ambientField
    D.totalField E.realization.jointExtension

/-- The literal inclusion of the common coefficient field in this
scalar-extended edge. -/
def totalFieldToField : (↥D.totalField) →ₐ[k] (↥E.field) :=
  IntermediateField.inclusion E.totalField_le_field

/-- The literal selected nine-coordinate edge lies in its scalar extension. -/
theorem jointField_le_field : E.realization.jointField ≤ E.field := by
  letI := E.realization.jointExtension_finiteDimensional hψ
  have h := FiniteExtensionCompositum.normal_le_field
    E.realization.ambientField D.totalField E.realization.jointExtension
    E.ambient_le_totalField
  change E.realization.jointField ≤
    FiniteExtensionCompositum.field E.realization.ambientField
      D.totalField E.realization.jointExtension
  simpa [QWitness.PsiChunkRelationRealization.jointExtension] using h

/-- One literal selected coordinate of the complete edge, viewed in the
scalar-extended field. -/
def selectedCoordinate (i : Fin 9) : E.field :=
  ⟨E.realization.jointTuple i,
    E.jointField_le_field (subset_adjoin k _ (Set.mem_range_self i))⟩

@[simp] theorem selectedCoordinate_val (i : Fin 9) :
    (E.selectedCoordinate i : K) = E.realization.jointTuple i :=
  rfl

/-- The right rank-two parameter and its selected scalar coordinate form a
literal subfield of the scalar-extended complete edge. -/
theorem rightScalarField_le_field :
    rankTwoScalarField (k := k) E.realization.b E.realization.t ≤ E.field := by
  apply le_trans ?_ E.jointField_le_field
  unfold rankTwoScalarField
    QWitness.PsiChunkRelationRealization.jointField
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  show rankTwoScalarTuple E.realization.b E.realization.t i ∈
    Set.range E.realization.jointTuple
  fin_cases i
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨7, rfl⟩

/-- Literal inclusion of the selected right scalar branch extension in the
scalar-extended complete edge. -/
def rightScalarExtensionToField :
    (rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) →ₐ[k] E.field :=
  IntermediateField.inclusion E.rightScalarField_le_field

@[simp] theorem rightScalarExtensionToField_val
    (z : rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) :
    (E.rightScalarExtensionToField z : K) = z :=
  rfl

/-- The scalar-extended edge is still contained in the literal common
twenty-eight-coordinate selected field. -/
theorem field_le_jointField : E.field ≤ L.jointField := by
  letI := E.realization.jointExtension_finiteDimensional hψ
  apply FiniteExtensionCompositum.field_le_of_le
    E.realization.ambientField D.totalField E.realization.jointExtension
    L.ambientTotalField_le_jointField
  simpa [QWitness.PsiChunkRelationRealization.jointExtension] using
    E.joint_le_jointField

/-- The scalar-extended edge displayed as a finite extension of the common
sixteen-coordinate coefficient field. -/
def overTotal : IntermediateField (↥D.totalField) K :=
  extendScalars E.totalField_le_field

/-- Scalar extension preserves finiteness of the complete edge. -/
theorem overTotal_finiteDimensional :
    FiniteDimensional (↥D.totalField) (↥E.overTotal) := by
  letI := E.realization.jointExtension_finiteDimensional hψ
  exact FiniteExtensionCompositum.over_finiteDimensional
    E.realization.ambientField D.totalField E.realization.jointExtension
    E.ambient_le_totalField

end TotalBaseChangedEdge

private theorem ambientField_le_totalField_of_index
    (R : w.PsiChunkRelationRealization) (j : Fin 6 → Fin 16)
    (hj : D.totalTuple ∘ j = R.ambientTuple) :
    R.ambientField ≤ D.totalField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  show R.ambientTuple i ∈ Set.range D.totalTuple
  exact ⟨j i, congrFun hj i⟩

private theorem jointField_le_jointField_of_index
    (R : w.PsiChunkRelationRealization) (j : Fin 9 → Fin 28)
    (hj : L.jointTuple ∘ j = R.jointTuple) :
    R.jointField ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  show R.jointTuple i ∈ Set.range L.jointTuple
  exact ⟨j i, congrFun hj i⟩

/-- The complete `s·e=u` edge after scalar extension to the common
sixteen-coordinate coefficient field. -/
def seTotalBaseChangedEdge : L.TotalBaseChangedEdge where
  realization := L.seRealization
  ambient_le_totalField := ambientField_le_totalField_of_index
    L.seRealization
    RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.seIndex
    (by
      funext i
      fin_cases i <;> rfl)
  joint_le_jointField := jointField_le_jointField_of_index
    L L.seRealization seIndex
    (by
      funext i
      fin_cases i <;> rfl)

/-- The complete `sA·a=u` edge after scalar extension to the common
sixteen-coordinate coefficient field. -/
def sA_aTotalBaseChangedEdge : L.TotalBaseChangedEdge where
  realization := L.sA_aRealization
  ambient_le_totalField := ambientField_le_totalField_of_index
    L.sA_aRealization
    RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.sAaIndex
    (by
      funext i
      fin_cases i <;> rfl)
  joint_le_jointField := jointField_le_jointField_of_index
    L L.sA_aRealization sAaIndex
    (by
      funext i
      fin_cases i <;> rfl)

/-- The complete `s·b=uB` edge after scalar extension to the common
sixteen-coordinate coefficient field. -/
def s_bTotalBaseChangedEdge : L.TotalBaseChangedEdge where
  realization := L.s_bRealization
  ambient_le_totalField := ambientField_le_totalField_of_index
    L.s_bRealization
    RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.sbIndex
    (by
      funext i
      fin_cases i <;> rfl)
  joint_le_jointField := jointField_le_jointField_of_index
    L L.s_bRealization sbIndex
    (by
      funext i
      fin_cases i <;> rfl)

/-- The complete `sA·c=uB` edge after scalar extension to the common
sixteen-coordinate coefficient field. -/
def sA_cTotalBaseChangedEdge : L.TotalBaseChangedEdge where
  realization := L.sA_cRealization
  ambient_le_totalField := ambientField_le_totalField_of_index
    L.sA_cRealization
    RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.sAcIndex
    (by
      funext i
      fin_cases i <;> rfl)
  joint_le_jointField := jointField_le_jointField_of_index
    L L.sA_cRealization sAcIndex
    (by
      funext i
      fin_cases i <;> rfl)

/-- Literal inclusion of the first edge's right `B/T` branch in its
scalar-extended complete edge. -/
def seRightScalarExtensionToField :
    (rankTwoScalarExtension (k := k) e L.se_e) →ₐ[k]
      L.seTotalBaseChangedEdge.field :=
  L.seTotalBaseChangedEdge.rightScalarExtensionToField

/-- Literal inclusion of the inverse-input edge's right `B/T` branch. -/
def sA_aRightScalarExtensionToField :
    (rankTwoScalarExtension (k := k) a L.sA_a_a) →ₐ[k]
      L.sA_aTotalBaseChangedEdge.field :=
  L.sA_aTotalBaseChangedEdge.rightScalarExtensionToField

/-- Literal inclusion of the second-input edge's right `B/T` branch. -/
def s_bRightScalarExtensionToField :
    (rankTwoScalarExtension (k := k) b L.s_b_b) →ₐ[k]
      L.s_bTotalBaseChangedEdge.field :=
  L.s_bTotalBaseChangedEdge.rightScalarExtensionToField

/-- Literal inclusion of the output edge's right `B/T` branch. -/
def sA_cRightScalarExtensionToField :
    (rankTwoScalarExtension (k := k) D.c L.sA_c_c) →ₐ[k]
      L.sA_cTotalBaseChangedEdge.field :=
  L.sA_cTotalBaseChangedEdge.rightScalarExtensionToField

@[simp] theorem seRightScalarExtensionToField_val
    (z : rankTwoScalarExtension (k := k) e L.se_e) :
    (L.seRightScalarExtensionToField z : K) = z :=
  rfl

@[simp] theorem sA_aRightScalarExtensionToField_val
    (z : rankTwoScalarExtension (k := k) a L.sA_a_a) :
    (L.sA_aRightScalarExtensionToField z : K) = z :=
  rfl

@[simp] theorem s_bRightScalarExtensionToField_val
    (z : rankTwoScalarExtension (k := k) b L.s_b_b) :
    (L.s_bRightScalarExtensionToField z : K) = z :=
  rfl

@[simp] theorem sA_cRightScalarExtensionToField_val
    (z : rankTwoScalarExtension (k := k) D.c L.sA_c_c) :
    (L.sA_cRightScalarExtensionToField z : K) = z :=
  rfl

/-- The literal joint field, and therefore every scalar-extended selected
edge, lies in the final reference normal cover. -/
theorem jointField_le_referenceNormalCover :
    L.jointField ≤ L.referenceNormalCover.restrictScalars k := by
  intro z hz
  change z ∈ L.referenceNormalCover
  apply L.normalizedOverInput_le_referenceNormalCover
  change z ∈ L.normalizedField
  exact (L.jointField_le_eNormalizedField.trans <|
    L.eNormalizedField_le_aNormalizedField.trans <|
      L.aNormalizedField_le_bNormalizedField.trans
        L.bNormalizedField_le_normalizedField) hz

/-- Any of the four scalar-extended complete edges embeds literally in the
final reference normal cover. -/
theorem TotalBaseChangedEdge.field_le_referenceNormalCover
    (E : L.TotalBaseChangedEdge) :
    E.field ≤ L.referenceNormalCover.restrictScalars k :=
  E.field_le_jointField.trans L.jointField_le_referenceNormalCover

/-- The inclusion of a scalar-extended complete edge in the final reference
normal cover. -/
def TotalBaseChangedEdge.toReferenceNormalCover
    (E : L.TotalBaseChangedEdge) :
    (↥E.field) →ₐ[k] (↥L.referenceNormalCover) :=
  IntermediateField.algHomIntoOfLeRestrictScalars E.field
    L.referenceNormalCover E.field_le_referenceNormalCover

/-- Direct inclusion of a selected right scalar branch in the final
reference normal cover. -/
def TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCover
    (E : L.TotalBaseChangedEdge)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) E.realization.b E.realization.t)).restrictScalars k ≤
          L.normalizedField) :
    (rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) →ₐ[k]
        L.referenceNormalCover :=
  (L.scalarNormalFieldToReferenceNormalCover
      E.realization.b E.realization.t hfield).comp
    ((FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) E.realization.b E.realization.t)).restrictScalars k)

/-- Inclusion of the same right scalar branch through the scalar-extended
complete edge. -/
def TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCoverViaEdge
    (E : L.TotalBaseChangedEdge) :
    (rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) →ₐ[k]
        L.referenceNormalCover :=
  (TotalBaseChangedEdge.toReferenceNormalCover L E).comp
    E.rightScalarExtensionToField

@[simp] theorem TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCover_val
    (E : L.TotalBaseChangedEdge)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) E.realization.b E.realization.t)).restrictScalars k ≤
          L.normalizedField)
    (z : rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) :
    ((TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCover
      L E hfield z : L.referenceNormalCover) : K) = z := by
  rfl

@[simp] theorem TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCoverViaEdge_val
    (E : L.TotalBaseChangedEdge)
    (z : rankTwoScalarExtension
      (k := k) E.realization.b E.realization.t) :
    ((TotalBaseChangedEdge.rightScalarExtensionToReferenceNormalCoverViaEdge
      L E z : L.referenceNormalCover) : K) = z := by
  rfl

/-- Direct inclusion of the first edge's right scalar branch in the final
reference normal cover. -/
def seRightScalarExtensionToReferenceNormalCover :
    (rankTwoScalarExtension (k := k) e L.se_e) →ₐ[k]
      L.referenceNormalCover :=
  (L.scalarNormalFieldToReferenceNormalCover e L.se_e
      L.eNormalField_le_normalizedField).comp
    ((FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) e L.se_e)).restrictScalars k)

/-- Inclusion of the first edge's right scalar branch through its complete
scalar-extended edge. -/
def seRightScalarExtensionToReferenceNormalCoverViaEdge :
    (rankTwoScalarExtension (k := k) e L.se_e) →ₐ[k]
      L.referenceNormalCover :=
  (TotalBaseChangedEdge.toReferenceNormalCover L
      L.seTotalBaseChangedEdge).comp L.seRightScalarExtensionToField

@[simp] theorem seRightScalarExtensionToReferenceNormalCover_val
    (z : rankTwoScalarExtension (k := k) e L.se_e) :
    ((L.seRightScalarExtensionToReferenceNormalCover z :
      L.referenceNormalCover) : K) = z :=
  rfl

@[simp] theorem seRightScalarExtensionToReferenceNormalCoverViaEdge_val
    (z : rankTwoScalarExtension (k := k) e L.se_e) :
    ((L.seRightScalarExtensionToReferenceNormalCoverViaEdge z :
      L.referenceNormalCover) : K) = z :=
  rfl

/-- The first edge's right scalar branch has the same literal inclusion in
the reference normal cover by either route. -/
theorem seRightScalarExtensionToReferenceNormalCover_eq
    (z : rankTwoScalarExtension (k := k) e L.se_e) :
    L.seRightScalarExtensionToReferenceNormalCover z =
      L.seRightScalarExtensionToReferenceNormalCoverViaEdge z := by
  apply Subtype.ext
  rw [L.seRightScalarExtensionToReferenceNormalCover_val,
    L.seRightScalarExtensionToReferenceNormalCoverViaEdge_val]

/-- Direct inclusion of the inverse-input edge's right scalar branch in
the final reference normal cover. -/
def sA_aRightScalarExtensionToReferenceNormalCover :
    (rankTwoScalarExtension (k := k) a L.sA_a_a) →ₐ[k]
      L.referenceNormalCover :=
  (L.scalarNormalFieldToReferenceNormalCover a L.sA_a_a
      L.aNormalField_le_normalizedField).comp
    ((FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) a L.sA_a_a)).restrictScalars k)

/-- Inclusion of the inverse-input edge's right scalar branch through its
complete scalar-extended edge. -/
def sA_aRightScalarExtensionToReferenceNormalCoverViaEdge :
    (rankTwoScalarExtension (k := k) a L.sA_a_a) →ₐ[k]
      L.referenceNormalCover :=
  (TotalBaseChangedEdge.toReferenceNormalCover L
      L.sA_aTotalBaseChangedEdge).comp L.sA_aRightScalarExtensionToField

@[simp] theorem sA_aRightScalarExtensionToReferenceNormalCover_val
    (z : rankTwoScalarExtension (k := k) a L.sA_a_a) :
    ((L.sA_aRightScalarExtensionToReferenceNormalCover z :
      L.referenceNormalCover) : K) = z :=
  rfl

@[simp] theorem sA_aRightScalarExtensionToReferenceNormalCoverViaEdge_val
    (z : rankTwoScalarExtension (k := k) a L.sA_a_a) :
    ((L.sA_aRightScalarExtensionToReferenceNormalCoverViaEdge z :
      L.referenceNormalCover) : K) = z :=
  rfl

/-- The inverse-input edge's right scalar branch has the same literal
inclusion in the reference normal cover by either route. -/
theorem sA_aRightScalarExtensionToReferenceNormalCover_eq
    (z : rankTwoScalarExtension (k := k) a L.sA_a_a) :
    L.sA_aRightScalarExtensionToReferenceNormalCover z =
      L.sA_aRightScalarExtensionToReferenceNormalCoverViaEdge z := by
  apply Subtype.ext
  rw [L.sA_aRightScalarExtensionToReferenceNormalCover_val,
    L.sA_aRightScalarExtensionToReferenceNormalCoverViaEdge_val]

/-- Direct inclusion of the second-input edge's right scalar branch in the
final reference normal cover. -/
def s_bRightScalarExtensionToReferenceNormalCover :
    (rankTwoScalarExtension (k := k) b L.s_b_b) →ₐ[k]
      L.referenceNormalCover :=
  (L.scalarNormalFieldToReferenceNormalCover b L.s_b_b
      L.bNormalField_le_normalizedField).comp
    ((FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) b L.s_b_b)).restrictScalars k)

/-- Inclusion of the second-input edge's right scalar branch through its
complete scalar-extended edge. -/
def s_bRightScalarExtensionToReferenceNormalCoverViaEdge :
    (rankTwoScalarExtension (k := k) b L.s_b_b) →ₐ[k]
      L.referenceNormalCover :=
  (TotalBaseChangedEdge.toReferenceNormalCover L
      L.s_bTotalBaseChangedEdge).comp L.s_bRightScalarExtensionToField

@[simp] theorem s_bRightScalarExtensionToReferenceNormalCover_val
    (z : rankTwoScalarExtension (k := k) b L.s_b_b) :
    ((L.s_bRightScalarExtensionToReferenceNormalCover z :
      L.referenceNormalCover) : K) = z :=
  rfl

@[simp] theorem s_bRightScalarExtensionToReferenceNormalCoverViaEdge_val
    (z : rankTwoScalarExtension (k := k) b L.s_b_b) :
    ((L.s_bRightScalarExtensionToReferenceNormalCoverViaEdge z :
      L.referenceNormalCover) : K) = z :=
  rfl

/-- The second-input edge's right scalar branch has the same literal
inclusion in the reference normal cover by either route. -/
theorem s_bRightScalarExtensionToReferenceNormalCover_eq
    (z : rankTwoScalarExtension (k := k) b L.s_b_b) :
    L.s_bRightScalarExtensionToReferenceNormalCover z =
      L.s_bRightScalarExtensionToReferenceNormalCoverViaEdge z := by
  apply Subtype.ext
  rw [L.s_bRightScalarExtensionToReferenceNormalCover_val,
    L.s_bRightScalarExtensionToReferenceNormalCoverViaEdge_val]

/-- Direct inclusion of the output edge's right scalar branch in the final
reference normal cover. -/
def sA_cRightScalarExtensionToReferenceNormalCover :
    (rankTwoScalarExtension (k := k) D.c L.sA_c_c) →ₐ[k]
      L.referenceNormalCover :=
  (L.scalarNormalFieldToReferenceNormalCover D.c L.sA_c_c
      L.cNormalField_le_normalizedField).comp
    ((FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) D.c L.sA_c_c)).restrictScalars k)

/-- Inclusion of the output edge's right scalar branch through its complete
scalar-extended edge. -/
def sA_cRightScalarExtensionToReferenceNormalCoverViaEdge :
    (rankTwoScalarExtension (k := k) D.c L.sA_c_c) →ₐ[k]
      L.referenceNormalCover :=
  (TotalBaseChangedEdge.toReferenceNormalCover L
      L.sA_cTotalBaseChangedEdge).comp L.sA_cRightScalarExtensionToField

@[simp] theorem sA_cRightScalarExtensionToReferenceNormalCover_val
    (z : rankTwoScalarExtension (k := k) D.c L.sA_c_c) :
    ((L.sA_cRightScalarExtensionToReferenceNormalCover z :
      L.referenceNormalCover) : K) = z :=
  rfl

@[simp] theorem sA_cRightScalarExtensionToReferenceNormalCoverViaEdge_val
    (z : rankTwoScalarExtension (k := k) D.c L.sA_c_c) :
    ((L.sA_cRightScalarExtensionToReferenceNormalCoverViaEdge z :
      L.referenceNormalCover) : K) = z :=
  rfl

/-- The output edge's right scalar branch has the same literal inclusion in
the reference normal cover by either route. -/
theorem sA_cRightScalarExtensionToReferenceNormalCover_eq
    (z : rankTwoScalarExtension (k := k) D.c L.sA_c_c) :
    L.sA_cRightScalarExtensionToReferenceNormalCover z =
      L.sA_cRightScalarExtensionToReferenceNormalCoverViaEdge z := by
  apply Subtype.ext
  rw [L.sA_cRightScalarExtensionToReferenceNormalCover_val,
    L.sA_cRightScalarExtensionToReferenceNormalCoverViaEdge_val]

/-- The common sixteen-coordinate coefficient field embeds directly in the
final reference normal cover. -/
def totalFieldToReferenceNormalCover :
    (↥D.totalField) →ₐ[k] (↥L.referenceNormalCover) :=
  IntermediateField.algHomIntoOfLeRestrictScalars D.totalField
    L.referenceNormalCover
    (L.ambientTotalField_le_jointField.trans
      L.jointField_le_referenceNormalCover)

/-- The same selected edge coordinate, viewed directly in the final
reference normal cover. -/
def TotalBaseChangedEdge.referenceCoordinate
    (E : L.TotalBaseChangedEdge) (i : Fin 9) : L.referenceNormalCover :=
  ⟨E.realization.jointTuple i,
    L.jointField_le_referenceNormalCover
      (E.joint_le_jointField
        (subset_adjoin k _ (Set.mem_range_self i)))⟩

/-- Inclusion in the reference cover preserves every one of the nine
selected edge coordinates literally. -/
@[simp] theorem TotalBaseChangedEdge.toReferenceNormalCover_selectedCoordinate
    (E : L.TotalBaseChangedEdge) (i : Fin 9) :
    TotalBaseChangedEdge.toReferenceNormalCover L E
        (E.selectedCoordinate i) =
      TotalBaseChangedEdge.referenceCoordinate L E i :=
  rfl

/-- All four scalar-extended complete edge fields, in reference order. -/
def fourTotalBaseChangedEdges :=
  (L.seTotalBaseChangedEdge, L.sA_aTotalBaseChangedEdge,
    L.s_bTotalBaseChangedEdge, L.sA_cTotalBaseChangedEdge)

/-- The selected `B/T` scalar on each complete edge belongs to its
scalar-extended field and maps to the same literal scalar in the reference
normal cover. -/
theorem fourTotalBaseChangedEdges_selectedBScalar :
    TotalBaseChangedEdge.toReferenceNormalCover L L.seTotalBaseChangedEdge
        (L.seTotalBaseChangedEdge.selectedCoordinate 7) =
      TotalBaseChangedEdge.referenceCoordinate L
        L.seTotalBaseChangedEdge 7 ∧
    TotalBaseChangedEdge.toReferenceNormalCover L L.sA_aTotalBaseChangedEdge
        (L.sA_aTotalBaseChangedEdge.selectedCoordinate 7) =
      TotalBaseChangedEdge.referenceCoordinate L
        L.sA_aTotalBaseChangedEdge 7 ∧
    TotalBaseChangedEdge.toReferenceNormalCover L L.s_bTotalBaseChangedEdge
        (L.s_bTotalBaseChangedEdge.selectedCoordinate 7) =
      TotalBaseChangedEdge.referenceCoordinate L
        L.s_bTotalBaseChangedEdge 7 ∧
    TotalBaseChangedEdge.toReferenceNormalCover L L.sA_cTotalBaseChangedEdge
        (L.sA_cTotalBaseChangedEdge.selectedCoordinate 7) =
      TotalBaseChangedEdge.referenceCoordinate L
        L.sA_cTotalBaseChangedEdge 7 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end QWitness.PsiChunkFourArrowEdgeLifts

end
end AclGeom
