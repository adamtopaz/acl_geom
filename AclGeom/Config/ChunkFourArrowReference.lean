/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkFourArrowNormalization
import AclGeom.Correspondence.FiniteExtensionCompositum

/-!
# A common normalized `B/T` cover for the four-arrow component

The lifted four-arrow component contains four selected `B/T` scalar branch
fields.  Its first common normal cover contains the selected scalar values,
but need not contain all conjugates over the four smaller rank-two parameter
fields.  Here the four individual scalar normal fields are adjoined one at a
time by finite bases.  The resulting field is still finite over the original
eight-coordinate input field and literally contains all four normal fields.

Taking one final normal closure over the eight inputs produces an affine
source chart with dominant rational projections to all four normalized
`B/T` charts.  Composing with the existing reference-normalized transitions
puts `e`, inverse-`a`, `b`, and output-`c` on the single selected `(B,T)`
model.  This is the precise source needed for the remaining categorical
cancellation factorization.
-/

namespace AclGeom

open IntermediateField
open AlgebraicGeometry

noncomputable section

universe u

namespace QWitness.PsiChunkFourArrowEdgeLifts

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The `B/T` graph relation on the first based input. -/
theorem eProjectionRelation : w.psiBProjectionRelation e L.se_e :=
  PsiChunkProjectionRelation.bProjection w L.se_lift

/-- The `B/T` graph relation on the inverse input. -/
theorem aProjectionRelation : w.psiBProjectionRelation a L.sA_a_a :=
  PsiChunkProjectionRelation.bProjection w L.sA_a_lift

/-- The `B/T` graph relation on the second based input. -/
theorem bProjectionRelation : w.psiBProjectionRelation b L.s_b_b :=
  PsiChunkProjectionRelation.bProjection w L.s_b_lift

/-- The `B/T` graph relation on the selected output. -/
theorem cProjectionRelation : w.psiBProjectionRelation D.c L.sA_c_c :=
  PsiChunkProjectionRelation.bProjection w L.sA_c_lift

/-- Algebraicity of the first based scalar branch. -/
theorem eScalar_mem_racl : L.se_e ∈ racl k (Set.range e) :=
  PsiBProjectionRelation.scalar_mem_racl w hψ L.eProjectionRelation

/-- Algebraicity of the inverse-input scalar branch. -/
theorem aScalar_mem_racl : L.sA_a_a ∈ racl k (Set.range a) :=
  PsiBProjectionRelation.scalar_mem_racl w hψ L.aProjectionRelation

/-- Algebraicity of the second based scalar branch. -/
theorem bScalar_mem_racl : L.s_b_b ∈ racl k (Set.range b) :=
  PsiBProjectionRelation.scalar_mem_racl w hψ L.bProjectionRelation

/-- Algebraicity of the output scalar branch. -/
theorem cScalar_mem_racl : L.sA_c_c ∈ racl k (Set.range D.c) :=
  PsiBProjectionRelation.scalar_mem_racl w hψ L.cProjectionRelation

/-- The individual normal field of the first based scalar branch. -/
abbrev eNormalField : IntermediateField
    (↥(rankTwoParameterField (k := k) e)) K :=
  FiniteCover.normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField (k := k) e L.se_e)

/-- The individual normal field of the inverse-input scalar branch. -/
abbrev aNormalField : IntermediateField
    (↥(rankTwoParameterField (k := k) a)) K :=
  FiniteCover.normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField (k := k) a L.sA_a_a)

/-- The individual normal field of the second based scalar branch. -/
abbrev bNormalField : IntermediateField
    (↥(rankTwoParameterField (k := k) b)) K :=
  FiniteCover.normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField (k := k) b L.s_b_b)

/-- The individual normal field of the output scalar branch. -/
abbrev cNormalField : IntermediateField
    (↥(rankTwoParameterField (k := k) D.c)) K :=
  FiniteCover.normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField (k := k) D.c L.sA_c_c)

/-- The first based scalar normal field is finite over its rank-two block. -/
theorem eNormalField_finiteDimensional :
    FiniteDimensional (↥(rankTwoParameterField (k := k) e))
      (↥L.eNormalField) :=
  rankTwoScalarNormalField_finiteDimensional (k := k) L.eScalar_mem_racl

/-- The inverse-input scalar normal field is finite over its rank-two block. -/
theorem aNormalField_finiteDimensional :
    FiniteDimensional (↥(rankTwoParameterField (k := k) a))
      (↥L.aNormalField) :=
  rankTwoScalarNormalField_finiteDimensional (k := k) L.aScalar_mem_racl

/-- The second based scalar normal field is finite over its rank-two block. -/
theorem bNormalField_finiteDimensional :
    FiniteDimensional (↥(rankTwoParameterField (k := k) b))
      (↥L.bNormalField) :=
  rankTwoScalarNormalField_finiteDimensional (k := k) L.bScalar_mem_racl

/-- The output scalar normal field is finite over its rank-two block. -/
theorem cNormalField_finiteDimensional :
    FiniteDimensional (↥(rankTwoParameterField (k := k) D.c))
      (↥L.cNormalField) :=
  rankTwoScalarNormalField_finiteDimensional (k := k) L.cScalar_mem_racl

/-- The first based rank-two parameter field lies in the joint component. -/
theorem eParameterField_le_jointField :
    rankTwoParameterField (k := k) e ≤ L.jointField :=
  (rankTwoParameterField_le_rankTwoScalarField (k := k) e L.se_e).trans
    L.eScalarField_le_jointField

/-- The inverse-input rank-two parameter field lies in the joint component. -/
theorem aParameterField_le_jointField :
    rankTwoParameterField (k := k) a ≤ L.jointField :=
  (rankTwoParameterField_le_rankTwoScalarField (k := k) a L.sA_a_a).trans
    L.aScalarField_le_jointField

/-- The second based rank-two parameter field lies in the joint component. -/
theorem bParameterField_le_jointField :
    rankTwoParameterField (k := k) b ≤ L.jointField :=
  (rankTwoParameterField_le_rankTwoScalarField (k := k) b L.s_b_b).trans
    L.bScalarField_le_jointField

/-- The output rank-two parameter field lies in the joint component. -/
theorem cParameterField_le_jointField :
    rankTwoParameterField (k := k) D.c ≤ L.jointField :=
  (rankTwoParameterField_le_rankTwoScalarField (k := k) D.c L.sA_c_c).trans
    L.cScalarField_le_jointField

/-- First enlarge the joint component by a finite basis of the `e` scalar
normal field. -/
def eNormalizedField : IntermediateField k K := by
  letI := L.eNormalField_finiteDimensional
  exact FiniteExtensionCompositum.field
    (rankTwoParameterField (k := k) e) L.jointField L.eNormalField

/-- Next adjoin a finite basis of the inverse-`a` scalar normal field. -/
def aNormalizedField : IntermediateField k K := by
  letI := L.aNormalField_finiteDimensional
  exact FiniteExtensionCompositum.field
    (rankTwoParameterField (k := k) a) L.eNormalizedField L.aNormalField

/-- Next adjoin a finite basis of the `b` scalar normal field. -/
def bNormalizedField : IntermediateField k K := by
  letI := L.bNormalField_finiteDimensional
  exact FiniteExtensionCompositum.field
    (rankTwoParameterField (k := k) b) L.aNormalizedField L.bNormalField

/-- Finally adjoin a finite basis of the output-`c` scalar normal field. -/
def normalizedField : IntermediateField k K := by
  letI := L.cNormalField_finiteDimensional
  exact FiniteExtensionCompositum.field
    (rankTwoParameterField (k := k) D.c) L.bNormalizedField L.cNormalField

/-- The original joint field lies in the first enlargement. -/
theorem jointField_le_eNormalizedField : L.jointField ≤ L.eNormalizedField := by
  letI := L.eNormalField_finiteDimensional
  exact FiniteExtensionCompositum.le_field
    (rankTwoParameterField (k := k) e) L.jointField L.eNormalField

/-- The first enlargement lies in the second. -/
theorem eNormalizedField_le_aNormalizedField :
    L.eNormalizedField ≤ L.aNormalizedField := by
  letI := L.aNormalField_finiteDimensional
  exact FiniteExtensionCompositum.le_field
    (rankTwoParameterField (k := k) a) L.eNormalizedField L.aNormalField

/-- The second enlargement lies in the third. -/
theorem aNormalizedField_le_bNormalizedField :
    L.aNormalizedField ≤ L.bNormalizedField := by
  letI := L.bNormalField_finiteDimensional
  exact FiniteExtensionCompositum.le_field
    (rankTwoParameterField (k := k) b) L.aNormalizedField L.bNormalField

/-- The third enlargement lies in the final normalized field. -/
theorem bNormalizedField_le_normalizedField :
    L.bNormalizedField ≤ L.normalizedField := by
  letI := L.cNormalField_finiteDimensional
  exact FiniteExtensionCompositum.le_field
    (rankTwoParameterField (k := k) D.c) L.bNormalizedField L.cNormalField

/-- The eight-coordinate input field lies in the final normalized field. -/
theorem inputField_le_normalizedField : D.inputField ≤ L.normalizedField :=
  L.inputField_le_jointField.trans <|
    L.jointField_le_eNormalizedField.trans <|
      L.eNormalizedField_le_aNormalizedField.trans <|
        L.aNormalizedField_le_bNormalizedField.trans
          L.bNormalizedField_le_normalizedField

/-- The first scalar normal field lies in the final normalized field. -/
theorem eNormalField_le_normalizedField :
    L.eNormalField.restrictScalars k ≤ L.normalizedField := by
  letI := L.eNormalField_finiteDimensional
  exact (FiniteExtensionCompositum.normal_le_field
    (rankTwoParameterField (k := k) e) L.jointField L.eNormalField
    L.eParameterField_le_jointField).trans <|
      L.eNormalizedField_le_aNormalizedField.trans <|
        L.aNormalizedField_le_bNormalizedField.trans
          L.bNormalizedField_le_normalizedField

/-- The inverse-input scalar normal field lies in the final normalized
field. -/
theorem aNormalField_le_normalizedField :
    L.aNormalField.restrictScalars k ≤ L.normalizedField := by
  letI := L.aNormalField_finiteDimensional
  exact (FiniteExtensionCompositum.normal_le_field
    (rankTwoParameterField (k := k) a) L.eNormalizedField L.aNormalField
    (L.aParameterField_le_jointField.trans
      L.jointField_le_eNormalizedField)).trans <|
        L.aNormalizedField_le_bNormalizedField.trans
          L.bNormalizedField_le_normalizedField

/-- The second based scalar normal field lies in the final normalized
field. -/
theorem bNormalField_le_normalizedField :
    L.bNormalField.restrictScalars k ≤ L.normalizedField := by
  letI := L.bNormalField_finiteDimensional
  exact (FiniteExtensionCompositum.normal_le_field
    (rankTwoParameterField (k := k) b) L.aNormalizedField L.bNormalField
    ((L.bParameterField_le_jointField.trans
      L.jointField_le_eNormalizedField).trans
        L.eNormalizedField_le_aNormalizedField)).trans
          L.bNormalizedField_le_normalizedField

/-- The output scalar normal field lies in the final normalized field. -/
theorem cNormalField_le_normalizedField :
    L.cNormalField.restrictScalars k ≤ L.normalizedField := by
  letI := L.cNormalField_finiteDimensional
  exact FiniteExtensionCompositum.normal_le_field
    (rankTwoParameterField (k := k) D.c) L.bNormalizedField L.cNormalField
    (((L.cParameterField_le_jointField.trans
      L.jointField_le_eNormalizedField).trans
        L.eNormalizedField_le_aNormalizedField).trans
          L.aNormalizedField_le_bNormalizedField)

/-- The final basis-enlarged field as an extension of the original eight
input coordinates. -/
def normalizedOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars L.inputField_le_normalizedField

/-- The first basis enlargement as an extension of the joint field. -/
def eNormalizedOverJoint : IntermediateField (↥L.jointField) K :=
  extendScalars L.jointField_le_eNormalizedField

/-- The inverse-input enlargement as an extension of the first enlargement. -/
def aNormalizedOverE : IntermediateField (↥L.eNormalizedField) K :=
  extendScalars L.eNormalizedField_le_aNormalizedField

/-- The second-input enlargement as an extension of the preceding field. -/
def bNormalizedOverA : IntermediateField (↥L.aNormalizedField) K :=
  extendScalars L.aNormalizedField_le_bNormalizedField

/-- The final enlargement as an extension of the preceding field. -/
def normalizedOverB : IntermediateField (↥L.bNormalizedField) K :=
  extendScalars L.bNormalizedField_le_normalizedField

/-- The first basis enlargement is finite over the joint field. -/
theorem eNormalizedOverJoint_finiteDimensional :
    FiniteDimensional (↥L.jointField) (↥L.eNormalizedOverJoint) := by
  letI := L.eNormalField_finiteDimensional
  change FiniteDimensional (↥L.jointField)
    (↥(FiniteExtensionCompositum.over
      (rankTwoParameterField (k := k) e) L.jointField L.eNormalField))
  exact FiniteExtensionCompositum.over_finiteDimensional
    (rankTwoParameterField (k := k) e) L.jointField L.eNormalField
    L.eParameterField_le_jointField

/-- The inverse-input basis enlargement is finite over the preceding field. -/
theorem aNormalizedOverE_finiteDimensional :
    FiniteDimensional (↥L.eNormalizedField) (↥L.aNormalizedOverE) := by
  letI := L.aNormalField_finiteDimensional
  change FiniteDimensional (↥L.eNormalizedField)
    (↥(FiniteExtensionCompositum.over
      (rankTwoParameterField (k := k) a) L.eNormalizedField L.aNormalField))
  exact FiniteExtensionCompositum.over_finiteDimensional
    (rankTwoParameterField (k := k) a) L.eNormalizedField L.aNormalField
    (L.aParameterField_le_jointField.trans L.jointField_le_eNormalizedField)

/-- The second-input basis enlargement is finite over the preceding field. -/
theorem bNormalizedOverA_finiteDimensional :
    FiniteDimensional (↥L.aNormalizedField) (↥L.bNormalizedOverA) := by
  letI := L.bNormalField_finiteDimensional
  change FiniteDimensional (↥L.aNormalizedField)
    (↥(FiniteExtensionCompositum.over
      (rankTwoParameterField (k := k) b) L.aNormalizedField L.bNormalField))
  exact FiniteExtensionCompositum.over_finiteDimensional
    (rankTwoParameterField (k := k) b) L.aNormalizedField L.bNormalField
    ((L.bParameterField_le_jointField.trans
      L.jointField_le_eNormalizedField).trans
        L.eNormalizedField_le_aNormalizedField)

/-- The output basis enlargement is finite over the preceding field. -/
theorem normalizedOverB_finiteDimensional :
    FiniteDimensional (↥L.bNormalizedField) (↥L.normalizedOverB) := by
  letI := L.cNormalField_finiteDimensional
  change FiniteDimensional (↥L.bNormalizedField)
    (↥(FiniteExtensionCompositum.over
      (rankTwoParameterField (k := k) D.c) L.bNormalizedField L.cNormalField))
  exact FiniteExtensionCompositum.over_finiteDimensional
    (rankTwoParameterField (k := k) D.c) L.bNormalizedField L.cNormalField
    (((L.cParameterField_le_jointField.trans
      L.jointField_le_eNormalizedField).trans
        L.eNormalizedField_le_aNormalizedField).trans
          L.aNormalizedField_le_bNormalizedField)

/-- The first basis enlargement as a direct extension of the original input
field. -/
def eNormalizedOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars
    (L.inputField_le_jointField.trans L.jointField_le_eNormalizedField)

/-- The second basis enlargement as a direct extension of the original
input field. -/
def aNormalizedOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars
    ((L.inputField_le_jointField.trans L.jointField_le_eNormalizedField).trans
      L.eNormalizedField_le_aNormalizedField)

/-- The third basis enlargement as a direct extension of the original input
field. -/
def bNormalizedOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars
    (((L.inputField_le_jointField.trans L.jointField_le_eNormalizedField).trans
      L.eNormalizedField_le_aNormalizedField).trans
        L.aNormalizedField_le_bNormalizedField)

/-- The first basis-enlarged field is finite over the original inputs. -/
theorem eNormalizedOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.eNormalizedOverInput) :=
  FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    L.inputField_le_jointField L.jointField_le_eNormalizedField
    L.jointOverInput_finiteDimensional
    L.eNormalizedOverJoint_finiteDimensional

/-- The second basis-enlarged field is finite over the original inputs. -/
theorem aNormalizedOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.aNormalizedOverInput) :=
  FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    (L.inputField_le_jointField.trans L.jointField_le_eNormalizedField)
    L.eNormalizedField_le_aNormalizedField
    L.eNormalizedOverInput_finiteDimensional
    L.aNormalizedOverE_finiteDimensional

/-- The third basis-enlarged field is finite over the original inputs. -/
theorem bNormalizedOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.bNormalizedOverInput) :=
  FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    ((L.inputField_le_jointField.trans L.jointField_le_eNormalizedField).trans
      L.eNormalizedField_le_aNormalizedField)
    L.aNormalizedField_le_bNormalizedField
    L.aNormalizedOverInput_finiteDimensional
    L.bNormalizedOverA_finiteDimensional

/-- Adjoining all four individual scalar normal fields still gives a finite
extension of the original eight-coordinate input field. -/
theorem normalizedOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.normalizedOverInput) :=
  FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    (((L.inputField_le_jointField.trans L.jointField_le_eNormalizedField).trans
      L.eNormalizedField_le_aNormalizedField).trans
        L.aNormalizedField_le_bNormalizedField)
    L.bNormalizedField_le_normalizedField
    L.bNormalizedOverInput_finiteDimensional
    L.normalizedOverB_finiteDimensional

/-- One final normal closure over the eight-coordinate input field containing
the joint component and all four individual `B/T` normal fields. -/
def referenceNormalCover : IntermediateField (↥D.inputField) K :=
  FiniteCover.normalClosureOver L.inputField_le_normalizedField

/-- The basis-enlarged field embeds in the final common normal cover. -/
theorem normalizedOverInput_le_referenceNormalCover :
    L.normalizedOverInput ≤ L.referenceNormalCover :=
  FiniteCover.extendScalars_le_normalClosureOver
    L.inputField_le_normalizedField

/-- The final common cover remains finite over the original eight inputs. -/
theorem referenceNormalCover_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.referenceNormalCover) :=
  FiniteCover.normalClosureOver_finiteDimensional
    L.inputField_le_normalizedField
    L.normalizedOverInput_finiteDimensional

/-- Over an algebraically closed ambient field, the final common cover is
normal over the eight-coordinate input field. -/
theorem referenceNormalCover_normal [IsAlgClosed K] :
    Normal (↥D.inputField) (↥L.referenceNormalCover) := by
  letI := L.normalizedOverInput_finiteDimensional
  exact FiniteCover.normalClosureOver_normal
    L.inputField_le_normalizedField
    (Algebra.IsAlgebraic.of_finite
      (↥D.inputField) (↥L.normalizedOverInput))

/-- The integral affine source chart carrying the complete lifted component
and all four normalized `B/T` branch fields. -/
abbrev referenceAlgebraicChart : Scheme := by
  letI := L.referenceNormalCover_finiteDimensional
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥D.inputField) (L := ↥L.referenceNormalCover) D.inputCoordinates

/-- Any scalar normal field contained in the basis-enlarged field embeds in
the final common normal cover. -/
def scalarNormalFieldToReferenceNormalCover
    (p : Fin 2 → K) (x : K)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    rankTwoScalarNormalField (k := k) p x →ₐ[k]
      (↥L.referenceNormalCover) := by
  let hle : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤
      L.referenceNormalCover.restrictScalars k := by
    intro z hz
    apply L.normalizedOverInput_le_referenceNormalCover
    exact hfield hz
  exact IntermediateField.inclusion hle

/-- A dominant rational projection from the final common chart to any
contained normalized scalar branch chart. -/
def projectionToNormalizedScalar (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p))
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    Scheme.RationalMap L.referenceAlgebraicChart
      (rankTwoScalarAlgebraicChart (k := k) p x hx) := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  exact FiniteExtensionProjection.rationalMap
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) p)
    D.adjoin_inputCoordinates_eq_top
    (L.scalarNormalFieldToReferenceNormalCover p x hfield)

/-- Direct projection to the normalized first-input `B/T` chart. -/
abbrev toNormalizedE : Scheme.RationalMap L.referenceAlgebraicChart
    (w.psiBProjectionAlgebraicChart hψ L.eProjectionRelation) :=
  L.projectionToNormalizedScalar e L.se_e L.eScalar_mem_racl
    L.eNormalField_le_normalizedField

/-- Direct projection to the normalized inverse-input `B/T` chart. -/
abbrev toNormalizedA : Scheme.RationalMap L.referenceAlgebraicChart
    (w.psiBProjectionAlgebraicChart hψ L.aProjectionRelation) :=
  L.projectionToNormalizedScalar a L.sA_a_a L.aScalar_mem_racl
    L.aNormalField_le_normalizedField

/-- Direct projection to the normalized second-input `B/T` chart. -/
abbrev toNormalizedB : Scheme.RationalMap L.referenceAlgebraicChart
    (w.psiBProjectionAlgebraicChart hψ L.bProjectionRelation) :=
  L.projectionToNormalizedScalar b L.s_b_b L.bScalar_mem_racl
    L.bNormalField_le_normalizedField

/-- Direct projection to the normalized output `B/T` chart. -/
abbrev toNormalizedC : Scheme.RationalMap L.referenceAlgebraicChart
    (w.psiBProjectionAlgebraicChart hψ L.cProjectionRelation) :=
  L.projectionToNormalizedScalar D.c L.sA_c_c L.cScalar_mem_racl
    L.cNormalField_le_normalizedField

instance toNormalizedE_isDominant : L.toNormalizedE.IsDominant := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := L.eNormalField_finiteDimensional
  unfold toNormalizedE projectionToNormalizedScalar
  exact FiniteExtensionProjection.rationalMap_isDominant
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) e)
    D.adjoin_inputCoordinates_eq_top
    (L.scalarNormalFieldToReferenceNormalCover e L.se_e
      L.eNormalField_le_normalizedField)
instance toNormalizedA_isDominant : L.toNormalizedA.IsDominant := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := L.aNormalField_finiteDimensional
  unfold toNormalizedA projectionToNormalizedScalar
  exact FiniteExtensionProjection.rationalMap_isDominant
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) a)
    D.adjoin_inputCoordinates_eq_top
    (L.scalarNormalFieldToReferenceNormalCover a L.sA_a_a
      L.aNormalField_le_normalizedField)
instance toNormalizedB_isDominant : L.toNormalizedB.IsDominant := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := L.bNormalField_finiteDimensional
  unfold toNormalizedB projectionToNormalizedScalar
  exact FiniteExtensionProjection.rationalMap_isDominant
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) b)
    D.adjoin_inputCoordinates_eq_top
    (L.scalarNormalFieldToReferenceNormalCover b L.s_b_b
      L.bNormalField_le_normalizedField)
instance toNormalizedC_isDominant : L.toNormalizedC.IsDominant := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := L.cNormalField_finiteDimensional
  unfold toNormalizedC projectionToNormalizedScalar
  exact FiniteExtensionProjection.rationalMap_isDominant
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) D.c)
    D.adjoin_inputCoordinates_eq_top
    (L.scalarNormalFieldToReferenceNormalCover D.c L.sA_c_c
      L.cNormalField_le_normalizedField)

/-- The selected `(B,T)` tuple is itself a realization of the `B/T`
projection graph. -/
theorem selectedBProjectionRelation :
    w.psiBProjectionRelation w.bReps w.T.rep := by
  rfl

/-- The one selected normalized `B/T` chart used as reference for all four
based blocks. -/
abbrev selectedBAlgebraicChart : Scheme :=
  w.psiBProjectionAlgebraicChart hψ
    (selectedBProjectionRelation (w := w))

/-- The first based input, transported to the selected `B/T` reference
model. -/
def toReferenceE [IsAlgClosed K] : Scheme.RationalMap L.referenceAlgebraicChart
    (selectedBAlgebraicChart (w := w) (hψ := hψ)) :=
  L.toNormalizedE.comp
    (w.psiBProjectionReferenceRationalMap hψ L.eProjectionRelation
      (selectedBProjectionRelation (w := w)))

/-- The inverse input, transported to the selected `B/T` reference model. -/
def toReferenceA [IsAlgClosed K] : Scheme.RationalMap L.referenceAlgebraicChart
    (selectedBAlgebraicChart (w := w) (hψ := hψ)) :=
  L.toNormalizedA.comp
    (w.psiBProjectionReferenceRationalMap hψ L.aProjectionRelation
      (selectedBProjectionRelation (w := w)))

/-- The second based input, transported to the selected `B/T` reference
model. -/
def toReferenceB [IsAlgClosed K] : Scheme.RationalMap L.referenceAlgebraicChart
    (selectedBAlgebraicChart (w := w) (hψ := hψ)) :=
  L.toNormalizedB.comp
    (w.psiBProjectionReferenceRationalMap hψ L.bProjectionRelation
      (selectedBProjectionRelation (w := w)))

/-- The output, transported to the selected `B/T` reference model. -/
def toReferenceC [IsAlgClosed K] : Scheme.RationalMap L.referenceAlgebraicChart
    (selectedBAlgebraicChart (w := w) (hψ := hψ)) :=
  L.toNormalizedC.comp
    (w.psiBProjectionReferenceRationalMap hψ L.cProjectionRelation
      (selectedBProjectionRelation (w := w)))

instance toReferenceE_isDominant [IsAlgClosed K] : L.toReferenceE.IsDominant := by
  unfold toReferenceE
  infer_instance
instance toReferenceA_isDominant [IsAlgClosed K] : L.toReferenceA.IsDominant := by
  unfold toReferenceA
  infer_instance
instance toReferenceB_isDominant [IsAlgClosed K] : L.toReferenceB.IsDominant := by
  unfold toReferenceB
  infer_instance
instance toReferenceC_isDominant [IsAlgClosed K] : L.toReferenceC.IsDominant := by
  unfold toReferenceC
  infer_instance

end QWitness.PsiChunkFourArrowEdgeLifts

end

end AclGeom
