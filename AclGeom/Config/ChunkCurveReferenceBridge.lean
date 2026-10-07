/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource
import AclGeom.Config.ChunkGermCoordinates
import AclGeom.Config.ChunkRelationScalarExtension

/-!
# A common field for the curve action and the normalized reference chart

The semantic four-arrow action is constructed in the algebraic closure of
`K(X)`, whereas the normalized `B/T` reference chart was first constructed
inside `K`.  The canonical embedding `K → AlgebraicClosure K(X)` transports
the entire normalized reference cover into the curve ambient field.

This file places that transported cover and the coefficient-faithful curve
action in one finite normal field.  In particular, the two constructions now
have a literal common codomain for comparing their contravariant function-
field embeddings; no abstract comparison of unrelated algebraic closures is
needed.
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

/-- The canonical embedding of `K` into the common curve ambient, shared by the
reference-bridge modules. -/
abbrev curveEmbedding : K →ₐ[k] CommonCurveAmbient K :=
  commonCurveEmbedding (k := k) (K := K)

/-- The raw common curve-source type before restricting its displayed
coefficient field to `k`.  This short private name keeps later chart types
readable while preserving the exact algebra instance used by the covers. -/
private abbrev semanticCommonSourceType
    (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D) :=
  ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField

/-- The eight-input field of the normalized reference construction,
transported into the common curve ambient field. -/
def mappedReferenceInputField
    (_R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
    (_L : w.PsiChunkFourArrowEdgeLifts hψ D) :
    IntermediateField k (CommonCurveAmbient K) :=
  D.inputField.map (curveEmbedding (k := k) (K := K))

/-- The transported reference input field is literally the coefficient
field used by all four common-source curve triangles. -/
theorem mappedReferenceInputField_eq_commonCoefficientField :
    R.mappedReferenceInputField L = R.seCommonBaseData.coefficientField := by
  unfold mappedReferenceInputField
    RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.inputField
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.coefficientField
    commonInputTuple curveEmbedding
  rw [adjoin_map]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨rankTwoFourTuple s e a b i, ⟨i, rfl⟩, rfl⟩

/-- The final normalized reference cover, transported coefficientwise into
the common curve ambient field. -/
def mappedReferenceNormalField
    (_R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
    (L : w.PsiChunkFourArrowEdgeLifts hψ D) :
    IntermediateField k (CommonCurveAmbient K) :=
  (L.referenceNormalCover.restrictScalars k).map
    (curveEmbedding (k := k) (K := K))

/-- The transported input field lies in the transported normalized cover. -/
theorem mappedReferenceInputField_le_mappedReferenceNormalField :
    R.mappedReferenceInputField L ≤ R.mappedReferenceNormalField L := by
  apply IntermediateField.map_mono
  intro z hz
  change z ∈ L.referenceNormalCover
  exact L.referenceNormalCover.algebraMap_mem ⟨z, hz⟩

/-- The transported normalized cover, displayed as an extension of the
transported eight-input field. -/
def mappedReferenceNormalOverInput :
    IntermediateField (↥(R.mappedReferenceInputField L))
      (CommonCurveAmbient K) :=
  extendScalars
    (R.mappedReferenceInputField_le_mappedReferenceNormalField L)

/-- Transporting the normalized cover does not change its finite degree
over the transported eight-input field. -/
theorem mappedReferenceNormalOverInput_finiteDimensional :
    FiniteDimensional (↥(R.mappedReferenceInputField L))
      (↥(R.mappedReferenceNormalOverInput L)) := by
  let ι : K →ₐ[k] CommonCurveAmbient K :=
    curveEmbedding (k := k) (K := K)
  let N₀ : IntermediateField k K :=
    L.referenceNormalCover.restrictScalars k
  have h₀ : D.inputField ≤ N₀ := by
    intro z hz
    change z ∈ L.referenceNormalCover
    exact L.referenceNormalCover.algebraMap_mem ⟨z, hz⟩
  let e₀ : D.inputField ≃ₐ[k] D.inputField.map ι :=
    D.inputField.equivMap ι
  let e₁ : N₀ ≃ₐ[k] N₀.map ι := N₀.equivMap ι
  let : Algebra (↥D.inputField) (↥N₀) :=
    (IntermediateField.inclusion h₀).toAlgebra
  let : Algebra (↥(D.inputField.map ι)) (↥(N₀.map ι)) :=
    (IntermediateField.inclusion
      (IntermediateField.map_mono ι h₀)).toAlgebra
  let : FiniteDimensional (↥D.inputField) (↥N₀) := by
    change FiniteDimensional (↥D.inputField) (↥L.referenceNormalCover)
    exact L.referenceNormalCover_finiteDimensional
  change FiniteDimensional (↥(D.inputField.map ι)) (↥(N₀.map ι))
  apply Module.Finite.of_equiv_equiv e₀.toRingEquiv e₁.toRingEquiv
  apply RingHom.ext
  intro x
  rfl

/-- The literal common coefficient/source field over which the semantic
four-arrow cover is normal. -/
abbrev semanticCommonSourceField :
    IntermediateField k (CommonCurveAmbient K) :=
  (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
    (R := R.se) R.seCommonBaseData hψ).sourceField.restrictScalars k

/-- The literal compositum of the original semantic source and the
genuinely different algebraic-output source presentation.  Unlike the
earlier source automorphisms, this construction does not identify the two
fields: it retains both selected embeddings in one ambient field. -/
def rightSourceJointField :
    IntermediateField k (CommonCurveAmbient K) :=
  R.semanticCommonSourceField ⊔ R.rightCSourceField

/-- The original semantic source is a literal subfield of the joint source
model. -/
theorem semanticCommonSourceField_le_rightSourceJointField :
    R.semanticCommonSourceField ≤ R.rightSourceJointField :=
  le_sup_left

/-- The algebraic-output source is the other literal subfield of the joint
source model. -/
theorem rightCSourceField_le_rightSourceJointField :
    R.rightCSourceField ≤ R.rightSourceJointField :=
  le_sup_right

/-- The selected inclusion of the original semantic source in the joint
source field. -/
def semanticSourceToRightSourceJoint :
    (↥R.semanticCommonSourceField) →ₐ[k] (↥R.rightSourceJointField) :=
  IntermediateField.inclusion
    R.semanticCommonSourceField_le_rightSourceJointField

/-- The selected inclusion of the genuinely different algebraic-output
source in the same joint field. -/
def rightCSourceToRightSourceJoint :
    (↥R.rightCSourceField) →ₐ[k] (↥R.rightSourceJointField) :=
  IntermediateField.inclusion R.rightCSourceField_le_rightSourceJointField

/-- The joint source displayed as an extension of the original semantic
source. -/
def rightSourceJointOverSemantic :
    IntermediateField (↥R.semanticCommonSourceField)
      (CommonCurveAmbient K) :=
  extendScalars R.semanticCommonSourceField_le_rightSourceJointField

/-- The same joint source displayed as an extension of the algebraic-output
source. -/
def rightSourceJointOverC :
    IntermediateField (↥R.rightCSourceField) (CommonCurveAmbient K) :=
  extendScalars R.rightCSourceField_le_rightSourceJointField

/-- The joint source is finite over the original semantic presentation.
This uses the literal four-arrow interalgebraicity chain, rather than the
abstract `e→c` function-field equivalence. -/
theorem rightSourceJointOverSemantic_finiteDimensional :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic) := by
  have key : R.rightSourceJointOverSemantic =
      adjoin (↥R.semanticCommonSourceField)
        (Set.range R.rightCSourceTuple) := by
    refine restrictScalars_injective k ?_
    unfold rightSourceJointOverSemantic rightSourceJointField
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup]
    rfl
  rw [key]
  let : Fintype (Set.range R.rightCSourceTuple) :=
    Set.Finite.fintype (Set.finite_range R.rightCSourceTuple)
  exact finiteDimensional_adjoin fun z hz ↦ by
    have hzr : z ∈ racl k (Set.range R.rightESourceTuple) := by
      rw [R.rightESource_racl_eq_rightCSource]
      exact subset_racl k _ hz
    have hzAlg : IsAlgebraic (↥R.rightESourceField) z :=
      (mem_racl_iff k).1 hzr
    rw [R.rightESourceField_eq_commonSourceField] at hzAlg
    exact hzAlg.isIntegral

/-- Symmetrically, the same joint source is finite over the genuine `c`
presentation.  Both legs may therefore be normalized without erasing the
semilinear base change. -/
theorem rightSourceJointOverC_finiteDimensional :
    FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointOverC) := by
  have key : R.rightSourceJointOverC =
      adjoin (↥R.rightCSourceField)
        (Set.range R.rightESourceTuple) := by
    refine restrictScalars_injective k ?_
    unfold rightSourceJointOverC rightSourceJointField
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup]
    change R.semanticCommonSourceField ⊔ R.rightCSourceField =
      R.rightCSourceField ⊔ R.rightESourceField
    calc
      R.semanticCommonSourceField ⊔ R.rightCSourceField =
          R.rightCSourceField ⊔ R.semanticCommonSourceField :=
        sup_comm _ _
      _ = R.rightCSourceField ⊔ R.rightESourceField :=
        congrArg (fun F : IntermediateField k (CommonCurveAmbient K) ↦
          R.rightCSourceField ⊔ F)
          R.rightESourceField_eq_commonSourceField.symm
  rw [key]
  let : Fintype (Set.range R.rightESourceTuple) :=
    Set.Finite.fintype (Set.finite_range R.rightESourceTuple)
  exact finiteDimensional_adjoin fun z hz ↦ by
    have hzr : z ∈ racl k (Set.range R.rightCSourceTuple) := by
      rw [← R.rightESource_racl_eq_rightCSource]
      exact subset_racl k _ hz
    exact ((mem_racl_iff k).1 hzr).isIntegral

/-- A chosen algebraic-closure equivalence extending the literal inclusion
of the semantic source in the joint source. -/
noncomputable def semanticSourceToRightSourceJointClosureRingEquiv :
    AlgebraicClosure (↥R.semanticCommonSourceField) ≃+*
      AlgebraicClosure (↥R.rightSourceJointField) := by
  let hSJ := R.semanticCommonSourceField_le_rightSourceJointField
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    (IntermediateField.inclusion hSJ).toAlgebra
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic)
    exact R.rightSourceJointOverSemantic_finiteDimensional
  exact (IsAlgClosure.equivOfAlgebraic
    (↥R.semanticCommonSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))
    (AlgebraicClosure (↥R.semanticCommonSourceField))).symm.toRingEquiv

/-- The chosen equivalence carries the semantic base to its selected
literal image in the joint source. -/
@[simp] theorem semanticSourceToRightSourceJointClosureRingEquiv_algebraMap
    (x : R.semanticCommonSourceField) :
    R.semanticSourceToRightSourceJointClosureRingEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField)) x) =
      algebraMap (↥R.rightSourceJointField)
        (AlgebraicClosure (↥R.rightSourceJointField))
        (R.semanticSourceToRightSourceJoint x) := by
  let hSJ := R.semanticCommonSourceField_le_rightSourceJointField
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    (IntermediateField.inclusion hSJ).toAlgebra
  let : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic)
    exact R.rightSourceJointOverSemantic_finiteDimensional
  let phi := IsAlgClosure.equivOfAlgebraic
    (↥R.semanticCommonSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))
    (AlgebraicClosure (↥R.semanticCommonSourceField))
  change phi.symm
      (algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField)) x) = _
  apply phi.injective
  rw [phi.apply_symm_apply]
  change algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)) x =
    phi (algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (algebraMap (↥R.semanticCommonSourceField)
        (↥R.rightSourceJointField) x))
  rw [← IsScalarTower.algebraMap_apply
    (↥R.semanticCommonSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))]
  exact (phi.commutes x).symm

/-- A second chosen algebraic-closure equivalence extending the literal
inclusion of the `c` source in the same joint source. -/
noncomputable def rightCSourceToRightSourceJointClosureRingEquiv :
    AlgebraicClosure (↥R.rightCSourceField) ≃+*
      AlgebraicClosure (↥R.rightSourceJointField) := by
  let hCJ := R.rightCSourceField_le_rightSourceJointField
  letI : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    (IntermediateField.inclusion hCJ).toAlgebra
  letI : FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointField) := by
    change FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointOverC)
    exact R.rightSourceJointOverC_finiteDimensional
  exact (IsAlgClosure.equivOfAlgebraic
    (↥R.rightCSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))
    (AlgebraicClosure (↥R.rightCSourceField))).symm.toRingEquiv

/-- The `c`-source closure equivalence likewise preserves its literal base
embedding. -/
@[simp] theorem rightCSourceToRightSourceJointClosureRingEquiv_algebraMap
    (x : R.rightCSourceField) :
    R.rightCSourceToRightSourceJointClosureRingEquiv
        (algebraMap (↥R.rightCSourceField)
          (AlgebraicClosure (↥R.rightCSourceField)) x) =
      algebraMap (↥R.rightSourceJointField)
        (AlgebraicClosure (↥R.rightSourceJointField))
        (R.rightCSourceToRightSourceJoint x) := by
  let hCJ := R.rightCSourceField_le_rightSourceJointField
  let : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    (IntermediateField.inclusion hCJ).toAlgebra
  let : FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointField) := by
    change FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointOverC)
    exact R.rightSourceJointOverC_finiteDimensional
  let phi := IsAlgClosure.equivOfAlgebraic
    (↥R.rightCSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))
    (AlgebraicClosure (↥R.rightCSourceField))
  change phi.symm
      (algebraMap (↥R.rightCSourceField)
        (AlgebraicClosure (↥R.rightCSourceField)) x) = _
  apply phi.injective
  rw [phi.apply_symm_apply]
  change algebraMap (↥R.rightCSourceField)
      (AlgebraicClosure (↥R.rightCSourceField)) x =
    phi (algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (algebraMap (↥R.rightCSourceField) (↥R.rightSourceJointField) x))
  rw [← IsScalarTower.algebraMap_apply
    (↥R.rightCSourceField) (↥R.rightSourceJointField)
    (AlgebraicClosure (↥R.rightSourceJointField))]
  exact (phi.commutes x).symm

/-- The transported eight-input field embeds in the semantic source field;
the additional generator of the latter is the formal curve coordinate. -/
theorem mappedReferenceInputField_le_semanticCommonSourceField :
    R.mappedReferenceInputField L ≤ R.semanticCommonSourceField := by
  rw [R.mappedReferenceInputField_eq_commonCoefficientField L]
  intro z hz
  change z ∈
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField
  exact
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).sourceField.algebraMap_mem
        ⟨z, hz⟩

/-- Adjoin the transported normalized reference cover to the semantic
coefficient/source field.  This is finite over the semantic source because
the reference cover was already finite over the smaller eight-input field. -/
def referenceSemanticJoin
    (_hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField k (CommonCurveAmbient K) := by
  letI := R.mappedReferenceNormalOverInput_finiteDimensional L
  exact FiniteExtensionCompositum.field
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)

/-- The semantic coefficient/source field lies in the reference/semantic
compositum. -/
theorem semanticCommonSourceField_le_referenceSemanticJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.semanticCommonSourceField ≤ R.referenceSemanticJoin L hind := by
  let := R.mappedReferenceNormalOverInput_finiteDimensional L
  exact FiniteExtensionCompositum.le_field
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)

/-- The reference/semantic compositum, displayed over the semantic common
source field. -/
def referenceSemanticJoinOverSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (↥R.semanticCommonSourceField)
      (CommonCurveAmbient K) :=
  extendScalars (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)

/-- The reference/semantic compositum is finite over the semantic common
source field. -/
theorem referenceSemanticJoinOverSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.referenceSemanticJoinOverSource L hind)) := by
  let := R.mappedReferenceNormalOverInput_finiteDimensional L
  exact FiniteExtensionCompositum.over_finiteDimensional
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

/-- The two algebraic output parameters and four selected semantic
right-branch endpoint pairs. -/
def selectedSemanticReferenceTuple
    (_L : w.PsiChunkFourArrowEdgeLifts hψ D) :
    Fin 10 → CommonCurveAmbient K :=
  ![commonCurveEmbedding (k := k) (K := K) (D.c 0),
    commonCurveEmbedding (k := k) (K := K) (D.c 1),
    R.se.middle, R.se.target,
    R.sAa.middle, R.sAa.target,
    R.sb.middle, R.sb.target,
    R.sAc.middle, R.sAc.target]

private theorem c_isAlgebraic_over_semanticCommonSourceField (i : Fin 2) :
    IsAlgebraic (↥R.semanticCommonSourceField)
      (commonCurveEmbedding (k := k) (K := K) (D.c i)) := by
  let A := R.seCommonBaseData.coefficientField
  have hcA : IsAlgebraic (↥A)
      (commonCurveEmbedding (k := k) (K := K) (D.c i)) := by
    change IsAlgebraic
      (↥(adjoin k (Set.range R.commonInputTuple)))
      (commonCurveEmbedding (k := k) (K := K) (D.c i))
    exact (mem_racl_iff k).1 (R.c_mem_commonInput_racl i)
  have hAS : A ≤ R.semanticCommonSourceField := by
    intro z hz
    change z ∈
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField
    exact
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField.algebraMap_mem ⟨z, hz⟩
  let : Algebra (↥A) (↥R.semanticCommonSourceField) :=
    (IntermediateField.inclusion hAS).toAlgebra
  let : IsScalarTower (↥A) (↥R.semanticCommonSourceField)
      (CommonCurveAmbient K) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact IsAlgebraic.tower_top (L := ↥R.semanticCommonSourceField) hcA

private theorem se_middle_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.se.middle := by
  exact (mem_racl_iff (↥R.seCommonBaseData.coefficientField)).1
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).target_mem_source

private theorem se_target_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.se.target := by
  have ht :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).target_mem_source
  have hm :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).target_mem_source
  exact (mem_racl_iff (↥R.seCommonBaseData.coefficientField)).1
    (mem_racl_trans (w := R.se.middle) ht hm)

private theorem sAa_middle_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sAa.middle := by
  exact (mem_racl_iff (↥R.sAaCommonBaseData.coefficientField)).1
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).target_mem_source

private theorem sAa_target_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sAa.target := by
  have ht :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).target_mem_source
  have hm :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).target_mem_source
  exact (mem_racl_iff (↥R.sAaCommonBaseData.coefficientField)).1
    (mem_racl_trans (w := R.sAa.middle) ht hm)

private theorem sb_middle_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sb.middle := by
  exact (mem_racl_iff (↥R.sbCommonBaseData.coefficientField)).1
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).target_mem_source

private theorem sb_target_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sb.target := by
  have ht :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).target_mem_source
  have hm :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).target_mem_source
  exact (mem_racl_iff (↥R.sbCommonBaseData.coefficientField)).1
    (mem_racl_trans (w := R.sb.middle) ht hm)

private theorem sAc_middle_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sAc.middle := by
  exact (mem_racl_iff (↥R.sAcCommonBaseData.coefficientField)).1
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).target_mem_source

private theorem sAc_target_isAlgebraic_over_semanticCommonSourceField :
    IsAlgebraic (↥R.semanticCommonSourceField) R.sAc.target := by
  have ht :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).target_mem_source
  have hm :=
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).target_mem_source
  exact (mem_racl_iff (↥R.sAcCommonBaseData.coefficientField)).1
    (mem_racl_trans (w := R.sAc.middle) ht hm)

/-- The selected semantic coordinates as one finite extension of the
literal common source field. -/
def selectedSemanticBranchExtension :
    IntermediateField (↥R.semanticCommonSourceField) (CommonCurveAmbient K) :=
  adjoin (↥R.semanticCommonSourceField)
    (Set.range (R.selectedSemanticReferenceTuple L))

/-- Adjoining the selected semantic coordinates and the two `c` parameters
is finite over the literal common source field. -/
theorem selectedSemanticBranchExtension_finiteDimensional :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticBranchExtension L)) := by
  unfold selectedSemanticBranchExtension
  exact finiteDimensional_adjoin fun z hz ↦ by
    obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · exact (R.c_isAlgebraic_over_semanticCommonSourceField 0).isIntegral
    · exact (R.c_isAlgebraic_over_semanticCommonSourceField 1).isIntegral
    · exact R.se_middle_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.se_target_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sAa_middle_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sAa_target_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sb_middle_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sb_target_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sAc_middle_isAlgebraic_over_semanticCommonSourceField.isIntegral
    · exact R.sAc_target_isAlgebraic_over_semanticCommonSourceField.isIntegral

/-- The transported reference compositum with the four concrete semantic
right branches adjoined before any normal-closure canonicalization. -/
def selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField k (CommonCurveAmbient K) := by
  letI := R.selectedSemanticBranchExtension_finiteDimensional L
  exact FiniteExtensionCompositum.field
    R.semanticCommonSourceField (R.referenceSemanticJoin L hind)
      (R.selectedSemanticBranchExtension L)

/-- The original transported reference compositum lies in the enlarged
selected semantic/reference joint field. -/
theorem referenceSemanticJoin_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.referenceSemanticJoin L hind ≤
      R.selectedSemanticReferenceJoin L hind := by
  let := R.selectedSemanticBranchExtension_finiteDimensional L
  exact FiniteExtensionCompositum.le_field
    R.semanticCommonSourceField (R.referenceSemanticJoin L hind)
      (R.selectedSemanticBranchExtension L)

/-- The finite extension generated by the selected semantic coordinates
lies in the enlarged joint field. -/
theorem selectedSemanticBranchExtension_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedSemanticBranchExtension L).restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let := R.selectedSemanticBranchExtension_finiteDimensional L
  exact FiniteExtensionCompositum.normal_le_field
    R.semanticCommonSourceField (R.referenceSemanticJoin L hind)
      (R.selectedSemanticBranchExtension L)
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)

/-- Every explicitly adjoined coordinate belongs to the concrete selected
semantic/reference joint field. -/
theorem selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 10) :
    R.selectedSemanticReferenceTuple L i ∈
      R.selectedSemanticReferenceJoin L hind := by
  apply R.selectedSemanticBranchExtension_le_selectedSemanticReferenceJoin L hind
  exact subset_adjoin (↥R.semanticCommonSourceField) _
    (Set.mem_range_self i)

/-- The literal common coefficient/source field lies in the selected joint
field. -/
theorem semanticCommonSourceField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.semanticCommonSourceField ≤ R.selectedSemanticReferenceJoin L hind :=
  (R.semanticCommonSourceField_le_referenceSemanticJoin L hind).trans
    (R.referenceSemanticJoin_le_selectedSemanticReferenceJoin L hind)

/-- The common eight-input coefficient field lies in the selected joint
field. -/
theorem commonCoefficientField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seCommonBaseData.coefficientField ≤
      R.selectedSemanticReferenceJoin L hind := by
  rw [← R.mappedReferenceInputField_eq_commonCoefficientField L]
  exact (R.mappedReferenceInputField_le_semanticCommonSourceField L).trans
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)

/-- The complete common-base semantic right branch on the `s·e=u` face lies
literally in the selected joint field. -/
theorem seSemanticRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  let hA := R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 2
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 3
  intro z hz
  apply hQ
  exact hz

/-- The complete common-base semantic right branch on the `sA·a=u` face
lies literally in the selected joint field. -/
theorem sAaSemanticRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  let hA := R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 4
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 5
  intro z hz
  apply hQ
  exact hz

/-- The complete common-base semantic right branch on the `s·b=uB` face
lies literally in the selected joint field. -/
theorem sbSemanticRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  let hA := R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 6
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 7
  intro z hz
  apply hQ
  exact hz

/-- The complete common-base semantic right branch on the `sA·c=uB` face
lies literally in the selected joint field. -/
theorem sAcSemanticRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  let hA := R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 8
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 9
  intro z hz
  apply hQ
  exact hz

/-- The original relocated `e` parameter field lies in the selected joint
field through the common eight-input coefficient field. -/
theorem seRelocatedParameterField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.selectedSemanticReferenceJoin L hind := by
  unfold FiniteCorrespondenceFamilyMember.parameterField
  apply adjoin_le_iff.2
  rintro _ ⟨i, rfl⟩
  apply R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  change commonCurveEmbedding (k := k) (K := K) (e i) ∈
    adjoin k (Set.range R.commonInputTuple)
  fin_cases i
  · exact subset_adjoin k _ ⟨2, rfl⟩
  · exact subset_adjoin k _ ⟨3, rfl⟩

/-- The original relocated `a` parameter field lies in the selected joint
field through the common eight-input coefficient field. -/
theorem sAaRelocatedParameterField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.selectedSemanticReferenceJoin L hind := by
  unfold FiniteCorrespondenceFamilyMember.parameterField
  apply adjoin_le_iff.2
  rintro _ ⟨i, rfl⟩
  apply R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  change commonCurveEmbedding (k := k) (K := K) (a i) ∈
    adjoin k (Set.range R.commonInputTuple)
  fin_cases i
  · exact subset_adjoin k _ ⟨4, rfl⟩
  · exact subset_adjoin k _ ⟨5, rfl⟩

/-- The original relocated `b` parameter field lies in the selected joint
field through the common eight-input coefficient field. -/
theorem sbRelocatedParameterField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.selectedSemanticReferenceJoin L hind := by
  unfold FiniteCorrespondenceFamilyMember.parameterField
  apply adjoin_le_iff.2
  rintro _ ⟨i, rfl⟩
  apply R.commonCoefficientField_le_selectedSemanticReferenceJoin L hind
  change commonCurveEmbedding (k := k) (K := K) (b i) ∈
    adjoin k (Set.range R.commonInputTuple)
  fin_cases i
  · exact subset_adjoin k _ ⟨6, rfl⟩
  · exact subset_adjoin k _ ⟨7, rfl⟩

/-- The algebraic relocated `c` parameter field lies in the selected joint
field because its two coordinates were adjoined explicitly. -/
theorem sAcRelocatedParameterField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).parameterField ≤
      R.selectedSemanticReferenceJoin L hind := by
  unfold FiniteCorrespondenceFamilyMember.parameterField
  apply adjoin_le_iff.2
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
      L hind 0
  · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
      L hind 1

/-- The original complete relocated `e` right branch lies literally in the
same selected joint field as its common-base semantic branch. -/
theorem seRelocatedRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.se.bCorrespondenceFamilyMember hψ
  let hP := R.seRelocatedParameterField_le_selectedSemanticReferenceJoin L hind
  have hG : G.toPair.branchField ≤ extendScalars hP := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 2
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 3
  intro z hz
  apply hG
  exact hz

/-- The original complete relocated `a` right branch lies literally in the
same selected joint field as its common-base semantic branch. -/
theorem sAaRelocatedRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sAa.bCorrespondenceFamilyMember hψ
  let hP := R.sAaRelocatedParameterField_le_selectedSemanticReferenceJoin L hind
  have hG : G.toPair.branchField ≤ extendScalars hP := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 4
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 5
  intro z hz
  apply hG
  exact hz

/-- The original complete relocated `b` right branch lies literally in the
same selected joint field as its common-base semantic branch. -/
theorem sbRelocatedRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sb.bCorrespondenceFamilyMember hψ
  let hP := R.sbRelocatedParameterField_le_selectedSemanticReferenceJoin L hind
  have hG : G.toPair.branchField ≤ extendScalars hP := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 6
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 7
  intro z hz
  apply hG
  exact hz

/-- The original complete relocated `c` right branch lies literally in the
same selected joint field as its common-base semantic branch. -/
theorem sAcRelocatedRightBranch_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sAc.bCorrespondenceFamilyMember hψ
  let hP := R.sAcRelocatedParameterField_le_selectedSemanticReferenceJoin L hind
  have hG : G.toPair.branchField ≤ extendScalars hP := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ R.selectedSemanticReferenceJoin L hind
    rcases hz with rfl | rfl
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 8
    · exact R.selectedSemanticReferenceTuple_mem_selectedSemanticReferenceJoin
        L hind 9
  intro z hz
  apply hG
  exact hz

/-- The full relocated `e` parameter/source field lies in the selected
joint field.  This is the base-field inclusion needed to rebase its native
normal cover without changing the selected complete branch. -/
theorem seRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.se.bCorrespondenceFamilyMember hψ
  intro z hz
  apply R.seRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind
  rw [← G.familyField_eq_toPair_branchField]
  exact G.parameterSourceField_le_familyField hz

/-- The full relocated `a` parameter/source field lies in the same selected
joint field. -/
theorem sAaRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sAa.bCorrespondenceFamilyMember hψ
  intro z hz
  apply R.sAaRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind
  rw [← G.familyField_eq_toPair_branchField]
  exact G.parameterSourceField_le_familyField hz

/-- The full relocated `b` parameter/source field lies in the same selected
joint field. -/
theorem sbRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sb.bCorrespondenceFamilyMember hψ
  intro z hz
  apply R.sbRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind
  rw [← G.familyField_eq_toPair_branchField]
  exact G.parameterSourceField_le_familyField hz

/-- The full algebraic-output `c` parameter/source field also lies in the
selected joint field; the two output parameters were included explicitly
when that field was formed. -/
theorem sAcRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind := by
  let G := R.sAc.bCorrespondenceFamilyMember hψ
  intro z hz
  apply R.sAcRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind
  rw [← G.familyField_eq_toPair_branchField]
  exact G.parameterSourceField_le_familyField hz

/-- The concrete joint field displayed as an extension of the literal
common coefficient/source field. -/
def selectedSemanticReferenceJoinOverSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (↥R.semanticCommonSourceField)
      (CommonCurveAmbient K) :=
  extendScalars
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)

/-- The concrete semantic/reference joint field is finite over the literal
common coefficient/source field. -/
theorem selectedSemanticReferenceJoinOverSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind)) := by
  let := R.selectedSemanticBranchExtension_finiteDimensional L
  exact FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
    (R.referenceSemanticJoin_le_selectedSemanticReferenceJoin L hind)
    (R.referenceSemanticJoinOverSource_finiteDimensional L hind)
    (FiniteExtensionCompositum.over_finiteDimensional
      R.semanticCommonSourceField (R.referenceSemanticJoin L hind)
        (R.selectedSemanticBranchExtension L)
        (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))

/-- One concrete normal closure, before canonicalization, of the
transported reference cover and all four selected semantic right branches. -/
def selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (↥R.semanticCommonSourceField)
      (CommonCurveAmbient K) :=
  FiniteCover.normalClosureOver
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)

/-- The entire selected joint field embeds in its concrete normal closure
after restriction to the ground field. -/
theorem selectedSemanticReferenceJoin_le_normalField_restrictScalars
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.selectedSemanticReferenceJoin L hind ≤
      (R.selectedSemanticReferenceNormalField L hind).restrictScalars k := by
  change extendScalars
      (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind) ≤
    R.selectedSemanticReferenceNormalField L hind
  exact FiniteCover.extendScalars_le_normalClosureOver
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)

/-- All four complete common-base semantic right branches lie in the one
selected semantic/reference normal closure. -/
theorem fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k := by
  let hJ := R.selectedSemanticReferenceJoin_le_normalField_restrictScalars L hind
  exact ⟨(R.seSemanticRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAaSemanticRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sbSemanticRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAcSemanticRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ⟩

/-- The concrete selected normal field canonicalized once over the common
source. -/
def selectedSemanticReferenceSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.semanticCommonSourceField) where
  field := FiniteCover.canonicalNormalClosure
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
  finiteDimensional :=
    FiniteCover.canonicalNormalClosure_finiteDimensional
      (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
      (R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind)
  normal := by
    let : FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(extendScalars
          (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind))) := by
      change FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(R.selectedSemanticReferenceJoinOverSource L hind))
      exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
    exact FiniteCover.canonicalNormalClosure_normal
      (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
      (Algebra.IsAlgebraic.of_finite _ _)

/-- The concrete selected normal field and its once-canonicalized cover are
equivalent over the full common coefficient/source field. -/
noncomputable def selectedSemanticReferenceNormalEquivSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedSemanticReferenceNormalField L hind)) ≃ₐ[
      ↥R.semanticCommonSourceField]
      (↥(R.selectedSemanticReferenceSourceCover L hind).field) := by
  let hJ := R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars hJ)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  exact FiniteCover.normalClosureOverEquivCanonical hJ
    (Algebra.IsAlgebraic.of_finite _ _)

/-- The unique canonicalization map selected for the concrete joint normal
field. -/
noncomputable def ambientSelectedSemanticReferenceNormalFieldToSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedSemanticReferenceNormalField L hind)) →ₐ[k]
      (↥(R.selectedSemanticReferenceSourceCover L hind).field) :=
  (R.selectedSemanticReferenceNormalEquivSourceCover L hind).toAlgHom
    |>.restrictScalars k

/-- Literal inclusion of the common-base `e` right branch into the concrete
selected normal field. -/
noncomputable def seSemanticRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.1 hz)

/-- Canonicalize the selected semantic `e` branch after its literal ambient
inclusion. -/
noncomputable def seSemanticRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.seSemanticRightBranchToSelectedNormalRingHom L hind)

/-- One literal normal source containing both the established coherent
semantic branch-comparison cover and the once-canonicalized selected
semantic/reference cover.  This is the comparison field in which the old
four-face branch anchors and the new intrinsic coefficient embeddings can
be related without another independent canonicalization. -/
noncomputable def selectedGraphSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.branchComparisonSourceCover hind).sup
    (R.selectedSemanticReferenceSourceCover L hind)

/-- The coherent semantic branch-comparison cover is a literal subcover of
the selected graph source. -/
theorem branchComparisonSourceCover_le_selectedGraphSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.branchComparisonSourceCover hind).field ≤
      (R.selectedGraphSourceCover L hind).field :=
  le_sup_left

/-- The selected semantic/reference cover is a literal subcover of the
same graph source. -/
theorem selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedSemanticReferenceSourceCover L hind).field ≤
      (R.selectedGraphSourceCover L hind).field :=
  le_sup_right

/-- Literal inclusion of the coherent semantic comparison cover into the
selected graph source. -/
noncomputable def branchComparisonSourceCoverToSelectedGraphSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.branchComparisonSourceCover hind).field →ₐ[k]
      (R.selectedGraphSourceCover L hind).field :=
  (IntermediateField.inclusion
    (R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind))
      |>.restrictScalars k

/-- The same literal subcover inclusion, retaining its algebra structure
over the full common curve source. -/
noncomputable def branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.branchComparisonSourceCover hind).field) →ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) :=
  IntermediateField.inclusion
    (R.branchComparisonSourceCover_le_selectedGraphSourceCover L hind)

/-- Extend the `s·e=u` coefficient/source chart from the coherent semantic
subcover to the entire selected graph source. -/
noncomputable def seSelectedGraphSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.seRepeatedUTotalAnchorAlignmentAut hind)

/-- Extend the `sA·a=u` coefficient/source chart to the selected graph
source. -/
noncomputable def sAaSelectedGraphSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.sAaRepeatedUTotalAnchorAlignmentAut hind)

/-- Extend the `s·b=uB` coefficient/source chart to the selected graph
source. -/
noncomputable def sbSelectedGraphSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.sbRepeatedUBTotalAnchorAlignmentAut hind)

/-- Extend the `sA·c=uB` coefficient/source chart to the selected graph
source. -/
noncomputable def sAcSelectedGraphSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource L hind)
    (R.sAcRepeatedUBTotalAnchorAlignmentAut hind)

/-- The strict `s·e=u` composition triangle acting on the unified selected
graph source. -/
noncomputable def seSelectedGraphCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    (R.selectedGraphSourceCover L hind)

/-- The strict `sA·a=u` composition triangle on the same unified source. -/
noncomputable def sAaSelectedGraphCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (R.selectedGraphSourceCover L hind)

/-- The strict `s·b=uB` composition triangle on the unified source. -/
noncomputable def sbSelectedGraphCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.selectedGraphSourceCover L hind)

/-- The strict `sA·c=uB` composition triangle on the unified source. -/
noncomputable def sAcSelectedGraphCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (R.selectedGraphSourceCover L hind)

/-- Literal inclusion of the once-canonicalized selected cover into the
selected graph source. -/
noncomputable def selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedSemanticReferenceSourceCover L hind).field) →ₐ[k]
      (↥(R.selectedGraphSourceCover L hind).field) :=
  IntermediateField.inclusion (show
    (R.selectedSemanticReferenceSourceCover L hind).field.restrictScalars k ≤
      (R.selectedGraphSourceCover L hind).field.restrictScalars k from
    R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover L hind)

/-- The selected semantic face extension lies in the one concrete normal
field used for the semantic/reference comparison. -/
theorem selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.selectedSemanticBranchExtension L ≤
      R.selectedSemanticReferenceNormalField L hind := by
  intro z hz
  apply FiniteCover.extendScalars_le_normalClosureOver
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
  exact R.selectedSemanticBranchExtension_le_selectedSemanticReferenceJoin
    L hind hz

set_option synthInstance.maxHeartbeats 100000 in
-- The nested scalar-tower search for the whole-face algebra map exceeds the default budget.
/-- One coherent embedding of the entire selected semantic face extension
into the unified graph source.  All four facewise branch anchors below are
restrictions of this single map, so their shared coordinates cannot acquire
independent deck corrections. -/
noncomputable def selectedSemanticBranchExtensionToSelectedGraphSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedSemanticBranchExtension L)) →ₐ[
      ↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField]
      (↥(R.selectedGraphSourceCover L hind).field) :=
  (IntermediateField.inclusion
    (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
      L hind)).comp
    ((R.selectedSemanticReferenceNormalEquivSourceCover L hind).toAlgHom.comp
      (IntermediateField.inclusion
        (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
          L hind)))

/-- The selected common-base semantic `e` branch in the graph source. -/
noncomputable def seSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seSemanticRightBranchToSelectedSourceRingHom L hind)

/-- A canonical finite normal cover of the semantic source field containing
the transported normalized reference field. -/
def transportedReferenceSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.semanticCommonSourceField) where
  field := FiniteCover.canonicalNormalClosure
    (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
  finiteDimensional :=
    FiniteCover.canonicalNormalClosure_finiteDimensional
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
      (R.referenceSemanticJoinOverSource_finiteDimensional L hind)
  normal := by
    let : FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(extendScalars
          (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))) := by
      change FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(R.referenceSemanticJoinOverSource L hind))
      exact R.referenceSemanticJoinOverSource_finiteDimensional L hind
    exact FiniteCover.canonicalNormalClosure_normal
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
      (Algebra.IsAlgebraic.of_finite _ _)

/-- One finite normal source cover now contains both the complete semantic
four-arrow branch cover and a transported copy of the explicit normalized
`B/T` reference cover. -/
def referenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.semanticCommonSourceField) :=
  (R.branchComparisonSourceCover hind).sup
    (R.transportedReferenceSourceCover L hind)

/-- Literal inclusion of the intrinsic selected-`B` germ coefficient field
in the rank-two parameter field generated by the selected `B` tuple. -/
def bGermCoefficientToSelectedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(rankTwoParameterField (k := k) w.bReps)) :=
  IntermediateField.inclusion (show w.bGermCoefficientField hψ ≤
      rankTwoParameterField (k := k) w.bReps from by
    intro z hz
    change z ∈ w.bField
    exact w.bGermCoefficientField_le_bField hψ hz)

/-- Canonical transport of intrinsic selected-`B` germ coefficients to the
parameter field of an arbitrary `B/T` projection realization. -/
noncomputable def bGermCoefficientToProjectionParameterAlgHom
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(rankTwoParameterField (k := k) p)) :=
  (locusFunctionFieldEquivOfIdealEq
      (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)).toAlgHom.comp
    (bGermCoefficientToSelectedBParameterAlgHom (w := w) (hψ := hψ))

/-- The selected `B` correspondence family transported into the common
curve ambient field. -/
abbrev mappedSelectedBFamily :
    FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2 :=
  (w.yzCorrespondenceFamilyMember hψ).map
    (commonCurveEmbedding (k := k) (K := K))

/-- The original selected `B` parameter field is canonically identified
with the parameter field of any relocated mapped `B` family member on the
same complete family locus. -/
noncomputable def selectedBToRelocatedBParameterEquiv
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal) :
    (↥w.bField) ≃ₐ[k] (↥G.parameterField) :=
  ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
      (commonCurveEmbedding (k := k) (K := K))).trans
    ((mappedSelectedBFamily (w := w) (hψ := hψ)).parameterEquivOfIdealEq
      G h)

/-- The selected-to-relocated parameter equivalence sends every original
`B` parameter coordinate to the corresponding relocated coordinate. -/
@[simp] theorem selectedBToRelocatedBParameterEquiv_apply
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (i : Fin 2) :
    selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ) G h
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      ⟨G.parameter i, IntermediateField.subset_adjoin k _
        (Set.mem_range_self i)⟩ := by
  change (((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
      (commonCurveEmbedding (k := k) (K := K))).trans
        ((mappedSelectedBFamily (w := w) (hψ := hψ)).parameterEquivOfIdealEq
          G h))
      ⟨(w.yzCorrespondenceFamilyMember hψ).parameter i,
        IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩ = _
  rw [AlgEquiv.trans_apply]
  rw [FiniteCorrespondenceFamilyMember.parameterMapEquiv_apply]
  rw [FiniteCorrespondenceFamilyMember.parameterEquivOfIdealEq_apply]

/-- Mapping a displayed rank-two parameter tuple into the common curve
ambient field gives a canonical equivalence of its parameter fields. -/
noncomputable def rankTwoParameterCurveEquiv (p : Fin 2 → K) :
    (↥(rankTwoParameterField (k := k) p)) ≃ₐ[k]
      (↥(rankTwoParameterField (k := k)
        (commonCurveEmbedding (k := k) (K := K) ∘ p))) :=
  ((rankTwoParameterField (k := k) p).equivMap
      (commonCurveEmbedding (k := k) (K := K))).trans
    (IntermediateField.equivOfEq (by
      rw [rankTwoParameterField, IntermediateField.adjoin_map]
      congr 1
      ext z
      simp))

/-- The mapped parameter equivalence sends every displayed coordinate to
its literal image in the common curve ambient field. -/
@[simp] theorem rankTwoParameterCurveEquiv_apply
    (p : Fin 2 → K) (i : Fin 2) :
    rankTwoParameterCurveEquiv (k := k) (K := K) p
        ⟨p i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      ⟨commonCurveEmbedding (k := k) (K := K) (p i),
        IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  rfl

/-- If a relocated family displays the mapped tuple `p`, the preceding
equivalence lands in that family's literal parameter field. -/
noncomputable def rankTwoParameterCurveEquivToFamily
    (p : Fin 2 → K)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥(rankTwoParameterField (k := k) p)) ≃ₐ[k]
      (↥G.parameterField) :=
  (rankTwoParameterCurveEquiv (k := k) (K := K) p).trans
    (IntermediateField.equivOfEq (by
      rw [FiniteCorrespondenceFamilyMember.parameterField, hG]
      rfl))

/-- The parameter-field equivalence into a relocated family sends each
displayed coordinate to that family's corresponding parameter. -/
@[simp] theorem rankTwoParameterCurveEquivToFamily_apply
    (p : Fin 2 → K)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (i : Fin 2) :
    rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) p G hG
        ⟨p i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩ =
      ⟨G.parameter i, IntermediateField.subset_adjoin k _
        (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  simp [rankTwoParameterCurveEquivToFamily, hG]

/-- Equality of the full mapped family locus and equality of the normalized
`B/T` scalar locus induce the same parameter-field transport. -/
theorem selectedBToRelocatedBParameterEquiv_eq_projection
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ) G h =
      (locusFunctionFieldEquivOfIdealEq
        (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)).trans
      (rankTwoParameterCurveEquivToFamily
          (k := k) (K := K) p G hG) := by
  apply AlgEquiv.coe_toAlgHom_injective
  unfold QWitness.bField
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  change ↑(selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ) G h
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩) =
    ↑(((locusFunctionFieldEquivOfIdealEq
          (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)).trans
        (rankTwoParameterCurveEquivToFamily
          (k := k) (K := K) p G hG))
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩)
  apply Subtype.ext
  calc
    _ = G.parameter i := by
      exact congrArg Subtype.val
        (selectedBToRelocatedBParameterEquiv_apply
          (w := w) (hψ := hψ) G h i)
    _ = ↑(((locusFunctionFieldEquivOfIdealEq
          (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)).trans
        (rankTwoParameterCurveEquivToFamily
          (k := k) (K := K) p G hG))
        ⟨w.bReps i, IntermediateField.subset_adjoin k _
          (Set.mem_range_self i)⟩) := by
      rw [AlgEquiv.trans_apply]
      rw [locusFunctionFieldEquivOfIdealEq_apply]
      exact (congrArg Subtype.val
        (rankTwoParameterCurveEquivToFamily_apply
          (k := k) (K := K) p G hG i)).symm

/-- The canonical transport of intrinsic selected-`B` coefficients to a
relocated family is a map on the whole intrinsic coefficient field, not
merely a list of coordinate formulas. -/
noncomputable def bGermCoefficientToRelocatedBParameterAlgHom
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k] (↥G.parameterField) :=
  (rankTwoParameterCurveEquivToFamily
      (k := k) (K := K) p G hG).toAlgHom.comp
    (bGermCoefficientToProjectionParameterAlgHom
      (w := w) (hψ := hψ) hp)

/-- Include the intrinsic coefficient field of a relocated canonical curve
in its complete selected right-branch field.  The map uses only literal
ambient inclusions: coefficients first lie in the displayed parameter
field, hence in the curve source field, and finally in the complete branch
over that source. -/
noncomputable def relocatedBCoefficientToCompleteRightBranchRingHom
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2) :
    (↥(G.toPair.curveCoefficientField k G.parameterField)) →+*
      (↥G.toPair.branchOverSource) where
  toFun z := ⟨z.1, by
    let zP : G.parameterField :=
      ⟨z.1, G.toPair.curveCoefficientField_le k G.parameterField z.2⟩
    let zS : G.toPair.sourceField :=
      ⟨z.1, G.toPair.sourceField.algebraMap_mem zP⟩
    have hz := G.toPair.branchOverSource.algebraMap_mem zS
    simpa [zS] using hz⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

/-- The mapped selected `B` family locus equals the relocated right-family
locus in the `s·e=u` face. -/
theorem seMappedSelectedBFamily_ideal_eq :
    (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal =
      (R.se.bCorrespondenceFamilyMember hψ).ideal := by
  exact (R.se.bFamilyLocus hψ).symm

/-- The mapped selected `B` family locus equals the relocated right-family
locus in the `sA·a=u` face. -/
theorem sAaMappedSelectedBFamily_ideal_eq :
    (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal =
      (R.sAa.bCorrespondenceFamilyMember hψ).ideal := by
  exact (R.sAa.bFamilyLocus hψ).symm

/-- The mapped selected `B` family locus equals the relocated right-family
locus in the `s·b=uB` face. -/
theorem sbMappedSelectedBFamily_ideal_eq :
    (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal =
      (R.sb.bCorrespondenceFamilyMember hψ).ideal := by
  exact (R.sb.bFamilyLocus hψ).symm

/-- The mapped selected `B` family locus equals the relocated right-family
locus in the `sA·c=uB` face. -/
theorem sAcMappedSelectedBFamily_ideal_eq :
    (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal =
      (R.sAc.bCorrespondenceFamilyMember hψ).ideal := by
  exact (R.sAc.bFamilyLocus hψ).symm

/-- The complete selected `B` branch is equivalent to the relocated
complete right branch on the `e` face, using equality of the full family
loci rather than only their coefficient fields. -/
noncomputable def seSelectedBCompleteBranchRingEquiv :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) ≃+*
      (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ))
    |>.completeBranchRingEquivOfIdealEq
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq

/-- The corresponding complete-branch equivalence on the `a` face. -/
noncomputable def sAaSelectedBCompleteBranchRingEquiv :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) ≃+*
      (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ))
    |>.completeBranchRingEquivOfIdealEq
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq

/-- The corresponding complete-branch equivalence on the `b` face. -/
noncomputable def sbSelectedBCompleteBranchRingEquiv :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) ≃+*
      (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ))
    |>.completeBranchRingEquivOfIdealEq
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq

/-- The corresponding complete-branch equivalence on the algebraic `c`
face. -/
noncomputable def sAcSelectedBCompleteBranchRingEquiv :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) ≃+*
      (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ))
    |>.completeBranchRingEquivOfIdealEq
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq

/-- The selected-branch-corrected normal-cover equivalence from the mapped
selected `B` family to the relocated `e` family. -/
noncomputable def seSelectedBNormalCoverRingEquiv :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) ≃+*
      (↥(FiniteCover.normalClosureOver
        (R.se.bCorrespondenceFamilyMember hψ
          |>.parameterSourceField_le_familyField))) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ)
    |>.basedNormalEquivOfIdealEq
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq).toRingEquiv

/-- The corresponding corrected normal-cover equivalence for the relocated
`a` family. -/
noncomputable def sAaSelectedBNormalCoverRingEquiv :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) ≃+*
      (↥(FiniteCover.normalClosureOver
        (R.sAa.bCorrespondenceFamilyMember hψ
          |>.parameterSourceField_le_familyField))) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ)
    |>.basedNormalEquivOfIdealEq
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq).toRingEquiv

/-- The corresponding corrected normal-cover equivalence for the relocated
`b` family. -/
noncomputable def sbSelectedBNormalCoverRingEquiv :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) ≃+*
      (↥(FiniteCover.normalClosureOver
        (R.sb.bCorrespondenceFamilyMember hψ
          |>.parameterSourceField_le_familyField))) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ)
    |>.basedNormalEquivOfIdealEq
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq).toRingEquiv

/-- The corresponding corrected normal-cover equivalence for the algebraic
relocated `c` family. -/
noncomputable def sAcSelectedBNormalCoverRingEquiv :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) ≃+*
      (↥(FiniteCover.normalClosureOver
        (R.sAc.bCorrespondenceFamilyMember hψ
          |>.parameterSourceField_le_familyField))) :=
  (mappedSelectedBFamily (w := w) (hψ := hψ)
    |>.basedNormalEquivOfIdealEq
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq).toRingEquiv

/-- Rebase the native normal cover of a relocated right-family member to
the one selected semantic/reference joint field.  The construction retains
the native normal field as a named selected subextension. -/
noncomputable def relocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥(R.selectedSemanticReferenceJoin L hind)) := by
  let N := FiniteCover.normalClosureOver
    G.parameterSourceField_le_familyField
  letI : FiniteDimensional (↥G.parameterSourceField)
      (↥(extendScalars G.parameterSourceField_le_familyField)) :=
    G.familyOverParameterSource_finiteDimensional
  letI : FiniteDimensional (↥G.parameterSourceField) (↥N) :=
    FiniteCover.normalClosureOver_finiteDimensional
      G.parameterSourceField_le_familyField
      G.familyOverParameterSource_finiteDimensional
  exact FiniteExtensionCompositum.canonicalCover
    G.parameterSourceField (R.selectedSemanticReferenceJoin L hind) N hG

/-- The selected native normal field embeds in its scalar-rebased canonical
cover through the branch-preserving map of the finite-basis compositum. -/
noncomputable def relocatedRightNormalToRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind) :
    (↥(FiniteCover.normalClosureOver
      G.parameterSourceField_le_familyField)) →+*
      (↥(R.relocatedRightRebasedCover L hind G hG).field) := by
  let N := FiniteCover.normalClosureOver
    G.parameterSourceField_le_familyField
  letI : FiniteDimensional (↥G.parameterSourceField)
      (↥(extendScalars G.parameterSourceField_le_familyField)) :=
    G.familyOverParameterSource_finiteDimensional
  letI : FiniteDimensional (↥G.parameterSourceField) (↥N) :=
    FiniteCover.normalClosureOver_finiteDimensional
      G.parameterSourceField_le_familyField
      G.familyOverParameterSource_finiteDimensional
  exact FiniteExtensionCompositum.originalToCanonicalRingHom
    G.parameterSourceField (R.selectedSemanticReferenceJoin L hind) N hG

/-- The scalar-rebased native normal cover for the `e` right face. -/
noncomputable def seRelocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.relocatedRightRebasedCover L hind
    (R.se.bCorrespondenceFamilyMember hψ)
    (R.seRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)

/-- The scalar-rebased native normal cover for the `a` right face. -/
noncomputable def sAaRelocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.relocatedRightRebasedCover L hind
    (R.sAa.bCorrespondenceFamilyMember hψ)
    (R.sAaRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)

/-- The scalar-rebased native normal cover for the `b` right face. -/
noncomputable def sbRelocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.relocatedRightRebasedCover L hind
    (R.sb.bCorrespondenceFamilyMember hψ)
    (R.sbRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)

/-- The scalar-rebased native normal cover for the algebraic `c` right
face. -/
noncomputable def sAcRelocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.relocatedRightRebasedCover L hind
    (R.sAc.bCorrespondenceFamilyMember hψ)
    (R.sAcRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)

/-- One finite normal cover over the selected joint field containing all
four scalar-rebased relocated right normal covers. -/
noncomputable def fourRelocatedRightRebasedCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (((R.seRelocatedRightRebasedCover L hind).sup
      (R.sAaRelocatedRightRebasedCover L hind)).sup
        (R.sbRelocatedRightRebasedCover L hind)).sup
      (R.sAcRelocatedRightRebasedCover L hind)

/-- Carry one relocated native normal cover through scalar rebase and into
the common four-face right cover. -/
noncomputable def relocatedRightNormalToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind)
    (hcover : (R.relocatedRightRebasedCover L hind G hG).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field) :
    (↥(FiniteCover.normalClosureOver
      G.parameterSourceField_le_familyField)) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (IntermediateField.inclusion hcover).toRingHom.comp
    (R.relocatedRightNormalToRebasedCoverRingHom L hind G hG)

/-- Carry the complete selected branch of one relocated right-family member
through its native normal cover, its branch-preserving scalar rebase, and
finally the literal inclusion in the four-face right cover. -/
noncomputable def relocatedCompleteBranchToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameterSourceField ≤
      R.selectedSemanticReferenceJoin L hind)
    (hcover : (R.relocatedRightRebasedCover L hind G hG).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field) :
    (↥G.toPair.branchOverSource) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedRightNormalToFourRebasedCoverRingHom
    L hind G hG hcover).comp G.completeBranchToNormalCoverRingHom

/-- The literal common semantic source included in the selected joint
field.  Naming this map lets the algebraic-closure transport expose its
coefficient square without installing a global scalar-tower instance. -/
def semanticSourceToSelectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥R.semanticCommonSourceField) →ₐ[k]
      (↥(R.selectedSemanticReferenceJoin L hind)) :=
  IntermediateField.inclusion
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)

/-- A chosen equivalence from the algebraic closure of the finite selected
joint field to the algebraic closure of the literal common semantic source.
It is linear over the smaller source field internally, but is exposed as a
ring equivalence so its type does not retain a locally installed tower. -/
noncomputable def selectedJointAlgebraicClosureRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)) ≃+*
      AlgebraicClosure (↥R.semanticCommonSourceField) := by
  let hSJ :=
    R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) :=
    (IntermediateField.inclusion hSJ).toAlgebra
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  exact (IsAlgClosure.equivOfAlgebraic
    (↥R.semanticCommonSourceField)
    (↥(R.selectedSemanticReferenceJoin L hind))
    (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
    (AlgebraicClosure (↥R.semanticCommonSourceField))).toRingEquiv

/-- The chosen algebraic-closure equivalence carries the embedded literal
semantic source to its canonical copy in the target algebraic closure. -/
@[simp] theorem selectedJointAlgebraicClosureRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.selectedJointAlgebraicClosureRingEquiv L hind
        (algebraMap (↥(R.selectedSemanticReferenceJoin L hind))
          (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
          (R.semanticSourceToSelectedSemanticReferenceJoin L hind x)) =
      algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField)) x := by
  let hSJ :=
    R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind
  let : Algebra (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) :=
    (IntermediateField.inclusion hSJ).toAlgebra
  let : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  change (IsAlgClosure.equivOfAlgebraic
      (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind))
      (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
      (AlgebraicClosure (↥R.semanticCommonSourceField)))
        (algebraMap (↥(R.selectedSemanticReferenceJoin L hind))
          (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
          (algebraMap (↥R.semanticCommonSourceField)
            (↥(R.selectedSemanticReferenceJoin L hind)) x)) = _
  rw [← IsScalarTower.algebraMap_apply
    (↥R.semanticCommonSourceField)
    (↥(R.selectedSemanticReferenceJoin L hind))
    (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))]
  exact (IsAlgClosure.equivOfAlgebraic
    (↥R.semanticCommonSourceField)
    (↥(R.selectedSemanticReferenceJoin L hind))
    (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
    (AlgebraicClosure (↥R.semanticCommonSourceField))).commutes x

/-- The image of the common four-face right cover in the algebraic closure
of the literal semantic source.  It is finite over that smaller source,
although it need not yet be normal there. -/
def fourRelocatedRightTransportedField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    IntermediateField (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)) where
  carrier := R.selectedJointAlgebraicClosureRingEquiv L hind ''
    (R.fourRelocatedRightRebasedCover L hind).field
  zero_mem' := ⟨0,
    (R.fourRelocatedRightRebasedCover L hind).field.zero_mem, by simp⟩
  one_mem' := ⟨1,
    (R.fourRelocatedRightRebasedCover L hind).field.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y,
      (R.fourRelocatedRightRebasedCover L hind).field.add_mem hx hy,
      by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y,
      (R.fourRelocatedRightRebasedCover L hind).field.mul_mem hx hy,
      by simp⟩
  algebraMap_mem' := fun x ↦
    ⟨algebraMap (↥(R.selectedSemanticReferenceJoin L hind))
        (AlgebraicClosure (↥(R.selectedSemanticReferenceJoin L hind)))
        (R.semanticSourceToSelectedSemanticReferenceJoin L hind x),
      (R.fourRelocatedRightRebasedCover L hind).field.algebraMap_mem _,
      R.selectedJointAlgebraicClosureRingEquiv_algebraMap L hind x⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹,
      (R.fourRelocatedRightRebasedCover L hind).field.inv_mem hx,
      by simp⟩

/-- Restriction of the chosen algebraic-closure equivalence identifies the
four-face right cover with its transported image. -/
def fourRelocatedRightTransportedFieldRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.fourRelocatedRightRebasedCover L hind).field) ≃+*
      (↥(R.fourRelocatedRightTransportedField L hind)) where
  toFun x := ⟨R.selectedJointAlgebraicClosureRingEquiv L hind x,
    ⟨x, x.2, rfl⟩⟩
  invFun y :=
    ⟨(R.selectedJointAlgebraicClosureRingEquiv L hind).symm y, by
      obtain ⟨x, hx, hxy⟩ := y.2
      have : (R.selectedJointAlgebraicClosureRingEquiv L hind).symm y = x := by
        rw [← hxy]
        simp
      exact this ▸ hx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- On the literal common source, the restricted field equivalence is the
canonical algebra map. -/
@[simp] theorem fourRelocatedRightTransportedFieldRingEquiv_source
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.fourRelocatedRightTransportedFieldRingEquiv L hind
        (algebraMap (↥(R.selectedSemanticReferenceJoin L hind))
          (↥(R.fourRelocatedRightRebasedCover L hind).field)
          (R.semanticSourceToSelectedSemanticReferenceJoin L hind x)) =
      algebraMap (↥R.semanticCommonSourceField)
        (↥(R.fourRelocatedRightTransportedField L hind)) x := by
  apply Subtype.ext
  exact R.selectedJointAlgebraicClosureRingEquiv_algebraMap L hind x

/-- The transported four-face field is finite over the literal semantic
source: first use finiteness of the selected joint field, then finiteness of
the four-face cover, and finally the restricted field equivalence. -/
theorem fourRelocatedRightTransportedField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.fourRelocatedRightTransportedField L hind)) := by
  let hSJ :=
    R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind
  let : Algebra (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) :=
    (IntermediateField.inclusion hSJ).toAlgebra
  let : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  let : FiniteDimensional (↥(R.selectedSemanticReferenceJoin L hind))
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
    (R.fourRelocatedRightRebasedCover L hind).finiteDimensional
  let : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
    FiniteDimensional.trans
      (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoin L hind))
      (↥(R.fourRelocatedRightRebasedCover L hind).field)
  apply Module.Finite.of_equiv_equiv
    (RingEquiv.refl (↥R.semanticCommonSourceField))
    (R.fourRelocatedRightTransportedFieldRingEquiv L hind)
  apply RingHom.ext
  intro x
  exact
    (R.fourRelocatedRightTransportedFieldRingEquiv_source L hind x).symm

/-- Normal closure of the transported four-face right field over the
literal common semantic source. -/
def fourRelocatedRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.semanticCommonSourceField) where
  field := normalClosure (↥R.semanticCommonSourceField)
    (↥(R.fourRelocatedRightTransportedField L hind))
    (AlgebraicClosure (↥R.semanticCommonSourceField))
  finiteDimensional := by
    let : FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(R.fourRelocatedRightTransportedField L hind)) :=
      R.fourRelocatedRightTransportedField_finiteDimensional L hind
    exact normalClosure.is_finiteDimensional
      (↥R.semanticCommonSourceField)
      (↥(R.fourRelocatedRightTransportedField L hind))
      (AlgebraicClosure (↥R.semanticCommonSourceField))
  normal := by
    let : FiniteDimensional (↥R.semanticCommonSourceField)
        (↥(R.fourRelocatedRightTransportedField L hind)) :=
      R.fourRelocatedRightTransportedField_finiteDimensional L hind
    let : Algebra.IsAlgebraic (↥R.semanticCommonSourceField)
        (↥(R.fourRelocatedRightTransportedField L hind)) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact
      (Algebra.IsAlgebraic.isNormalClosure_normalClosure
        (F := ↥R.semanticCommonSourceField)
        (K := ↥(R.fourRelocatedRightTransportedField L hind))
        (L := AlgebraicClosure (↥R.semanticCommonSourceField))
        (fun _ ↦ IsAlgClosed.splits _)).normal

/-- One final source cover containing both all established graph/source
coherence and the transported common four-face right cover. -/
noncomputable def selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphSourceCover L hind).sup
    (R.fourRelocatedRightSourceCover L hind)

/-- Lift the coefficient-moving `e→a` automorphism of the literal semantic
source to its chosen algebraic closure. -/
noncomputable def rightACommonSourceClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport (↥R.semanticCommonSourceField)
      (↥R.semanticCommonSourceField) :=
  AlgebraicClosureTransport.lift
    (R.commonSourceRightAAut hind).toRingEquiv

/-- Lift the analogous `e→b` semantic-source automorphism. -/
noncomputable def rightBCommonSourceClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport (↥R.semanticCommonSourceField)
      (↥R.semanticCommonSourceField) :=
  AlgebraicClosureTransport.lift
    (R.commonSourceRightBAut hind).toRingEquiv

/-- Lift the genuine `e→c` equivalence from the semantic common source to
the independent algebraic-output source field. -/
noncomputable def rightCSourceClosureTransport
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport (↥R.semanticCommonSourceField)
      (↥R.rightCSourceField) :=
  AlgebraicClosureTransport.lift
    (R.commonSourceToRightCSourceEquiv hind).toRingEquiv

/-- The selected graph/right source cover transported through the genuine
semilinear `e→a` base automorphism. -/
noncomputable def rightASelectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceCover L hind).map
    (R.rightACommonSourceClosureTransport hind)

/-- The corresponding finite normal source cover for the `e→b` chart. -/
noncomputable def rightBSelectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceCover L hind).map
    (R.rightBCommonSourceClosureTransport hind)

/-- The selected graph/right source transported to a finite normal cover
over the genuinely different `c` source field. -/
noncomputable def rightCSelectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceCover L hind).map
    (R.rightCSourceClosureTransport hind)

/-- Restriction of the lifted `a` algebraic-closure transport to the finite
selected graph/right source cover. -/
noncomputable def selectedGraphRightSourceToRightARingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      (↥(R.rightASelectedGraphRightSourceCover L hind).field) :=
  (R.selectedGraphRightSourceCover L hind).mapEquiv
    (R.rightACommonSourceClosureTransport hind)

/-- Restriction of the lifted `b` transport to the same finite source
cover. -/
noncomputable def selectedGraphRightSourceToRightBRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      (↥(R.rightBSelectedGraphRightSourceCover L hind).field) :=
  (R.selectedGraphRightSourceCover L hind).mapEquiv
    (R.rightBCommonSourceClosureTransport hind)

/-- Restriction of the lifted `c` base change to the finite selected
graph/right source cover. -/
noncomputable def selectedGraphRightSourceToRightCRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      (↥(R.rightCSelectedGraphRightSourceCover L hind).field) :=
  (R.selectedGraphRightSourceCover L hind).mapEquiv
    (R.rightCSourceClosureTransport hind)

/-! ### One finite normal codomain for the four semilinear source charts -/

/-- Rebase the original selected graph/right source cover over the literal
joint source field, retaining its selected embedding. -/
noncomputable def rightESelectedGraphJointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.rightSourceJointField) := by
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (R.selectedGraphRightSourceCover L hind).rebaseCover
    R.semanticSourceToRightSourceJointClosureRingEquiv

/-- Rebase the semilinear `a` image cover over the same joint source. -/
noncomputable def rightASelectedGraphJointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.rightSourceJointField) := by
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (R.rightASelectedGraphRightSourceCover L hind).rebaseCover
    R.semanticSourceToRightSourceJointClosureRingEquiv

/-- Rebase the semilinear `b` image cover over the same joint source. -/
noncomputable def rightBSelectedGraphJointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.rightSourceJointField) := by
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (R.rightBSelectedGraphRightSourceCover L hind).rebaseCover
    R.semanticSourceToRightSourceJointClosureRingEquiv

/-- Rebase the genuine `c` image cover from its distinct source into the
same joint source. -/
noncomputable def rightCSelectedGraphJointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥R.rightSourceJointField) := by
  letI : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    R.rightCSourceToRightSourceJoint.toAlgebra
  exact (R.rightCSelectedGraphRightSourceCover L hind).rebaseCover
    R.rightCSourceToRightSourceJointClosureRingEquiv

/-- One finite normal cover over the joint source containing all four
selected semilinear source images. -/
noncomputable def fourSelectedGraphJointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (((R.rightESelectedGraphJointCover L hind).sup
      (R.rightASelectedGraphJointCover L hind)).sup
        (R.rightBSelectedGraphJointCover L hind)).sup
      (R.rightCSelectedGraphJointCover L hind)

/-- The rebased `e` image is a literal subcover of the four-face joint
cover. -/
theorem rightESelectedGraphJointCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.rightESelectedGraphJointCover L hind).field ≤
      (R.fourSelectedGraphJointCover L hind).field :=
  (le_sup_left.trans le_sup_left).trans le_sup_left

/-- The rebased `a` image is a literal subcover of the four-face joint
cover. -/
theorem rightASelectedGraphJointCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.rightASelectedGraphJointCover L hind).field ≤
      (R.fourSelectedGraphJointCover L hind).field :=
  (le_sup_right.trans le_sup_left).trans le_sup_left

/-- The rebased `b` image is a literal subcover of the four-face joint
cover. -/
theorem rightBSelectedGraphJointCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.rightBSelectedGraphJointCover L hind).field ≤
      (R.fourSelectedGraphJointCover L hind).field :=
  le_sup_right.trans le_sup_left

/-- The rebased `c` image is a literal subcover of the four-face joint
cover. -/
theorem rightCSelectedGraphJointCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.rightCSelectedGraphJointCover L hind).field ≤
      (R.fourSelectedGraphJointCover L hind).field :=
  le_sup_right

set_option maxHeartbeats 800000 in
-- The nested rebase and three-level cover supremum require extra elaboration.
/-- Carry the original selected graph/right source into the `e` leg of the
one four-face joint cover. -/
noncomputable def selectedGraphRightSourceToRightEJointRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field) := by
  letI : Algebra R.semanticCommonSourceType
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (IntermediateField.inclusion
    (R.rightESelectedGraphJointCover_le_four L hind)).toRingHom.comp
      ((R.selectedGraphRightSourceCover L hind).rebaseRingHom
        R.semanticSourceToRightSourceJointClosureRingEquiv
        (fun x ↦ by
          change R.semanticSourceToRightSourceJointClosureRingEquiv
              (algebraMap (↥R.semanticCommonSourceField)
                (AlgebraicClosure (↥R.semanticCommonSourceField)) x) =
            algebraMap (↥R.rightSourceJointField)
              (AlgebraicClosure (↥R.rightSourceJointField))
              (R.semanticSourceToRightSourceJoint x)
          exact
            R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap x))

set_option maxHeartbeats 800000 in
-- The nested rebase and three-level cover supremum require extra elaboration.
/-- Carry the selected source through the semilinear `a` chart and then
into the `a` leg of the joint cover. -/
noncomputable def selectedGraphRightSourceToRightAJointRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field) := by
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (IntermediateField.inclusion
    (R.rightASelectedGraphJointCover_le_four L hind)).toRingHom.comp
      (((R.rightASelectedGraphRightSourceCover L hind).rebaseRingHom
        R.semanticSourceToRightSourceJointClosureRingEquiv
        (fun x ↦ by
          change R.semanticSourceToRightSourceJointClosureRingEquiv
              (algebraMap (↥R.semanticCommonSourceField)
                (AlgebraicClosure (↥R.semanticCommonSourceField)) x) =
            algebraMap (↥R.rightSourceJointField)
              (AlgebraicClosure (↥R.rightSourceJointField))
              (R.semanticSourceToRightSourceJoint x)
          exact
            R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap x)).comp
          (R.selectedGraphRightSourceToRightARingEquiv L hind).toRingHom)

set_option maxHeartbeats 800000 in
-- The nested rebase and three-level cover supremum require extra elaboration.
/-- Carry the selected source through the semilinear `b` chart and then
into the `b` leg of the joint cover. -/
noncomputable def selectedGraphRightSourceToRightBJointRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field) := by
  letI : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  exact (IntermediateField.inclusion
    (R.rightBSelectedGraphJointCover_le_four L hind)).toRingHom.comp
      (((R.rightBSelectedGraphRightSourceCover L hind).rebaseRingHom
        R.semanticSourceToRightSourceJointClosureRingEquiv
        (fun x ↦ by
          change R.semanticSourceToRightSourceJointClosureRingEquiv
              (algebraMap (↥R.semanticCommonSourceField)
                (AlgebraicClosure (↥R.semanticCommonSourceField)) x) =
            algebraMap (↥R.rightSourceJointField)
              (AlgebraicClosure (↥R.rightSourceJointField))
              (R.semanticSourceToRightSourceJoint x)
          exact
            R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap x)).comp
          (R.selectedGraphRightSourceToRightBRingEquiv L hind).toRingHom)

set_option maxHeartbeats 800000 in
-- The nested rebase and three-level cover supremum require extra elaboration.
/-- Carry the selected source through the genuine semilinear `c` chart and
then into the `c` leg of the same joint cover. -/
noncomputable def selectedGraphRightSourceToRightCJointRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field) := by
  letI : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    R.rightCSourceToRightSourceJoint.toAlgebra
  exact (IntermediateField.inclusion
    (R.rightCSelectedGraphJointCover_le_four L hind)).toRingHom.comp
      (((R.rightCSelectedGraphRightSourceCover L hind).rebaseRingHom
        R.rightCSourceToRightSourceJointClosureRingEquiv
        R.rightCSourceToRightSourceJointClosureRingEquiv_algebraMap).comp
          (R.selectedGraphRightSourceToRightCRingEquiv L hind).toRingHom)

/-- The base map underlying the selected `e` embedding into the joint
cover. -/
def rightEToJointBaseRingHom :
    (↥R.semanticCommonSourceField) →+* (↥R.rightSourceJointField) :=
  R.semanticSourceToRightSourceJoint.toRingHom

/-- The base map underlying the selected `a` embedding: first move the
semantic source presentation from `e` to `a`, then use its literal
inclusion in the joint source. -/
noncomputable def rightAToJointBaseRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥R.semanticCommonSourceField) →+* (↥R.rightSourceJointField) :=
  R.semanticSourceToRightSourceJoint.toRingHom.comp
    (R.commonSourceRightAAut hind).toRingEquiv.toRingHom

/-- The analogous full semantic-source map for the `b` presentation. -/
noncomputable def rightBToJointBaseRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥R.semanticCommonSourceField) →+* (↥R.rightSourceJointField) :=
  R.semanticSourceToRightSourceJoint.toRingHom.comp
    (R.commonSourceRightBAut hind).toRingEquiv.toRingHom

/-- The full base map for the genuine `c` presentation, through its
distinct source field and then the literal `Sc → S ⊔ Sc` inclusion. -/
noncomputable def rightCToJointBaseRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥R.semanticCommonSourceField) →+* (↥R.rightSourceJointField) :=
  R.rightCSourceToRightSourceJoint.toRingHom.comp
    (R.commonSourceToRightCSourceEquiv hind).toRingEquiv.toRingHom

/-- The joint source remains finite when its semantic-base algebra
structure is twisted by the `e → a` source automorphism. -/
theorem rightSourceJointOverA_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥R.semanticCommonSourceField)
        (↥R.rightSourceJointField) :=
      (R.rightAToJointBaseRingHom hind).toAlgebra
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) := by
  let S := ↥R.semanticCommonSourceField
  let J := ↥R.rightSourceJointField
  let oldAlgebra : Algebra S J :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  let newAlgebra : Algebra S J :=
    (R.rightAToJointBaseRingHom hind).toAlgebra
  let oldModule : Module S J := oldAlgebra.toModule
  let oldFinite : @Module.Finite S J _ _ oldModule := by
    let : Algebra S J := oldAlgebra
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic)
    exact R.rightSourceJointOverSemantic_finiteDimensional
  let : Algebra S J := newAlgebra
  exact @Module.Finite.of_equiv_equiv S J S J _ _ _ _
    oldAlgebra newAlgebra
    (R.commonSourceRightAAut hind).symm.toRingEquiv
    (RingEquiv.refl J) (by
      apply RingHom.ext
      intro x
      change R.rightAToJointBaseRingHom hind
          ((R.commonSourceRightAAut hind).symm x) =
        R.semanticSourceToRightSourceJoint x
      simp [rightAToJointBaseRingHom]) oldFinite

/-- The same finite-extension transport for the `e → b` source
automorphism. -/
theorem rightSourceJointOverB_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥R.semanticCommonSourceField)
        (↥R.rightSourceJointField) :=
      (R.rightBToJointBaseRingHom hind).toAlgebra
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) := by
  let S := ↥R.semanticCommonSourceField
  let J := ↥R.rightSourceJointField
  let oldAlgebra : Algebra S J :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  let newAlgebra : Algebra S J :=
    (R.rightBToJointBaseRingHom hind).toAlgebra
  let oldModule : Module S J := oldAlgebra.toModule
  let oldFinite : @Module.Finite S J _ _ oldModule := by
    let : Algebra S J := oldAlgebra
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic)
    exact R.rightSourceJointOverSemantic_finiteDimensional
  let : Algebra S J := newAlgebra
  exact @Module.Finite.of_equiv_equiv S J S J _ _ _ _
    oldAlgebra newAlgebra
    (R.commonSourceRightBAut hind).symm.toRingEquiv
    (RingEquiv.refl J) (by
      apply RingHom.ext
      intro x
      change R.rightBToJointBaseRingHom hind
          ((R.commonSourceRightBAut hind).symm x) =
        R.semanticSourceToRightSourceJoint x
      simp [rightBToJointBaseRingHom]) oldFinite

/-- The joint source is finite over the common semantic source through the
genuine `S ≃ Sc` chart used by the `c` leg. -/
theorem rightSourceJointOverCChart_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    letI : Algebra (↥R.semanticCommonSourceField)
        (↥R.rightSourceJointField) :=
      (R.rightCToJointBaseRingHom hind).toAlgebra
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) := by
  let S := ↥R.semanticCommonSourceField
  let Sc := ↥R.rightCSourceField
  let J := ↥R.rightSourceJointField
  let oldAlgebra : Algebra Sc J :=
    R.rightCSourceToRightSourceJoint.toAlgebra
  let newAlgebra : Algebra S J :=
    (R.rightCToJointBaseRingHom hind).toAlgebra
  let oldModule : Module Sc J := oldAlgebra.toModule
  let oldFinite : @Module.Finite Sc J _ _ oldModule := by
    let : Algebra Sc J := oldAlgebra
    change FiniteDimensional (↥R.rightCSourceField)
      (↥R.rightSourceJointOverC)
    exact R.rightSourceJointOverC_finiteDimensional
  let : Algebra S J := newAlgebra
  exact @Module.Finite.of_equiv_equiv Sc J S J _ _ _ _
    oldAlgebra newAlgebra
    (R.commonSourceToRightCSourceEquiv hind).symm.toRingEquiv
    (RingEquiv.refl J) (by
      apply RingHom.ext
      intro x
      change R.rightCToJointBaseRingHom hind
          ((R.commonSourceToRightCSourceEquiv hind).symm x) =
        R.rightCSourceToRightSourceJoint x
      simp [rightCToJointBaseRingHom]) oldFinite

set_option synthInstance.maxHeartbeats 100000 in
-- The nested selected source algebra map needs additional instance search.
set_option maxHeartbeats 800000 in
-- The selected map unfolds through a finite-basis rebase and a three-level supremum.
/-- On the entire semantic source field, not only on its nine displayed
generators, the selected `e` embedding extends the literal joint-source
inclusion. -/
@[simp] theorem selectedGraphRightSourceToRightEJointRingHom_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.selectedGraphRightSourceToRightEJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightEToJointBaseRingHom x) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap x

set_option synthInstance.maxHeartbeats 100000 in
-- The nested selected source algebra map needs additional instance search.
set_option maxHeartbeats 800000 in
-- The selected map unfolds through semilinear transport and finite-basis rebase.
/-- The selected `a` embedding extends its full coefficient-moving base
map into the joint source. -/
@[simp] theorem selectedGraphRightSourceToRightAJointRingHom_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.selectedGraphRightSourceToRightAJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightAToJointBaseRingHom hind x) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.semanticSourceToRightSourceJointClosureRingEquiv
      ((R.rightACommonSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField)) x)) = _
  rw [AlgebraicClosureTransport.commutes_apply]
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap _

set_option synthInstance.maxHeartbeats 100000 in
-- The nested selected source algebra map needs additional instance search.
set_option maxHeartbeats 800000 in
-- The selected map unfolds through semilinear transport and finite-basis rebase.
/-- The selected `b` embedding likewise extends its full source map. -/
@[simp] theorem selectedGraphRightSourceToRightBJointRingHom_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.selectedGraphRightSourceToRightBJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightBToJointBaseRingHom hind x) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.semanticSourceToRightSourceJointClosureRingEquiv
      ((R.rightBCommonSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField)) x)) = _
  rw [AlgebraicClosureTransport.commutes_apply]
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap _

set_option synthInstance.maxHeartbeats 100000 in
-- The nested selected source algebra map needs additional instance search.
set_option maxHeartbeats 800000 in
-- The genuine c map passes through two different source algebraic closures.
/-- The selected `c` embedding extends the full `S → Sc → S ⊔ Sc` base
map. -/
@[simp] theorem selectedGraphRightSourceToRightCJointRingHom_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.semanticCommonSourceField) :
    R.selectedGraphRightSourceToRightCJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightCToJointBaseRingHom hind x) := by
  let : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    R.rightCSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.rightCSourceToRightSourceJointClosureRingEquiv
      ((R.rightCSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField)) x)) = _
  rw [AlgebraicClosureTransport.commutes_apply]
  exact R.rightCSourceToRightSourceJointClosureRingEquiv_algebraMap _

/-- The literal semantic base embedding in the selected graph/right source
cover, exposed as a ring hom so it can be compared with all four joint
embeddings without relying on a synthesized scalar tower. -/
def semanticSourceToSelectedGraphRightSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥R.semanticCommonSourceField) →+*
      (↥(R.selectedGraphRightSourceCover L hind).field) where
  toFun x :=
    ⟨algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField)) x,
      (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul _ x y
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ x y

/-- The first selected joint embedding extends its displayed semantic-base
map as an equality of ring homomorphisms. -/
theorem selectedGraphRightSourceToRightEJointRingHom_comp_source
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightEJointRingHom L hind).comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp
          R.rightEToJointBaseRingHom := by
  apply RingHom.ext
  intro x
  exact R.selectedGraphRightSourceToRightEJointRingHom_algebraMap L hind x

/-- The selected `a` joint embedding has the coefficient-moving `a` base
map as its exact restriction. -/
theorem selectedGraphRightSourceToRightAJointRingHom_comp_source
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightAJointRingHom L hind).comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp
          (R.rightAToJointBaseRingHom hind) := by
  apply RingHom.ext
  intro x
  exact R.selectedGraphRightSourceToRightAJointRingHom_algebraMap L hind x

/-- The analogous full restriction square for the selected `b` joint
embedding. -/
theorem selectedGraphRightSourceToRightBJointRingHom_comp_source
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightBJointRingHom L hind).comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp
          (R.rightBToJointBaseRingHom hind) := by
  apply RingHom.ext
  intro x
  exact R.selectedGraphRightSourceToRightBJointRingHom_algebraMap L hind x

/-- The genuine `c` joint embedding restricts to the composite base chart
through the independent `c` source field. -/
theorem selectedGraphRightSourceToRightCJointRingHom_comp_source
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphRightSourceToRightCJointRingHom L hind).comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp
          (R.rightCToJointBaseRingHom hind) := by
  apply RingHom.ext
  intro x
  exact R.selectedGraphRightSourceToRightCJointRingHom_algebraMap L hind x

/-- Common tower argument extending any one of the four selected embeddings
to algebraic closures once its semantic-base square and the finiteness of
the corresponding twisted joint-source algebra are known. -/
private noncomputable def selectedGraphRightSourceToJointClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (f : (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field))
    (g : (↥R.semanticCommonSourceField) →+*
      (↥R.rightSourceJointField))
    (hfin : @Module.Finite (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) _ _ g.toAlgebra.toModule)
    (hcomp : f.comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp g) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv f := by
  let S := ↥R.semanticCommonSourceField
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let J := ↥R.rightSourceJointField
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let iSN : S →+* N :=
    R.semanticSourceToSelectedGraphRightSourceRingHom L hind
  letI : Algebra S N := iSN.toAlgebra
  letI : Algebra N P := f.toAlgebra
  letI : Algebra S J := g.toAlgebra
  let algSJP : Algebra S P := ((algebraMap J P).comp g).toAlgebra
  letI : Algebra S P := algSJP
  let towerSJP : IsScalarTower S J P :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower S J P := towerSJP
  letI : FiniteDimensional S J := hfin
  letI : FiniteDimensional J P :=
    (R.fourSelectedGraphJointCover L hind).finiteDimensional
  letI : Algebra.IsAlgebraic S J := Algebra.IsAlgebraic.of_finite S J
  letI : Algebra.IsAlgebraic J P := Algebra.IsAlgebraic.of_finite J P
  letI : Algebra.IsAlgebraic S P := by
    exact Algebra.IsAlgebraic.trans S J P
  letI : IsScalarTower S N P :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  letI : Algebra.IsAlgebraic N P :=
    Algebra.IsAlgebraic.tower_top (K := S) (A := P) N
  exact AlgebraicClosureTransport.EmbeddingClosureEquiv.ofAlgebraic f rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The finite algebraic towers use selected, noncanonical algebra maps.
set_option maxHeartbeats 800000 in
-- The finite towers are installed locally because their algebra maps are selected data.
/-- Extend the selected `e` embedding of the whole graph/right source to an
equivalence of algebraic closures of the source cover and the joint cover,
retaining its exact restriction square as data.  The joint cover is finite
over the selected source image: it is already finite over the joint base,
which is finite over the semantic source. -/
noncomputable def selectedGraphRightSourceToRightEJointClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.selectedGraphRightSourceToRightEJointRingHom L hind) :=
  selectedGraphRightSourceToJointClosureExtension R L hind
    (R.selectedGraphRightSourceToRightEJointRingHom L hind)
    R.rightEToJointBaseRingHom (by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointOverSemantic)
    exact R.rightSourceJointOverSemantic_finiteDimensional)
    (R.selectedGraphRightSourceToRightEJointRingHom_comp_source L hind)

/-- Extend the selected `a` embedding to algebraic closures while retaining
its exact coefficient-moving restriction. -/
noncomputable def selectedGraphRightSourceToRightAJointClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.selectedGraphRightSourceToRightAJointRingHom L hind) :=
  selectedGraphRightSourceToJointClosureExtension R L hind
    (R.selectedGraphRightSourceToRightAJointRingHom L hind)
    (R.rightAToJointBaseRingHom hind)
    (R.rightSourceJointOverA_finiteDimensional hind)
    (R.selectedGraphRightSourceToRightAJointRingHom_comp_source L hind)

/-- Extend the selected `b` embedding through the same common joint cover. -/
noncomputable def selectedGraphRightSourceToRightBJointClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.selectedGraphRightSourceToRightBJointRingHom L hind) :=
  selectedGraphRightSourceToJointClosureExtension R L hind
    (R.selectedGraphRightSourceToRightBJointRingHom L hind)
    (R.rightBToJointBaseRingHom hind)
    (R.rightSourceJointOverB_finiteDimensional hind)
    (R.selectedGraphRightSourceToRightBJointRingHom_comp_source L hind)

/-- Extend the genuine `c` embedding, including its passage through the
independent `c` source presentation, to the common algebraic closure. -/
noncomputable def selectedGraphRightSourceToRightCJointClosureExtension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.EmbeddingClosureEquiv
      (R.selectedGraphRightSourceToRightCJointRingHom L hind) :=
  selectedGraphRightSourceToJointClosureExtension R L hind
    (R.selectedGraphRightSourceToRightCJointRingHom L hind)
    (R.rightCToJointBaseRingHom hind)
    (R.rightSourceJointOverCChart_finiteDimensional hind)
    (R.selectedGraphRightSourceToRightCJointRingHom_comp_source L hind)

/-- The established selected graph source is a literal subcover of the
right-enlarged graph source. -/
theorem selectedGraphSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedGraphSourceCover L hind).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  le_sup_left

set_option synthInstance.maxHeartbeats 100000 in
-- The nested two-stage source-cover definitions need a larger synthesis budget.
/-- Literal inclusion of the established selected graph source into the
right-enlarged source, retaining linearity over the full curve source. -/
noncomputable def selectedGraphSourceCoverToSelectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.selectedGraphSourceCover L hind).field) →ₐ[R.semanticCommonSourceType]
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
  IntermediateField.inclusion
    (R.selectedGraphSourceCover_le_selectedGraphRightSourceCover L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The normal-cover algebra tower is hidden behind two named sup constructions.
/-- Extend any established selected-graph source chart across the common
right-cover enlargement. -/
noncomputable def selectedGraphRightSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[R.semanticCommonSourceType]
      (↥(R.selectedGraphSourceCover L hind).field)) :
    (↥(R.selectedGraphRightSourceCover L hind).field) ≃ₐ[R.semanticCommonSourceType]
      (↥(R.selectedGraphRightSourceCover L hind).field) := by
  letI : Normal R.semanticCommonSourceType
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
    (R.selectedGraphRightSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong
    (R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind) σ

set_option synthInstance.maxHeartbeats 100000 in
-- The restriction theorem elaborates the same hidden normal-cover algebra tower.
/-- The extended source chart restricts to the prescribed chart on the
entire established selected graph source. -/
@[simp] theorem selectedGraphRightSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (σ : (↥(R.selectedGraphSourceCover L hind).field) ≃ₐ[R.semanticCommonSourceType]
      (↥(R.selectedGraphSourceCover L hind).field))
    (x : (R.selectedGraphSourceCover L hind).field) :
    R.selectedGraphRightSourceChartAut L hind σ
        (R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind x) =
      R.selectedGraphSourceCoverToSelectedGraphRightSourceCover L hind
        (σ x) := by
  let : Normal R.semanticCommonSourceType
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
    (R.selectedGraphRightSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- The `s·e=u` source chart on the right-enlarged graph source. -/
noncomputable def seSelectedGraphRightSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.selectedGraphRightSourceChartAut L hind
    (R.seSelectedGraphSourceChartAut L hind)

/-- The `sA·a=u` source chart on the right-enlarged graph source. -/
noncomputable def sAaSelectedGraphRightSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.selectedGraphRightSourceChartAut L hind
    (R.sAaSelectedGraphSourceChartAut L hind)

/-- The `s·b=uB` source chart on the right-enlarged graph source. -/
noncomputable def sbSelectedGraphRightSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.selectedGraphRightSourceChartAut L hind
    (R.sbSelectedGraphSourceChartAut L hind)

/-- The `sA·c=uB` source chart on the right-enlarged graph source. -/
noncomputable def sAcSelectedGraphRightSourceChartAut
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  R.selectedGraphRightSourceChartAut L hind
    (R.sAcSelectedGraphSourceChartAut L hind)

/-- The strict `s·e=u` composition triangle on the right-enlarged graph
source. -/
noncomputable def seSelectedGraphRightCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.se) R.seCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)

/-- The strict `sA·a=u` composition triangle on the same right-enlarged
graph source. -/
noncomputable def sAaSelectedGraphRightCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)

/-- The strict `s·b=uB` composition triangle on the same right-enlarged
graph source. -/
noncomputable def sbSelectedGraphRightCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sb) R.sbCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)

/-- The strict `sA·c=uB` composition triangle on the same right-enlarged
graph source. -/
noncomputable def sAcSelectedGraphRightCompositionTriangle
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAc) R.sAcCommonBaseData hψ)
    (R.selectedGraphRightSourceCover L hind)

/-- The four relocated right-family members display the four mapped
normalized parameter tuples literally. -/
theorem relocatedBFamily_parameters :
    (R.se.bCorrespondenceFamilyMember hψ).parameter =
        commonCurveEmbedding (k := k) (K := K) ∘ e ∧
      (R.sAa.bCorrespondenceFamilyMember hψ).parameter =
        commonCurveEmbedding (k := k) (K := K) ∘ a ∧
      (R.sb.bCorrespondenceFamilyMember hψ).parameter =
        commonCurveEmbedding (k := k) (K := K) ∘ b ∧
      (R.sAc.bCorrespondenceFamilyMember hψ).parameter =
        commonCurveEmbedding (k := k) (K := K) ∘ D.c := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The whole intrinsic selected-`B` coefficient field transported to the
relocated right-family parameter field on the `s·e=u` face. -/
noncomputable def seBGermCoefficientToRelocatedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField) :=
  bGermCoefficientToRelocatedBParameterAlgHom
    (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
    (R.se.bCorrespondenceFamilyMember hψ)
    R.relocatedBFamily_parameters.1

/-- The corresponding whole-field transport on the `sA·a=u` face. -/
noncomputable def sAaBGermCoefficientToRelocatedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :=
  bGermCoefficientToRelocatedBParameterAlgHom
    (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
    (R.sAa.bCorrespondenceFamilyMember hψ)
    R.relocatedBFamily_parameters.2.1

/-- The corresponding whole-field transport on the `s·b=uB` face. -/
noncomputable def sbBGermCoefficientToRelocatedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField) :=
  bGermCoefficientToRelocatedBParameterAlgHom
    (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
    (R.sb.bCorrespondenceFamilyMember hψ)
    R.relocatedBFamily_parameters.2.2.1

/-- The corresponding whole-field transport on the `sA·c=uB` face. -/
noncomputable def sAcBGermCoefficientToRelocatedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :=
  bGermCoefficientToRelocatedBParameterAlgHom
    (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
    (R.sAc.bCorrespondenceFamilyMember hψ)
    R.relocatedBFamily_parameters.2.2.2

end ReferenceFieldAliases

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
