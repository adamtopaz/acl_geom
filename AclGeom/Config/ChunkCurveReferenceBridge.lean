/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource
import AclGeom.Config.ChunkFourArrowReference
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

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

private abbrev curveEmbedding : K →ₐ[k] CommonCurveAmbient K :=
  commonCurveEmbedding (k := k) (K := K)

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
  letI : Algebra (↥D.inputField) (↥N₀) :=
    (IntermediateField.inclusion h₀).toAlgebra
  letI : Algebra (↥(D.inputField.map ι)) (↥(N₀.map ι)) :=
    (IntermediateField.inclusion
      (IntermediateField.map_mono ι h₀)).toAlgebra
  letI : FiniteDimensional (↥D.inputField) (↥N₀) := by
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
  letI := R.mappedReferenceNormalOverInput_finiteDimensional L
  exact FiniteExtensionCompositum.le_field
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)

/-- The transported normalized reference field lies in the same
reference/semantic compositum. -/
theorem mappedReferenceNormalField_le_referenceSemanticJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.mappedReferenceNormalField L ≤ R.referenceSemanticJoin L hind := by
  letI := R.mappedReferenceNormalOverInput_finiteDimensional L
  change (R.mappedReferenceNormalOverInput L).restrictScalars k ≤ _
  exact FiniteExtensionCompositum.normal_le_field
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

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
  letI := R.mappedReferenceNormalOverInput_finiteDimensional L
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
  letI : Algebra (↥A) (↥R.semanticCommonSourceField) :=
    (IntermediateField.inclusion hAS).toAlgebra
  letI : IsScalarTower (↥A) (↥R.semanticCommonSourceField)
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
  letI := R.selectedSemanticBranchExtension_finiteDimensional L
  exact FiniteExtensionCompositum.le_field
    R.semanticCommonSourceField (R.referenceSemanticJoin L hind)
      (R.selectedSemanticBranchExtension L)

/-- The finite extension generated by the selected semantic coordinates
lies in the enlarged joint field. -/
theorem selectedSemanticBranchExtension_le_selectedSemanticReferenceJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.selectedSemanticBranchExtension L).restrictScalars k ≤
      R.selectedSemanticReferenceJoin L hind := by
  letI := R.selectedSemanticBranchExtension_finiteDimensional L
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
  letI := R.selectedSemanticBranchExtension_finiteDimensional L
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

/-- The single concrete selected semantic/reference normal closure is
finite over the common source field. -/
theorem selectedSemanticReferenceNormalField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceNormalField L hind)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
    (R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind)

/-- The single concrete selected semantic/reference normal closure is
normal over the common source field. -/
theorem selectedSemanticReferenceNormalField_normal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Normal (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceNormalField L hind)) := by
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars
        (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin
          L hind))) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  exact FiniteCover.normalClosureOver_normal
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
    (Algebra.IsAlgebraic.of_finite _ _)

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

/-- The transported normalized reference field lies in the same concrete
normal closure as all selected semantic and relocated branches. -/
theorem mappedReferenceNormalField_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.mappedReferenceNormalField L ≤
      (R.selectedSemanticReferenceNormalField L hind).restrictScalars k :=
  (R.mappedReferenceNormalField_le_referenceSemanticJoin L hind).trans
    ((R.referenceSemanticJoin_le_selectedSemanticReferenceJoin L hind).trans
      (R.selectedSemanticReferenceJoin_le_normalField_restrictScalars L hind))

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

/-- All four original complete relocated right branches lie in the same
selected semantic/reference normal closure. -/
theorem fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sb.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k := by
  let hJ := R.selectedSemanticReferenceJoin_le_normalField_restrictScalars L hind
  exact ⟨(R.seRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAaRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sbRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAcRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ⟩

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
    letI : FiniteDimensional (↥R.semanticCommonSourceField)
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

/-- Literal inclusion of the common-base `a` right branch. -/
noncomputable def sAaSemanticRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.1 hz)

/-- Literal inclusion of the common-base `b` right branch. -/
noncomputable def sbSemanticRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.1 hz)

/-- Literal inclusion of the common-base `c` right branch. -/
noncomputable def sAcSemanticRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.2 hz)

/-- Literal inclusion of the original relocated `e` right branch. -/
noncomputable def seRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.se.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.1 hz)

/-- Literal inclusion of the original relocated `a` right branch. -/
noncomputable def sAaRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sAa.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.1 hz)

/-- Literal inclusion of the original relocated `b` right branch. -/
noncomputable def sbRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sb.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.1 hz)

/-- Literal inclusion of the original relocated `c` right branch. -/
noncomputable def sAcRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sAc.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.2 hz)

/-- Canonicalize the selected semantic `e` branch after its literal ambient
inclusion. -/
noncomputable def seSemanticRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.seSemanticRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the selected semantic `a` branch. -/
noncomputable def sAaSemanticRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAaSemanticRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the selected semantic `b` branch. -/
noncomputable def sbSemanticRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sbSemanticRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the selected semantic `c` branch. -/
noncomputable def sAcSemanticRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAcSemanticRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `e` branch after literal inclusion. -/
noncomputable def seRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.seRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `a` branch. -/
noncomputable def sAaRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAaRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `b` branch. -/
noncomputable def sbRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sbRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `c` branch. -/
noncomputable def sAcRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAcRelocatedRightBranchToSelectedNormalRingHom L hind)

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

/-- The enlarged `e` source chart restricts exactly to the established
semantic source chart on the whole branch-comparison subcover. -/
@[simp] theorem seSelectedGraphSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.seSelectedGraphSourceChartAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.seRepeatedUTotalAnchorAlignmentAut hind x) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- The enlarged `a` source chart restricts to its established semantic
source chart. -/
@[simp] theorem sAaSelectedGraphSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.sAaSelectedGraphSourceChartAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.sAaRepeatedUTotalAnchorAlignmentAut hind x) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- The enlarged `b` source chart restricts to its established semantic
source chart. -/
@[simp] theorem sbSelectedGraphSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.sbSelectedGraphSourceChartAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.sbRepeatedUBTotalAnchorAlignmentAut hind x) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

/-- The enlarged `c` source chart restricts to its established semantic
source chart. -/
@[simp] theorem sAcSelectedGraphSourceChartAut_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.branchComparisonSourceCover hind).field) :
    R.sAcSelectedGraphSourceChartAut L hind
        (R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
          L hind x) =
      R.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource
        L hind (R.sAcRepeatedUBTotalAnchorAlignmentAut hind x) := by
  letI : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

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
    (R.selectedSemanticReferenceSourceCover L hind).field →ₐ[k]
      (R.selectedGraphSourceCover L hind).field :=
  (IntermediateField.inclusion
    (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
      L hind)).restrictScalars k

/-- The literal common curve source is contained in the finite extension
generated by all selected semantic face coordinates. -/
theorem semanticCommonSourceField_le_selectedSemanticBranchExtension :
    R.semanticCommonSourceField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  intro z hz
  exact (R.selectedSemanticBranchExtension L).algebraMap_mem ⟨z, hz⟩

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

/-- The common eight-input coefficient field is already contained in the
selected semantic face extension. -/
theorem commonCoefficientField_le_selectedSemanticBranchExtension :
    R.seCommonBaseData.coefficientField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  rw [← R.mappedReferenceInputField_eq_commonCoefficientField L]
  exact (R.mappedReferenceInputField_le_semanticCommonSourceField L).trans
    (R.semanticCommonSourceField_le_selectedSemanticBranchExtension L)

set_option maxHeartbeats 800000 in
-- Expanding the two-generator branch field through the ten-coordinate adjoin is expensive.
/-- The full common-base semantic `e` right branch is contained in the one
selected semantic face extension, before normal closure. -/
theorem seSemanticRightBranch_le_selectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchField.restrictScalars k ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  let hA : R.seCommonBaseData.coefficientField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k :=
    R.commonCoefficientField_le_selectedSemanticBranchExtension L
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change R.se.middle ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨2, rfl⟩
    · change R.se.target ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨3, rfl⟩
  intro z hz
  exact hQ hz

set_option maxHeartbeats 800000 in
-- Expanding the two-generator branch field through the ten-coordinate adjoin is expensive.
/-- The full common-base semantic `a` right branch lies in the same face
extension. -/
theorem sAaSemanticRightBranch_le_selectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchField.restrictScalars k ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  let hA : R.sAaCommonBaseData.coefficientField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k :=
    R.commonCoefficientField_le_selectedSemanticBranchExtension L
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change R.sAa.middle ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨4, rfl⟩
    · change R.sAa.target ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨5, rfl⟩
  intro z hz
  exact hQ hz

set_option maxHeartbeats 800000 in
-- Expanding the two-generator branch field through the ten-coordinate adjoin is expensive.
/-- The full common-base semantic `b` right branch lies in the same face
extension. -/
theorem sbSemanticRightBranch_le_selectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchField.restrictScalars k ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  let hA : R.sbCommonBaseData.coefficientField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k :=
    R.commonCoefficientField_le_selectedSemanticBranchExtension L
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change R.sb.middle ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨6, rfl⟩
    · change R.sb.target ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨7, rfl⟩
  intro z hz
  exact hQ hz

set_option maxHeartbeats 800000 in
-- Expanding the two-generator branch field through the ten-coordinate adjoin is expensive.
/-- The full common-base semantic `c` right branch, including its algebraic
parameter presentation, lies in the same face extension. -/
theorem sAcSemanticRightBranch_le_selectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchField.restrictScalars k ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k := by
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  let hA : R.sAcCommonBaseData.coefficientField ≤
      (R.selectedSemanticBranchExtension L).restrictScalars k :=
    R.commonCoefficientField_le_selectedSemanticBranchExtension L
  have hQ : Q.branchField ≤ extendScalars hA := by
    unfold FiniteCorrespondencePair.branchField
    apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change R.sAc.middle ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨8, rfl⟩
    · change R.sAc.target ∈ R.selectedSemanticBranchExtension L
      exact subset_adjoin _ _ ⟨9, rfl⟩
  intro z hz
  exact hQ hz

/-- Literal inclusion of the semantic `e` branch in the coherent whole-face
extension. -/
noncomputable def seSemanticRightBranchToSelectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticBranchExtension L :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticBranchExtension L)
    (fun _ hz ↦
      R.seSemanticRightBranch_le_selectedSemanticBranchExtension L hz)

/-- Literal inclusion of the semantic `a` branch in the coherent whole-face
extension. -/
noncomputable def sAaSemanticRightBranchToSelectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticBranchExtension L :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticBranchExtension L)
    (fun _ hz ↦
      R.sAaSemanticRightBranch_le_selectedSemanticBranchExtension L hz)

/-- Literal inclusion of the semantic `b` branch in the coherent whole-face
extension. -/
noncomputable def sbSemanticRightBranchToSelectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticBranchExtension L :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticBranchExtension L)
    (fun _ hz ↦
      R.sbSemanticRightBranch_le_selectedSemanticBranchExtension L hz)

/-- Literal inclusion of the semantic `c` branch in the coherent whole-face
extension. -/
noncomputable def sAcSemanticRightBranchToSelectedSemanticBranchExtension :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource →+*
      R.selectedSemanticBranchExtension L :=
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticBranchExtension L)
    (fun _ hz ↦
      R.sAcSemanticRightBranch_le_selectedSemanticBranchExtension L hz)

/-- The selected common-base semantic `e` branch in the graph source. -/
noncomputable def seSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seSemanticRightBranchToSelectedSourceRingHom L hind)

/-- The selected common-base semantic `a` branch in the graph source. -/
noncomputable def sAaSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAaSemanticRightBranchToSelectedSourceRingHom L hind)

/-- The selected common-base semantic `b` branch in the graph source. -/
noncomputable def sbSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sbSemanticRightBranchToSelectedSourceRingHom L hind)

/-- The selected common-base semantic `c` branch in the graph source. -/
noncomputable def sAcSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAcSemanticRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `e` branch in the same graph source. -/
noncomputable def seRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `a` branch in the same graph source. -/
noncomputable def sAaRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `b` branch in the same graph source. -/
noncomputable def sbRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `c` branch in the same graph source. -/
noncomputable def sAcRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- Before the shared canonicalization, the semantic `e` branch inclusion
factors through the coherent whole-face extension. -/
theorem seSemanticRightBranchToSelectedNormal_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seSemanticRightBranchToSelectedNormalRingHom L hind =
      (IntermediateField.inclusion
        (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
          L hind)).toRingHom.comp
        (R.seSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  unfold seSemanticRightBranchToSelectedNormalRingHom
    seSemanticRightBranchToSelectedSemanticBranchExtension
  exact
    FiniteCorrespondencePair.branchOverSourceToIntermediateFieldRingHom_trans
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ)
      (R.selectedSemanticBranchExtension L)
      (R.selectedSemanticReferenceNormalField L hind)
      (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
        L hind)
      (fun _ hz ↦
        R.seSemanticRightBranch_le_selectedSemanticBranchExtension L hz)
      (fun _ hz ↦
        R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
          L hind |>.1 hz)

/-- The semantic `a` branch uses the same whole-face extension before
canonicalization. -/
theorem sAaSemanticRightBranchToSelectedNormal_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAaSemanticRightBranchToSelectedNormalRingHom L hind =
      (IntermediateField.inclusion
        (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
          L hind)).toRingHom.comp
        (R.sAaSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  unfold sAaSemanticRightBranchToSelectedNormalRingHom
    sAaSemanticRightBranchToSelectedSemanticBranchExtension
  exact
    FiniteCorrespondencePair.branchOverSourceToIntermediateFieldRingHom_trans
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (R.selectedSemanticBranchExtension L)
      (R.selectedSemanticReferenceNormalField L hind)
      (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
        L hind)
      (fun _ hz ↦
        R.sAaSemanticRightBranch_le_selectedSemanticBranchExtension L hz)
      (fun _ hz ↦
        R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
          L hind |>.2.1 hz)

/-- The semantic `b` branch uses the same whole-face extension before
canonicalization. -/
theorem sbSemanticRightBranchToSelectedNormal_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sbSemanticRightBranchToSelectedNormalRingHom L hind =
      (IntermediateField.inclusion
        (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
          L hind)).toRingHom.comp
        (R.sbSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  unfold sbSemanticRightBranchToSelectedNormalRingHom
    sbSemanticRightBranchToSelectedSemanticBranchExtension
  exact
    FiniteCorrespondencePair.branchOverSourceToIntermediateFieldRingHom_trans
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ)
      (R.selectedSemanticBranchExtension L)
      (R.selectedSemanticReferenceNormalField L hind)
      (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
        L hind)
      (fun _ hz ↦
        R.sbSemanticRightBranch_le_selectedSemanticBranchExtension L hz)
      (fun _ hz ↦
        R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
          L hind |>.2.2.1 hz)

/-- The algebraic semantic `c` branch uses the same whole-face extension
before canonicalization. -/
theorem sAcSemanticRightBranchToSelectedNormal_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAcSemanticRightBranchToSelectedNormalRingHom L hind =
      (IntermediateField.inclusion
        (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
          L hind)).toRingHom.comp
        (R.sAcSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  unfold sAcSemanticRightBranchToSelectedNormalRingHom
    sAcSemanticRightBranchToSelectedSemanticBranchExtension
  exact
    FiniteCorrespondencePair.branchOverSourceToIntermediateFieldRingHom_trans
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ)
      (R.selectedSemanticBranchExtension L)
      (R.selectedSemanticReferenceNormalField L hind)
      (R.selectedSemanticBranchExtension_le_selectedSemanticReferenceNormalField
        L hind)
      (fun _ hz ↦
        R.sAcSemanticRightBranch_le_selectedSemanticBranchExtension L hz)
      (fun _ hz ↦
        R.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField
          L hind |>.2.2.2 hz)

/-- In the unified selected graph, the entire semantic `e` branch is a
restriction of the single coherent whole-face anchor. -/
theorem seSemanticRightBranchToSelectedGraph_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seSemanticRightBranchToSelectedGraphSourceRingHom L hind =
      (R.selectedSemanticBranchExtensionToSelectedGraphSource
        L hind).toRingHom.comp
        (R.seSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  apply RingHom.ext
  intro z
  unfold seSemanticRightBranchToSelectedGraphSourceRingHom
    selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    seSemanticRightBranchToSelectedSourceRingHom
    ambientSelectedSemanticReferenceNormalFieldToSourceCover
    selectedSemanticBranchExtensionToSelectedGraphSource
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  have hz := DFunLike.congr_fun
    (R.seSemanticRightBranchToSelectedNormal_factor_extension L hind) z
  exact congrArg (fun y ↦
    (IntermediateField.inclusion
      (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
        L hind))
      (R.selectedSemanticReferenceNormalEquivSourceCover L hind y)) hz

/-- In the same graph, the entire semantic `a` branch is a restriction of
the same coherent whole-face anchor. -/
theorem sAaSemanticRightBranchToSelectedGraph_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAaSemanticRightBranchToSelectedGraphSourceRingHom L hind =
      (R.selectedSemanticBranchExtensionToSelectedGraphSource
        L hind).toRingHom.comp
        (R.sAaSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  apply RingHom.ext
  intro z
  unfold sAaSemanticRightBranchToSelectedGraphSourceRingHom
    selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    sAaSemanticRightBranchToSelectedSourceRingHom
    ambientSelectedSemanticReferenceNormalFieldToSourceCover
    selectedSemanticBranchExtensionToSelectedGraphSource
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  have hz := DFunLike.congr_fun
    (R.sAaSemanticRightBranchToSelectedNormal_factor_extension L hind) z
  exact congrArg (fun y ↦
    (IntermediateField.inclusion
      (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
        L hind))
      (R.selectedSemanticReferenceNormalEquivSourceCover L hind y)) hz

/-- In the same graph, the entire semantic `b` branch is a restriction of
the same coherent whole-face anchor. -/
theorem sbSemanticRightBranchToSelectedGraph_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sbSemanticRightBranchToSelectedGraphSourceRingHom L hind =
      (R.selectedSemanticBranchExtensionToSelectedGraphSource
        L hind).toRingHom.comp
        (R.sbSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  apply RingHom.ext
  intro z
  unfold sbSemanticRightBranchToSelectedGraphSourceRingHom
    selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    sbSemanticRightBranchToSelectedSourceRingHom
    ambientSelectedSemanticReferenceNormalFieldToSourceCover
    selectedSemanticBranchExtensionToSelectedGraphSource
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  have hz := DFunLike.congr_fun
    (R.sbSemanticRightBranchToSelectedNormal_factor_extension L hind) z
  exact congrArg (fun y ↦
    (IntermediateField.inclusion
      (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
        L hind))
      (R.selectedSemanticReferenceNormalEquivSourceCover L hind y)) hz

/-- In the same graph, the entire algebraic semantic `c` branch is a
restriction of the same coherent whole-face anchor. -/
theorem sAcSemanticRightBranchToSelectedGraph_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.sAcSemanticRightBranchToSelectedGraphSourceRingHom L hind =
      (R.selectedSemanticBranchExtensionToSelectedGraphSource
        L hind).toRingHom.comp
        (R.sAcSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  apply RingHom.ext
  intro z
  unfold sAcSemanticRightBranchToSelectedGraphSourceRingHom
    selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    sAcSemanticRightBranchToSelectedSourceRingHom
    ambientSelectedSemanticReferenceNormalFieldToSourceCover
    selectedSemanticBranchExtensionToSelectedGraphSource
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  have hz := DFunLike.congr_fun
    (R.sAcSemanticRightBranchToSelectedNormal_factor_extension L hind) z
  exact congrArg (fun y ↦
    (IntermediateField.inclusion
      (R.selectedSemanticReferenceSourceCover_le_selectedGraphSourceCover
        L hind))
      (R.selectedSemanticReferenceNormalEquivSourceCover L hind y)) hz

/-- Simultaneously, all four complete semantic right branches are
restrictions of one coherent whole-face embedding into the selected graph. -/
theorem fourSemanticRightBranchesToSelectedGraph_factor_extension
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seSemanticRightBranchToSelectedGraphSourceRingHom L hind =
        (R.selectedSemanticBranchExtensionToSelectedGraphSource
          L hind).toRingHom.comp
          (R.seSemanticRightBranchToSelectedSemanticBranchExtension L) ∧
      R.sAaSemanticRightBranchToSelectedGraphSourceRingHom L hind =
        (R.selectedSemanticBranchExtensionToSelectedGraphSource
          L hind).toRingHom.comp
          (R.sAaSemanticRightBranchToSelectedSemanticBranchExtension L) ∧
      R.sbSemanticRightBranchToSelectedGraphSourceRingHom L hind =
        (R.selectedSemanticBranchExtensionToSelectedGraphSource
          L hind).toRingHom.comp
          (R.sbSemanticRightBranchToSelectedSemanticBranchExtension L) ∧
      R.sAcSemanticRightBranchToSelectedGraphSourceRingHom L hind =
        (R.selectedSemanticBranchExtensionToSelectedGraphSource
          L hind).toRingHom.comp
          (R.sAcSemanticRightBranchToSelectedSemanticBranchExtension L) := by
  exact ⟨R.seSemanticRightBranchToSelectedGraph_factor_extension L hind,
    R.sAaSemanticRightBranchToSelectedGraph_factor_extension L hind,
    R.sbSemanticRightBranchToSelectedGraph_factor_extension L hind,
    R.sAcSemanticRightBranchToSelectedGraph_factor_extension L hind⟩

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
    letI : FiniteDimensional (↥R.semanticCommonSourceField)
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

/-- The coefficient-faithful semantic source cover embeds in the combined
reference/semantic cover. -/
theorem branchComparisonSourceCover_le_referenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.branchComparisonSourceCover hind).field ≤
      (R.referenceSemanticSourceCover L hind).field :=
  le_sup_left

/-- The literal inclusion of the semantic branch-comparison cover in the
combined semantic/reference source cover. -/
def branchComparisonSourceCoverToReferenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.branchComparisonSourceCover hind).field →ₐ[k]
      (R.referenceSemanticSourceCover L hind).field :=
  (IntermediateField.inclusion
    (R.branchComparisonSourceCover_le_referenceSemanticSourceCover
      L hind)).restrictScalars k

/-- The transported explicit reference cover embeds in the combined
reference/semantic cover. -/
theorem transportedReferenceSourceCover_le_referenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.transportedReferenceSourceCover L hind).field ≤
    (R.referenceSemanticSourceCover L hind).field :=
  le_sup_right

/-- The original eight-input field maps into the semantic common source by
the canonical ambient embedding. -/
def referenceInputToSemanticSource :
    (↥D.inputField) →ₐ[k] (↥R.semanticCommonSourceField) where
  toFun z := ⟨curveEmbedding (k := k) (K := K) z,
    R.mappedReferenceInputField_le_semanticCommonSourceField L
      ((IntermediateField.map_mem_map
        (S := D.inputField) (curveEmbedding (k := k) (K := K))).2 z.2)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' x := by ext; rfl

@[simp] theorem referenceInputToSemanticSource_val (z : D.inputField) :
    ((R.referenceInputToSemanticSource L z : R.semanticCommonSourceField) :
      CommonCurveAmbient K) =
      curveEmbedding (k := k) (K := K) z :=
  rfl

/-- The transported explicit reference field lies in the ambient normal
closure used before passing to its canonical algebraic-closure model. -/
theorem mappedReferenceNormalField_le_ambientReferenceNormalClosure
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.mappedReferenceNormalField L ≤
      (FiniteCover.normalClosureOver
        (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
          ).restrictScalars k := by
  intro z hz
  apply FiniteCover.extendScalars_le_normalClosureOver
    (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
  change z ∈ R.referenceSemanticJoin L hind
  exact R.mappedReferenceNormalField_le_referenceSemanticJoin L hind hz

/-- The original normalized reference cover embeds into its transported
image in the common curve ambient field. -/
def referenceNormalCoverToMappedReference :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.mappedReferenceNormalField L)) where
  toFun z := ⟨curveEmbedding (k := k) (K := K) z,
    ⟨z, z.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' x := by ext; rfl

@[simp] theorem referenceNormalCoverToMappedReference_val
    (z : L.referenceNormalCover) :
    ((R.referenceNormalCoverToMappedReference L z :
      R.mappedReferenceNormalField L) : CommonCurveAmbient K) =
      curveEmbedding (k := k) (K := K) z :=
  rfl

/-- Include the transported reference field in the concrete normal closure
of the reference/semantic compositum. -/
def mappedReferenceToAmbientReferenceNormalClosure
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.mappedReferenceNormalField L)) →ₐ[k]
      (↥(FiniteCover.normalClosureOver
        (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))) :=
  IntermediateField.algHomIntoOfLeRestrictScalars
    (R.mappedReferenceNormalField L)
    (FiniteCover.normalClosureOver
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))
    (R.mappedReferenceNormalField_le_ambientReferenceNormalClosure L hind)

/-- Move the concrete normal closure of the compositum into its canonical
algebraic-closure model. -/
noncomputable def ambientReferenceNormalClosureToTransportedSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.normalClosureOver
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))) →ₐ[k]
      (↥(R.transportedReferenceSourceCover L hind).field) := by
  let hSJ := R.semanticCommonSourceField_le_referenceSemanticJoin L hind
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars hSJ)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.referenceSemanticJoinOverSource L hind))
    exact R.referenceSemanticJoinOverSource_finiteDimensional L hind
  exact (FiniteCover.normalClosureOverEquivCanonical hSJ
    (Algebra.IsAlgebraic.of_finite _ _)).toAlgHom.restrictScalars k

/-- The canonicalization map remains linear over the full semantic source
field, even though it is exposed above only as a ground-field map. -/
theorem ambientReferenceNormalClosureToTransportedSourceCover_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : R.semanticCommonSourceField) :
    R.ambientReferenceNormalClosureToTransportedSourceCover L hind
        (algebraMap (↥R.semanticCommonSourceField)
          (↥(FiniteCover.normalClosureOver
            (R.semanticCommonSourceField_le_referenceSemanticJoin L hind))) z) =
      algebraMap (↥R.semanticCommonSourceField)
        (↥(R.transportedReferenceSourceCover L hind).field) z := by
  let hSJ := R.semanticCommonSourceField_le_referenceSemanticJoin L hind
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars hSJ)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.referenceSemanticJoinOverSource L hind))
    exact R.referenceSemanticJoinOverSource_finiteDimensional L hind
  let halg : Algebra.IsAlgebraic (↥R.semanticCommonSourceField)
      (↥(extendScalars hSJ)) := Algebra.IsAlgebraic.of_finite _ _
  change (FiniteCover.normalClosureOverEquivCanonical hSJ halg)
      (algebraMap (↥R.semanticCommonSourceField)
        (↥(FiniteCover.normalClosureOver hSJ)) z) =
    algebraMap (↥R.semanticCommonSourceField)
      (↥(FiniteCover.canonicalNormalClosure hSJ)) z
  exact (FiniteCover.normalClosureOverEquivCanonical hSJ halg).commutes z

/-- Include the transported canonical source cover in the final joined
semantic/reference source cover. -/
def transportedSourceCoverToReferenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.transportedReferenceSourceCover L hind).field) →ₐ[k]
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (IntermediateField.inclusion
    (R.transportedReferenceSourceCover_le_referenceSemanticSourceCover
      L hind)).restrictScalars k

/-- The exact coefficient-linear embedding of the original normalized
reference cover into the combined semantic/reference source cover. -/
def referenceNormalCoverToReferenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.transportedSourceCoverToReferenceSemanticSourceCover L hind).comp
    ((R.ambientReferenceNormalClosureToTransportedSourceCover L hind).comp
      ((R.mappedReferenceToAmbientReferenceNormalClosure L hind).comp
        (R.referenceNormalCoverToMappedReference L)))

/-- On every one of the eight free input coefficients, the transported
reference-cover embedding is exactly the semantic common-source algebra
map.  This is the coefficient square needed before comparing the four
explicit reference projections with the semantic four-arrow charts. -/
theorem referenceNormalCoverToReferenceSemanticSourceCover_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : D.inputField) :
    R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (algebraMap (↥D.inputField) (↥L.referenceNormalCover) z) =
      algebraMap (↥R.semanticCommonSourceField)
        (↥(R.referenceSemanticSourceCover L hind).field)
        (R.referenceInputToSemanticSource L z) := by
  let y : FiniteCover.normalClosureOver
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind) :=
    R.mappedReferenceToAmbientReferenceNormalClosure L hind
      (R.referenceNormalCoverToMappedReference L
        (algebraMap (↥D.inputField) (↥L.referenceNormalCover) z))
  have hy : y = algebraMap (↥R.semanticCommonSourceField)
      (↥(FiniteCover.normalClosureOver
        (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)))
      (R.referenceInputToSemanticSource L z) := by
    apply Subtype.ext
    rfl
  unfold referenceNormalCoverToReferenceSemanticSourceCover
  simp only [AlgHom.comp_apply]
  change R.transportedSourceCoverToReferenceSemanticSourceCover L hind
      (R.ambientReferenceNormalClosureToTransportedSourceCover L hind y) = _
  rw [hy]
  have hcanonical :
      R.ambientReferenceNormalClosureToTransportedSourceCover L hind
          (algebraMap (↥R.semanticCommonSourceField)
            (↥(FiniteCover.normalClosureOver
              (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)))
            (R.referenceInputToSemanticSource L z)) =
        algebraMap (↥R.semanticCommonSourceField)
          (↥(R.transportedReferenceSourceCover L hind).field)
          (R.referenceInputToSemanticSource L z) := by
    exact R.ambientReferenceNormalClosureToTransportedSourceCover_algebraMap
      L hind (R.referenceInputToSemanticSource L z)
  rw [hcanonical]
  rfl

/-- Embed the transported reference normal cover in the concrete selected
semantic/reference normal field.  This is the literal transported-image
inclusion, before the single canonicalization chosen for the selected
cover. -/
noncomputable def referenceNormalCoverToSelectedNormal
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.selectedSemanticReferenceNormalField L hind)) :=
  (IntermediateField.algHomIntoOfLeRestrictScalars
    (R.mappedReferenceNormalField L)
    (R.selectedSemanticReferenceNormalField L hind)
    (R.mappedReferenceNormalField_le_selectedSemanticReferenceNormalField
      L hind)).comp
    (R.referenceNormalCoverToMappedReference L)

/-- Pass the transported reference normal cover through the same single
canonicalization as all selected semantic and relocated branches. -/
noncomputable def referenceNormalCoverToSelectedSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.selectedSemanticReferenceSourceCover L hind).field) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).comp
    (R.referenceNormalCoverToSelectedNormal L hind)

/-- The transported reference normal cover in the final selected graph
source.  Its image now shares a literal codomain with the four lifted
semantic source charts and all eight selected branch embeddings. -/
noncomputable def referenceNormalCoverToSelectedGraphSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.selectedGraphSourceCover L hind).field) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
    L hind).comp
    (R.referenceNormalCoverToSelectedSource L hind)

/-- Embed one complete scalar-extended reference edge in the selected graph
source through the same transported normal cover and canonicalization. -/
noncomputable def totalBaseChangedEdgeToSelectedGraphSource
    (E : L.TotalBaseChangedEdge)
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥E.field) →ₐ[k]
      (↥(R.selectedGraphSourceCover L hind).field) :=
  (R.referenceNormalCoverToSelectedGraphSource L hind).comp
    (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.toReferenceNormalCover
      L E)

/-- The selected-graph embedding of a complete edge preserves every one of
its nine selected coordinates, via the corresponding literal coordinate
of the transported reference normal cover. -/
@[simp] theorem totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate
    (E : L.TotalBaseChangedEdge)
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 9) :
    R.totalBaseChangedEdgeToSelectedGraphSource L E hind
        (E.selectedCoordinate i) =
      R.referenceNormalCoverToSelectedGraphSource L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L E i) := by
  unfold totalBaseChangedEdgeToSelectedGraphSource
  rw [AlgHom.comp_apply]
  rw [PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.toReferenceNormalCover_selectedCoordinate]

/-- All four complete normalized reference edges now lie in the selected
graph source, and their selected `B/T` scalars retain their literal
same-edge coordinates there. -/
theorem fourTotalBaseChangedEdges_selectedBScalar_inSelectedGraphSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.totalBaseChangedEdgeToSelectedGraphSource L
        L.seTotalBaseChangedEdge hind
        (L.seTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToSelectedGraphSource L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.seTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToSelectedGraphSource L
        L.sA_aTotalBaseChangedEdge hind
        (L.sA_aTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToSelectedGraphSource L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.sA_aTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToSelectedGraphSource L
        L.s_bTotalBaseChangedEdge hind
        (L.s_bTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToSelectedGraphSource L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.s_bTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToSelectedGraphSource L
        L.sA_cTotalBaseChangedEdge hind
        (L.sA_cTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToSelectedGraphSource L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.sA_cTotalBaseChangedEdge 7) := by
  exact
    ⟨R.totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate
        L L.seTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate
        L L.sA_aTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate
        L L.s_bTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate
        L L.sA_cTotalBaseChangedEdge hind 7⟩

/-- Embed one complete edge after scalar extension to the common
sixteen-coordinate coefficient field into the common formal-source cover.
The map factors through the literal final reference normal cover, so it
retains the selected edge rather than making a new branch choice. -/
def totalBaseChangedEdgeToReferenceSemanticSourceCover
    (E : L.TotalBaseChangedEdge)
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥E.field) →ₐ[k]
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceNormalCoverToReferenceSemanticSourceCover L hind).comp
    (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.toReferenceNormalCover
      L E)

/-- The scalar-extended edge embedding sends every selected coordinate to
the transported image of the same literal coordinate in the reference
normal cover. -/
@[simp] theorem totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
    (E : L.TotalBaseChangedEdge)
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (i : Fin 9) :
    R.totalBaseChangedEdgeToReferenceSemanticSourceCover L E hind
        (E.selectedCoordinate i) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L E i) := by
  unfold totalBaseChangedEdgeToReferenceSemanticSourceCover
  rw [AlgHom.comp_apply]
  rw [PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.toReferenceNormalCover_selectedCoordinate]

/-- The four selected `B/T` scalar branches now occur in one common
formal-source normal cover through coefficient-compatible embeddings of
their complete scalar-extended edges. -/
theorem fourTotalBaseChangedEdges_selectedBScalar_inReferenceSemanticSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.seTotalBaseChangedEdge hind
        (L.seTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.seTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.sA_aTotalBaseChangedEdge hind
        (L.sA_aTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.sA_aTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.s_bTotalBaseChangedEdge hind
        (L.s_bTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.s_bTotalBaseChangedEdge 7) ∧
    R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.sA_cTotalBaseChangedEdge hind
        (L.sA_cTotalBaseChangedEdge.selectedCoordinate 7) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.referenceCoordinate
          L L.sA_cTotalBaseChangedEdge 7) := by
  exact
    ⟨R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
        L L.seTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
        L L.sA_aTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
        L L.s_bTotalBaseChangedEdge hind 7,
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
        L L.sA_cTotalBaseChangedEdge hind 7⟩

/-- The generic-point identification between the full normalized reference
chart and its ambient normal cover. -/
noncomputable def referenceFunctionFieldRingEquiv :
    L.referenceAlgebraicChart.functionField ≃+* ↥L.referenceNormalCover := by
  letI := L.referenceNormalCover_finiteDimensional
  exact (FiniteExtensionChart.functionFieldAlgEquiv
      (k := k) (K := ↥D.inputField) (L := ↥L.referenceNormalCover)
      D.inputCoordinates D.adjoin_inputCoordinates_eq_top).toRingEquiv

/-- Conjugate the function field of the explicit normalized source chart
back to its selected ambient cover and then embed it in the common
semantic/reference source cover. -/
noncomputable def referenceChartFunctionFieldToSemanticSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    L.referenceAlgebraicChart.functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceNormalCoverToReferenceSemanticSourceCover L hind).toRingHom.comp
    (referenceFunctionFieldRingEquiv (L := L)).toRingHom

/-- The exact embedding of an arbitrary normalized `B/T` projection into
the combined semantic/reference source. -/
noncomputable def projectionToReferenceInSemanticSourceRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceChartFunctionFieldToSemanticSourceRingHom L hind).comp
    ((L.projectionFunctionFieldRingHom p x
      (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hfield).comp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) hp))

/-- The intrinsic coefficient field of the selected `B` germ lies in the
selected normalized `B/T` cover. -/
theorem bGermCoefficientField_le_selectedBNormalField :
    w.bGermCoefficientField hψ ≤
      (FiniteCover.normalClosureOver
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep)).restrictScalars k := by
  intro z hz
  apply FiniteCover.extendScalars_le_normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField
      (k := k) w.bReps w.T.rep)
  change z ∈ rankTwoScalarField (k := k) w.bReps w.T.rep
  apply rankTwoParameterField_le_rankTwoScalarField
  change z ∈ w.bField
  exact w.bGermCoefficientField_le_bField hψ hz

/-- Literal inclusion of the intrinsic selected-`B` germ coefficient field
in the rank-two parameter field generated by the selected `B` tuple. -/
def bGermCoefficientToSelectedBParameterAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(rankTwoParameterField (k := k) w.bReps)) where
  toFun z := ⟨z, by
    change z.1 ∈ w.bField
    exact w.bGermCoefficientField_le_bField hψ z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Include the intrinsic selected-`B` coefficient field in the whole
selected nonnormal `B/T` scalar branch.  This is the common domain on which
the four complete-edge restrictions will be compared. -/
def bGermCoefficientToSelectedBScalarExtensionAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (rankTwoScalarExtension (k := k) w.bReps w.T.rep) :=
  (IntermediateField.inclusion
    (rankTwoParameterField_le_rankTwoScalarField
      (k := k) w.bReps w.T.rep)).comp
    (bGermCoefficientToSelectedBParameterAlgHom (w := w) (hψ := hψ))

/-- Literal inclusion of the intrinsic selected-`B` germ coefficient field
in the selected normalized `B/T` cover. -/
def bGermCoefficientToSelectedBNormalAlgHom :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      rankTwoScalarNormalField (k := k) w.bReps w.T.rep :=
  IntermediateField.algHomIntoOfLeRestrictScalars
    (w.bGermCoefficientField hψ)
    (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) w.bReps w.T.rep))
    (bGermCoefficientField_le_selectedBNormalField (w := w) (hψ := hψ))

/-- The direct inclusion in the selected scalar normal field factors through
the selected rank-two parameter field. -/
theorem bGermCoefficientToSelectedBNormalAlgHom_eq_algebraMap
    (z : w.bGermCoefficientField hψ) :
    bGermCoefficientToSelectedBNormalAlgHom (w := w) (hψ := hψ) z =
      algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep)
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) := by
  apply Subtype.ext
  rfl

/-- The generic-point identification between the selected normalized
`B/T` chart and its ambient normal field, with its finite-dimensional
instance sealed inside the definition. -/
noncomputable def selectedBFunctionFieldAlgEquiv :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField ≃+*
      rankTwoScalarNormalField (k := k) w.bReps w.T.rep := by
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (w.T_rep_mem_racl_bReps hψ)
  exact (FiniteExtensionChart.functionFieldAlgEquiv
    (k := k) (K := ↥(rankTwoParameterField (k := k) w.bReps))
    (L := rankTwoScalarNormalField (k := k) w.bReps w.T.rep)
    (rankTwoParameterCoordinates (k := k) w.bReps)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) w.bReps)).toRingEquiv

/-- The selected `B/T` scalar generator, expressed intrinsically in the
function field of the selected normalized chart. -/
noncomputable def selectedBScalarFunctionFieldElement :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField :=
  (selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)).symm
    (rankTwoScalarSelectedNormalElement
      (k := k) w.bReps w.T.rep)

/-- Embed the entire selected, generally nonnormal `B/T` scalar branch in
the function field of its normalized chart. -/
noncomputable def selectedBScalarExtensionToFunctionFieldRingHom :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
        (k := k) (K := K) (w := w) (hψ := hψ)).functionField :=
  (selectedBFunctionFieldAlgEquiv
      (w := w) (hψ := hψ)).symm.toRingHom.comp
    (FiniteCover.selectedEmbedding
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) w.bReps w.T.rep)).toRingHom

/-- Conjugating the selected scalar-branch inclusion through the generic
point identification recovers its literal normal-cover embedding. -/
theorem selectedBScalarExtensionToFunctionFieldRingHom_conjugate
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)
        (selectedBScalarExtensionToFunctionFieldRingHom
          (w := w) (hψ := hψ) z) =
      FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z := by
  unfold selectedBScalarExtensionToFunctionFieldRingHom
  simp only [RingHom.comp_apply]
  exact (selectedBFunctionFieldAlgEquiv
    (w := w) (hψ := hψ)).apply_symm_apply _

/-- Pointwise form of the selected scalar-branch inclusion. -/
theorem selectedBScalarExtensionToFunctionFieldRingHom_eq
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    selectedBScalarExtensionToFunctionFieldRingHom
        (w := w) (hψ := hψ) z =
      (selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)).symm
        (FiniteCover.selectedEmbedding
          (rankTwoParameterField_le_rankTwoScalarField
            (k := k) w.bReps w.T.rep) z) :=
  rfl

@[simp] theorem selectedBFunctionFieldAlgEquiv_selectedBScalar :
    selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep := by
  simp [selectedBScalarFunctionFieldElement]

/-- Embed the intrinsic selected-`B` germ coefficients into the
scheme-theoretic function field of the selected normalized `B/T` chart. -/
noncomputable def bGermCoefficientToSelectedBFunctionFieldRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
        (k := k) (K := K) (w := w) (hψ := hψ)).functionField := by
  exact (selectedBFunctionFieldAlgEquiv
    (w := w) (hψ := hψ)).symm.toRingHom.comp
      (bGermCoefficientToSelectedBNormalAlgHom (w := w) (hψ := hψ)).toRingHom

/-- Conjugating the intrinsic coefficient embedding back through the
selected chart recovers its literal inclusion in the selected normal field. -/
theorem bGermCoefficientToSelectedBFunctionFieldRingHom_conjugate
    (z : w.bGermCoefficientField hψ) :
    selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)
        (bGermCoefficientToSelectedBFunctionFieldRingHom
          (w := w) (hψ := hψ) z) =
      bGermCoefficientToSelectedBNormalAlgHom (w := w) (hψ := hψ) z := by
  simp [bGermCoefficientToSelectedBFunctionFieldRingHom]

/-- Equivalently, the intrinsic coefficient embedding in the selected
chart is the inverse generic-point image of its literal normal-field
inclusion. -/
theorem bGermCoefficientToSelectedBFunctionFieldRingHom_eq
    (z : w.bGermCoefficientField hψ) :
    bGermCoefficientToSelectedBFunctionFieldRingHom
        (w := w) (hψ := hψ) z =
      (selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)).symm
        (bGermCoefficientToSelectedBNormalAlgHom
          (w := w) (hψ := hψ) z) := by
  apply (selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ)).injective
  rw [bGermCoefficientToSelectedBFunctionFieldRingHom_conjugate]
  exact (selectedBFunctionFieldAlgEquiv
    (w := w) (hψ := hψ)).apply_symm_apply _ |>.symm

/-- The ambient normal-cover equivalence carried by the selected-to-`p`
reference transition. -/
noncomputable def selectedBNormalEquivProjection [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x) :
    rankTwoScalarNormalField (k := k) w.bReps w.T.rep ≃ₐ[k]
      rankTwoScalarNormalField (k := k) p x :=
  (rankTwoScalarLocusReferenceAlgEquiv
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (w.T_rep_mem_racl_bReps hψ)
    hp.symm
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBProjectionRelation
      (w := w)).symm).symm

/-- On the selected parameter field, the normalized reference transition is
the canonical function-field transport induced by equality of the two
rank-two parameter loci. -/
theorem selectedBNormalEquivProjection_algebraMap [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x)
    (z : rankTwoParameterField (k := k) w.bReps) :
    selectedBNormalEquivProjection (w := w) (hψ := hψ) hp
        (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
          (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) =
      algebraMap (↥(rankTwoParameterField (k := k) p))
        (rankTwoScalarNormalField (k := k) p x)
        (locusFunctionFieldEquivOfIdealEq
          (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm) z) := by
  rw [selectedBNormalEquivProjection,
    rankTwoScalarLocusReferenceAlgEquiv_symm]
  let hselected := w.T_rep_mem_racl_bReps hψ
  let hself : idealOf k (rankTwoScalarTuple w.bReps w.T.rep) =
      idealOf k (rankTwoScalarTuple w.bReps w.T.rep) := rfl
  let es := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected hselected hself
  let ep := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
  change ep (es.symm
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z)) = _
  have hes : es
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) =
      algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z := by
    change rankTwoScalarLocusBasedNormalCoverAlgEquiv
        hselected hselected hself
        (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
          (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) = _
    rw [rankTwoScalarLocusBasedNormalCoverAlgEquiv_algebraMap]
    change algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep)
        (locusFunctionFieldEquivOfIdealEq
          (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hself) z) = _
    rw [locusFunctionFieldEquivOfIdealEq_refl]
    rfl
  have hes' : es.symm
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) =
      algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z :=
    es.symm_apply_eq.mpr hes.symm
  rw [hes']
  change rankTwoScalarLocusBasedNormalCoverAlgEquiv hselected
      (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) = _
  rw [rankTwoScalarLocusBasedNormalCoverAlgEquiv_algebraMap]
  rfl

/-- The normalized selected-to-projection transport carries the literal
selected scalar branch to the literal scalar displayed by that projection. -/
theorem selectedBNormalEquivProjection_selected [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x) :
    selectedBNormalEquivProjection (w := w) (hψ := hψ) hp
        (rankTwoScalarSelectedNormalElement
          (k := k) w.bReps w.T.rep) =
      rankTwoScalarSelectedNormalElement (k := k) p x := by
  rw [selectedBNormalEquivProjection,
    rankTwoScalarLocusReferenceAlgEquiv_symm]
  let hselected := w.T_rep_mem_racl_bReps hψ
  let hself : idealOf k (rankTwoScalarTuple w.bReps w.T.rep) =
      idealOf k (rankTwoScalarTuple w.bReps w.T.rep) := rfl
  let es := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected hselected hself
  let ep := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
  change ep (es.symm
      (rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep)) = _
  have hes : es
      (rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep) =
      rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep := by
    change rankTwoScalarLocusBasedNormalCoverAlgEquiv
        hselected hselected hself
        (rankTwoScalarSelectedNormalElement
          (k := k) w.bReps w.T.rep) = _
    exact rankTwoScalarLocusBasedNormalCoverAlgEquiv_selected
      hselected hselected hself
  have hes' : es.symm
      (rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep) =
      rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep :=
    es.symm_apply_eq.mpr hes.symm
  rw [hes']
  change rankTwoScalarLocusBasedNormalCoverAlgEquiv hselected
      (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
      (rankTwoScalarSelectedNormalElement
        (k := k) w.bReps w.T.rep) = _
  exact rankTwoScalarLocusBasedNormalCoverAlgEquiv_selected
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm

/-- The normalized selected-to-projection transition preserves the whole
literal nonnormal scalar branch, through the canonical total-field
equivalence induced by equality of the displayed `B/T` loci. -/
theorem selectedBNormalEquivProjection_selectedExtension [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x)
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    selectedBNormalEquivProjection (w := w) (hψ := hψ) hp
        (FiniteCover.selectedEmbedding
          (rankTwoParameterField_le_rankTwoScalarField
            (k := k) w.bReps w.T.rep) z) =
      FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField (k := k) p x)
        ((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) hp.symm).totalEquiv z) := by
  rw [selectedBNormalEquivProjection,
    rankTwoScalarLocusReferenceAlgEquiv_symm]
  let hselected := w.T_rep_mem_racl_bReps hψ
  let hself : idealOf k (rankTwoScalarTuple w.bReps w.T.rep) =
      idealOf k (rankTwoScalarTuple w.bReps w.T.rep) := rfl
  let es := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected hselected hself
  let ep := rankTwoScalarLocusBasedNormalCoverAlgEquiv
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
  change ep (es.symm
      (FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z)) = _
  have hes : es
      (FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z) =
      FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z := by
    have hz := (rankTwoScalarLocusBasedNormalEquiv
      hselected hselected hself).map_selected_apply z
    have htotal :
        (rankTwoScalarExtensionEquivOfIdealEq
          (k := k) hself).totalEquiv = AlgEquiv.refl := by
      exact locusFunctionFieldEquivOfIdealEq_refl _
    rw [htotal] at hz
    exact hz
  have hes' : es.symm
      (FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z) =
      FiniteCover.selectedEmbedding
        (rankTwoParameterField_le_rankTwoScalarField
          (k := k) w.bReps w.T.rep) z :=
    es.symm_apply_eq.mpr hes.symm
  rw [hes']
  exact (rankTwoScalarLocusBasedNormalEquiv hselected
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
      hp.symm).map_selected_apply z

/-- Canonical transport of intrinsic selected-`B` germ coefficients to the
parameter field of an arbitrary `B/T` projection realization. -/
noncomputable def bGermCoefficientToProjectionParameterAlgHom
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x) :
    (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(rankTwoParameterField (k := k) p)) :=
  (locusFunctionFieldEquivOfIdealEq
      (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)).toAlgHom.comp
    (bGermCoefficientToSelectedBParameterAlgHom (w := w) (hψ := hψ))

/-- The selected-to-projection normal equivalence restricts on intrinsic
germ coefficients to their canonical parameter-field transport. -/
theorem selectedBNormalEquivProjection_bGermCoefficient
    [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x)
    (z : w.bGermCoefficientField hψ) :
    selectedBNormalEquivProjection (w := w) (hψ := hψ) hp
        (bGermCoefficientToSelectedBNormalAlgHom
          (w := w) (hψ := hψ) z) =
      algebraMap (↥(rankTwoParameterField (k := k) p))
        (rankTwoScalarNormalField (k := k) p x)
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) hp z) := by
  rw [bGermCoefficientToSelectedBNormalAlgHom_eq_algebraMap]
  rw [selectedBNormalEquivProjection_algebraMap]
  rfl

/-- The generic-point identification of an arbitrary normalized `B/T`
projection chart with its ambient scalar normal field. -/
noncomputable def projectionBFunctionFieldRingEquiv [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x) :
    (w.psiBProjectionAlgebraicChart hψ hp).functionField ≃+*
      rankTwoScalarNormalField (k := k) p x := by
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
  exact (FiniteExtensionChart.functionFieldAlgEquiv
    (k := k) (K := ↥(rankTwoParameterField (k := k) p))
    (L := rankTwoScalarNormalField (k := k) p x)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)).toRingEquiv

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating the selected-to-projection chart transition by the two
generic-point identifications recovers the ambient normalized reference
equivalence exactly. -/
theorem normalizedToSelectedFunctionFieldRingHom_conjugate
    [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hp : w.psiBProjectionRelation p x)
    (z : rankTwoScalarNormalField (k := k) w.bReps w.T.rep) :
    projectionBFunctionFieldRingEquiv (w := w) (hψ := hψ) hp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) hp
          ((selectedBFunctionFieldAlgEquiv
            (w := w) (hψ := hψ)).symm z)) =
      selectedBNormalEquivProjection (w := w) (hψ := hψ) hp z := by
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (w.T_rep_mem_racl_bReps hψ)
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
  let hx := PsiBProjectionRelation.scalar_mem_racl w hψ hp
  let hy := w.T_rep_mem_racl_bReps hψ
  let ep := FiniteExtensionChart.functionFieldAlgEquiv
    (k := k) (K := ↥(rankTwoParameterField (k := k) p))
    (L := rankTwoScalarNormalField (k := k) p x)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
  let eb := FiniteExtensionChart.functionFieldAlgEquiv
    (k := k) (K := ↥(rankTwoParameterField (k := k) w.bReps))
    (L := rankTwoScalarNormalField (k := k) w.bReps w.T.rep)
    (rankTwoParameterCoordinates (k := k) w.bReps)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) w.bReps)
  let en := rankTwoScalarLocusReferenceAlgEquiv
    hy hx hy hp.symm
      (QWitness.PsiChunkFourArrowEdgeLifts.selectedBProjectionRelation
        (w := w)).symm
  change ep ((FiniteExtensionTransition.functionFieldAlgEquiv
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates (k := k) w.bReps)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) w.bReps)
      en).symm (eb.symm z)) = en.symm z
  rw [← FiniteExtensionTransition.functionFieldAlgEquiv_symm]
  simp [FiniteExtensionTransition.functionFieldAlgEquiv, ep, eb]

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating a direct normalized projection by the generic-point
identifications recovers the literal inclusion of its ambient scalar normal
field in the full reference normal cover. -/
theorem projectionFunctionFieldRingHom_conjugate [IsAlgClosed K]
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (z : (w.psiBProjectionAlgebraicChart hψ hp).functionField) :
    (referenceFunctionFieldRingEquiv (L := L)).toRingHom
        (L.projectionFunctionFieldRingHom p x
          (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hfield z) =
      L.scalarNormalFieldToReferenceNormalCover p x hfield
        (projectionBFunctionFieldRingEquiv (w := w) (hψ := hψ) hp z) := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
  change FiniteExtensionChart.functionFieldAlgEquiv
      (k := k) (K := ↥D.inputField) (L := ↥L.referenceNormalCover)
      D.inputCoordinates D.adjoin_inputCoordinates_eq_top
      (FiniteExtensionProjection.functionFieldAlgHom
        D.inputCoordinates (rankTwoParameterCoordinates (k := k) p)
        D.adjoin_inputCoordinates_eq_top
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
        (L.scalarNormalFieldToReferenceNormalCover p x hfield) z) =
    L.scalarNormalFieldToReferenceNormalCover p x hfield
      (FiniteExtensionChart.functionFieldAlgEquiv
        (k := k) (K := ↥(rankTwoParameterField (k := k) p))
        (L := rankTwoScalarNormalField (k := k) p x)
        (rankTwoParameterCoordinates (k := k) p)
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p) z)
  exact FiniteExtensionProjection.functionFieldAlgHom_commutes
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) p)
    D.adjoin_inputCoordinates_eq_top
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (L.scalarNormalFieldToReferenceNormalCover p x hfield) z

/-- Evaluating a promoted reference map on an element of the selected
normalized `B/T` field has the expected literal ambient formula: apply the
selected-to-projection normal-cover equivalence, include that scalar cover
in the original reference cover, and finally use the common-codomain
embedding. -/
theorem projectionToReferenceInSemanticSourceRingHom_apply_selectedNormal
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (z : rankTwoScalarNormalField (k := k) w.bReps w.T.rep) :
    R.projectionToReferenceInSemanticSourceRingHom L hind p x hp hfield
        ((selectedBFunctionFieldAlgEquiv
          (w := w) (hψ := hψ)).symm z) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (L.scalarNormalFieldToReferenceNormalCover p x hfield
          (selectedBNormalEquivProjection (w := w) (hψ := hψ) hp z)) := by
  letI := L.referenceNormalCover_finiteDimensional
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (w.T_rep_mem_racl_bReps hψ)
  letI := rankTwoScalarNormalField_finiteDimensional
    (k := k) (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
  unfold projectionToReferenceInSemanticSourceRingHom
    referenceChartFunctionFieldToSemanticSourceRingHom
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  rw [projectionFunctionFieldRingHom_conjugate
    (L := L) p x hp hfield]
  rw [normalizedToSelectedFunctionFieldRingHom_conjugate
    (w := w) (hψ := hψ) hp z]
  rfl

/-- A promoted projection on the whole selected nonnormal `B/T` branch is
the canonical total-field transport followed by the two literal cover
inclusions. -/
theorem projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    R.projectionToReferenceInSemanticSourceRingHom L hind p x hp hfield
        (selectedBScalarExtensionToFunctionFieldRingHom
          (w := w) (hψ := hψ) z) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (L.scalarNormalFieldToReferenceNormalCover p x hfield
          (FiniteCover.selectedEmbedding
            (rankTwoParameterField_le_rankTwoScalarField (k := k) p x)
            ((rankTwoScalarExtensionEquivOfIdealEq
              (k := k) hp.symm).totalEquiv z))) := by
  rw [selectedBScalarExtensionToFunctionFieldRingHom_eq]
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedNormal
    L hind p x hp hfield]
  rw [selectedBNormalEquivProjection_selectedExtension
    (w := w) (hψ := hψ) hp z]

/-- Every promoted projection sends the intrinsic selected scalar generator
to the literal selected scalar in that projection's ambient normal cover. -/
theorem projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    R.projectionToReferenceInSemanticSourceRingHom L hind p x hp hfield
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (L.scalarNormalFieldToReferenceNormalCover p x hfield
          (rankTwoScalarSelectedNormalElement (k := k) p x)) := by
  unfold selectedBScalarFunctionFieldElement
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedNormal
    L hind p x hp hfield]
  rw [selectedBNormalEquivProjection_selected (w := w) (hψ := hψ) hp]

/-- Restrict a promoted reference projection to the intrinsic coefficient
field of the selected `B` germ. -/
noncomputable def projectionToReferenceOnBGermCoefficientRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.projectionToReferenceInSemanticSourceRingHom L hind p x hp hfield).comp
    (bGermCoefficientToSelectedBFunctionFieldRingHom (w := w) (hψ := hψ))

/-- On intrinsic germ coefficients, the promoted projection has a completely
ambient description: include the coefficient in the selected normal cover,
apply the normalized selected-to-projection equivalence, and use the two
literal cover inclusions. -/
theorem projectionToReferenceOnBGermCoefficientRingHom_apply
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (z : w.bGermCoefficientField hψ) :
    R.projectionToReferenceOnBGermCoefficientRingHom
        L hind p x hp hfield z =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (L.scalarNormalFieldToReferenceNormalCover p x hfield
          (selectedBNormalEquivProjection (w := w) (hψ := hψ) hp
            (bGermCoefficientToSelectedBNormalAlgHom
              (w := w) (hψ := hψ) z))) := by
  unfold projectionToReferenceOnBGermCoefficientRingHom
  simp only [RingHom.comp_apply]
  rw [bGermCoefficientToSelectedBFunctionFieldRingHom_eq]
  exact R.projectionToReferenceInSemanticSourceRingHom_apply_selectedNormal
    L hind p x hp hfield
    (bGermCoefficientToSelectedBNormalAlgHom (w := w) (hψ := hψ) z)

/-- The same restriction formula expressed entirely through the canonical
intrinsic-coefficient transport to the displayed projection parameter field. -/
theorem projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (z : w.bGermCoefficientField hψ) :
    R.projectionToReferenceOnBGermCoefficientRingHom
        L hind p x hp hfield z =
      R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (L.scalarNormalFieldToReferenceNormalCover p x hfield
          (algebraMap (↥(rankTwoParameterField (k := k) p))
            (rankTwoScalarNormalField (k := k) p x)
            (bGermCoefficientToProjectionParameterAlgHom
              (w := w) (hψ := hψ) hp z))) := by
  rw [R.projectionToReferenceOnBGermCoefficientRingHom_apply
    L hind p x hp hfield z]
  rw [selectedBNormalEquivProjection_bGermCoefficient]

/-- Restriction of the first-input reference embedding to intrinsic `B`
germ coefficients. -/
noncomputable def toReferenceEOnBGermCoefficientRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceOnBGermCoefficientRingHom L hind e L.se_e
    L.eProjectionRelation L.eNormalField_le_normalizedField

/-- Restriction of the inverse-input reference embedding to intrinsic `B`
germ coefficients. -/
noncomputable def toReferenceAOnBGermCoefficientRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceOnBGermCoefficientRingHom L hind a L.sA_a_a
    L.aProjectionRelation L.aNormalField_le_normalizedField

/-- Restriction of the second-input reference embedding to intrinsic `B`
germ coefficients. -/
noncomputable def toReferenceBOnBGermCoefficientRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceOnBGermCoefficientRingHom L hind b L.s_b_b
    L.bProjectionRelation L.bNormalField_le_normalizedField

/-- Restriction of the output reference embedding to intrinsic `B` germ
coefficients. -/
noncomputable def toReferenceCOnBGermCoefficientRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceOnBGermCoefficientRingHom L hind D.c L.sA_c_c
    L.cProjectionRelation L.cNormalField_le_normalizedField

/-- All four named reference restrictions are the canonical intrinsic
coefficient transports into their displayed rank-two parameter fields. -/
theorem toReferenceOnBGermCoefficientRingHom_apply_parameterTransport
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : w.bGermCoefficientField hψ) :
    R.toReferenceEOnBGermCoefficientRingHom L hind z =
        R.referenceNormalCoverToReferenceSemanticSourceCover L hind
          (L.scalarNormalFieldToReferenceNormalCover e L.se_e
            L.eNormalField_le_normalizedField
            (algebraMap (↥(rankTwoParameterField (k := k) e))
              (rankTwoScalarNormalField (k := k) e L.se_e)
              (bGermCoefficientToProjectionParameterAlgHom
                (w := w) (hψ := hψ) L.eProjectionRelation z))) ∧
      R.toReferenceAOnBGermCoefficientRingHom L hind z =
        R.referenceNormalCoverToReferenceSemanticSourceCover L hind
          (L.scalarNormalFieldToReferenceNormalCover a L.sA_a_a
            L.aNormalField_le_normalizedField
            (algebraMap (↥(rankTwoParameterField (k := k) a))
              (rankTwoScalarNormalField (k := k) a L.sA_a_a)
              (bGermCoefficientToProjectionParameterAlgHom
                (w := w) (hψ := hψ) L.aProjectionRelation z))) ∧
      R.toReferenceBOnBGermCoefficientRingHom L hind z =
        R.referenceNormalCoverToReferenceSemanticSourceCover L hind
          (L.scalarNormalFieldToReferenceNormalCover b L.s_b_b
            L.bNormalField_le_normalizedField
            (algebraMap (↥(rankTwoParameterField (k := k) b))
              (rankTwoScalarNormalField (k := k) b L.s_b_b)
              (bGermCoefficientToProjectionParameterAlgHom
                (w := w) (hψ := hψ) L.bProjectionRelation z))) ∧
      R.toReferenceCOnBGermCoefficientRingHom L hind z =
        R.referenceNormalCoverToReferenceSemanticSourceCover L hind
          (L.scalarNormalFieldToReferenceNormalCover D.c L.sA_c_c
            L.cNormalField_le_normalizedField
            (algebraMap (↥(rankTwoParameterField (k := k) D.c))
              (rankTwoScalarNormalField (k := k) D.c L.sA_c_c)
              (bGermCoefficientToProjectionParameterAlgHom
                (w := w) (hψ := hψ) L.cProjectionRelation z))) := by
  exact ⟨R.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
      L hind e L.se_e L.eProjectionRelation
        L.eNormalField_le_normalizedField z,
    R.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
      L hind a L.sA_a_a L.aProjectionRelation
        L.aNormalField_le_normalizedField z,
    R.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
      L hind b L.s_b_b L.bProjectionRelation
        L.bNormalField_le_normalizedField z,
    R.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
      L hind D.c L.sA_c_c L.cProjectionRelation
        L.cNormalField_le_normalizedField z⟩

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

/-- Under the preceding parameter equivalence, the selected canonical `B`
curve equation is exactly the canonical equation of the relocated branch. -/
theorem selectedBCurveEquation_map_relocated
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal) :
    MvPolynomial.map
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ) G h).toRingHom
        (w.yzCorrespondencePairOverB hψ).curveEquation =
      G.toPair.curveEquation := by
  let F := w.yzCorrespondenceFamilyMember hψ
  let ι := commonCurveEmbedding (k := k) (K := K)
  let e₁ := F.parameterMapEquiv ι
  let e₂ := (F.map ι).parameterEquivOfIdealEq G h
  change MvPolynomial.map (e₁.trans e₂).toRingHom
      F.toPair.curveEquation = G.toPair.curveEquation
  calc
    MvPolynomial.map (e₁.trans e₂).toRingHom
        F.toPair.curveEquation =
        MvPolynomial.map e₂.toRingHom
          (MvPolynomial.map e₁.toRingHom F.toPair.curveEquation) := by
      rw [MvPolynomial.map_map]
      rfl
    _ = MvPolynomial.map e₂.toRingHom
        (F.map ι).toPair.curveEquation := by
      rw [F.curveEquation_map_parameterMapEquiv ι]
    _ = G.toPair.curveEquation :=
      (F.map ι).curveEquation_map_parameterEquivOfIdealEq G h

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

/-- The intrinsic coordinate represented by one coefficient of the selected
canonical `B` curve equation. -/
noncomputable def selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) : w.bGermCoefficientField hψ :=
  (w.yzCorrespondencePairOverB hψ).curveCoefficientCoordinates
    k w.bField
    ⟨(((w.yzCorrespondencePairOverB hψ).curveEquation.coeff d :
        w.bField) : K), ⟨d, rfl⟩⟩

/-- Including an intrinsic coefficient coordinate into the selected
parameter field recovers the corresponding literal polynomial coefficient. -/
@[simp] theorem bGermCoefficientToSelectedBParameterAlgHom_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ)
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      (w.yzCorrespondencePairOverB hψ).curveEquation.coeff d :=
  by
    apply Subtype.ext
    rfl

/-- Two coefficient-linear maps out of the intrinsic selected-`B` germ
field are equal as soon as they agree on every canonical curve
coefficient.  This is the extensionality principle used to descend the
four-arrow comparison from relocated equations to the intrinsic chart. -/
theorem bGermCoefficientAlgHom_ext
    {F : Type u} [Field F] [Algebra k F]
    {f g : (↥(w.bGermCoefficientField hψ)) →ₐ[k] F}
    (h : ∀ d : Fin 2 →₀ ℕ,
      f (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        g (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) :
    f = g := by
  unfold QWitness.bGermCoefficientField
    FiniteCorrespondencePair.curveCoefficientField
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨d, rfl⟩
  exact h d

/-- Canonical normalized parameter transport carries every intrinsic
selected-`B` curve coefficient to the corresponding coefficient of the
relocated canonical curve equation. -/
theorem projectionParameterTransport_selectedBCurveCoefficient
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) p G hG
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) hp
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
      G.toPair.curveEquation.coeff d := by
  have hcurve := selectedBCurveEquation_map_relocated
    (w := w) (hψ := hψ) G h
  have hcoeff := congrArg (fun f => f.coeff d) hcurve
  rw [MvPolynomial.coeff_map] at hcoeff
  rw [selectedBToRelocatedBParameterEquiv_eq_projection
    (w := w) (hψ := hψ) p x hp G h hG] at hcoeff
  change rankTwoParameterCurveEquivToFamily
      (k := k) (K := K) p G hG
      (locusFunctionFieldEquivOfIdealEq
        (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ)
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d))) = _
  rw [bGermCoefficientToSelectedBParameterAlgHom_selectedBCurveCoefficient]
  change rankTwoParameterCurveEquivToFamily
      (k := k) (K := K) p G hG
      (locusFunctionFieldEquivOfIdealEq
        (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)
        ((w.yzCorrespondencePairOverB hψ).curveEquation.coeff d)) = _
    at hcoeff
  exact hcoeff

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

/-- On every canonical generator, the whole-field relocated parameter map
recovers the matching coefficient of the relocated curve equation. -/
@[simp] theorem
    bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      G.toPair.curveEquation.coeff d := by
  exact projectionParameterTransport_selectedBCurveCoefficient
    (w := w) (hψ := hψ) p x hp G h hG d

/-- The ambient form of the intrinsic coefficient transport.  Its image is
exactly the intrinsic coefficient field of the relocated canonical curve. -/
private noncomputable def bGermToRelocatedAmbientAlgHom
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥((w.yzCorrespondencePairOverB hψ).curveCoefficientField
      k w.bField)) →ₐ[k] CommonCurveAmbient K :=
  G.parameterField.val.comp
    (bGermCoefficientToRelocatedBParameterAlgHom
      (w := w) (hψ := hψ) p x hp G hG)

private theorem bGermToRelocatedAmbient_fieldRange
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (bGermToRelocatedAmbientAlgHom
      (w := w) (hψ := hψ) p x hp G hG).fieldRange =
      G.toPair.curveCoefficientField k G.parameterField := by
  have htop := (w.yzCorrespondencePairOverB hψ).adjoin_curveCoefficientCoordinates_eq_top
    k w.bField
  have htop' : (⊤ : IntermediateField k
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientField k w.bField)) =
      IntermediateField.adjoin k
        (Set.range ((w.yzCorrespondencePairOverB hψ).curveCoefficientCoordinates
          k w.bField)) := htop.symm
  rw [AlgHom.fieldRange_eq_map, htop', IntermediateField.adjoin_map]
  unfold FiniteCorrespondencePair.curveCoefficientField
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := c.2
    have hc : c = ⟨_, ⟨d, rfl⟩⟩ := Subtype.ext hd.symm
    subst c
    refine ⟨d, ?_⟩
    exact (congrArg Subtype.val
      (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
        (w := w) (hψ := hψ) p x hp G h hG d)).symm
  · rintro ⟨d, rfl⟩
    refine ⟨selectedBCurveCoefficient (w := w) (hψ := hψ) d, ?_, ?_⟩
    · exact ⟨⟨_, ⟨d, rfl⟩⟩, rfl⟩
    · exact congrArg Subtype.val
        (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
          (w := w) (hψ := hψ) p x hp G h hG d)

private theorem bGermToRelocatedAmbient_mem_curveCoefficientField
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (z : w.bGermCoefficientField hψ) :
    bGermToRelocatedAmbientAlgHom
        (w := w) (hψ := hψ) p x hp G hG z ∈
      G.toPair.curveCoefficientField k G.parameterField := by
  rw [← bGermToRelocatedAmbient_fieldRange
    (w := w) (hψ := hψ) p x hp G h hG]
  exact AlgHom.mem_fieldRange.mpr ⟨z, rfl⟩

/-- The intrinsic selected-`B` coefficient field is canonically equivalent
to the intrinsic coefficient field of any relocated canonical curve on the
same family locus. -/
noncomputable def bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥(G.toPair.curveCoefficientField k G.parameterField)) := by
  let f : (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(G.toPair.curveCoefficientField k G.parameterField)) :=
    (bGermToRelocatedAmbientAlgHom
      (w := w) (hψ := hψ) p x hp G hG).codRestrict
      (G.toPair.curveCoefficientField k G.parameterField).toSubalgebra
      (bGermToRelocatedAmbient_mem_curveCoefficientField
        (w := w) (hψ := hψ) p x hp G h hG)
  apply AlgEquiv.ofBijective f
  constructor
  · exact f.injective
  · intro y
    have hy : (y : CommonCurveAmbient K) ∈
        (bGermToRelocatedAmbientAlgHom
          (w := w) (hψ := hψ) p x hp G hG).fieldRange := by
      rw [bGermToRelocatedAmbient_fieldRange
        (w := w) (hψ := hψ) p x hp G h hG]
      exact y.2
    obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hy
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz

/-- The intrinsic coefficient equivalence preserves the monomial index of
every canonical curve coefficient. -/
@[simp] theorem bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToRelocatedBCoefficientAlgEquiv
        (w := w) (hψ := hψ) p x hp G h hG
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      ⟨((G.toPair.curveEquation.coeff d : G.parameterField) :
          CommonCurveAmbient K),
        G.toPair.coeff_mem_curveCoefficientField k G.parameterField d⟩ := by
  apply Subtype.ext
  change ((bGermCoefficientToRelocatedBParameterAlgHom
      (w := w) (hψ := hψ) p x hp G hG
      (selectedBCurveCoefficient (w := w) (hψ := hψ) d) :
        G.parameterField) : CommonCurveAmbient K) = _
  exact congrArg Subtype.val
    (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
      (w := w) (hψ := hψ) p x hp G h hG d)

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

/-- The complete-branch inclusion does not change the ambient value of an
intrinsic relocated coefficient. -/
@[simp] theorem relocatedBCoefficientToCompleteRightBranchRingHom_val
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (z : G.toPair.curveCoefficientField k G.parameterField) :
    ((relocatedBCoefficientToCompleteRightBranchRingHom G z :
        G.toPair.branchOverSource) : CommonCurveAmbient K) = z :=
  rfl

/-- The whole relocated parameter transport is the intrinsic coefficient
equivalence followed by the literal inclusion of the relocated coefficient
field into its displayed parameter field. -/
theorem bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG =
      (IntermediateField.inclusion
        (G.toPair.curveCoefficientField_le k G.parameterField)).comp
        (bGermCoefficientToRelocatedBCoefficientAlgEquiv
          (w := w) (hψ := hψ) p x hp G h hG).toAlgHom := by
  apply bGermCoefficientAlgHom_ext (w := w) (hψ := hψ)
  intro d
  rw [bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (w := w) (hψ := hψ) p x hp G h hG d]
  apply Subtype.ext
  exact (congrArg Subtype.val
    (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
      (w := w) (hψ := hψ) p x hp G h hG d)).symm

/-- Embedding the relocated parameter transport in the complete branch is
the same map as passing through the intrinsic relocated coefficient field.
This turns the coefficient factorization into an exact branch restriction. -/
theorem bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (algebraMap (↥G.parameterField)
        (↥G.toPair.branchOverSource)).comp
          (bGermCoefficientToRelocatedBParameterAlgHom
            (w := w) (hψ := hψ) p x hp G hG).toRingHom =
      (relocatedBCoefficientToCompleteRightBranchRingHom G).comp
        (bGermCoefficientToRelocatedBCoefficientAlgEquiv
          (w := w) (hψ := hψ) p x hp G h hG).toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  change algebraMap (↥G.parameterField) (↥G.toPair.branchOverSource)
      (bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG z) =
    relocatedBCoefficientToCompleteRightBranchRingHom G
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv
        (w := w) (hψ := hψ) p x hp G h hG z)
  rw [DFunLike.congr_fun
    (bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) p x hp G h hG) z]
  apply Subtype.ext
  rfl

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

/-- Include the original selected `B` parameter field in the complete
branch of its mapped family member.  This is the one common middle-branch
map from which the four relocated complete-branch transports start. -/
noncomputable def selectedBParameterToMappedCompleteBranchRingHom :
    (↥w.bField) →+*
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) :=
  (algebraMap
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).parameterField)
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource)).comp
    ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
      (commonCurveEmbedding (k := k) (K := K))).toRingEquiv.toRingHom

/-- Restrict the common mapped selected-`B` branch to the intrinsic germ
coefficient field.  This is the candidate common middle map for the final
right-restriction package. -/
noncomputable def bGermCoefficientToMappedCompleteBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) :=
  (selectedBParameterToMappedCompleteBranchRingHom
    (w := w) (hψ := hψ)).comp
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ)).toRingHom

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

/-- Simultaneously, the four full branch equivalences restrict on the
whole selected `B` parameter field to the canonical selected-to-relocated
parameter transports.  Thus the common middle branch is already identified
before passing to normal middle and target covers. -/
theorem fourSelectedBCompleteBranchRingEquiv_parameter :
    R.seSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.se.bCorrespondenceFamilyMember hψ)
              R.seMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sAaSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sAa.bCorrespondenceFamilyMember hψ)
              R.sAaMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sbSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sb.bCorrespondenceFamilyMember hψ)
              R.sbMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sAcSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sAc.bCorrespondenceFamilyMember hψ)
              R.sAcMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply RingHom.ext <;> intro z
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))

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

/-- Simultaneously, the four corrected normal-cover equivalences extend the
four full complete-branch equivalences.  This is the normal middle-cover
transport required before the four target covers are joined. -/
theorem fourSelectedBNormalCoverRingEquiv_completeBranch :
    R.seSelectedBNormalCoverRingEquiv.toRingHom.comp
        (mappedSelectedBFamily (w := w) (hψ := hψ)
          |>.completeBranchToNormalCoverRingHom) =
      (R.se.bCorrespondenceFamilyMember hψ
        |>.completeBranchToNormalCoverRingHom).comp
          R.seSelectedBCompleteBranchRingEquiv.toRingHom ∧
    R.sAaSelectedBNormalCoverRingEquiv.toRingHom.comp
        (mappedSelectedBFamily (w := w) (hψ := hψ)
          |>.completeBranchToNormalCoverRingHom) =
      (R.sAa.bCorrespondenceFamilyMember hψ
        |>.completeBranchToNormalCoverRingHom).comp
          R.sAaSelectedBCompleteBranchRingEquiv.toRingHom ∧
    R.sbSelectedBNormalCoverRingEquiv.toRingHom.comp
        (mappedSelectedBFamily (w := w) (hψ := hψ)
          |>.completeBranchToNormalCoverRingHom) =
      (R.sb.bCorrespondenceFamilyMember hψ
        |>.completeBranchToNormalCoverRingHom).comp
          R.sbSelectedBCompleteBranchRingEquiv.toRingHom ∧
    R.sAcSelectedBNormalCoverRingEquiv.toRingHom.comp
        (mappedSelectedBFamily (w := w) (hψ := hψ)
          |>.completeBranchToNormalCoverRingHom) =
      (R.sAc.bCorrespondenceFamilyMember hψ
        |>.completeBranchToNormalCoverRingHom).comp
          R.sAcSelectedBCompleteBranchRingEquiv.toRingHom := by
  exact ⟨mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.basedNormalEquivOfIdealEq_completeBranch
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq,
    mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.basedNormalEquivOfIdealEq_completeBranch
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq,
    mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.basedNormalEquivOfIdealEq_completeBranch
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq,
    mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.basedNormalEquivOfIdealEq_completeBranch
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq⟩

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

/-- All four normalized parameter transports carry each intrinsic selected
`B` coefficient to the coefficient with the same monomial index in the
corresponding relocated right-branch equation. -/
theorem fourProjectionParameterTransports_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) e
        (R.se.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.eProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) a
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.aProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) b
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.bProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) D.c
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.2
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.cProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d := by
  exact ⟨projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.2 d⟩

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

/-- The intrinsic coefficient equivalence for the relocated right family in
the `s·e=u` face. -/
noncomputable def seBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.se.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.se.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
    (R.se.bCorrespondenceFamilyMember hψ)
    R.seMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `sA·a=u` face. -/
noncomputable def sAaBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sAa.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
    (R.sAa.bCorrespondenceFamilyMember hψ)
    R.sAaMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `s·b=uB` face. -/
noncomputable def sbBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sb.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
    (R.sb.bCorrespondenceFamilyMember hψ)
    R.sbMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.2.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `sA·c=uB` face. -/
noncomputable def sAcBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sAc.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
    (R.sAc.bCorrespondenceFamilyMember hψ)
    R.sAcMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.2.2

/-- The intrinsic selected-`B` coefficient field embedded in the complete
right `e` branch through its relocated coefficient field. -/
noncomputable def seBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.se.bCorrespondenceFamilyMember hψ)).comp
      (R.seBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `a`
branch. -/
noncomputable def sAaBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sAa.bCorrespondenceFamilyMember hψ)).comp
      (R.sAaBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `b`
branch. -/
noncomputable def sbBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sb.bCorrespondenceFamilyMember hψ)).comp
      (R.sbBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `c`
branch. -/
noncomputable def sAcBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sAc.bCorrespondenceFamilyMember hψ)).comp
      (R.sAcBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The four intrinsic complete-branch embeddings are restrictions of the
four full branch equivalences from one common mapped selected-`B` branch.
This is the branch-level middle chart, before extension to the four normal
middle covers. -/
theorem fourBGermCoefficientCompleteBranch_factor_selectedB :
    R.seSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.seBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sAaSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sbSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sbBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sAcSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L := by
  obtain ⟨he, ha, hb, hc⟩ :=
    R.fourSelectedBCompleteBranchRingEquiv_parameter
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply RingHom.ext <;> intro z
  · have hbranch := DFunLike.congr_fun he
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.seBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.1) z
    change algebraMap
        (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.seBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.seBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun ha
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.1) z
    change algebraMap
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sAaBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun hb
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.1) z
    change algebraMap
        (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sbBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sbBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun hc
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.2)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.2) z
    change algebraMap
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sAcBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)

/-- On every canonical generator, the four complete-branch embeddings are
the literal same-index relocated curve coefficients. -/
theorem fourBGermCoefficientToCompleteRightBranchRingHom_selected
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.se.bCorrespondenceFamilyMember hψ)
          ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.se.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sAa.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sAa.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sbBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sb.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sb.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sAc.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sAc.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩ := by
  simp only [seBGermCoefficientToCompleteRightBranchRingHom,
    sAaBGermCoefficientToCompleteRightBranchRingHom,
    sbBGermCoefficientToCompleteRightBranchRingHom,
    sAcBGermCoefficientToCompleteRightBranchRingHom, RingHom.comp_apply]
  exact ⟨congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.se.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sAa.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sb.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.2.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sAc.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.2.2 d)⟩

/-- The intrinsic selected-`B` coefficient field embedded through the
original relocated `e` branch into the once-canonicalized selected cover. -/
noncomputable def seBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.seRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.seBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `a` branch. -/
noncomputable def sAaBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sAaBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `b` branch. -/
noncomputable def sbBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sbBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `c` branch. -/
noncomputable def sAcBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sAcBGermCoefficientToCompleteRightBranchRingHom L)

/-- On every canonical coefficient, the four selected-cover maps are
exactly the once-canonicalized literal relocated coefficients in their
complete branches. -/
theorem fourBGermCoefficientToSelectedSourceRingHom_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.seRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.se.bCorrespondenceFamilyMember hψ)
            ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.se.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAaBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAa.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAa.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sbBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sbRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sb.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sb.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAcBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAc.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAc.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩) := by
  unfold seBGermCoefficientToSelectedSourceRingHom
    sAaBGermCoefficientToSelectedSourceRingHom
    sbBGermCoefficientToSelectedSourceRingHom
    sAcBGermCoefficientToSelectedSourceRingHom
  simp only [RingHom.comp_apply]
  obtain ⟨he, ha, hb, hc⟩ :=
    R.fourBGermCoefficientToCompleteRightBranchRingHom_selected L d
  exact ⟨congrArg (R.seRelocatedRightBranchToSelectedSourceRingHom L hind) he,
    congrArg (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind) ha,
    congrArg (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind) hb,
    congrArg (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind) hc⟩

/-- The intrinsic selected-`B` coefficient field on the `e` face, now in
the graph source that also contains the coherent semantic cover. -/
noncomputable def seBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `a` face in the same graph
source. -/
noncomputable def sAaBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAaBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `b` face in the same graph
source. -/
noncomputable def sbBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sbBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `c` face in the same graph
source. -/
noncomputable def sAcBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAcBGermCoefficientToSelectedSourceRingHom L hind)

/-- Passing to the enlarged graph source preserves all four exact
same-index coefficient formulas. -/
theorem fourBGermCoefficientToSelectedGraphSourceRingHom_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.seRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.se.bCorrespondenceFamilyMember hψ)
            ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.se.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAaBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAaRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAa.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAa.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sbBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sbRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sb.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sb.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAcBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAcRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAc.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAc.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩) := by
  let ι :=
    R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover L hind
  constructor
  · have he :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).1
    simpa [seBGermCoefficientToSelectedGraphSourceRingHom,
      seRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι he
  constructor
  · have ha :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.1
    simpa [sAaBGermCoefficientToSelectedGraphSourceRingHom,
      sAaRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι ha
  constructor
  · have hb :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.2.1
    simpa [sbBGermCoefficientToSelectedGraphSourceRingHom,
      sbRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι hb
  · have hc :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.2.2
    simpa [sAcBGermCoefficientToSelectedGraphSourceRingHom,
      sAcRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι hc

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

/-- Simultaneously, the four whole-field maps recover the coefficient with
the same monomial index in each relocated right-family equation. -/
theorem
    fourBGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d := by
  exact R.fourProjectionParameterTransports_selectedBCurveCoefficient L d

/-- Include a relocated right-family parameter field in the final
semantic/reference source by returning through its displayed rank-two
parameter chart and then using the normalized scalar-cover embedding. -/
noncomputable def relocatedBParameterToReferenceSemanticSourceRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥G.parameterField) →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceNormalCoverToReferenceSemanticSourceCover L hind).toRingHom.comp
    ((L.scalarNormalFieldToReferenceNormalCover p x hfield).toRingHom.comp
      ((algebraMap (↥(rankTwoParameterField (k := k) p))
          (rankTwoScalarNormalField (k := k) p x)).comp
        (rankTwoParameterCurveEquivToFamily
          (k := k) (K := K) p G hG).symm.toRingEquiv.toRingHom))

/-- The promoted intrinsic reference map factors on the entire germ
coefficient field through the corresponding relocated family parameter
field. -/
theorem
    projectionToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    R.projectionToReferenceOnBGermCoefficientRingHom
        L hind p x hp hfield =
      (R.relocatedBParameterToReferenceSemanticSourceRingHom
        L hind p x hfield G hG).comp
      (bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG).toRingHom := by
  apply RingHom.ext
  intro z
  rw [R.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport
    L hind p x hp hfield z]
  unfold relocatedBParameterToReferenceSemanticSourceRingHom
    bGermCoefficientToRelocatedBParameterAlgHom
  simp only [RingHom.comp_apply]
  let ep := rankTwoParameterCurveEquivToFamily
    (k := k) (K := K) p G hG
  change _ = R.referenceNormalCoverToReferenceSemanticSourceCover L hind
    (L.scalarNormalFieldToReferenceNormalCover p x hfield
      (algebraMap (↥(rankTwoParameterField (k := k) p))
        (rankTwoScalarNormalField (k := k) p x)
        (ep.symm (ep
          (bGermCoefficientToProjectionParameterAlgHom
            (w := w) (hψ := hψ) hp z)))))
  rw [ep.symm_apply_apply]

/-- All four explicit intrinsic reference maps factor through their full
relocated right-family parameter fields.  Together with the preceding
generator formulas, this reduces the remaining semantic comparison to an
equality on canonical curve coefficients. -/
theorem fourToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEOnBGermCoefficientRingHom L hind =
        (R.relocatedBParameterToReferenceSemanticSourceRingHom L hind
          e L.se_e L.eNormalField_le_normalizedField
          (R.se.bCorrespondenceFamilyMember hψ)
          R.relocatedBFamily_parameters.1).comp
          (R.seBGermCoefficientToRelocatedBParameterAlgHom L).toRingHom ∧
      R.toReferenceAOnBGermCoefficientRingHom L hind =
        (R.relocatedBParameterToReferenceSemanticSourceRingHom L hind
          a L.sA_a_a L.aNormalField_le_normalizedField
          (R.sAa.bCorrespondenceFamilyMember hψ)
          R.relocatedBFamily_parameters.2.1).comp
          (R.sAaBGermCoefficientToRelocatedBParameterAlgHom L).toRingHom ∧
      R.toReferenceBOnBGermCoefficientRingHom L hind =
        (R.relocatedBParameterToReferenceSemanticSourceRingHom L hind
          b L.s_b_b L.bNormalField_le_normalizedField
          (R.sb.bCorrespondenceFamilyMember hψ)
          R.relocatedBFamily_parameters.2.2.1).comp
          (R.sbBGermCoefficientToRelocatedBParameterAlgHom L).toRingHom ∧
      R.toReferenceCOnBGermCoefficientRingHom L hind =
        (R.relocatedBParameterToReferenceSemanticSourceRingHom L hind
          D.c L.sA_c_c L.cNormalField_le_normalizedField
          (R.sAc.bCorrespondenceFamilyMember hψ)
          R.relocatedBFamily_parameters.2.2.2).comp
          (R.sAcBGermCoefficientToRelocatedBParameterAlgHom L).toRingHom := by
  exact
    ⟨R.projectionToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
        L hind e L.se_e L.eProjectionRelation
        L.eNormalField_le_normalizedField
        (R.se.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.1,
      R.projectionToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
        L hind a L.sA_a_a L.aProjectionRelation
        L.aNormalField_le_normalizedField
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.1,
      R.projectionToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
        L hind b L.s_b_b L.bProjectionRelation
        L.bNormalField_le_normalizedField
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.1,
      R.projectionToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter
        L hind D.c L.sA_c_c L.cProjectionRelation
        L.cNormalField_le_normalizedField
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.2⟩

/-- The first-input `toReferenceE` embedding, now with the same literal
codomain as the semantic four-arrow action. -/
noncomputable def toReferenceEInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceInSemanticSourceRingHom L hind e L.se_e
    L.eProjectionRelation L.eNormalField_le_normalizedField

/-- The inverse-input `toReferenceA` embedding in the combined source. -/
noncomputable def toReferenceAInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceInSemanticSourceRingHom L hind a L.sA_a_a
    L.aProjectionRelation L.aNormalField_le_normalizedField

/-- The second-input `toReferenceB` embedding in the combined source. -/
noncomputable def toReferenceBInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceInSemanticSourceRingHom L hind b L.s_b_b
    L.bProjectionRelation L.bNormalField_le_normalizedField

/-- The output `toReferenceC` embedding in the combined source. -/
noncomputable def toReferenceCInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  R.projectionToReferenceInSemanticSourceRingHom L hind D.c L.sA_c_c
    L.cProjectionRelation L.cNormalField_le_normalizedField

/-- The ambient description of a promoted projection on the entire
selected normalized `B/T` field: first use the based selected-to-projection
normal-cover equivalence and then the two literal cover inclusions. -/
noncomputable def selectedBNormalProjectionInSemanticSourceRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    rankTwoScalarNormalField (k := k) w.bReps w.T.rep →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.referenceNormalCoverToReferenceSemanticSourceCover L hind).toRingHom.comp
    ((L.scalarNormalFieldToReferenceNormalCover p x hfield).toRingHom.comp
      (selectedBNormalEquivProjection
        (w := w) (hψ := hψ) hp).toRingEquiv.toRingHom)

/-- Pull the preceding ambient normal-field map back across the canonical
generic-point identification of the selected normalized chart. -/
noncomputable def projectionViaSelectedBNormalInSemanticSourceRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.selectedBNormalProjectionInSemanticSourceRingHom
      L hind p x hp hfield).comp
    (selectedBFunctionFieldAlgEquiv
      (w := w) (hψ := hψ)).toRingHom

/-- A promoted projection agrees on the whole selected normalized function
field with its based ambient normal-cover map. -/
theorem projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (hfield : (FiniteCover.normalClosureOver
      (rankTwoParameterField_le_rankTwoScalarField
        (k := k) p x)).restrictScalars k ≤ L.normalizedField) :
    R.projectionToReferenceInSemanticSourceRingHom L hind p x hp hfield =
      R.projectionViaSelectedBNormalInSemanticSourceRingHom
        L hind p x hp hfield := by
  apply RingHom.ext
  intro z
  have hnormal :=
    R.projectionToReferenceInSemanticSourceRingHom_apply_selectedNormal
      L hind p x hp hfield
        (selectedBFunctionFieldAlgEquiv (w := w) (hψ := hψ) z)
  simpa [projectionViaSelectedBNormalInSemanticSourceRingHom,
    selectedBNormalProjectionInSemanticSourceRingHom] using hnormal

/-- Simultaneously, the four named `toReference` embeddings are exactly
their based ambient normal-cover descriptions on the full selected
normalized function field. -/
theorem fourToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEInSemanticSourceRingHom L hind =
        R.projectionViaSelectedBNormalInSemanticSourceRingHom
          L hind e L.se_e L.eProjectionRelation
            L.eNormalField_le_normalizedField ∧
      R.toReferenceAInSemanticSourceRingHom L hind =
        R.projectionViaSelectedBNormalInSemanticSourceRingHom
          L hind a L.sA_a_a L.aProjectionRelation
            L.aNormalField_le_normalizedField ∧
      R.toReferenceBInSemanticSourceRingHom L hind =
        R.projectionViaSelectedBNormalInSemanticSourceRingHom
          L hind b L.s_b_b L.bProjectionRelation
            L.bNormalField_le_normalizedField ∧
      R.toReferenceCInSemanticSourceRingHom L hind =
        R.projectionViaSelectedBNormalInSemanticSourceRingHom
          L hind D.c L.sA_c_c L.cProjectionRelation
            L.cNormalField_le_normalizedField := by
  exact
    ⟨R.projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
        L hind e L.se_e L.eProjectionRelation
          L.eNormalField_le_normalizedField,
      R.projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
        L hind a L.sA_a_a L.aProjectionRelation
          L.aNormalField_le_normalizedField,
      R.projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
        L hind b L.s_b_b L.bProjectionRelation
          L.bNormalField_le_normalizedField,
      R.projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal
        L hind D.c L.sA_c_c L.cProjectionRelation
          L.cNormalField_le_normalizedField⟩

/-- The complete selected right `e` curve branch, acted on by the semantic
right arrow and included in the combined semantic/reference source. -/
noncomputable def seSemanticRightCurveBranchToReferenceSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchOverSource →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToReferenceSemanticSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightE.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).seY.toRingHom.comp
        (R.seSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- Pointwise, the preceding complete-branch map is the charted semantic
right arrow followed by the literal final-cover inclusion. -/
theorem seSemanticRightCurveBranchToReferenceSourceRingHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).branchOverSource) :
    R.seSemanticRightCurveBranchToReferenceSourceRingHom L hind z =
      R.branchComparisonSourceCoverToReferenceSemanticSourceCover L hind
        ((R.coefficientFourArrowDiagram hind).rightE
          ((R.coefficientFourTriangleReference hind).seY
            ((R.seSelectedRightBranchInComparisonMiddleCover
              hind).toAlgHom z))) :=
  rfl

/-- The complete selected right `a` curve branch after its semantic right
arrow, in the same combined source. -/
noncomputable def sAaSemanticRightCurveBranchToReferenceSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToReferenceSemanticSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightA.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sAaY.toRingHom.comp
        (R.sAaSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- Pointwise description of the charted semantic `a` arrow on its complete
curve branch field. -/
theorem sAaSemanticRightCurveBranchToReferenceSourceRingHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource) :
    R.sAaSemanticRightCurveBranchToReferenceSourceRingHom L hind z =
      R.branchComparisonSourceCoverToReferenceSemanticSourceCover L hind
        ((R.coefficientFourArrowDiagram hind).rightA
          ((R.coefficientFourTriangleReference hind).sAaY
            ((R.sAaSelectedRightBranchInComparisonMiddleCover
              hind).toAlgHom z))) :=
  rfl

/-- The complete selected right `b` curve branch after its semantic right
arrow, in the combined source. -/
noncomputable def sbSemanticRightCurveBranchToReferenceSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchOverSource →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToReferenceSemanticSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightB.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sbY.toRingHom.comp
        (R.sbSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- Pointwise description of the charted semantic `b` arrow on its complete
curve branch field. -/
theorem sbSemanticRightCurveBranchToReferenceSourceRingHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sb) R.sbCommonBaseData hψ).branchOverSource) :
    R.sbSemanticRightCurveBranchToReferenceSourceRingHom L hind z =
      R.branchComparisonSourceCoverToReferenceSemanticSourceCover L hind
        ((R.coefficientFourArrowDiagram hind).rightB
          ((R.coefficientFourTriangleReference hind).sbY
            ((R.sbSelectedRightBranchInComparisonMiddleCover
              hind).toAlgHom z))) :=
  rfl

/-- The complete selected right `c` curve branch after its semantic right
arrow, in the combined source. -/
noncomputable def sAcSemanticRightCurveBranchToReferenceSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToReferenceSemanticSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightC.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sAcY.toRingHom.comp
        (R.sAcSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- Pointwise description of the charted semantic `c` arrow on its complete
curve branch field. -/
theorem sAcSemanticRightCurveBranchToReferenceSourceRingHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z :
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource) :
    R.sAcSemanticRightCurveBranchToReferenceSourceRingHom L hind z =
      R.branchComparisonSourceCoverToReferenceSemanticSourceCover L hind
        ((R.coefficientFourArrowDiagram hind).rightC
          ((R.coefficientFourTriangleReference hind).sAcY
            ((R.sAcSelectedRightBranchInComparisonMiddleCover
              hind).toAlgHom z))) :=
  rfl

/-- The charted semantic `e` branch in the selected graph source.  Its
codomain now also contains the once-canonicalized relocated branch and its
intrinsic coefficient embedding. -/
noncomputable def seChartedSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.se) R.seCommonBaseData hψ).branchOverSource →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightE.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).seY.toRingHom.comp
        (R.seSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- The charted semantic `a` branch in the same selected graph source. -/
noncomputable def sAaChartedSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ).branchOverSource →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightA.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sAaY.toRingHom.comp
        (R.sAaSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- The charted semantic `b` branch in the same selected graph source. -/
noncomputable def sbChartedSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sb) R.sbCommonBaseData hψ).branchOverSource →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightB.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sbY.toRingHom.comp
        (R.sbSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- The charted semantic `c` branch in the same selected graph source. -/
noncomputable def sAcChartedSemanticRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAc) R.sAcCommonBaseData hψ).branchOverSource →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.branchComparisonSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    ((R.coefficientFourArrowDiagram hind).rightC.toRingHom.comp
      ((R.coefficientFourTriangleReference hind).sAcY.toRingHom.comp
        (R.sAcSelectedRightBranchInComparisonMiddleCover
          hind).toAlgHom.toRingHom))

/-- Transport the selected nonnormal `B/T` branch to the first complete
edge and include it in that scalar-extended edge. -/
noncomputable def selectedBScalarExtensionToSeEdgeRingHom :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      L.seTotalBaseChangedEdge.field :=
  L.seRightScalarExtensionToField.toRingHom.comp
    (rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.eProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom

/-- Restriction of the promoted first-input reference embedding to the
whole selected nonnormal `B/T` branch. -/
noncomputable def toReferenceEOnSelectedBScalarExtensionRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.toReferenceEInSemanticSourceRingHom L hind).comp
    (selectedBScalarExtensionToFunctionFieldRingHom
      (w := w) (hψ := hψ))

/-- The same branch map obtained by canonical total-field transport to the
first complete edge followed by its literal inclusion. -/
noncomputable def seEdgeOnSelectedBScalarExtensionRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
      L.seTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSeEdgeRingHom (w := w) L)

/-- On the entire selected nonnormal `B/T` branch, the first-input
reference embedding is the literal scalar-extended complete-edge map. -/
theorem toReferenceEOnSelectedBScalarExtensionRingHom_apply
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    R.toReferenceEOnSelectedBScalarExtensionRingHom L hind z =
      R.seEdgeOnSelectedBScalarExtensionRingHom L hind z := by
  unfold toReferenceEOnSelectedBScalarExtensionRingHom
    seEdgeOnSelectedBScalarExtensionRingHom
  simp only [RingHom.comp_apply]
  unfold toReferenceEInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension
    L hind e L.se_e L.eProjectionRelation
      L.eNormalField_le_normalizedField z]
  unfold selectedBScalarExtensionToSeEdgeRingHom
    totalBaseChangedEdgeToReferenceSemanticSourceCover
  simp only [RingHom.comp_apply]
  apply congrArg
  exact L.seRightScalarExtensionToReferenceNormalCover_eq
    ((rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.eProjectionRelation.symm).totalEquiv z)

/-- Transport the selected nonnormal `B/T` branch to the inverse-input
complete edge and include it in that scalar-extended edge. -/
noncomputable def selectedBScalarExtensionToSAaEdgeRingHom :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      L.sA_aTotalBaseChangedEdge.field :=
  L.sA_aRightScalarExtensionToField.toRingHom.comp
    (rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.aProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom

/-- Restriction of the promoted inverse-input reference embedding to the
whole selected nonnormal `B/T` branch. -/
noncomputable def toReferenceAOnSelectedBScalarExtensionRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.toReferenceAInSemanticSourceRingHom L hind).comp
    (selectedBScalarExtensionToFunctionFieldRingHom
      (w := w) (hψ := hψ))

/-- The same branch map obtained through the inverse-input complete edge. -/
noncomputable def sAaEdgeOnSelectedBScalarExtensionRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
      L.sA_aTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSAaEdgeRingHom (w := w) L)

/-- On the entire selected nonnormal `B/T` branch, the inverse-input
reference embedding is the literal scalar-extended complete-edge map. -/
theorem toReferenceAOnSelectedBScalarExtensionRingHom_apply
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    R.toReferenceAOnSelectedBScalarExtensionRingHom L hind z =
      R.sAaEdgeOnSelectedBScalarExtensionRingHom L hind z := by
  unfold toReferenceAOnSelectedBScalarExtensionRingHom
    sAaEdgeOnSelectedBScalarExtensionRingHom
  simp only [RingHom.comp_apply]
  unfold toReferenceAInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension
    L hind a L.sA_a_a L.aProjectionRelation
      L.aNormalField_le_normalizedField z]
  unfold selectedBScalarExtensionToSAaEdgeRingHom
    totalBaseChangedEdgeToReferenceSemanticSourceCover
  simp only [RingHom.comp_apply]
  apply congrArg
  exact L.sA_aRightScalarExtensionToReferenceNormalCover_eq
    ((rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.aProjectionRelation.symm).totalEquiv z)

/-- Transport the selected nonnormal `B/T` branch to the second-input
complete edge and include it in that scalar-extended edge. -/
noncomputable def selectedBScalarExtensionToSbEdgeRingHom :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      L.s_bTotalBaseChangedEdge.field :=
  L.s_bRightScalarExtensionToField.toRingHom.comp
    (rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.bProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom

/-- Restriction of the promoted second-input reference embedding to the
whole selected nonnormal `B/T` branch. -/
noncomputable def toReferenceBOnSelectedBScalarExtensionRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.toReferenceBInSemanticSourceRingHom L hind).comp
    (selectedBScalarExtensionToFunctionFieldRingHom
      (w := w) (hψ := hψ))

/-- The same branch map obtained through the second-input complete edge. -/
noncomputable def sbEdgeOnSelectedBScalarExtensionRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
      L.s_bTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSbEdgeRingHom (w := w) L)

/-- On the entire selected nonnormal `B/T` branch, the second-input
reference embedding is the literal scalar-extended complete-edge map. -/
theorem toReferenceBOnSelectedBScalarExtensionRingHom_apply
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    R.toReferenceBOnSelectedBScalarExtensionRingHom L hind z =
      R.sbEdgeOnSelectedBScalarExtensionRingHom L hind z := by
  unfold toReferenceBOnSelectedBScalarExtensionRingHom
    sbEdgeOnSelectedBScalarExtensionRingHom
  simp only [RingHom.comp_apply]
  unfold toReferenceBInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension
    L hind b L.s_b_b L.bProjectionRelation
      L.bNormalField_le_normalizedField z]
  unfold selectedBScalarExtensionToSbEdgeRingHom
    totalBaseChangedEdgeToReferenceSemanticSourceCover
  simp only [RingHom.comp_apply]
  apply congrArg
  exact L.s_bRightScalarExtensionToReferenceNormalCover_eq
    ((rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.bProjectionRelation.symm).totalEquiv z)

/-- Transport the selected nonnormal `B/T` branch to the output complete
edge and include it in that scalar-extended edge. -/
noncomputable def selectedBScalarExtensionToSAcEdgeRingHom :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      L.sA_cTotalBaseChangedEdge.field :=
  L.sA_cRightScalarExtensionToField.toRingHom.comp
    (rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.cProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom

/-- Restriction of the promoted output reference embedding to the whole
selected nonnormal `B/T` branch. -/
noncomputable def toReferenceCOnSelectedBScalarExtensionRingHom
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.toReferenceCInSemanticSourceRingHom L hind).comp
    (selectedBScalarExtensionToFunctionFieldRingHom
      (w := w) (hψ := hψ))

/-- The same branch map obtained through the output complete edge. -/
noncomputable def sAcEdgeOnSelectedBScalarExtensionRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.referenceSemanticSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
      L.sA_cTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSAcEdgeRingHom (w := w) L)

/-- On the entire selected nonnormal `B/T` branch, the output reference
embedding is the literal scalar-extended complete-edge map. -/
theorem toReferenceCOnSelectedBScalarExtensionRingHom_apply
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : rankTwoScalarExtension (k := k) w.bReps w.T.rep) :
    R.toReferenceCOnSelectedBScalarExtensionRingHom L hind z =
      R.sAcEdgeOnSelectedBScalarExtensionRingHom L hind z := by
  unfold toReferenceCOnSelectedBScalarExtensionRingHom
    sAcEdgeOnSelectedBScalarExtensionRingHom
  simp only [RingHom.comp_apply]
  unfold toReferenceCInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension
    L hind D.c L.sA_c_c L.cProjectionRelation
      L.cNormalField_le_normalizedField z]
  unfold selectedBScalarExtensionToSAcEdgeRingHom
    totalBaseChangedEdgeToReferenceSemanticSourceCover
  simp only [RingHom.comp_apply]
  apply congrArg
  exact L.sA_cRightScalarExtensionToReferenceNormalCover_eq
    ((rankTwoScalarExtensionEquivOfIdealEq
      (k := k) L.cProjectionRelation.symm).totalEquiv z)

/-- Simultaneously, all four promoted reference embeddings restrict on the
selected nonnormal `B/T` branch to the corresponding complete-edge maps. -/
theorem fourReferenceEmbeddingsOnSelectedBScalarExtension
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEOnSelectedBScalarExtensionRingHom L hind =
        R.seEdgeOnSelectedBScalarExtensionRingHom L hind ∧
      R.toReferenceAOnSelectedBScalarExtensionRingHom L hind =
        R.sAaEdgeOnSelectedBScalarExtensionRingHom L hind ∧
      R.toReferenceBOnSelectedBScalarExtensionRingHom L hind =
        R.sbEdgeOnSelectedBScalarExtensionRingHom L hind ∧
      R.toReferenceCOnSelectedBScalarExtensionRingHom L hind =
        R.sAcEdgeOnSelectedBScalarExtensionRingHom L hind := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro z
    exact R.toReferenceEOnSelectedBScalarExtensionRingHom_apply L hind z
  · apply RingHom.ext
    intro z
    exact R.toReferenceAOnSelectedBScalarExtensionRingHom_apply L hind z
  · apply RingHom.ext
    intro z
    exact R.toReferenceBOnSelectedBScalarExtensionRingHom_apply L hind z
  · apply RingHom.ext
    intro z
    exact R.toReferenceCOnSelectedBScalarExtensionRingHom_apply L hind z

/-- Transport the whole selected nonnormal `B/T` branch to the first
reference edge and then into the selected graph source. -/
noncomputable def selectedBScalarExtensionToReferenceEInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.referenceNormalCoverToSelectedGraphSource L hind).toRingHom.comp
    (L.seRightScalarExtensionToReferenceNormalCover.toRingHom.comp
      (rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.eProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom)

/-- The same whole branch carried through the literal first complete edge. -/
noncomputable def selectedBScalarExtensionToSeEdgeInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToSelectedGraphSource L
      L.seTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSeEdgeRingHom (w := w) L)

/-- Transport the whole selected `B/T` branch to the inverse-input
reference edge in the selected graph source. -/
noncomputable def selectedBScalarExtensionToReferenceAInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.referenceNormalCoverToSelectedGraphSource L hind).toRingHom.comp
    (L.sA_aRightScalarExtensionToReferenceNormalCover.toRingHom.comp
      (rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.aProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom)

/-- The same whole branch carried through the literal inverse-input edge. -/
noncomputable def selectedBScalarExtensionToSAaEdgeInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToSelectedGraphSource L
      L.sA_aTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSAaEdgeRingHom (w := w) L)

/-- Transport the whole selected `B/T` branch to the second-input
reference edge in the selected graph source. -/
noncomputable def selectedBScalarExtensionToReferenceBInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.referenceNormalCoverToSelectedGraphSource L hind).toRingHom.comp
    (L.s_bRightScalarExtensionToReferenceNormalCover.toRingHom.comp
      (rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.bProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom)

/-- The same whole branch carried through the literal second-input edge. -/
noncomputable def selectedBScalarExtensionToSbEdgeInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToSelectedGraphSource L
      L.s_bTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSbEdgeRingHom (w := w) L)

/-- Transport the whole selected `B/T` branch to the algebraic output
reference edge in the selected graph source. -/
noncomputable def selectedBScalarExtensionToReferenceCInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.referenceNormalCoverToSelectedGraphSource L hind).toRingHom.comp
    (L.sA_cRightScalarExtensionToReferenceNormalCover.toRingHom.comp
      (rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.cProjectionRelation.symm).totalEquiv.toRingEquiv.toRingHom)

/-- The same whole branch carried through the literal output edge. -/
noncomputable def selectedBScalarExtensionToSAcEdgeInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (rankTwoScalarExtension (k := k) w.bReps w.T.rep) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.totalBaseChangedEdgeToSelectedGraphSource L
      L.sA_cTotalBaseChangedEdge hind).toRingHom.comp
    (selectedBScalarExtensionToSAcEdgeRingHom (w := w) L)

/-- In the selected graph source, each promoted normalized reference map
agrees on the entire selected nonnormal branch with transport through its
literal complete edge.  In particular this comparison includes the
algebraic output edge, not only its selected scalar generator. -/
theorem fourReferenceEdgesOnSelectedBScalarExtensionInSelectedGraph
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.selectedBScalarExtensionToReferenceEInSelectedGraphRingHom L hind =
        R.selectedBScalarExtensionToSeEdgeInSelectedGraphRingHom L hind ∧
      R.selectedBScalarExtensionToReferenceAInSelectedGraphRingHom L hind =
        R.selectedBScalarExtensionToSAaEdgeInSelectedGraphRingHom L hind ∧
      R.selectedBScalarExtensionToReferenceBInSelectedGraphRingHom L hind =
        R.selectedBScalarExtensionToSbEdgeInSelectedGraphRingHom L hind ∧
      R.selectedBScalarExtensionToReferenceCInSelectedGraphRingHom L hind =
        R.selectedBScalarExtensionToSAcEdgeInSelectedGraphRingHom L hind := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro z
    unfold selectedBScalarExtensionToReferenceEInSelectedGraphRingHom
      selectedBScalarExtensionToSeEdgeInSelectedGraphRingHom
      selectedBScalarExtensionToSeEdgeRingHom
      totalBaseChangedEdgeToSelectedGraphSource
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    apply congrArg
    exact L.seRightScalarExtensionToReferenceNormalCover_eq
      ((rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.eProjectionRelation.symm).totalEquiv z)
  · apply RingHom.ext
    intro z
    unfold selectedBScalarExtensionToReferenceAInSelectedGraphRingHom
      selectedBScalarExtensionToSAaEdgeInSelectedGraphRingHom
      selectedBScalarExtensionToSAaEdgeRingHom
      totalBaseChangedEdgeToSelectedGraphSource
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    apply congrArg
    exact L.sA_aRightScalarExtensionToReferenceNormalCover_eq
      ((rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.aProjectionRelation.symm).totalEquiv z)
  · apply RingHom.ext
    intro z
    unfold selectedBScalarExtensionToReferenceBInSelectedGraphRingHom
      selectedBScalarExtensionToSbEdgeInSelectedGraphRingHom
      selectedBScalarExtensionToSbEdgeRingHom
      totalBaseChangedEdgeToSelectedGraphSource
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    apply congrArg
    exact L.s_bRightScalarExtensionToReferenceNormalCover_eq
      ((rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.bProjectionRelation.symm).totalEquiv z)
  · apply RingHom.ext
    intro z
    unfold selectedBScalarExtensionToReferenceCInSelectedGraphRingHom
      selectedBScalarExtensionToSAcEdgeInSelectedGraphRingHom
      selectedBScalarExtensionToSAcEdgeRingHom
      totalBaseChangedEdgeToSelectedGraphSource
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    apply congrArg
    exact L.sA_cRightScalarExtensionToReferenceNormalCover_eq
      ((rankTwoScalarExtensionEquivOfIdealEq
        (k := k) L.cProjectionRelation.symm).totalEquiv z)

/-- Restrict the first selected-graph reference edge map to the whole
intrinsic selected-`B` germ coefficient field. -/
noncomputable def seBGermCoefficientToReferenceInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedBScalarExtensionToReferenceEInSelectedGraphRingHom L hind).comp
    (bGermCoefficientToSelectedBScalarExtensionAlgHom
      (w := w) (hψ := hψ)).toRingHom

/-- The analogous whole intrinsic-field restriction for the inverse-input
reference edge. -/
noncomputable def sAaBGermCoefficientToReferenceInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedBScalarExtensionToReferenceAInSelectedGraphRingHom L hind).comp
    (bGermCoefficientToSelectedBScalarExtensionAlgHom
      (w := w) (hψ := hψ)).toRingHom

/-- The analogous whole intrinsic-field restriction for the second-input
reference edge. -/
noncomputable def sbBGermCoefficientToReferenceInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedBScalarExtensionToReferenceBInSelectedGraphRingHom L hind).comp
    (bGermCoefficientToSelectedBScalarExtensionAlgHom
      (w := w) (hψ := hψ)).toRingHom

/-- The analogous whole intrinsic-field restriction for the algebraic
output reference edge. -/
noncomputable def sAcBGermCoefficientToReferenceInSelectedGraphRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedBScalarExtensionToReferenceCInSelectedGraphRingHom L hind).comp
    (bGermCoefficientToSelectedBScalarExtensionAlgHom
      (w := w) (hψ := hψ)).toRingHom

/-- All four selected-graph reference maps restrict on the whole intrinsic
coefficient field through their literal complete edges.  These are the
non-coordinatewise edge restrictions needed before identifying the
semantic right-arrow charts. -/
theorem fourReferenceEdgesOnBGermCoefficientInSelectedGraph
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.seBGermCoefficientToReferenceInSelectedGraphRingHom L hind =
        (R.selectedBScalarExtensionToSeEdgeInSelectedGraphRingHom L hind).comp
          (bGermCoefficientToSelectedBScalarExtensionAlgHom
            (w := w) (hψ := hψ)).toRingHom ∧
      R.sAaBGermCoefficientToReferenceInSelectedGraphRingHom L hind =
        (R.selectedBScalarExtensionToSAaEdgeInSelectedGraphRingHom L hind).comp
          (bGermCoefficientToSelectedBScalarExtensionAlgHom
            (w := w) (hψ := hψ)).toRingHom ∧
      R.sbBGermCoefficientToReferenceInSelectedGraphRingHom L hind =
        (R.selectedBScalarExtensionToSbEdgeInSelectedGraphRingHom L hind).comp
          (bGermCoefficientToSelectedBScalarExtensionAlgHom
            (w := w) (hψ := hψ)).toRingHom ∧
      R.sAcBGermCoefficientToReferenceInSelectedGraphRingHom L hind =
        (R.selectedBScalarExtensionToSAcEdgeInSelectedGraphRingHom L hind).comp
          (bGermCoefficientToSelectedBScalarExtensionAlgHom
            (w := w) (hψ := hψ)).toRingHom := by
  obtain ⟨he, ha, hb, hc⟩ :=
    R.fourReferenceEdgesOnSelectedBScalarExtensionInSelectedGraph L hind
  exact ⟨congrArg (fun f ↦ f.comp
      (bGermCoefficientToSelectedBScalarExtensionAlgHom
        (w := w) (hψ := hψ)).toRingHom) he,
    congrArg (fun f ↦ f.comp
      (bGermCoefficientToSelectedBScalarExtensionAlgHom
        (w := w) (hψ := hψ)).toRingHom) ha,
    congrArg (fun f ↦ f.comp
      (bGermCoefficientToSelectedBScalarExtensionAlgHom
        (w := w) (hψ := hψ)).toRingHom) hb,
    congrArg (fun f ↦ f.comp
      (bGermCoefficientToSelectedBScalarExtensionAlgHom
        (w := w) (hψ := hψ)).toRingHom) hc⟩

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

/-- The first-input reference embedding and the literal base-changed
complete edge agree on the selected scalar generator. -/
theorem toReferenceEInSemanticSourceRingHom_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEInSemanticSourceRingHom L hind
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.seTotalBaseChangedEdge hind
        (L.seTotalBaseChangedEdge.selectedCoordinate 7) := by
  unfold toReferenceEInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar
    L hind e L.se_e L.eProjectionRelation
      L.eNormalField_le_normalizedField]
  rw [R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
    L L.seTotalBaseChangedEdge hind 7]
  apply congrArg
  apply Subtype.ext
  rfl

/-- The inverse-input reference embedding and the literal base-changed
complete edge agree on the selected scalar generator. -/
theorem toReferenceAInSemanticSourceRingHom_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceAInSemanticSourceRingHom L hind
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.sA_aTotalBaseChangedEdge hind
        (L.sA_aTotalBaseChangedEdge.selectedCoordinate 7) := by
  unfold toReferenceAInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar
    L hind a L.sA_a_a L.aProjectionRelation
      L.aNormalField_le_normalizedField]
  rw [R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
    L L.sA_aTotalBaseChangedEdge hind 7]
  apply congrArg
  apply Subtype.ext
  rfl

/-- The second-input reference embedding and the literal base-changed
complete edge agree on the selected scalar generator. -/
theorem toReferenceBInSemanticSourceRingHom_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceBInSemanticSourceRingHom L hind
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.s_bTotalBaseChangedEdge hind
        (L.s_bTotalBaseChangedEdge.selectedCoordinate 7) := by
  unfold toReferenceBInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar
    L hind b L.s_b_b L.bProjectionRelation
      L.bNormalField_le_normalizedField]
  rw [R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
    L L.s_bTotalBaseChangedEdge hind 7]
  apply congrArg
  apply Subtype.ext
  rfl

/-- The output reference embedding and the literal base-changed complete
edge agree on the selected scalar generator. -/
theorem toReferenceCInSemanticSourceRingHom_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceCInSemanticSourceRingHom L hind
        (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
      R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
        L.sA_cTotalBaseChangedEdge hind
        (L.sA_cTotalBaseChangedEdge.selectedCoordinate 7) := by
  unfold toReferenceCInSemanticSourceRingHom
  rw [R.projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar
    L hind D.c L.sA_c_c L.cProjectionRelation
      L.cNormalField_le_normalizedField]
  rw [R.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate
    L L.sA_cTotalBaseChangedEdge hind 7]
  apply congrArg
  apply Subtype.ext
  rfl

/-- All four promoted reference embeddings meet the literal selected
complete edges at coordinate `7` inside the one common semantic source. -/
theorem fourToReferenceInSemanticSourceRingHom_selectedBScalar
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEInSemanticSourceRingHom L hind
          (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
        R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
          L.seTotalBaseChangedEdge hind
          (L.seTotalBaseChangedEdge.selectedCoordinate 7) ∧
      R.toReferenceAInSemanticSourceRingHom L hind
          (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
        R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
          L.sA_aTotalBaseChangedEdge hind
          (L.sA_aTotalBaseChangedEdge.selectedCoordinate 7) ∧
      R.toReferenceBInSemanticSourceRingHom L hind
          (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
        R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
          L.s_bTotalBaseChangedEdge hind
          (L.s_bTotalBaseChangedEdge.selectedCoordinate 7) ∧
      R.toReferenceCInSemanticSourceRingHom L hind
          (selectedBScalarFunctionFieldElement (w := w) (hψ := hψ)) =
        R.totalBaseChangedEdgeToReferenceSemanticSourceCover L
          L.sA_cTotalBaseChangedEdge hind
          (L.sA_cTotalBaseChangedEdge.selectedCoordinate 7) := by
  exact ⟨R.toReferenceEInSemanticSourceRingHom_selectedBScalar L hind,
    R.toReferenceAInSemanticSourceRingHom_selectedBScalar L hind,
    R.toReferenceBInSemanticSourceRingHom_selectedBScalar L hind,
    R.toReferenceCInSemanticSourceRingHom_selectedBScalar L hind⟩

/-- The four named intrinsic-germ maps are literally the restrictions of
the four promoted reference embeddings to the selected `B` germ chart. -/
theorem fourToReferenceInSemanticSourceRingHom_restrict_bGerm
    [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.toReferenceEOnBGermCoefficientRingHom L hind =
        (R.toReferenceEInSemanticSourceRingHom L hind).comp
          (bGermCoefficientToSelectedBFunctionFieldRingHom
            (w := w) (hψ := hψ)) ∧
      R.toReferenceAOnBGermCoefficientRingHom L hind =
        (R.toReferenceAInSemanticSourceRingHom L hind).comp
          (bGermCoefficientToSelectedBFunctionFieldRingHom
            (w := w) (hψ := hψ)) ∧
      R.toReferenceBOnBGermCoefficientRingHom L hind =
        (R.toReferenceBInSemanticSourceRingHom L hind).comp
          (bGermCoefficientToSelectedBFunctionFieldRingHom
            (w := w) (hψ := hψ)) ∧
      R.toReferenceCOnBGermCoefficientRingHom L hind =
        (R.toReferenceCInSemanticSourceRingHom L hind).comp
          (bGermCoefficientToSelectedBFunctionFieldRingHom
            (w := w) (hψ := hψ)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
