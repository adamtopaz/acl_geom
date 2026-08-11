/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource
import AclGeom.Config.ChunkFourArrowReference

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

/-- The exact coefficient-linear embedding of the original normalized
reference cover into the combined semantic/reference source cover. -/
def referenceNormalCoverToReferenceSemanticSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥L.referenceNormalCover) →ₐ[k]
      (↥(R.referenceSemanticSourceCover L hind).field) := by
  let hSJ := R.semanticCommonSourceField_le_referenceSemanticJoin L hind
  letI : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars hSJ)) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.referenceSemanticJoinOverSource L hind))
    exact R.referenceSemanticJoinOverSource_finiteDimensional L hind
  let halg : Algebra.IsAlgebraic (↥R.semanticCommonSourceField)
      (↥(extendScalars hSJ)) := Algebra.IsAlgebraic.of_finite _ _
  let f₁ := R.referenceNormalCoverToMappedReference L
  let f₂ := IntermediateField.algHomIntoOfLeRestrictScalars
    (R.mappedReferenceNormalField L)
    (FiniteCover.normalClosureOver hSJ)
    (R.mappedReferenceNormalField_le_ambientReferenceNormalClosure L hind)
  let f₃ :=
    (FiniteCover.normalClosureOverEquivCanonical hSJ halg).toAlgHom.restrictScalars k
  let f₄ :=
    (IntermediateField.inclusion
      (R.transportedReferenceSourceCover_le_referenceSemanticSourceCover
        L hind)).restrictScalars k
  exact f₄.comp (f₃.comp (f₂.comp f₁))

/-- On every one of the eight free input coefficients, the transported
reference-cover embedding is exactly the semantic common-source algebra
map.  This is the coefficient square needed before comparing the four
explicit reference projections with the semantic four-arrow charts. -/
set_option maxHeartbeats 800000 in
theorem referenceNormalCoverToReferenceSemanticSourceCover_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (z : D.inputField) :
    R.referenceNormalCoverToReferenceSemanticSourceCover L hind
        (algebraMap (↥D.inputField) (↥L.referenceNormalCover) z) =
      algebraMap (↥R.semanticCommonSourceField)
        (↥(R.referenceSemanticSourceCover L hind).field)
        (R.referenceInputToSemanticSource L z) := by
  unfold referenceNormalCoverToReferenceSemanticSourceCover
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars']
  apply Subtype.ext
  dsimp only [IntermediateField.inclusion, Subalgebra.inclusion,
    IntermediateField.algHomIntoOfLeRestrictScalars,
    referenceNormalCoverToMappedReference]
  change
    (FiniteCover.normalClosureOverEquivCanonical
      (R.semanticCommonSourceField_le_referenceSemanticJoin L hind)
      _)
        ⟨curveEmbedding (k := k) (K := K) z,
          R.mappedReferenceNormalField_le_ambientReferenceNormalClosure L hind
            ⟨z, L.referenceNormalCover.algebraMap_mem z, rfl⟩⟩ =
      algebraMap (↥R.semanticCommonSourceField)
        (↥(R.transportedReferenceSourceCover L hind).field)
        (R.referenceInputToSemanticSource L z)
  exact (FiniteCover.normalClosureOverEquivCanonical
    (R.semanticCommonSourceField_le_referenceSemanticJoin L hind) _).commutes _

/-- Conjugate the function field of the explicit normalized source chart
back to its selected ambient cover and then embed it in the common
semantic/reference source cover. -/
noncomputable def referenceChartFunctionFieldToSemanticSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    L.referenceAlgebraicChart.functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) := by
  letI := L.referenceNormalCover_finiteDimensional
  exact (R.referenceNormalCoverToReferenceSemanticSourceCover L hind).toRingHom.comp
    (FiniteExtensionChart.functionFieldAlgEquiv
      (k := k) (K := ↥D.inputField) (L := ↥L.referenceNormalCover)
      D.inputCoordinates D.adjoin_inputCoordinates_eq_top).toRingHom

/-- The first-input `toReferenceE` embedding, now with the same literal
codomain as the semantic four-arrow action. -/
noncomputable def toReferenceEInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceChartFunctionFieldToSemanticSourceRingHom L hind).comp
    ((L.projectionFunctionFieldRingHom e L.se_e L.eScalar_mem_racl
      L.eNormalField_le_normalizedField).comp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) L.eProjectionRelation))

/-- The inverse-input `toReferenceA` embedding in the combined source. -/
noncomputable def toReferenceAInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceChartFunctionFieldToSemanticSourceRingHom L hind).comp
    ((L.projectionFunctionFieldRingHom a L.sA_a_a L.aScalar_mem_racl
      L.aNormalField_le_normalizedField).comp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) L.aProjectionRelation))

/-- The second-input `toReferenceB` embedding in the combined source. -/
noncomputable def toReferenceBInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceChartFunctionFieldToSemanticSourceRingHom L hind).comp
    ((L.projectionFunctionFieldRingHom b L.s_b_b L.bScalar_mem_racl
      L.bNormalField_le_normalizedField).comp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) L.bProjectionRelation))

/-- The output `toReferenceC` embedding in the combined source. -/
noncomputable def toReferenceCInSemanticSourceRingHom [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (QWitness.PsiChunkFourArrowEdgeLifts.selectedBAlgebraicChart
      (k := k) (K := K) (w := w) (hψ := hψ)).functionField →+*
      (↥(R.referenceSemanticSourceCover L hind).field) :=
  (R.referenceChartFunctionFieldToSemanticSourceRingHom L hind).comp
    ((L.projectionFunctionFieldRingHom D.c L.sA_c_c L.cScalar_mem_racl
      L.cNormalField_le_normalizedField).comp
        (QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom
          (w := w) (hψ := hψ) L.cProjectionRelation))

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
