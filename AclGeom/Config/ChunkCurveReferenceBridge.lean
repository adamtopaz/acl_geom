/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource
import AclGeom.Config.ChunkFourArrowReference
import AclGeom.Config.ChunkGermCoordinates

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
  let es := rankTwoScalarLocusNormalCoverAlgEquiv
    hselected hselected hself
  let ep := rankTwoScalarLocusNormalCoverAlgEquiv
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm
  change ep (es.symm
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z)) = _
  have hes : es
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) =
      algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z := by
    have hz := rankTwoScalarNormalCoverEquivOfIdealEq_algebraMap
      hselected hselected hself z
    rw [locusFunctionFieldEquivOfIdealEq_refl] at hz
    exact hz
  have hes' : es.symm
      (algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z) =
      algebraMap (↥(rankTwoParameterField (k := k) w.bReps))
        (rankTwoScalarNormalField (k := k) w.bReps w.T.rep) z :=
    es.symm_apply_eq.mpr hes.symm
  rw [hes']
  exact rankTwoScalarNormalCoverEquivOfIdealEq_algebraMap
    hselected (PsiBProjectionRelation.scalar_mem_racl w hψ hp) hp.symm z

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

private abbrev mappedSelectedBFamily :
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

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
