/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge

/-!
# Selected-B scalar extension and reference embeddings

The selected-`B` scalar extension, the reference embeddings on it and on the
`B`-germ coefficient field. Split from `AclGeom.Config.ChunkCurveReferenceBridge` (#18).
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

/-- The transported normalized reference field lies in the same
reference/semantic compositum. -/
theorem mappedReferenceNormalField_le_referenceSemanticJoin
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.mappedReferenceNormalField L ≤ R.referenceSemanticJoin L hind := by
  let := R.mappedReferenceNormalOverInput_finiteDimensional L
  change (R.mappedReferenceNormalOverInput L).restrictScalars k ≤ _
  exact FiniteExtensionCompositum.normal_le_field
    (R.mappedReferenceInputField L) R.semanticCommonSourceField
    (R.mappedReferenceNormalOverInput L)
    (R.mappedReferenceInputField_le_semanticCommonSourceField L)

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
  let : FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(extendScalars
        (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin
          L hind))) := by
    change FiniteDimensional (↥R.semanticCommonSourceField)
      (↥(R.selectedSemanticReferenceJoinOverSource L hind))
    exact R.selectedSemanticReferenceJoinOverSource_finiteDimensional L hind
  exact FiniteCover.normalClosureOver_normal
    (R.semanticCommonSourceField_le_selectedSemanticReferenceJoin L hind)
    (Algebra.IsAlgebraic.of_finite _ _)

/-- The transported normalized reference field lies in the same concrete
normal closure as all selected semantic and relocated branches. -/
theorem mappedReferenceNormalField_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.mappedReferenceNormalField L ≤
      (R.selectedSemanticReferenceNormalField L hind).restrictScalars k :=
  (R.mappedReferenceNormalField_le_referenceSemanticJoin L hind).trans
    ((R.referenceSemanticJoin_le_selectedSemanticReferenceJoin L hind).trans
      (R.selectedSemanticReferenceJoin_le_normalField_restrictScalars L hind))

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
  let : Normal
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
  let : Normal
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
  let : Normal
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
  let : Normal
      (↥(PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.se) R.seCommonBaseData hψ).sourceField)
      (↥(R.selectedGraphSourceCover L hind).field) :=
    (R.selectedGraphSourceCover L hind).normal
  exact NormalBranchEmbedding.extendAlong_apply _ _ _

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
  let : FiniteDimensional (↥R.semanticCommonSourceField)
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
  let := rankTwoScalarNormalField_finiteDimensional
    (k := k) (w.T_rep_mem_racl_bReps hψ)
  let := rankTwoScalarNormalField_finiteDimensional
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
  let := L.referenceNormalCover_finiteDimensional
  let := rankTwoScalarNormalField_finiteDimensional
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
  let := L.referenceNormalCover_finiteDimensional
  let := rankTwoScalarNormalField_finiteDimensional
    (k := k) (w.T_rep_mem_racl_bReps hψ)
  let := rankTwoScalarNormalField_finiteDimensional
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

/-- The complete-branch inclusion does not change the ambient value of an
intrinsic relocated coefficient. -/
@[simp] theorem relocatedBCoefficientToCompleteRightBranchRingHom_val
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (z : G.toPair.curveCoefficientField k G.parameterField) :
    ((relocatedBCoefficientToCompleteRightBranchRingHom G z :
        G.toPair.branchOverSource) : CommonCurveAmbient K) = z :=
  rfl

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

/-- The lifted `a` transport still carries every displayed rational-source
coordinate to the same-position coordinate in the `a` presentation. -/
@[simp] theorem rightACommonSourceClosureTransport_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    (R.rightACommonSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField))
          (R.rightESemanticSourceCoordinate i)) =
      algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.rightASemanticSourceCoordinate i) := by
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)))
    (R.commonSourceRightAAut_apply hind i)

/-- Same-position coordinate formula for the lifted `b` transport. -/
@[simp] theorem rightBCommonSourceClosureTransport_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    (R.rightBCommonSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField))
          (R.rightESemanticSourceCoordinate i)) =
      algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.rightBSemanticSourceCoordinate i) := by
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.semanticCommonSourceField)
      (AlgebraicClosure (↥R.semanticCommonSourceField)))
    (R.commonSourceRightBAut_apply hind i)

/-- The lifted `c` transport retains the exact coordinatewise source
formula, including the distinguished block whose value is the selected
algebraic output `c`. -/
@[simp] theorem rightCSourceClosureTransport_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    (R.rightCSourceClosureTransport hind).closureEquiv
        (algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField))
          (R.rightESemanticSourceCoordinate i)) =
      algebraMap (↥R.rightCSourceField)
        (AlgebraicClosure (↥R.rightCSourceField))
        (R.rightCSourceCoordinate i) := by
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥R.rightCSourceField)
      (AlgebraicClosure (↥R.rightCSourceField)))
    (R.commonSourceToRightCSourceEquiv_apply hind i)

set_option synthInstance.maxHeartbeats 100000 in
-- The nested source-cover algebra tower is hidden behind named sup constructions.
/-- On the finite source cover, the `a` chart carries every displayed base
coordinate to its literal `a`-presentation counterpart. -/
@[simp] theorem selectedGraphRightSourceToRightARingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightARingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField))
          (R.rightASemanticSourceCoordinate i),
        (R.rightASelectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact R.rightACommonSourceClosureTransport_algebraMap hind i

set_option synthInstance.maxHeartbeats 100000 in
-- The nested source-cover algebra tower is hidden behind named sup constructions.
/-- Finite-cover coordinate formula for the `b` chart. -/
@[simp] theorem selectedGraphRightSourceToRightBRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightBRingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥R.semanticCommonSourceField)
          (AlgebraicClosure (↥R.semanticCommonSourceField))
          (R.rightBSemanticSourceCoordinate i),
        (R.rightBSelectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact R.rightBCommonSourceClosureTransport_algebraMap hind i

set_option synthInstance.maxHeartbeats 100000 in
-- The nested source-cover algebra tower is hidden behind named sup constructions.
/-- Finite-cover coordinate formula for the genuine `c` base change. -/
@[simp] theorem selectedGraphRightSourceToRightCRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightCRingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      ⟨algebraMap (↥R.rightCSourceField)
          (AlgebraicClosure (↥R.rightCSourceField))
          (R.rightCSourceCoordinate i),
        (R.rightCSelectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ := by
  apply Subtype.ext
  exact R.rightCSourceClosureTransport_algebraMap hind i

/-! ### One finite normal codomain for the four semilinear source charts -/

/-- The underlying common algebraic-closure chart for the `e` leg. -/
noncomputable def selectedGraphRightSourceToRightEJointClosureRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind).closureEquiv

/-- The underlying algebraic-closure chart for the selected `a` leg. -/
noncomputable def selectedGraphRightSourceToRightAJointClosureRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind).closureEquiv

/-- The underlying algebraic-closure chart for the selected `b` leg. -/
noncomputable def selectedGraphRightSourceToRightBJointClosureRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightBJointClosureExtension L hind).closureEquiv

/-- The underlying algebraic-closure chart for the selected `c` leg. -/
noncomputable def selectedGraphRightSourceToRightCJointClosureRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (↥(R.selectedGraphRightSourceCover L hind).field) ≃+*
      AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightCJointClosureExtension L hind).closureEquiv

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the selected algebraic-closure extension recreates its tower.
set_option maxHeartbeats 800000 in
-- This replays the same selected finite tower used in the definition above.
/-- The common algebraic-closure equivalence restricts on every element of
the old graph/right source to the originally selected `e` embedding. -/
@[simp] theorem selectedGraphRightSourceToRightEJointClosureRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.selectedGraphRightSourceToRightEJointClosureRingEquiv L hind
        (algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
          (AlgebraicClosure
            (↥(R.selectedGraphRightSourceCover L hind).field)) x) =
      algebraMap (↥(R.fourSelectedGraphJointCover L hind).field)
        (AlgebraicClosure
          (↥(R.fourSelectedGraphJointCover L hind).field))
        (R.selectedGraphRightSourceToRightEJointRingHom L hind x) := by
  exact (R.selectedGraphRightSourceToRightEJointClosureExtension L hind).commutes x

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the selected algebraic-closure extension recreates its tower.
set_option maxHeartbeats 800000 in
-- This replays the twisted finite tower used for the a chart.
/-- The `a` closure chart restricts exactly to the selected `a` embedding
on the whole old source-cover field. -/
@[simp] theorem selectedGraphRightSourceToRightAJointClosureRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.selectedGraphRightSourceToRightAJointClosureRingEquiv L hind
        (algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
          (AlgebraicClosure
            (↥(R.selectedGraphRightSourceCover L hind).field)) x) =
      algebraMap (↥(R.fourSelectedGraphJointCover L hind).field)
        (AlgebraicClosure
          (↥(R.fourSelectedGraphJointCover L hind).field))
        (R.selectedGraphRightSourceToRightAJointRingHom L hind x) := by
  exact (R.selectedGraphRightSourceToRightAJointClosureExtension L hind).commutes x

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the selected algebraic-closure extension recreates its tower.
set_option maxHeartbeats 800000 in
-- This replays the twisted finite tower used for the b chart.
/-- The `b` closure chart restricts exactly to the selected `b` embedding. -/
@[simp] theorem selectedGraphRightSourceToRightBJointClosureRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.selectedGraphRightSourceToRightBJointClosureRingEquiv L hind
        (algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
          (AlgebraicClosure
            (↥(R.selectedGraphRightSourceCover L hind).field)) x) =
      algebraMap (↥(R.fourSelectedGraphJointCover L hind).field)
        (AlgebraicClosure
          (↥(R.fourSelectedGraphJointCover L hind).field))
        (R.selectedGraphRightSourceToRightBJointRingHom L hind x) := by
  exact (R.selectedGraphRightSourceToRightBJointClosureExtension L hind).commutes x

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the selected algebraic-closure extension recreates its tower.
set_option maxHeartbeats 800000 in
-- This replays the finite tower through the independent c source chart.
/-- The `c` closure chart restricts exactly to the genuine selected `c`
embedding on the whole old source-cover field. -/
@[simp] theorem selectedGraphRightSourceToRightCJointClosureRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : (R.selectedGraphRightSourceCover L hind).field) :
    R.selectedGraphRightSourceToRightCJointClosureRingEquiv L hind
        (algebraMap (↥(R.selectedGraphRightSourceCover L hind).field)
          (AlgebraicClosure
            (↥(R.selectedGraphRightSourceCover L hind).field)) x) =
      algebraMap (↥(R.fourSelectedGraphJointCover L hind).field)
        (AlgebraicClosure
          (↥(R.fourSelectedGraphJointCover L hind).field))
        (R.selectedGraphRightSourceToRightCJointRingHom L hind x) := by
  exact (R.selectedGraphRightSourceToRightCJointClosureExtension L hind).commutes x

set_option maxHeartbeats 800000 in
-- The exact coordinate statement unfolds the nested common cover.
/-- The `e` leg lands on the literal `e` source coordinate in the joint
source base. -/
@[simp] theorem selectedGraphRightSourceToRightEJointRingHom_coordinate
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightEJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.rightESemanticSourceCoordinate i)) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.semanticSourceToRightSourceJointClosureRingEquiv
      (algebraMap (↥R.semanticCommonSourceField)
        (AlgebraicClosure (↥R.semanticCommonSourceField))
        (R.rightESemanticSourceCoordinate i)) =
    algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (R.semanticSourceToRightSourceJoint
        (R.rightESemanticSourceCoordinate i))
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap _

set_option maxHeartbeats 800000 in
-- The exact coordinate statement unfolds the nested common cover.
/-- The `a` leg lands on the literal same-position `a` source coordinate in
the joint source base. -/
@[simp] theorem selectedGraphRightSourceToRightAJointRingHom_coordinate
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightAJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.rightASemanticSourceCoordinate i)) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.semanticSourceToRightSourceJointClosureRingEquiv
      (((R.selectedGraphRightSourceToRightARingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ :
        (R.rightASelectedGraphRightSourceCover L hind).field) :
          AlgebraicClosure (↥R.semanticCommonSourceField))) =
    algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (R.semanticSourceToRightSourceJoint
        (R.rightASemanticSourceCoordinate i))
  rw [R.selectedGraphRightSourceToRightARingEquiv_algebraMap]
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap _

set_option maxHeartbeats 800000 in
-- The exact coordinate statement unfolds the nested common cover.
/-- The `b` leg lands on the literal same-position `b` source coordinate in
the joint source base. -/
@[simp] theorem selectedGraphRightSourceToRightBJointRingHom_coordinate
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightBJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.semanticSourceToRightSourceJoint
          (R.rightBSemanticSourceCoordinate i)) := by
  let : Algebra (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) :=
    R.semanticSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.semanticSourceToRightSourceJointClosureRingEquiv
      (((R.selectedGraphRightSourceToRightBRingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ :
        (R.rightBSelectedGraphRightSourceCover L hind).field) :
          AlgebraicClosure (↥R.semanticCommonSourceField))) =
    algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (R.semanticSourceToRightSourceJoint
        (R.rightBSemanticSourceCoordinate i))
  rw [R.selectedGraphRightSourceToRightBRingEquiv_algebraMap]
  exact R.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap _

set_option maxHeartbeats 800000 in
-- The exact coordinate statement unfolds the nested common cover.
/-- The genuine `c` leg lands on the literal same-position `c` source
coordinate through its distinct inclusion in the joint source. -/
@[simp] theorem selectedGraphRightSourceToRightCJointRingHom_coordinate
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) (i : Fin 9) :
    R.selectedGraphRightSourceToRightCJointRingHom L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ =
      algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)
        (R.rightCSourceToRightSourceJoint (R.rightCSourceCoordinate i)) := by
  let : Algebra (↥R.rightCSourceField) (↥R.rightSourceJointField) :=
    R.rightCSourceToRightSourceJoint.toAlgebra
  apply Subtype.ext
  change R.rightCSourceToRightSourceJointClosureRingEquiv
      (((R.selectedGraphRightSourceToRightCRingEquiv L hind
        ⟨algebraMap (↥R.semanticCommonSourceField)
            (AlgebraicClosure (↥R.semanticCommonSourceField))
            (R.rightESemanticSourceCoordinate i),
          (R.selectedGraphRightSourceCover L hind).field.algebraMap_mem _⟩ :
        (R.rightCSelectedGraphRightSourceCover L hind).field) :
          AlgebraicClosure (↥R.rightCSourceField))) =
    algebraMap (↥R.rightSourceJointField)
      (AlgebraicClosure (↥R.rightSourceJointField))
      (R.rightCSourceToRightSourceJoint (R.rightCSourceCoordinate i))
  rw [R.selectedGraphRightSourceToRightCRingEquiv_algebraMap]
  exact R.rightCSourceToRightSourceJointClosureRingEquiv_algebraMap _

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

end ReferenceFieldAliases

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
