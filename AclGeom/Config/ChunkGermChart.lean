/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkGermCoordinates
import AclGeom.Correspondence.FiniteExtensionProjection

/-!
# Affine normalization of the intrinsic Ψ multiplication germ

The canonical curve coefficients are finite coordinate families for the
intrinsic `A`, `B`, and `C` parameter fields.  Their independent `A/B`
compositum likewise has a finite coordinate family.  This file uses those
coordinates to turn the common normal multiplication field into an integral
affine chart and spreads its three field inclusions to dominant rational
projections to the selected input and output parameter charts.

The result is a normalized algebraic multiplication graph.  Identifying its
output projection with a single-valued product on one reference germ chart
is the next group-chunk step.
-/

namespace AclGeom

open IntermediateField
open AlgebraicGeometry

noncomputable section

universe u

namespace QWitness

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (w : QWitness k K)

/-- The finite coordinate index of the inverse-oriented intrinsic `A`
germ. -/
abbrev aInverseGermCoordinateIndex (hψ : w.Psi) :=
  ((w.xyCorrespondencePairOverA hψ).swap).curveCoefficientSet k w.aField

/-- The finite coordinate index of the intrinsic `B` germ. -/
abbrev bGermCoordinateIndex (hψ : w.Psi) :=
  (w.yzCorrespondencePairOverB hψ).curveCoefficientSet k w.bField

/-- The finite coordinate index of the intrinsic output `C` germ. -/
abbrev cGermCoordinateIndex (hψ : w.Psi) :=
  (w.xzCorrespondencePairOverC hψ).curveCoefficientSet k w.cField

/-- The lifted canonical coefficients of the inverse-oriented `A` germ. -/
abbrev aInverseGermCoordinates (hψ : w.Psi) :
    w.aInverseGermCoordinateIndex hψ → w.aInverseGermCoefficientField hψ :=
  ((w.xyCorrespondencePairOverA hψ).swap).curveCoefficientCoordinates
    k w.aField

/-- The lifted canonical coefficients of the `B` germ. -/
abbrev bGermCoordinates (hψ : w.Psi) :
    w.bGermCoordinateIndex hψ → w.bGermCoefficientField hψ :=
  (w.yzCorrespondencePairOverB hψ).curveCoefficientCoordinates k w.bField

/-- The lifted canonical coefficients of the output `C` germ. -/
abbrev cGermCoordinates (hψ : w.Psi) :
    w.cGermCoordinateIndex hψ → w.cGermCoefficientField hψ :=
  (w.xzCorrespondencePairOverC hψ).curveCoefficientCoordinates k w.cField

/-- The inverse-`A` germ coordinates generate their intrinsic field. -/
theorem adjoin_aInverseGermCoordinates_eq_top (hψ : w.Psi) :
    adjoin k (Set.range (w.aInverseGermCoordinates hψ)) = ⊤ :=
  ((w.xyCorrespondencePairOverA hψ).swap).adjoin_curveCoefficientCoordinates_eq_top
    k w.aField

/-- The `B` germ coordinates generate their intrinsic field. -/
theorem adjoin_bGermCoordinates_eq_top (hψ : w.Psi) :
    adjoin k (Set.range (w.bGermCoordinates hψ)) = ⊤ :=
  (w.yzCorrespondencePairOverB hψ).adjoin_curveCoefficientCoordinates_eq_top
    k w.bField

/-- The output `C` germ coordinates generate their intrinsic field. -/
theorem adjoin_cGermCoordinates_eq_top (hψ : w.Psi) :
    adjoin k (Set.range (w.cGermCoordinates hψ)) = ⊤ :=
  (w.xzCorrespondencePairOverC hψ).adjoin_curveCoefficientCoordinates_eq_top
    k w.cField

/-- A finite disjoint coordinate family for the intrinsic independent
`A/B` input field. -/
abbrev abGermCoordinateIndex (hψ : w.Psi) :=
  w.aInverseGermCoordinateIndex hψ ⊕ w.bGermCoordinateIndex hψ

/-- The two canonical coefficient families, lifted into their compositum. -/
def abGermCoordinates (hψ : w.Psi) :
    w.abGermCoordinateIndex hψ → w.abGermCoefficientField hψ
  | Sum.inl z => ⟨z.1, by
      rw [abGermCoefficientField]
      exact (le_sup_left : w.aInverseGermCoefficientField hψ ≤
        w.aInverseGermCoefficientField hψ ⊔ w.bGermCoefficientField hψ)
          (subset_adjoin k _ z.2)⟩
  | Sum.inr z => ⟨z.1, by
      rw [abGermCoefficientField]
      exact (le_sup_right : w.bGermCoefficientField hψ ≤
        w.aInverseGermCoefficientField hψ ⊔ w.bGermCoefficientField hψ)
          (subset_adjoin k _ z.2)⟩

/-- The combined canonical coefficient family generates the full intrinsic
independent-input field. -/
theorem adjoin_abGermCoordinates_eq_top (hψ : w.Psi) :
    adjoin k (Set.range (w.abGermCoordinates hψ)) = ⊤ := by
  let F := w.abGermCoefficientField hψ
  apply F.lift_injective
  rw [F.lift_adjoin, F.lift_top]
  change adjoin k (Subtype.val '' Set.range (w.abGermCoordinates hψ)) = F
  have hrange : Subtype.val '' Set.range (w.abGermCoordinates hψ) =
      ((w.xyCorrespondencePairOverA hψ).swap).curveCoefficientSet k w.aField ∪
        (w.yzCorrespondencePairOverB hψ).curveCoefficientSet k w.bField := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      rcases i with i | i
      · exact Set.mem_union_left _ i.2
      · exact Set.mem_union_right _ i.2
    · rintro (hz | hz)
      · let c : w.aInverseGermCoordinateIndex hψ := ⟨z, hz⟩
        exact ⟨w.abGermCoordinates hψ (Sum.inl c),
          ⟨Sum.inl c, rfl⟩, rfl⟩
      · let c : w.bGermCoordinateIndex hψ := ⟨z, hz⟩
        exact ⟨w.abGermCoordinates hψ (Sum.inr c),
          ⟨Sum.inr c, rfl⟩, rfl⟩
  rw [hrange, adjoin_union]
  rfl

/-- The finite-extension affine chart of the selected inverse-oriented `A`
parameter germ. -/
abbrev aInverseGermAlgebraicChart (hψ : w.Psi) : Scheme := by
  letI := w.aParameterOverInverseGerm_finiteDimensional hψ
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(w.aInverseGermCoefficientField hψ))
    (L := ↥(w.aParameterOverInverseGerm hψ))
    (w.aInverseGermCoordinates hψ)

/-- The finite-extension affine chart of the selected `B` parameter germ. -/
abbrev bGermAlgebraicChart (hψ : w.Psi) : Scheme := by
  letI := w.bParameterOverGerm_finiteDimensional hψ
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(w.bGermCoefficientField hψ))
    (L := ↥(w.bParameterOverGerm hψ))
    (w.bGermCoordinates hψ)

/-- The finite-extension affine chart of the selected output `C` parameter
germ. -/
abbrev cGermAlgebraicChart (hψ : w.Psi) : Scheme := by
  letI := w.cParameterOverGerm_finiteDimensional hψ
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(w.cGermCoefficientField hψ))
    (L := ↥(w.cParameterOverGerm hψ))
    (w.cGermCoordinates hψ)

/-- The integral affine chart of the common normal multiplication graph over
the intrinsic independent `A/B` input field. -/
abbrev germMultiplicationAlgebraicChart (hψ : w.Psi) : Scheme := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(w.abGermCoefficientField hψ))
    (L := ↥(w.germMultiplicationNormalCover hψ))
    (w.abGermCoordinates hψ)

/-- The selected displayed `A` parameter field embeds in the common normal
multiplication field. -/
def aParameterToGermMultiplicationNormal (hψ : w.Psi) :
    (↥(w.aParameterOverInverseGerm hψ)) →ₐ[k]
      (↥(w.germMultiplicationNormalCover hψ)) := by
  let hle : (w.aParameterOverInverseGerm hψ).restrictScalars k ≤
      (w.germMultiplicationNormalCover hψ).restrictScalars k := by
    intro x hx
    apply w.abcOverAbGerm_le_germMultiplicationNormalCover hψ
    exact (w.aField_le_abField.trans w.abField_le_abcField) hx
  exact IntermediateField.inclusion hle

/-- The selected displayed `B` parameter field embeds in the common normal
multiplication field. -/
def bParameterToGermMultiplicationNormal (hψ : w.Psi) :
    (↥(w.bParameterOverGerm hψ)) →ₐ[k]
      (↥(w.germMultiplicationNormalCover hψ)) := by
  let hle : (w.bParameterOverGerm hψ).restrictScalars k ≤
      (w.germMultiplicationNormalCover hψ).restrictScalars k := by
    intro x hx
    apply w.abcOverAbGerm_le_germMultiplicationNormalCover hψ
    exact (w.bField_le_abField.trans w.abField_le_abcField) hx
  exact IntermediateField.inclusion hle

/-- The selected displayed output `C` parameter field embeds in the common
normal multiplication field. -/
def cParameterToGermMultiplicationNormal (hψ : w.Psi) :
    (↥(w.cParameterOverGerm hψ)) →ₐ[k]
      (↥(w.germMultiplicationNormalCover hψ)) := by
  let hle : (w.cParameterOverGerm hψ).restrictScalars k ≤
      (w.germMultiplicationNormalCover hψ).restrictScalars k := by
    intro x hx
    apply w.abcOverAbGerm_le_germMultiplicationNormalCover hψ
    exact w.cField_le_abcField hx
  exact IntermediateField.inclusion hle

/-- The dominant rational projection from the normalized multiplication
graph to its selected inverse-oriented `A` input chart. -/
def germMultiplicationToA (hψ : w.Psi) :
    Scheme.RationalMap (w.germMultiplicationAlgebraicChart hψ)
      (w.aInverseGermAlgebraicChart hψ) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.aParameterOverInverseGerm_finiteDimensional hψ
  letI : Fintype (w.aInverseGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xyCorrespondencePairOverA hψ).swap.curveCoefficientSet_finite
        k w.aField)
  exact FiniteExtensionProjection.rationalMap
    (w.abGermCoordinates hψ) (w.aInverseGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.aParameterToGermMultiplicationNormal hψ)

/-- The explicit contravariant function-field embedding induced by the
inverse-`A` projection of the normalized multiplication graph. -/
noncomputable def germMultiplicationToAFunctionFieldRingHom (hψ : w.Psi) :
    (w.aInverseGermAlgebraicChart hψ).functionField →+*
      (w.germMultiplicationAlgebraicChart hψ).functionField := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.aParameterOverInverseGerm_finiteDimensional hψ
  letI : Fintype (w.aInverseGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xyCorrespondencePairOverA hψ).swap.curveCoefficientSet_finite
        k w.aField)
  exact (FiniteExtensionProjection.functionFieldAlgHom
    (w.abGermCoordinates hψ) (w.aInverseGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_aInverseGermCoordinates_eq_top hψ)
    (w.aParameterToGermMultiplicationNormal hψ)).toRingHom

/-- The inverse-`A` graph projection has exactly its displayed field
embedding at the generic point. -/
theorem germMultiplicationToA_fromFunctionField (hψ : w.Psi) :
    (w.germMultiplicationToA hψ).fromFunctionField =
      Scheme.functionFieldMorphismOfHom
        (CommRingCat.ofHom
          (w.germMultiplicationToAFunctionFieldRingHom hψ)) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.aParameterOverInverseGerm_finiteDimensional hψ
  letI : Fintype (w.aInverseGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xyCorrespondencePairOverA hψ).swap.curveCoefficientSet_finite
        k w.aField)
  unfold germMultiplicationToA
    germMultiplicationToAFunctionFieldRingHom
  exact FiniteExtensionProjection.rationalMap_fromFunctionField
    (w.abGermCoordinates hψ) (w.aInverseGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_aInverseGermCoordinates_eq_top hψ)
    (w.aParameterToGermMultiplicationNormal hψ)

instance germMultiplicationToA_isDominant (hψ : w.Psi) :
    (w.germMultiplicationToA hψ).IsDominant := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.aParameterOverInverseGerm_finiteDimensional hψ
  letI : Fintype (w.aInverseGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xyCorrespondencePairOverA hψ).swap.curveCoefficientSet_finite
        k w.aField)
  unfold germMultiplicationToA
  infer_instance

/-- The dominant rational projection from the normalized multiplication
graph to its selected `B` input chart. -/
def germMultiplicationToB (hψ : w.Psi) :
    Scheme.RationalMap (w.germMultiplicationAlgebraicChart hψ)
      (w.bGermAlgebraicChart hψ) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.bParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.bGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientSet_finite
        k w.bField)
  exact FiniteExtensionProjection.rationalMap
    (w.abGermCoordinates hψ) (w.bGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.bParameterToGermMultiplicationNormal hψ)

/-- The explicit contravariant function-field embedding induced by the
`B`-input projection of the normalized multiplication graph. -/
noncomputable def germMultiplicationToBFunctionFieldRingHom (hψ : w.Psi) :
    (w.bGermAlgebraicChart hψ).functionField →+*
      (w.germMultiplicationAlgebraicChart hψ).functionField := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.bParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.bGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientSet_finite
        k w.bField)
  exact (FiniteExtensionProjection.functionFieldAlgHom
    (w.abGermCoordinates hψ) (w.bGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_bGermCoordinates_eq_top hψ)
    (w.bParameterToGermMultiplicationNormal hψ)).toRingHom

/-- The `B`-input graph projection has exactly its displayed field
embedding at the generic point. -/
theorem germMultiplicationToB_fromFunctionField (hψ : w.Psi) :
    (w.germMultiplicationToB hψ).fromFunctionField =
      Scheme.functionFieldMorphismOfHom
        (CommRingCat.ofHom
          (w.germMultiplicationToBFunctionFieldRingHom hψ)) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.bParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.bGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientSet_finite
        k w.bField)
  unfold germMultiplicationToB
    germMultiplicationToBFunctionFieldRingHom
  exact FiniteExtensionProjection.rationalMap_fromFunctionField
    (w.abGermCoordinates hψ) (w.bGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_bGermCoordinates_eq_top hψ)
    (w.bParameterToGermMultiplicationNormal hψ)

instance germMultiplicationToB_isDominant (hψ : w.Psi) :
    (w.germMultiplicationToB hψ).IsDominant := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.bParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.bGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientSet_finite
        k w.bField)
  unfold germMultiplicationToB
  infer_instance

/-- The dominant rational projection from the normalized multiplication
graph to its selected output `C` chart. -/
def germMultiplicationToC (hψ : w.Psi) :
    Scheme.RationalMap (w.germMultiplicationAlgebraicChart hψ)
      (w.cGermAlgebraicChart hψ) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.cParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.cGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xzCorrespondencePairOverC hψ).curveCoefficientSet_finite
        k w.cField)
  exact FiniteExtensionProjection.rationalMap
    (w.abGermCoordinates hψ) (w.cGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.cParameterToGermMultiplicationNormal hψ)

/-- The explicit contravariant function-field embedding induced by the
output-`C` projection of the normalized multiplication graph. -/
noncomputable def germMultiplicationToCFunctionFieldRingHom (hψ : w.Psi) :
    (w.cGermAlgebraicChart hψ).functionField →+*
      (w.germMultiplicationAlgebraicChart hψ).functionField := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.cParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.cGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xzCorrespondencePairOverC hψ).curveCoefficientSet_finite
        k w.cField)
  exact (FiniteExtensionProjection.functionFieldAlgHom
    (w.abGermCoordinates hψ) (w.cGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_cGermCoordinates_eq_top hψ)
    (w.cParameterToGermMultiplicationNormal hψ)).toRingHom

/-- The output-`C` graph projection has exactly its displayed field
embedding at the generic point. -/
theorem germMultiplicationToC_fromFunctionField (hψ : w.Psi) :
    (w.germMultiplicationToC hψ).fromFunctionField =
      Scheme.functionFieldMorphismOfHom
        (CommRingCat.ofHom
          (w.germMultiplicationToCFunctionFieldRingHom hψ)) := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.cParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.cGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xzCorrespondencePairOverC hψ).curveCoefficientSet_finite
        k w.cField)
  unfold germMultiplicationToC
    germMultiplicationToCFunctionFieldRingHom
  exact FiniteExtensionProjection.rationalMap_fromFunctionField
    (w.abGermCoordinates hψ) (w.cGermCoordinates hψ)
    (w.adjoin_abGermCoordinates_eq_top hψ)
    (w.adjoin_cGermCoordinates_eq_top hψ)
    (w.cParameterToGermMultiplicationNormal hψ)

instance germMultiplicationToC_isDominant (hψ : w.Psi) :
    (w.germMultiplicationToC hψ).IsDominant := by
  letI := w.germMultiplicationNormalCover_finiteDimensional hψ
  letI := w.cParameterOverGerm_finiteDimensional hψ
  letI : Fintype (w.cGermCoordinateIndex hψ) :=
    Set.Finite.fintype
      ((w.xzCorrespondencePairOverC hψ).curveCoefficientSet_finite
        k w.cField)
  unfold germMultiplicationToC
  infer_instance

end QWitness

end

end AclGeom
