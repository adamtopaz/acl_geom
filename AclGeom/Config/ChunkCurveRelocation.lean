/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkFiniteFieldAction
import AclGeom.Correspondence.FiniteCompositionTriangle

/-!
# Relocating the Ψ curve-coordinate composition triangle

A point of the rank-two parameter multiplication locus does not yet carry
the curve coordinates on which its three correspondence branches act.  This
file relocates the complete selected tuple

`(A, B, C, X, Y, Z)`

over any other realization `(a,b,c)` of the same parameter locus once a
source coordinate generic over those parameters has been chosen.  The
relocation fixes `(a,b,c,x)` literally and preserves the complete prime
locus.  Its three restrictions are therefore genuine members of the
selected `A`, `B`, and `C` curve-correspondence families with a shared
middle coordinate and shared endpoints.

This is the curve-coordinate input for constructing strict finite-cover
composition triangles over each edge of a normalized four-arrow diagram.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable (w : QWitness k K)

/-- The full parameter-and-curve tuple attached to one Ψ composition
triangle. -/
def psiCurveCompositionTuple (_w : QWitness k K)
    (a b c : Fin 2 → K) (x y z : K) :
    Fin 9 → K :=
  ![a 0, a 1, b 0, b 1, c 0, c 1, x, y, z]

/-- The selected full tuple `(A,B,C,X,Y,Z)` of the Ψ witness. -/
abbrev psiSelectedCurveCompositionTuple : Fin 9 → K :=
  w.psiCurveCompositionTuple w.aReps w.bReps w.cReps
    w.X.rep w.Y.rep w.Z.rep

/-- The six parameters followed by the source curve coordinate. -/
def psiCurveParameterSourceTuple (a b c : Fin 2 → K) (x : K) :
    Fin 7 → K :=
  Fin.snoc (compositionParameterTuple a b c) x

/-- Coordinate inclusion of `(a,b,c,x)` into the full nine-coordinate
curve-composition tuple. -/
def psiCurveParameterSourceIndex : Fin 7 → Fin 9 :=
  ![0, 1, 2, 3, 4, 5, 6]

/-- Coordinate inclusion of the six displayed parameters into the full
curve-composition tuple. -/
def psiCurveParameterIndex : Fin 6 → Fin 9 :=
  ![0, 1, 2, 3, 4, 5]

omit [Field K] in
/-- The `A` parameter coordinates occur among the six parameters of a
composition triangle. -/
theorem a_range_subset_compositionParameterTuple
    (a b c : Fin 2 → K) :
    Set.range a ⊆ Set.range (compositionParameterTuple a b c) := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [compositionParameterTuple]

omit [Field K] in
/-- The `B` parameter coordinates occur among the six parameters of a
composition triangle. -/
theorem b_range_subset_compositionParameterTuple
    (a b c : Fin 2 → K) :
    Set.range b ⊆ Set.range (compositionParameterTuple a b c) := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [compositionParameterTuple]

omit [Field K] in
/-- The `C` parameter coordinates occur among the six parameters of a
composition triangle. -/
theorem c_range_subset_compositionParameterTuple
    (a b c : Fin 2 → K) :
    Set.range c ⊆ Set.range (compositionParameterTuple a b c) := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [compositionParameterTuple]

/-- Restricting the full curve-composition tuple to the parameter/source
coordinates recovers the displayed seven-tuple. -/
@[simp] theorem psiCurveCompositionTuple_comp_parameterSourceIndex
    (a b c : Fin 2 → K) (x y z : K) :
    w.psiCurveCompositionTuple a b c x y z ∘
        psiCurveParameterSourceIndex =
      psiCurveParameterSourceTuple a b c x := by
  funext i
  fin_cases i <;> rfl

/-- The selected middle coordinate is algebraic over all six displayed
parameters and the selected source coordinate. -/
theorem Y_rep_mem_racl_abcReps_snoc_X (hψ : w.Psi) :
    w.Y.rep ∈ racl k
      (Set.range (Fin.snoc w.abcReps w.X.rep)) := by
  refine racl_mono ?_ (w.Y_rep_mem_racl_abReps_snoc_X hψ)
  rw [Fin.range_snoc, Fin.range_snoc]
  exact Set.union_subset_union Set.Subset.rfl
    w.abReps_range_subset_abcReps

/-- Every coordinate of the selected full composition tuple is algebraic
over its parameter/source prefix. -/
theorem psiSelectedCurveCompositionTuple_mem_parameterSource_racl
    (hψ : w.Psi) (i : Fin 9) :
    w.psiSelectedCurveCompositionTuple i ∈ racl k
      (Set.range (psiCurveParameterSourceTuple
        w.aReps w.bReps w.cReps w.X.rep)) := by
  fin_cases i
  · exact subset_racl k _ (Set.mem_range_self 0)
  · exact subset_racl k _ (Set.mem_range_self 1)
  · exact subset_racl k _ (Set.mem_range_self 2)
  · exact subset_racl k _ (Set.mem_range_self 3)
  · exact subset_racl k _ (Set.mem_range_self 4)
  · exact subset_racl k _ (Set.mem_range_self 5)
  · exact subset_racl k _ (Set.mem_range_self 6)
  · exact w.Y_rep_mem_racl_abcReps_snoc_X hψ
  · exact w.Z_rep_mem_racl_abcReps_snoc_X hψ

/-- A relocated Ψ curve-composition triangle over displayed rank-two
parameters.  Equality of the complete nine-coordinate locus retains the
chosen irreducible branches simultaneously. -/
structure PsiCurveCompositionRealization (a b c : Fin 2 → K) where
  /-- Shared source coordinate of the `A` and `C` branches. -/
  source : K
  /-- Shared middle coordinate between the `A` and `B` branches. -/
  middle : K
  /-- Shared target coordinate of the `B` and `C` branches. -/
  target : K
  /-- The full parameter-and-curve tuple has the selected Ψ locus. -/
  locus :
    idealOf k (w.psiCurveCompositionTuple a b c source middle target) =
      idealOf k w.psiSelectedCurveCompositionTuple

namespace PsiCurveCompositionRealization

variable {w : QWitness k K} {a b c : Fin 2 → K}
  (R : w.PsiCurveCompositionRealization a b c)

/-- The full tuple of a relocated curve-composition realization. -/
abbrev totalTuple : Fin 9 → K :=
  w.psiCurveCompositionTuple a b c R.source R.middle R.target

include R in
/-- The parameters of a relocated curve triangle remain on the selected
rank-two Ψ multiplication locus. -/
theorem parameterRelation : w.psiFamilyCompositionRelation a b c := by
  let e : Fin 6 → Fin 9 := ![0, 1, 2, 3, 4, 5]
  have h := idealOf_comp_eq_of_idealOf_eq
    (PsiCurveCompositionRealization.locus R) e
  change idealOf k (compositionParameterTuple a b c) =
    idealOf k w.abcReps
  calc
    idealOf k (compositionParameterTuple a b c) =
        idealOf k (R.totalTuple ∘ e) := by
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = idealOf k (w.psiSelectedCurveCompositionTuple ∘ e) := h
    _ = idealOf k w.abcReps := by
      congr 1
      funext i
      fin_cases i <;> rfl

include R in
/-- The relocated source remains generic over the complete six-parameter
coefficient tuple. -/
theorem source_notMem_racl_parameters (hψ : w.Psi) :
    R.source ∉ racl k
      (Set.range (compositionParameterTuple a b c)) := by
  have himageSelected :
      w.psiSelectedCurveCompositionTuple ''
          Set.range psiCurveParameterIndex =
        Set.range w.abcReps := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hselected : w.psiSelectedCurveCompositionTuple 6 ∉
      racl k (w.psiSelectedCurveCompositionTuple ''
        Set.range psiCurveParameterIndex) := by
    rw [himageSelected]
    exact w.X_rep_notMem_racl_abcReps hψ
  have ht := notMem_racl_image_of_idealOf_eq k
    (PsiCurveCompositionRealization.locus R).symm hselected
  have himage : R.totalTuple '' Set.range psiCurveParameterIndex =
      Set.range (compositionParameterTuple a b c) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [himage] at ht
  simpa [totalTuple, psiCurveCompositionTuple] using ht

include R in
/-- The relocated middle remains generic over the complete six-parameter
coefficient tuple. -/
theorem middle_notMem_racl_parameters (hψ : w.Psi) :
    R.middle ∉ racl k
      (Set.range (compositionParameterTuple a b c)) := by
  have himageSelected :
      w.psiSelectedCurveCompositionTuple ''
          Set.range psiCurveParameterIndex =
        Set.range w.abcReps := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hselected : w.psiSelectedCurveCompositionTuple 7 ∉
      racl k (w.psiSelectedCurveCompositionTuple ''
        Set.range psiCurveParameterIndex) := by
    rw [himageSelected]
    exact w.Y_rep_notMem_racl_abcReps hψ
  have ht := notMem_racl_image_of_idealOf_eq k
    (PsiCurveCompositionRealization.locus R).symm hselected
  have himage : R.totalTuple '' Set.range psiCurveParameterIndex =
      Set.range (compositionParameterTuple a b c) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [himage] at ht
  simpa [totalTuple, psiCurveCompositionTuple] using ht

include R in
/-- The relocated target remains generic over the complete six-parameter
coefficient tuple. -/
theorem target_notMem_racl_parameters (hψ : w.Psi) :
    R.target ∉ racl k
      (Set.range (compositionParameterTuple a b c)) := by
  have himageSelected :
      w.psiSelectedCurveCompositionTuple ''
          Set.range psiCurveParameterIndex =
        Set.range w.abcReps := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hselected : w.psiSelectedCurveCompositionTuple 8 ∉
      racl k (w.psiSelectedCurveCompositionTuple ''
        Set.range psiCurveParameterIndex) := by
    rw [himageSelected]
    exact w.Z_rep_notMem_racl_abcReps hψ
  have ht := notMem_racl_image_of_idealOf_eq k
    (PsiCurveCompositionRealization.locus R).symm hselected
  have himage : R.totalTuple '' Set.range psiCurveParameterIndex =
      Set.range (compositionParameterTuple a b c) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [himage] at ht
  simpa [totalTuple, psiCurveCompositionTuple] using ht

include R in
/-- The relocated `A` parameter retains rank two. -/
theorem aParameter_independent (hψ : w.Psi) :
    AlgebraicIndependent k a := by
  have hreal := (w.psiFamilyCompositionRelation_iff_isRealization
    hψ a b c).1 R.parameterRelation
  have h := AlgebraicIndependent.comp hreal.leftRight_independent
    (![0, 1] : Fin 2 → Fin 4) (by decide)
  convert h using 1
  funext i
  fin_cases i <;> rfl

include R in
/-- The relocated `B` parameter retains rank two. -/
theorem bParameter_independent (hψ : w.Psi) :
    AlgebraicIndependent k b := by
  have hreal := (w.psiFamilyCompositionRelation_iff_isRealization
    hψ a b c).1 R.parameterRelation
  have h := AlgebraicIndependent.comp hreal.leftRight_independent
    (![2, 3] : Fin 2 → Fin 4) (by decide)
  convert h using 1
  funext i
  fin_cases i <;> rfl

include R in
/-- The relocated `C` parameter retains rank two. -/
theorem cParameter_independent (hψ : w.Psi) :
    AlgebraicIndependent k c := by
  have hreal := (w.psiFamilyCompositionRelation_iff_isRealization
    hψ a b c).1 R.parameterRelation
  have h := AlgebraicIndependent.comp hreal.leftOutput_independent
    (![2, 3] : Fin 2 → Fin 4) (by decide)
  convert h using 1
  funext i
  fin_cases i <;> rfl

/-- Coordinate inclusion of the relocated `A` family member. -/
def aFamilyIndex : Fin 4 → Fin 9 := ![0, 1, 6, 7]

/-- Coordinate inclusion of the relocated `B` family member. -/
def bFamilyIndex : Fin 4 → Fin 9 := ![2, 3, 7, 8]

/-- Coordinate inclusion of the relocated `C` family member. -/
def cFamilyIndex : Fin 4 → Fin 9 := ![4, 5, 6, 8]

/-- The `A` family tuple is a coordinate restriction of the full
composition tuple. -/
@[simp] theorem totalTuple_comp_aFamilyIndex :
    R.totalTuple ∘ aFamilyIndex =
      Fin.snoc (Fin.snoc a R.source) R.middle := by
  funext i
  fin_cases i <;> rfl

/-- The `B` family tuple is a coordinate restriction of the full
composition tuple. -/
@[simp] theorem totalTuple_comp_bFamilyIndex :
    R.totalTuple ∘ bFamilyIndex =
      Fin.snoc (Fin.snoc b R.middle) R.target := by
  funext i
  fin_cases i <;> rfl

/-- The `C` family tuple is a coordinate restriction of the full
composition tuple. -/
@[simp] theorem totalTuple_comp_cFamilyIndex :
    R.totalTuple ∘ cFamilyIndex =
      Fin.snoc (Fin.snoc c R.source) R.target := by
  funext i
  fin_cases i <;> rfl

/-- The selected full tuple restricts to the selected `A` family member. -/
@[simp] theorem selectedTuple_comp_aFamilyIndex (hψ : w.Psi) :
    w.psiSelectedCurveCompositionTuple ∘ aFamilyIndex =
      (w.xyCorrespondenceFamilyMember hψ).tuple := by
  funext i
  fin_cases i <;> rfl

/-- The selected full tuple restricts to the selected `B` family member. -/
@[simp] theorem selectedTuple_comp_bFamilyIndex (hψ : w.Psi) :
    w.psiSelectedCurveCompositionTuple ∘ bFamilyIndex =
      (w.yzCorrespondenceFamilyMember hψ).tuple := by
  funext i
  fin_cases i <;> rfl

/-- The selected full tuple restricts to the selected `C` family member. -/
@[simp] theorem selectedTuple_comp_cFamilyIndex (hψ : w.Psi) :
    w.psiSelectedCurveCompositionTuple ∘ cFamilyIndex =
      (w.xzCorrespondenceFamilyMember hψ).tuple := by
  funext i
  fin_cases i <;> rfl

/-- The relocated `A` branch has exactly the selected `A` family locus. -/
theorem aFamilyLocus (hψ : w.Psi) :
    idealOf k (Fin.snoc (Fin.snoc a R.source) R.middle) =
      (w.xyCorrespondenceFamilyMember hψ).ideal := by
  have h := idealOf_comp_eq_of_idealOf_eq
    (PsiCurveCompositionRealization.locus R) aFamilyIndex
  change idealOf k (Fin.snoc (Fin.snoc a R.source) R.middle) =
    idealOf k (w.xyCorrespondenceFamilyMember hψ).tuple
  rw [← R.totalTuple_comp_aFamilyIndex,
    ← selectedTuple_comp_aFamilyIndex hψ]
  exact h

/-- The relocated `B` branch has exactly the selected `B` family locus. -/
theorem bFamilyLocus (hψ : w.Psi) :
    idealOf k (Fin.snoc (Fin.snoc b R.middle) R.target) =
      (w.yzCorrespondenceFamilyMember hψ).ideal := by
  have h := idealOf_comp_eq_of_idealOf_eq
    (PsiCurveCompositionRealization.locus R) bFamilyIndex
  change idealOf k (Fin.snoc (Fin.snoc b R.middle) R.target) =
    idealOf k (w.yzCorrespondenceFamilyMember hψ).tuple
  rw [← R.totalTuple_comp_bFamilyIndex,
    ← selectedTuple_comp_bFamilyIndex hψ]
  exact h

/-- The relocated `C` branch has exactly the selected `C` family locus. -/
theorem cFamilyLocus (hψ : w.Psi) :
    idealOf k (Fin.snoc (Fin.snoc c R.source) R.target) =
      (w.xzCorrespondenceFamilyMember hψ).ideal := by
  have h := idealOf_comp_eq_of_idealOf_eq
    (PsiCurveCompositionRealization.locus R) cFamilyIndex
  change idealOf k (Fin.snoc (Fin.snoc c R.source) R.target) =
    idealOf k (w.xzCorrespondenceFamilyMember hψ).tuple
  rw [← R.totalTuple_comp_cFamilyIndex,
    ← selectedTuple_comp_cFamilyIndex hψ]
  exact h

include R in
/-- The relocated source is generic over the `A` parameter. -/
theorem source_notMem_racl_a (hψ : w.Psi) :
    R.source ∉ racl k (Set.range a) := by
  intro hmem
  exact R.source_notMem_racl_parameters hψ
    (racl_mono (a_range_subset_compositionParameterTuple a b c) hmem)

include R in
/-- The relocated middle is generic over the `B` parameter. -/
theorem middle_notMem_racl_b (hψ : w.Psi) :
    R.middle ∉ racl k (Set.range b) := by
  intro hmem
  exact R.middle_notMem_racl_parameters hψ
    (racl_mono (b_range_subset_compositionParameterTuple a b c) hmem)

include R in
/-- The relocated source is generic over the `C` parameter. -/
theorem source_notMem_racl_c (hψ : w.Psi) :
    R.source ∉ racl k (Set.range c) := by
  intro hmem
  exact R.source_notMem_racl_parameters hψ
    (racl_mono (c_range_subset_compositionParameterTuple a b c) hmem)

/-- The relocated `A` restriction, packaged as a genuine generic member
of the selected rank-two correspondence family. -/
def aCorrespondenceFamilyMember (hψ : w.Psi) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 2 :=
  (w.xyCorrespondenceFamilyMember hψ).ofTupleIdealEq
    (algebraicIndependent_snoc (R.aParameter_independent hψ)
      (R.source_notMem_racl_a hψ))
    (R.aFamilyLocus hψ)

/-- The relocated `B` restriction, packaged as a genuine generic member
of the selected rank-two correspondence family. -/
def bCorrespondenceFamilyMember (hψ : w.Psi) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 2 :=
  (w.yzCorrespondenceFamilyMember hψ).ofTupleIdealEq
    (algebraicIndependent_snoc (R.bParameter_independent hψ)
      (R.middle_notMem_racl_b hψ))
    (R.bFamilyLocus hψ)

/-- The relocated `C` restriction, packaged as a genuine generic member
of the selected rank-two correspondence family. -/
def cCorrespondenceFamilyMember (hψ : w.Psi) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 2 :=
  (w.xzCorrespondenceFamilyMember hψ).ofTupleIdealEq
    (algebraicIndependent_snoc (R.cParameter_independent hψ)
      (R.source_notMem_racl_c hψ))
    (R.cFamilyLocus hψ)

/-- The coefficient field generated by all six displayed parameters of a
relocated composition triangle. -/
def coefficientField
    (_R : w.PsiCurveCompositionRealization a b c) :
    IntermediateField k K :=
  adjoin k (Set.range (compositionParameterTuple a b c))

/-- The relocated `A` branch as a finite correspondence over the common
six-parameter coefficient field. -/
def aCorrespondencePair (hψ : w.Psi) :
    FiniteCorrespondencePair (↥R.coefficientField) K where
  source := R.source
  target := R.middle
  source_generic := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact R.source_notMem_racl_parameters hψ
  target_mem_source := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.aCorrespondenceFamilyMember hψ)
      |>.target_mem_parameter_source
    change R.middle ∈ racl k (insert R.source (Set.range a)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (a_range_subset_compositionParameterTuple a b c)) h
  source_mem_target := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.aCorrespondenceFamilyMember hψ)
      |>.source_mem_parameter_target
    change R.source ∈ racl k (insert R.middle (Set.range a)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (a_range_subset_compositionParameterTuple a b c)) h

/-- The relocated `B` branch as a finite correspondence over the common
six-parameter coefficient field. -/
def bCorrespondencePair (hψ : w.Psi) :
    FiniteCorrespondencePair (↥R.coefficientField) K where
  source := R.middle
  target := R.target
  source_generic := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact R.middle_notMem_racl_parameters hψ
  target_mem_source := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.bCorrespondenceFamilyMember hψ)
      |>.target_mem_parameter_source
    change R.target ∈ racl k (insert R.middle (Set.range b)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (b_range_subset_compositionParameterTuple a b c)) h
  source_mem_target := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.bCorrespondenceFamilyMember hψ)
      |>.source_mem_parameter_target
    change R.middle ∈ racl k (insert R.target (Set.range b)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (b_range_subset_compositionParameterTuple a b c)) h

/-- The relocated `C` branch as a finite correspondence over the common
six-parameter coefficient field.  It has the same literal source and
target as the composite of the preceding two pairs. -/
def cCorrespondencePair (hψ : w.Psi) :
    FiniteCorrespondencePair (↥R.coefficientField) K where
  source := R.source
  target := R.target
  source_generic := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact R.source_notMem_racl_parameters hψ
  target_mem_source := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.cCorrespondenceFamilyMember hψ)
      |>.target_mem_parameter_source
    change R.target ∈ racl k (insert R.source (Set.range c)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (c_range_subset_compositionParameterTuple a b c)) h
  source_mem_target := by
    rw [coefficientField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have h := (R.cCorrespondenceFamilyMember hψ)
      |>.source_mem_parameter_target
    change R.source ∈ racl k (insert R.target (Set.range c)) at h
    exact racl_mono
      (Set.insert_subset_insert
        (c_range_subset_compositionParameterTuple a b c)) h

/-- The relocated `A` and `B` pairs share their middle coordinate
definitionally. -/
@[simp] theorem aPair_target_eq_bPair_source (hψ : w.Psi) :
    (R.aCorrespondencePair hψ).target =
      (R.bCorrespondencePair hψ).source := rfl

/-- The relocated `C` pair has exactly the endpoints of the `A`-then-`B`
composite. -/
@[simp] theorem composite_endpoints_eq_cPair (hψ : w.Psi) :
    ((R.aCorrespondencePair hψ).comp
      (R.bCorrespondencePair hψ)
      (R.aPair_target_eq_bPair_source hψ)).source =
        (R.cCorrespondencePair hψ).source ∧
    ((R.aCorrespondencePair hψ).comp
      (R.bCorrespondencePair hψ)
      (R.aPair_target_eq_bPair_source hψ)).target =
        (R.cCorrespondencePair hψ).target :=
  ⟨rfl, rfl⟩

/-- The common finite normal source cover of the relocated composition
triangle. -/
noncomputable def finiteSourceCover (hψ : w.Psi) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.sourceCover
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The common finite normal middle cover of the relocated composition
triangle. -/
noncomputable def finiteMiddleCover (hψ : w.Psi) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.middleCover
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The common finite normal target cover of the relocated composition
triangle. -/
noncomputable def finiteTargetCover (hψ : w.Psi) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.targetCover
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The relocated `A` branch restricted to the common finite normal
covers. -/
noncomputable def aFiniteCoverEquiv (hψ : w.Psi) :
    (↥(R.finiteSourceCover hψ).field) ≃+*
      (↥(R.finiteMiddleCover hψ).field) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.leftEquiv
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The relocated `B` branch restricted to the common finite normal
covers. -/
noncomputable def bFiniteCoverEquiv (hψ : w.Psi) :
    (↥(R.finiteMiddleCover hψ).field) ≃+*
      (↥(R.finiteTargetCover hψ).field) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.rightEquiv
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The deck-corrected direct branch on the relocated common finite normal
covers.  Its endpoints are those of the actual relocated `C` family
member. -/
noncomputable def strictCFiniteCoverEquiv (hψ : w.Psi) :
    (↥(R.finiteSourceCover hψ).field) ≃+*
      (↥(R.finiteTargetCover hψ).field) :=
  FiniteCorrespondencePair.FiniteCoverTriangle.strictDirectEquiv
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- Every relocated Ψ curve triangle therefore gives a literal
finite-normal-cover composition identity. -/
theorem finiteCoverStrictComposition (hψ : w.Psi) :
    (R.aFiniteCoverEquiv hψ).trans (R.bFiniteCoverEquiv hψ) =
      R.strictCFiniteCoverEquiv hψ :=
  FiniteCorrespondencePair.FiniteCoverTriangle.strictComposition
    (R.aCorrespondencePair hψ) (R.bCorrespondencePair hψ)
    (R.aPair_target_eq_bPair_source hψ)

/-- The relocated finite-cover action packaged as one literal composition
triangle. -/
noncomputable def finiteCoverCompositionTriangle (hψ : w.Psi) :
    FieldEquiv.CompositionTriangle
      (↥(R.finiteSourceCover hψ).field)
      (↥(R.finiteMiddleCover hψ).field)
      (↥(R.finiteTargetCover hψ).field) where
  left := R.aFiniteCoverEquiv hψ
  right := R.bFiniteCoverEquiv hψ
  direct := R.strictCFiniteCoverEquiv hψ
  composition := R.finiteCoverStrictComposition hψ

end PsiCurveCompositionRealization

/-- Relocate the complete selected curve-composition triangle over any
parameter realization and any source coordinate generic over those six
parameters.  The parameters and source are fixed literally. -/
theorem exists_psiCurveCompositionRealization [IsAlgClosed K]
    (hψ : w.Psi) {a b c : Fin 2 → K}
    (hrel : w.psiFamilyCompositionRelation a b c) {x : K}
    (hx : x ∉ racl k (Set.range (compositionParameterTuple a b c))) :
    ∃ R : w.PsiCurveCompositionRealization a b c, R.source = x := by
  have hparameter :
      idealOf k (compositionParameterTuple a b c) =
        idealOf k w.abcReps := by
    simpa [psiFamilyCompositionRelation] using hrel
  have hsource : w.X.rep ∉ racl k (Set.range w.abcReps) :=
    w.X_rep_notMem_racl_abcReps hψ
  have hfixed :
      idealOf k (psiCurveParameterSourceTuple a b c x) =
        idealOf k (psiCurveParameterSourceTuple
          w.aReps w.bReps w.cReps w.X.rep) := by
    have habc : compositionParameterTuple
        w.aReps w.bReps w.cReps = w.abcReps := by
      funext i
      fin_cases i <;> rfl
    change idealOf k (Fin.snoc (compositionParameterTuple a b c) x) =
      idealOf k (Fin.snoc
        (compositionParameterTuple w.aReps w.bReps w.cReps) w.X.rep)
    rw [habc]
    exact idealOf_snoc_eq_of_idealOf_eq_of_generic
      hparameter hx hsource
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing_locus
    hfixed
    (u := w.psiSelectedCurveCompositionTuple)
    (e := psiCurveParameterSourceIndex)
    (fun i ↦ congrFun
      (w.psiCurveCompositionTuple_comp_parameterSourceIndex
        w.aReps w.bReps w.cReps w.X.rep w.Y.rep w.Z.rep) i)
    (w.psiSelectedCurveCompositionTuple_mem_parameterSource_racl hψ)
  let y : K := v 7
  let z : K := v 8
  have htotal : w.psiCurveCompositionTuple a b c x y z = v := by
    funext i
    fin_cases i
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 0).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 1).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 2).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 3).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 4).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 5).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTuple, compositionParameterTuple,
        psiCurveCompositionTuple] using (hfix 6).symm
    · rfl
    · rfl
  let R : w.PsiCurveCompositionRealization a b c :=
    { source := x
      middle := y
      target := z
      locus := by rw [htotal]; exact hv }
  exact ⟨R, rfl⟩

end QWitness

end

end AclGeom
