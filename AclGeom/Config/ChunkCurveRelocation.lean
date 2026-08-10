/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkFiniteFieldAction

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
