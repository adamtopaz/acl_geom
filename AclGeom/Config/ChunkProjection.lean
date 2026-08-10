/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.CompositionIdentity

/-!
# The relational projection from the rank-two chunk to the quadrangle chunk

For a `Psi` witness, the points `S`, `T`, and `U` lie below the rank-two
parameter flats `A`, `B`, and `C`.  Thus their representatives are
algebraic over the corresponding parameter pairs.  This module packages
the complete joint locus of

`(A₁,A₂,B₁,B₂,C₁,C₂,S,T,U)`

and proves that every realization of the rank-two `A · B = C` locus lifts
to a compatible realization of the rank-one `S · T = U` locus.

The comparison is intentionally relational.  Incidence gives a dominant
generically positive-dimensional projection after finite cover; it does
not by itself give a literal function on the chosen representatives.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable (w : QWitness k K)

/-- The representatives of the dependent rank-one triple `(S,T,U)`. -/
def stuReps : Fin 3 → K := ![w.S.rep, w.T.rep, w.U.rep]

/-- The six rank-two parameter coordinates followed by their selected
rank-one coordinates `(S,T,U)`. -/
def abcStuReps : Fin 9 → K :=
  ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep,
    w.C₁.rep, w.C₂.rep, w.S.rep, w.T.rep, w.U.rep]

/-- A variable tuple on the joint rank-two/rank-one projection locus. -/
def chunkProjectionTuple (a b c : Fin 2 → K) (s t u : K) :
    Fin 9 → K :=
  ![a 0, a 1, b 0, b 1, c 0, c 1, s, t, u]

/-- A rank-two parameter pair together with one scalar projection
coordinate. -/
def rankTwoScalarTuple (p : Fin 2 → K) (x : K) : Fin 3 → K :=
  ![p 0, p 1, x]

/-- The complete joint locus comparing the rank-two composition parameters
with the dependent partial-quadrangle parameters. -/
def psiChunkProjectionRelation
    (a b c : Fin 2 → K) (s t u : K) : Prop :=
  idealOf k (chunkProjectionTuple a b c s t u) =
    idealOf k w.abcStuReps

/-- The complete graph relation from the rank-two `A` chart to its
selected scalar `S` coordinate. -/
def psiAProjectionRelation (a : Fin 2 → K) (s : K) : Prop :=
  idealOf k (rankTwoScalarTuple a s) =
    idealOf k (rankTwoScalarTuple w.aReps w.S.rep)

/-- The complete graph relation from the rank-two `B` chart to its
selected scalar `T` coordinate.  This is the chart used by right
cancellation in the ambient rank-two chunk. -/
def psiBProjectionRelation (b : Fin 2 → K) (t : K) : Prop :=
  idealOf k (rankTwoScalarTuple b t) =
    idealOf k (rankTwoScalarTuple w.bReps w.T.rep)

/-- The complete graph relation from the rank-two `C` chart to its
selected scalar `U` coordinate. -/
def psiCProjectionRelation (c : Fin 2 → K) (u : K) : Prop :=
  idealOf k (rankTwoScalarTuple c u) =
    idealOf k (rankTwoScalarTuple w.cReps w.U.rep)

/-- The displayed parameters of a `Psi` witness lie on the joint
projection locus. -/
theorem psiChunkProjectionRelation_selected :
    w.psiChunkProjectionRelation w.aReps w.bReps w.cReps
      w.S.rep w.T.rep w.U.rep := by
  change idealOf k w.abcStuReps = idealOf k w.abcStuReps
  rfl

/-- Clause `S ≤ A` makes the selected rank-one `S` coordinate algebraic
over the rank-two `A` parameter. -/
theorem S_rep_mem_racl_aReps (hψ : w.Psi) :
    w.S.rep ∈ racl k (Set.range w.aReps) := by
  have hle := hψ.S_le
  rw [w.a_eq_iSup_point] at hle
  exact mem_iSup_point_iff.1 (hle w.S.mem_rep)

/-- Clause `T ≤ B` makes the selected rank-one `T` coordinate algebraic
over the rank-two `B` parameter. -/
theorem T_rep_mem_racl_bReps (hψ : w.Psi) :
    w.T.rep ∈ racl k (Set.range w.bReps) := by
  have hle := hψ.T_le
  rw [w.b_eq_iSup_point] at hle
  exact mem_iSup_point_iff.1 (hle w.T.mem_rep)

/-- Clause `U ≤ C` makes the selected rank-one `U` coordinate algebraic
over the rank-two `C` parameter. -/
theorem U_rep_mem_racl_cReps (hψ : w.Psi) :
    w.U.rep ∈ racl k (Set.range w.cReps) := by
  have hle := hψ.U_le
  rw [w.c_eq_iSup_point] at hle
  exact mem_iSup_point_iff.1 (hle w.U.mem_rep)

/-- The `A` representatives occur among the full `A,B,C` tuple. -/
theorem aReps_range_subset_abcReps :
    Set.range w.aReps ⊆ Set.range w.abcReps :=
  w.aReps_range_subset_abReps.trans w.abReps_range_subset_abcReps

/-- The `B` representatives occur among the full `A,B,C` tuple. -/
theorem bReps_range_subset_abcReps :
    Set.range w.bReps ⊆ Set.range w.abcReps :=
  w.bReps_range_subset_abReps.trans w.abReps_range_subset_abcReps

/-- Every coordinate of the joint projection tuple is algebraic over the
six rank-two parameter coordinates. -/
theorem abcStuReps_mem_racl_abcReps (hψ : w.Psi) (i : Fin 9) :
    w.abcStuReps i ∈ racl k (Set.range w.abcReps) := by
  fin_cases i
  · exact subset_racl k _ (Set.mem_range_self 0)
  · exact subset_racl k _ (Set.mem_range_self 1)
  · exact subset_racl k _ (Set.mem_range_self 2)
  · exact subset_racl k _ (Set.mem_range_self 3)
  · exact subset_racl k _ (Set.mem_range_self 4)
  · exact subset_racl k _ (Set.mem_range_self 5)
  · exact racl_mono w.aReps_range_subset_abcReps
      (w.S_rep_mem_racl_aReps hψ)
  · exact racl_mono w.bReps_range_subset_abcReps
      (w.T_rep_mem_racl_bReps hψ)
  · exact racl_mono w.cReps_range_subset_abcReps
      (w.U_rep_mem_racl_cReps hψ)

/-- Every point of the rank-two multiplication locus lifts to compatible
rank-one projection coordinates on the fixed complete joint locus. -/
theorem exists_psiChunkProjection_of_relation [IsAlgClosed K]
    (hψ : w.Psi) {a b c : Fin 2 → K}
    (habc : w.psiFamilyCompositionRelation a b c) :
    ∃ s t u : K, w.psiChunkProjectionRelation a b c s t u := by
  classical
  let e : Fin 6 → Fin 9 := ![0, 1, 2, 3, 4, 5]
  have he (i : Fin 6) : w.abcStuReps (e i) = w.abcReps i := by
    fin_cases i <;> rfl
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing_locus
    habc he (w.abcStuReps_mem_racl_abcReps hψ)
  refine ⟨v 6, v 7, v 8, ?_⟩
  have hvtuple : v = chunkProjectionTuple a b c (v 6) (v 7) (v 8) := by
    funext i
    fin_cases i
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (0 : Fin 6)
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (1 : Fin 6)
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (2 : Fin 6)
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (3 : Fin 6)
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (4 : Fin 6)
    · simpa [e, compositionParameterTuple, chunkProjectionTuple] using
        hfix (5 : Fin 6)
    · rfl
    · rfl
    · rfl
  change idealOf k (chunkProjectionTuple a b c (v 6) (v 7) (v 8)) =
    idealOf k w.abcStuReps
  rw [← hvtuple]
  exact hv

/-- A joint projection realization restricts to its rank-two
`A · B = C` locus. -/
theorem PsiChunkProjectionRelation.psiFamilyComposition
    {a b c : Fin 2 → K} {s t u : K}
    (h : w.psiChunkProjectionRelation a b c s t u) :
    w.psiFamilyCompositionRelation a b c := by
  let e : Fin 6 → Fin 9 := ![0, 1, 2, 3, 4, 5]
  have ht := idealOf_comp_eq_of_idealOf_eq h e
  have hleft :
      chunkProjectionTuple a b c s t u ∘ e =
        compositionParameterTuple a b c := by
    funext i
    fin_cases i <;> rfl
  have hright : w.abcStuReps ∘ e = w.abcReps := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright] at ht
  exact ht

/-- A joint projection realization restricts to the dependent
`S · T = U` multiplication locus of every partial quadrangle supplied by
`Psi.quad`. -/
theorem PsiChunkProjectionRelation.parameterMultiplication
    {a b c : Fin 2 → K} {s t u : K}
    (h : w.psiChunkProjectionRelation a b c s t u)
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :
    (IsPartialQuadrangle.parameterMultiplication hquad).IsRealization s t u := by
  let e : Fin 3 → Fin 9 := ![6, 7, 8]
  have ht := idealOf_comp_eq_of_idealOf_eq h e
  have hleft : chunkProjectionTuple a b c s t u ∘ e = ![s, t, u] := by
    funext i
    fin_cases i <;> rfl
  have hright :
      w.abcStuReps ∘ e =
        (IsPartialQuadrangle.parameterMultiplication hquad).tuple := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright] at ht
  exact ht

/-- Restricting the joint comparison locus to coordinates `(A₁,A₂,S)`
gives the `A`-to-`S` graph relation. -/
theorem PsiChunkProjectionRelation.aProjection
    {a b c : Fin 2 → K} {s t u : K}
    (h : w.psiChunkProjectionRelation a b c s t u) :
    w.psiAProjectionRelation a s := by
  let e : Fin 3 → Fin 9 := ![0, 1, 6]
  have ht := idealOf_comp_eq_of_idealOf_eq h e
  have hleft : chunkProjectionTuple a b c s t u ∘ e =
      rankTwoScalarTuple a s := by
    funext i
    fin_cases i <;> rfl
  have hright : w.abcStuReps ∘ e =
      rankTwoScalarTuple w.aReps w.S.rep := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright] at ht
  exact ht

/-- Restricting the joint comparison locus to coordinates `(B₁,B₂,T)`
gives the `B`-to-`T` graph relation. -/
theorem PsiChunkProjectionRelation.bProjection
    {a b c : Fin 2 → K} {s t u : K}
    (h : w.psiChunkProjectionRelation a b c s t u) :
    w.psiBProjectionRelation b t := by
  let e : Fin 3 → Fin 9 := ![2, 3, 7]
  have ht := idealOf_comp_eq_of_idealOf_eq h e
  have hleft : chunkProjectionTuple a b c s t u ∘ e =
      rankTwoScalarTuple b t := by
    funext i
    fin_cases i <;> rfl
  have hright : w.abcStuReps ∘ e =
      rankTwoScalarTuple w.bReps w.T.rep := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright] at ht
  exact ht

/-- Restricting the joint comparison locus to coordinates `(C₁,C₂,U)`
gives the `C`-to-`U` graph relation. -/
theorem PsiChunkProjectionRelation.cProjection
    {a b c : Fin 2 → K} {s t u : K}
    (h : w.psiChunkProjectionRelation a b c s t u) :
    w.psiCProjectionRelation c u := by
  let e : Fin 3 → Fin 9 := ![4, 5, 8]
  have ht := idealOf_comp_eq_of_idealOf_eq h e
  have hleft : chunkProjectionTuple a b c s t u ∘ e =
      rankTwoScalarTuple c u := by
    funext i
    fin_cases i <;> rfl
  have hright : w.abcStuReps ∘ e =
      rankTwoScalarTuple w.cReps w.U.rep := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright] at ht
  exact ht

/-- Adjoining the selected scalar `T` coordinate does not enlarge the
closed rank-two `B` parameter: its graph has total rank two. -/
theorem bT_span_eq_bReps (hψ : w.Psi) :
    (⨆ i, ClosedIF.point k (rankTwoScalarTuple w.bReps w.T.rep i)) =
      ⨆ i, ClosedIF.point k (w.bReps i) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    fin_cases i
    · exact le_iSup_of_le 0 (by rfl)
    · exact le_iSup_of_le 1 (by rfl)
    · change ClosedIF.point k w.T.rep ≤
        ⨆ i, ClosedIF.point k (w.bReps i)
      rw [w.T.point_rep, ← w.b_eq_iSup_point]
      exact hψ.T_le
  · refine iSup_le fun i ↦ ?_
    fin_cases i
    · exact le_iSup_of_le 0 (by rfl)
    · exact le_iSup_of_le 1 (by rfl)

/-- The generic `B`-to-`T` projection graph has exact total rank two.
Since `T` itself is a point, this records the expected rank-one generic
fiber of the relational chart. -/
theorem bTProjection_rank (hψ : w.Psi) :
    RankEq 2
      (⨆ i, ClosedIF.point k (rankTwoScalarTuple w.bReps w.T.rep i)) := by
  exact RankEq.congr (w.bT_span_eq_bReps hψ).symm
    (rankEq_iSup_point (w.bReps_independent hψ))

end QWitness

end
end AclGeom
