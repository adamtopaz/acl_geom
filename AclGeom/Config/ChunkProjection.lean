/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.CompositionIdentity
import Mathlib.Algebra.Group.Subgroup.Ker

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
open CategoryTheory

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

/-- A rank-two parameter equipped with one scalar coordinate on the joint
presentation. -/
abbrev ChunkParameter := (Fin 2 → K) × K

/-- The ternary relation on joint parameters.  Its first coordinate is the
ambient `A/B/C` relation and its second coordinate is the dependent
`S/T/U` relation, retained on one complete prime locus. -/
def psiChunkFamilyRelation
    (p q r : ChunkParameter (K := K)) : Prop :=
  w.psiChunkProjectionRelation p.1 q.1 r.1 p.2 q.2 r.2

/-- The groupoid presented directly by the joint rank-two/scalar locus. -/
abbrev psiChunkFamilyGroupoid :=
  PresentedFamilyGroupoidOf w.psiChunkFamilyRelation

/-- The joint `A/S`-family arrow. -/
def psiChunkAArrow (p : ChunkParameter (K := K)) :
    PresentedFamilyGroupoidOf.x0 w.psiChunkFamilyRelation ⟶
      PresentedFamilyGroupoidOf.x1 w.psiChunkFamilyRelation :=
  PresentedFamilyGroupoidOf.t w.psiChunkFamilyRelation p

/-- The joint `B/T`-family arrow, which is the cancellation chart. -/
def psiChunkBArrow (p : ChunkParameter (K := K)) :
    PresentedFamilyGroupoidOf.x1 w.psiChunkFamilyRelation ⟶
      PresentedFamilyGroupoidOf.x2 w.psiChunkFamilyRelation :=
  PresentedFamilyGroupoidOf.s w.psiChunkFamilyRelation p

/-- The joint `C/U`-family arrow. -/
def psiChunkCArrow (p : ChunkParameter (K := K)) :
    PresentedFamilyGroupoidOf.x0 w.psiChunkFamilyRelation ⟶
      PresentedFamilyGroupoidOf.x2 w.psiChunkFamilyRelation :=
  PresentedFamilyGroupoidOf.u w.psiChunkFamilyRelation p

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

/-- Forgetting the scalar coordinate on every joint parameter defines a
functor from the joint presentation to the ambient rank-two presentation. -/
def psiChunkAmbientFunctor :
    w.psiChunkFamilyGroupoid ⥤ w.psiParameterFamilyGroupoid :=
  PresentedFamilyGroupoidOf.map w.psiChunkFamilyRelation Prod.fst (by
    intro p q r h
    change w.psiChunkProjectionRelation
      p.1 q.1 r.1 p.2 q.2 r.2 at h
    exact PsiChunkProjectionRelation.psiFamilyComposition w h)

@[simp] theorem psiChunkAmbientFunctor_map_a
    (p : ChunkParameter (K := K)) :
    w.psiChunkAmbientFunctor.map (w.psiChunkAArrow p) =
      w.psiAArrow p.1 := by
  change (PresentedFamilyGroupoidOf.freeRelabelFunctor
    w.psiFamilyCompositionRelation Prod.fst).map
      (FreeCorrespondenceFamilyGroupoid.t p) = _
  exact PresentedFamilyGroupoidOf.freeRelabelFunctor_t
    w.psiFamilyCompositionRelation Prod.fst p

@[simp] theorem psiChunkAmbientFunctor_map_b
    (p : ChunkParameter (K := K)) :
    w.psiChunkAmbientFunctor.map (w.psiChunkBArrow p) =
      w.psiBArrow p.1 := by
  change (PresentedFamilyGroupoidOf.freeRelabelFunctor
    w.psiFamilyCompositionRelation Prod.fst).map
      (FreeCorrespondenceFamilyGroupoid.s p) = _
  exact PresentedFamilyGroupoidOf.freeRelabelFunctor_s
    w.psiFamilyCompositionRelation Prod.fst p

@[simp] theorem psiChunkAmbientFunctor_map_c
    (p : ChunkParameter (K := K)) :
    w.psiChunkAmbientFunctor.map (w.psiChunkCArrow p) =
      w.psiCArrow p.1 := by
  change (PresentedFamilyGroupoidOf.freeRelabelFunctor
    w.psiFamilyCompositionRelation Prod.fst).map
      (FreeCorrespondenceFamilyGroupoid.u p) = _
  exact PresentedFamilyGroupoidOf.freeRelabelFunctor_u
    w.psiFamilyCompositionRelation Prod.fst p

/-- The generic relation presenting the scalar partial-quadrangle
groupoid, written in categorical order `T(t) ≫ S(s) = U(u)`. -/
def partialQuadrangleFamilyRelation
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (t s u : K) : Prop :=
  (IsPartialQuadrangle.parameterMultiplication hquad).IsRealization s t u

/-- The scalar groupoid presentation attached to the selected partial
quadrangle. -/
abbrev partialQuadrangleFamilyGroupoid
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :=
  PresentedFamilyGroupoidOf (w.partialQuadrangleFamilyRelation hquad)

/-- The scalar `T`-arrow in the generic presentation. -/
def partialQuadrangleTArrow
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) (t : K) :
    PresentedFamilyGroupoidOf.x0 (w.partialQuadrangleFamilyRelation hquad) ⟶
      PresentedFamilyGroupoidOf.x1 (w.partialQuadrangleFamilyRelation hquad) :=
  PresentedFamilyGroupoidOf.t (w.partialQuadrangleFamilyRelation hquad) t

/-- The scalar `S`-arrow in the generic presentation. -/
def partialQuadrangleSArrow
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) (s : K) :
    PresentedFamilyGroupoidOf.x1 (w.partialQuadrangleFamilyRelation hquad) ⟶
      PresentedFamilyGroupoidOf.x2 (w.partialQuadrangleFamilyRelation hquad) :=
  PresentedFamilyGroupoidOf.s (w.partialQuadrangleFamilyRelation hquad) s

/-- The scalar `U`-arrow in the generic presentation. -/
def partialQuadrangleUArrow
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) (u : K) :
    PresentedFamilyGroupoidOf.x0 (w.partialQuadrangleFamilyRelation hquad) ⟶
      PresentedFamilyGroupoidOf.x2 (w.partialQuadrangleFamilyRelation hquad) :=
  PresentedFamilyGroupoidOf.u (w.partialQuadrangleFamilyRelation hquad) u

/-- The scalar coordinate defines an anti-oriented functor from the joint
presentation: `A/S`, `B/T`, and `C/U` exchange the first two families, so
the target arrows are inverted. -/
def psiChunkScalarReverseFunctor
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :
    w.psiChunkFamilyGroupoid ⥤ w.partialQuadrangleFamilyGroupoid hquad :=
  PresentedFamilyGroupoidOf.reverseMap w.psiChunkFamilyRelation Prod.snd (by
    intro p q r h
    change w.psiChunkProjectionRelation
      p.1 q.1 r.1 p.2 q.2 r.2 at h
    exact PsiChunkProjectionRelation.parameterMultiplication w h hquad)

@[simp] theorem psiChunkScalarReverseFunctor_map_a
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (p : ChunkParameter (K := K)) :
    (w.psiChunkScalarReverseFunctor hquad).map (w.psiChunkAArrow p) =
      inv (w.partialQuadrangleSArrow hquad p.2) := by
  change (PresentedFamilyGroupoidOf.freeReverseRelabelFunctor
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd).map
      (FreeCorrespondenceFamilyGroupoid.t p) = _
  exact PresentedFamilyGroupoidOf.freeReverseRelabelFunctor_t
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd p

@[simp] theorem psiChunkScalarReverseFunctor_map_b
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (p : ChunkParameter (K := K)) :
    (w.psiChunkScalarReverseFunctor hquad).map (w.psiChunkBArrow p) =
      inv (w.partialQuadrangleTArrow hquad p.2) := by
  change (PresentedFamilyGroupoidOf.freeReverseRelabelFunctor
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd).map
      (FreeCorrespondenceFamilyGroupoid.s p) = _
  exact PresentedFamilyGroupoidOf.freeReverseRelabelFunctor_s
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd p

@[simp] theorem psiChunkScalarReverseFunctor_map_c
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (p : ChunkParameter (K := K)) :
    (w.psiChunkScalarReverseFunctor hquad).map (w.psiChunkCArrow p) =
      inv (w.partialQuadrangleUArrow hquad p.2) := by
  change (PresentedFamilyGroupoidOf.freeReverseRelabelFunctor
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd).map
      (FreeCorrespondenceFamilyGroupoid.u p) = _
  exact PresentedFamilyGroupoidOf.freeReverseRelabelFunctor_u
    (w.partialQuadrangleFamilyRelation hquad) Prod.snd p

/-- The ambient projection preserves the based difference product on the
joint `B/T` arrow chart. -/
theorem psiChunkAmbientFunctor_map_differenceProduct
    (e a b : ChunkParameter (K := K)) :
    w.psiChunkAmbientFunctor.map
        (groupoidDifferenceProduct (w.psiChunkBArrow e)
          (w.psiChunkBArrow a) (w.psiChunkBArrow b)) =
      groupoidDifferenceProduct (w.psiBArrow e.1)
        (w.psiBArrow a.1) (w.psiBArrow b.1) := by
  rw [map_groupoidDifferenceProduct]
  simp only [psiChunkAmbientFunctor_map_b]
  rfl

/-- The scalar projection reverses the order of the two variable inputs.
Equivalently, it sends a joint difference product to the inverse of the
oppositely ordered scalar difference product. -/
theorem psiChunkScalarReverseFunctor_map_differenceProduct
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (e a b : ChunkParameter (K := K)) :
    (w.psiChunkScalarReverseFunctor hquad).map
        (groupoidDifferenceProduct (w.psiChunkBArrow e)
          (w.psiChunkBArrow a) (w.psiChunkBArrow b)) =
      inv (groupoidDifferenceProduct
        (w.partialQuadrangleTArrow hquad e.2)
        (w.partialQuadrangleTArrow hquad b.2)
        (w.partialQuadrangleTArrow hquad a.2)) := by
  rw [map_groupoidDifferenceProduct]
  simp only [psiChunkScalarReverseFunctor_map_b]
  exact groupoidDifferenceProduct_inv
    (w.partialQuadrangleTArrow hquad e.2)
    (w.partialQuadrangleTArrow hquad a.2)
    (w.partialQuadrangleTArrow hquad b.2)

/-- The scalar projection induces a genuine homomorphism on the vertex
group at the source of the joint `B/T` arrow chart. -/
def psiChunkVertexHom
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :=
  (w.psiChunkScalarReverseFunctor hquad).mapVertexGroup
    (PresentedFamilyGroupoidOf.x1 w.psiChunkFamilyRelation)

/-- The categorical kernel of the joint-to-scalar chunk comparison. -/
def psiChunkKernel
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :=
  (w.psiChunkVertexHom hquad).ker

/-- The comparison kernel is normal for purely group-theoretic reasons:
it is the kernel of the induced vertex-group homomorphism. -/
instance psiChunkKernel_normal
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']) :
    (w.psiChunkKernel hquad).Normal :=
  MonoidHom.normal_ker (w.psiChunkVertexHom hquad)

/-- A joint based difference chart lies in the comparison kernel exactly
when its two scalar `T` arrows agree in the scalar presentation.  This
criterion deliberately asserts arrow equality, not injectivity of scalar
labels. -/
theorem groupoidDifferenceChart_mem_psiChunkKernel_iff
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    (e a : ChunkParameter (K := K)) :
    groupoidDifferenceChart (w.psiChunkBArrow e) (w.psiChunkBArrow a) ∈
        w.psiChunkKernel hquad ↔
      w.partialQuadrangleTArrow hquad a.2 =
        w.partialQuadrangleTArrow hquad e.2 := by
  change (w.psiChunkScalarReverseFunctor hquad).map
      (groupoidDifferenceChart (w.psiChunkBArrow e)
        (w.psiChunkBArrow a)) = 1 ↔ _
  rw [map_groupoidDifferenceChart]
  simp only [psiChunkScalarReverseFunctor_map_b]
  rw [groupoidDifferenceChart_eq_one_iff]
  exact IsIso.inv_eq_inv

/-- Four exact edges on the joint rank-two/scalar presentation.  Repeated
parameters are literal pairs, so the algebraic branch coordinate is shared
at every repeated vertex rather than chosen independently edge by edge. -/
structure PsiChunkFourArrowDifferenceDiagram
    (s a b e : ChunkParameter (K := K)) where
  /-- A joint output of `s · e`. -/
  u : ChunkParameter (K := K)
  /-- A joint left quotient solving `sA · a = u`. -/
  sA : ChunkParameter (K := K)
  /-- A joint output of `s · b`. -/
  uB : ChunkParameter (K := K)
  /-- The joint difference output solving `sA · c = uB`. -/
  c : ChunkParameter (K := K)
  /-- The edge `s · e = u`. -/
  se_u : w.psiChunkFamilyRelation s e u
  /-- The edge `sA · a = u`. -/
  sA_a_u : w.psiChunkFamilyRelation sA a u
  /-- The edge `s · b = uB`. -/
  s_b_uB : w.psiChunkFamilyRelation s b uB
  /-- The edge `sA · c = uB`. -/
  sA_c_uB : w.psiChunkFamilyRelation sA c uB

/-- The joint four-arrow diagram cancels exactly on its `B/T` chart. -/
theorem PsiChunkFourArrowDifferenceDiagram.cancellation
    {s a b e : ChunkParameter (K := K)}
    (D : w.PsiChunkFourArrowDifferenceDiagram s a b e) :
    w.psiChunkBArrow D.c =
      groupoidDifferenceProduct (w.psiChunkBArrow e)
        (w.psiChunkBArrow a) (w.psiChunkBArrow b) :=
  PresentedFamilyGroupoidOf.fourArrow_right_cancellation
    w.psiChunkFamilyRelation D.se_u D.sA_a_u D.s_b_uB D.sA_c_uB

/-- Forgetting scalar coordinates turns a joint four-arrow diagram into
the ambient rank-two `Psi` diagram. -/
def PsiChunkFourArrowDifferenceDiagram.ambientDiagram
    (hψ : w.Psi) {s a b e : ChunkParameter (K := K)}
    (D : w.PsiChunkFourArrowDifferenceDiagram s a b e) :
    w.PsiParameterFourArrowDifferenceDiagram hψ s.1 a.1 b.1 e.1 where
  u := D.u.1
  sA := D.sA.1
  uB := D.uB.1
  c := D.c.1
  se_u := by
    apply (w.psiFamilyCompositionRelation_iff_isRealization
      hψ s.1 e.1 D.u.1).1
    exact PsiChunkProjectionRelation.psiFamilyComposition w D.se_u
  sA_a_u := by
    apply (w.psiFamilyCompositionRelation_iff_isRealization
      hψ D.sA.1 a.1 D.u.1).1
    exact PsiChunkProjectionRelation.psiFamilyComposition w D.sA_a_u
  s_b_uB := by
    apply (w.psiFamilyCompositionRelation_iff_isRealization
      hψ s.1 b.1 D.uB.1).1
    exact PsiChunkProjectionRelation.psiFamilyComposition w D.s_b_uB
  sA_c_uB := by
    apply (w.psiFamilyCompositionRelation_iff_isRealization
      hψ D.sA.1 D.c.1 D.uB.1).1
    exact PsiChunkProjectionRelation.psiFamilyComposition w D.sA_c_uB

/-- Taking scalar coordinates turns the same joint four-arrow diagram into
the partial-quadrangle parameter diagram, with every repeated scalar branch
shared literally. -/
def PsiChunkFourArrowDifferenceDiagram.scalarDiagram
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    {s a b e : ChunkParameter (K := K)}
    (D : w.PsiChunkFourArrowDifferenceDiagram s a b e) :
    IsPartialQuadrangle.ParameterFourArrowDifferenceDiagram
      hquad s.2 a.2 b.2 e.2 where
  u := D.u.2
  sA := D.sA.2
  uB := D.uB.2
  c := D.c.2
  se_u := PsiChunkProjectionRelation.parameterMultiplication
    w D.se_u hquad
  sA_a_u := PsiChunkProjectionRelation.parameterMultiplication
    w D.sA_a_u hquad
  s_b_uB := PsiChunkProjectionRelation.parameterMultiplication
    w D.s_b_uB hquad
  sA_c_uB := PsiChunkProjectionRelation.parameterMultiplication
    w D.sA_c_uB hquad

/-- Ambient cancellation is the first-coordinate image of joint
cancellation. -/
theorem PsiChunkFourArrowDifferenceDiagram.ambient_cancellation
    (hψ : w.Psi) {s a b e : ChunkParameter (K := K)}
    (D : w.PsiChunkFourArrowDifferenceDiagram s a b e) :
    w.psiBArrow D.c.1 =
      groupoidDifferenceProduct (w.psiBArrow e.1)
        (w.psiBArrow a.1) (w.psiBArrow b.1) :=
  PsiParameterFourArrowDifferenceDiagram.cancellation w hψ
    (PsiChunkFourArrowDifferenceDiagram.ambientDiagram w hψ D)

/-- Scalar cancellation is the second-coordinate image of the same joint
diagram.  The two variable inputs occur in the opposite order, exactly as
predicted by `psiChunkScalarReverseFunctor`. -/
theorem PsiChunkFourArrowDifferenceDiagram.scalar_cancellation
    {S' T' U' : Point k K}
    (hquad : IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'])
    {s a b e : ChunkParameter (K := K)}
    (D : w.PsiChunkFourArrowDifferenceDiagram s a b e) :
    IsPartialQuadrangle.parameterTArrow hquad D.c.2 =
      groupoidDifferenceProduct
        (IsPartialQuadrangle.parameterTArrow hquad e.2)
        (IsPartialQuadrangle.parameterTArrow hquad b.2)
        (IsPartialQuadrangle.parameterTArrow hquad a.2) :=
  (PsiChunkFourArrowDifferenceDiagram.scalarDiagram w hquad D).cancellation hquad

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
