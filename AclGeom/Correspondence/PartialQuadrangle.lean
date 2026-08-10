/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Config.Language
import AclGeom.Correspondence.FiniteCover

/-!
# The correspondence groupoid carried by a partial quadrangle

For a partial quadrangle `(S,T,U,S',T',U')`, the four dependent triples
give the three finite-correspondence arrows

* `T : S' → U'`,
* `S : U' → T'`, and
* `U : S' → T'`.

They are constructed over the shared coefficient field `k(S,T,U)`.  The
free triples make their sources generic over that field, while the named
dependent triples make each endpoint pair interalgebraic.  Their literal
representatives share `U'`, so the selected component satisfies
`S ∘ T = U`.

This is the field-theoretic three-object groupoid in blueprint (8.4).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Representatives of two distinct geometric points are algebraically
independent. -/
theorem algebraicIndependent_rep_pair_of_ne
    {P Q : Point k K} (hPQ : P ≠ Q) :
    AlgebraicIndependent k ![P.rep, Q.rep] := by
  have hP : P.rep ∉ racl k ({Q.rep} : Set K) := by
    intro hmem
    have hle : P.1 ≤ Q.1 := by
      rw [← P.point_rep, ← Q.point_rep]
      exact ClosedIF.point_le_iff.2 hmem
    have heq : P.1 = Q.1 := (Q.2.le_iff_eq P.2.1).1 hle
    exact hPQ (Subtype.ext heq)
  have hQ : Q.rep ∉ racl k ({P.rep} : Set K) := by
    intro hmem
    have hle : Q.1 ≤ P.1 := by
      rw [← Q.point_rep, ← P.point_rep]
      exact ClosedIF.point_le_iff.2 hmem
    have heq : Q.1 = P.1 := (P.2.le_iff_eq Q.2.1).1 hle
    exact hPQ (Subtype.ext heq.symm)
  exact algebraicIndependent_pair hP hQ

/-- Two distinct points span a rank-two flat. -/
theorem rankEq_two_sup_of_ne {P Q : Point k K} (hPQ : P ≠ Q) :
    RankEq 2 (P.1 ⊔ Q.1) := by
  refine ⟨![P, Q], ?_, ?_⟩
  · unfold PointIndep
    rw [Fin.forall_fin_two]
    constructor
    · have himage :
        (![P, Q] '' {j | j ≠ (0 : Fin 2)}) = ({Q} : Set (Point k K)) := by
        ext X
        constructor
        · rintro ⟨j, hj, rfl⟩
          fin_cases j <;> simp_all
        · rintro (rfl : X = Q)
          exact ⟨1, by simp, rfl⟩
      rw [himage]
      intro hmem
      rw [mem_pointCl_iff_rep_mem] at hmem
      have hmem' : P.rep ∈ racl k ({Q.rep} : Set K) := by
        simpa using hmem
      have hle : P.1 ≤ Q.1 := by
        rw [← P.point_rep, ← Q.point_rep]
        exact ClosedIF.point_le_iff.2 hmem'
      exact hPQ (Subtype.ext ((Q.2.le_iff_eq P.2.1).1 hle))
    · have himage :
          (![P, Q] '' {j | j ≠ (1 : Fin 2)}) = ({P} : Set (Point k K)) := by
        ext X
        constructor
        · rintro ⟨j, hj, rfl⟩
          fin_cases j <;> simp_all
        · rintro (rfl : X = P)
          exact ⟨0, by simp, rfl⟩
      rw [himage]
      intro hmem
      rw [mem_pointCl_iff_rep_mem] at hmem
      have hmem' : Q.rep ∈ racl k ({P.rep} : Set K) := by
        simpa using hmem
      have hle : Q.1 ≤ P.1 := by
        rw [← Q.point_rep, ← P.point_rep]
        exact ClosedIF.point_le_iff.2 hmem'
      exact hPQ (Subtype.ext ((P.2.le_iff_eq Q.2.1).1 hle).symm)
  · rw [sup_eq_iSup_two]
    exact iSup_congr fun i ↦ by fin_cases i <;> rfl

/-- A ternary supremum as an indexed supremum over `Fin 3`. -/
theorem sup_eq_iSup_three {α : Type*} [CompleteLattice α] (a b c : α) :
    a ⊔ (b ⊔ c) = ⨆ i, (![a, b, c] : Fin 3 → α) i := by
  refine le_antisymm (sup_le ?_ (sup_le ?_ ?_)) (iSup_le fun i ↦ ?_)
  · exact le_iSup_of_le 0 (by simp)
  · exact le_iSup_of_le 1 (by simp)
  · exact le_iSup_of_le 2 (by simp)
  · fin_cases i
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right le_sup_right

/-- In a dependent rank-two triple, the closure of either distinct pair
is the closure of the whole triple. -/
theorem pair_sup_eq_triple_of_rankEq_two
    {P Q R : Point k K} (hPQ : P ≠ Q)
    (h : RankEq 2 (P.1 ⊔ (Q.1 ⊔ R.1))) :
    P.1 ⊔ Q.1 = P.1 ⊔ (Q.1 ⊔ R.1) := by
  apply RankEq.eq_of_le _ (rankEq_two_sup_of_ne hPQ) h
  exact sup_le le_sup_left (le_sup_of_le_right le_sup_left)

/-- The third representative in a dependent rank-two triple is algebraic
over either distinct pair. -/
theorem third_rep_mem_racl_pair_of_rankEq_two
    {P Q R : Point k K} (hPQ : P ≠ Q)
    (h : RankEq 2 (P.1 ⊔ (Q.1 ⊔ R.1))) :
    R.rep ∈ racl k ({P.rep, Q.rep} : Set K) := by
  have heq := pair_sup_eq_triple_of_rankEq_two hPQ h
  have hle : R.1 ≤ P.1 ⊔ Q.1 := by
    rw [heq]
    exact le_sup_of_le_right le_sup_right
  have hmem : R.rep ∈ (P.1 ⊔ Q.1).1 := hle R.mem_rep
  rw [← P.point_rep, ← Q.point_rep, coe_sup_point₂] at hmem
  exact hmem

/-- A rank-three triple has algebraically independent chosen
representatives. -/
theorem algebraicIndependent_rep_triple_of_rankEq_three
    {P Q R : Point k K}
    (h : RankEq 3 (P.1 ⊔ (Q.1 ⊔ R.1))) :
    AlgebraicIndependent k ![P.rep, Q.rep, R.rep] := by
  apply algebraicIndependent_of_rankEq_iSup_point
  apply h.congr
  rw [← P.point_rep, ← Q.point_rep, ← R.point_rep,
    sup_eq_iSup_three]
  exact iSup_congr fun i ↦ by fin_cases i <;> rfl

/-- If `(P,Q,R)` is dependent of rank two but `(P,Q,X)` is free of rank
three, then `X` stays generic after adjoining all three dependent
parameters. -/
theorem rep_notMem_racl_dependent_triple
    {P Q R X : Point k K} (hPQ : P ≠ Q)
    (hdep : RankEq 2 (P.1 ⊔ (Q.1 ⊔ R.1)))
    (hfree : RankEq 3 (P.1 ⊔ (Q.1 ⊔ X.1))) :
    X.rep ∉ racl k ({P.rep, Q.rep, R.rep} : Set K) := by
  have hfreeAI := algebraicIndependent_rep_triple_of_rankEq_three hfree
  have hnot := AlgebraicIndependent.notMem_racl_image hfreeAI
    (S := ({0, 1} : Set (Fin 3))) (i := 2) (by decide)
  have hnotPair : X.rep ∉ racl k ({P.rep, Q.rep} : Set K) := by
    simpa [Set.image_insert_eq] using hnot
  intro hx
  have htriple : X.rep ∈ (P.1 ⊔ (Q.1 ⊔ R.1)).1 := by
    rw [← P.point_rep, ← Q.point_rep, ← R.point_rep,
      coe_sup_point₃]
    exact hx
  have heq := pair_sup_eq_triple_of_rankEq_two hPQ hdep
  have hpair : X.rep ∈ (P.1 ⊔ Q.1).1 := by
    rw [heq]
    exact htriple
  rw [← P.point_rep, ← Q.point_rep, coe_sup_point₂] at hpair
  exact hnotPair hpair

namespace IsPartialQuadrangle

variable {f : Fin 6 → Point k K}

/-- The shared coefficient field generated by the three parameter points
`S,T,U`. -/
def parameterField (f : Fin 6 → Point k K) : IntermediateField k K :=
  adjoin k { (f 0).rep, (f 1).rep, (f 2).rep }

/-- The free triple `(S,T,S')`. -/
theorem rank_STS' (h : IsPartialQuadrangle f) :
    RankEq 3 ((f 0).1 ⊔ ((f 1).1 ⊔ (f 3).1)) := by
  have hr := IsPartialQuadrangle.rank_free h {0, 1, 3} (by decide) (by decide)
  simpa [Finset.sup_insert] using hr

/-- The free triple `(S,T,U')`. -/
theorem rank_STU'_free (h : IsPartialQuadrangle f) :
    RankEq 3 ((f 0).1 ⊔ ((f 1).1 ⊔ (f 5).1)) := by
  have hr := IsPartialQuadrangle.rank_free h {0, 1, 5} (by decide) (by decide)
  simpa [Finset.sup_insert] using hr

/-- The object `S'` is generic over the shared parameter field. -/
theorem S'_rep_generic_over_parameters (h : IsPartialQuadrangle f) :
    (f 3).rep ∉ racl k
      ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K) :=
  rep_notMem_racl_dependent_triple
    (P := f 0) (Q := f 1) (R := f 2) (X := f 3)
    ((IsPartialQuadrangle.injective h).ne (by decide))
    (IsPartialQuadrangle.rank_STU h) (rank_STS' h)

/-- The object `U'` is generic over the shared parameter field. -/
theorem U'_rep_generic_over_parameters (h : IsPartialQuadrangle f) :
    (f 5).rep ∉ racl k
      ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K) :=
  rep_notMem_racl_dependent_triple
    (P := f 0) (Q := f 1) (R := f 2) (X := f 5)
    ((IsPartialQuadrangle.injective h).ne (by decide))
    (IsPartialQuadrangle.rank_STU h) (rank_STU'_free h)

/-- The selected `T`-family arrow `S' → U'`. -/
def tPair (h : IsPartialQuadrangle f) :
    FiniteCorrespondencePair (↥(parameterField f)) K where
  source := (f 3).rep
  target := (f 5).rep
  source_generic := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact S'_rep_generic_over_parameters h
  target_mem_source := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 1).rep, (f 3).rep})
      (T := {(f 3).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 1) (Q := f 3) (R := f 5)
      ((IsPartialQuadrangle.injective h).ne (by decide))
      (IsPartialQuadrangle.rank_S'TU' h)
  source_mem_target := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 1).rep, (f 5).rep})
      (T := {(f 5).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 1) (Q := f 5) (R := f 3)
      ((IsPartialQuadrangle.injective h).ne (by decide)) (by
        simpa [sup_comm (f 3).1 (f 5).1, sup_left_comm]
          using IsPartialQuadrangle.rank_S'TU' h)

/-- The selected `S`-family arrow `U' → T'`. -/
def sPair (h : IsPartialQuadrangle f) :
    FiniteCorrespondencePair (↥(parameterField f)) K where
  source := (f 5).rep
  target := (f 4).rep
  source_generic := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact U'_rep_generic_over_parameters h
  target_mem_source := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 0).rep, (f 5).rep})
      (T := {(f 5).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 0) (Q := f 5) (R := f 4)
      ((IsPartialQuadrangle.injective h).ne (by decide)) (by
        simpa [sup_comm (f 4).1 (f 5).1]
          using IsPartialQuadrangle.rank_STU' h)
  source_mem_target := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 0).rep, (f 4).rep})
      (T := {(f 4).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 0) (Q := f 4) (R := f 5)
      ((IsPartialQuadrangle.injective h).ne (by decide)) (by
        simpa [sup_comm (f 4).1 (f 5).1, sup_left_comm]
          using IsPartialQuadrangle.rank_STU' h)

/-- The selected `U`-family endpoint arrow `S' → T'`. -/
def uPair (h : IsPartialQuadrangle f) :
    FiniteCorrespondencePair (↥(parameterField f)) K where
  source := (f 3).rep
  target := (f 4).rep
  source_generic := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact S'_rep_generic_over_parameters h
  target_mem_source := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 2).rep, (f 3).rep})
      (T := {(f 3).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 2) (Q := f 3) (R := f 4)
      ((IsPartialQuadrangle.injective h).ne (by decide)) (by
        simpa [sup_comm (f 2).1 (f 3).1, sup_left_comm]
          using IsPartialQuadrangle.rank_S'T'U h)
  source_mem_target := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    apply racl_mono (k := k)
      (S := {(f 2).rep, (f 4).rep})
      (T := {(f 4).rep, (f 0).rep, (f 1).rep, (f 2).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      (P := f 2) (Q := f 4) (R := f 3)
      ((IsPartialQuadrangle.injective h).ne (by decide)) (by
        simpa only [sup_comm (f 3).1 (f 4).1]
          using IsPartialQuadrangle.rank_S'T'U h)

@[simp] theorem tPair_source (h : IsPartialQuadrangle f) :
    (tPair h).source = (f 3).rep := rfl

@[simp] theorem tPair_target (h : IsPartialQuadrangle f) :
    (tPair h).target = (f 5).rep := rfl

@[simp] theorem sPair_source (h : IsPartialQuadrangle f) :
    (sPair h).source = (f 5).rep := rfl

@[simp] theorem sPair_target (h : IsPartialQuadrangle f) :
    (sPair h).target = (f 4).rep := rfl

@[simp] theorem uPair_source (h : IsPartialQuadrangle f) :
    (uPair h).source = (f 3).rep := rfl

@[simp] theorem uPair_target (h : IsPartialQuadrangle f) :
    (uPair h).target = (f 4).rep := rfl

/-- The selected three-object groupoid composition identity
`S ∘ T = U`. -/
theorem selected_correspondence_composes (h : IsPartialQuadrangle f) :
    FiniteCorrespondenceGerm.Composes
      (FiniteCorrespondenceGerm.ofPair (tPair h))
      (FiniteCorrespondenceGerm.ofPair (sPair h))
      (FiniteCorrespondenceGerm.ofPair (uPair h)) := by
  refine ⟨tPair h, sPair h, rfl, rfl, rfl, ?_⟩
  rfl

end IsPartialQuadrangle

end
end AclGeom
