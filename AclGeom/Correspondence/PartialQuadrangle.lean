/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Config.Language
import AclGeom.Correspondence.BranchGroupoid
import AclGeom.Correspondence.Family

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

/-- A point representative is generic over the representative of any
distinct point. -/
theorem point_rep_notMem_racl_rep_of_ne
    {P Q : Point k K} (hPQ : P ≠ Q) :
    P.rep ∉ racl k ({Q.rep} : Set K) := by
  intro hmem
  have hle : P.1 ≤ Q.1 := by
    rw [← P.point_rep, ← Q.point_rep]
    exact ClosedIF.point_le_iff.2 hmem
  have heq : P.1 = Q.1 := (Q.2.le_iff_eq P.2.1).1 hle
  exact hPQ (Subtype.ext heq)

/-- The one-tuple consisting of a point representative is algebraically
independent over the ground field. -/
theorem point_rep_singleton_independent (P : Point k K) :
    AlgebraicIndependent k ![P.rep] := by
  rw [algebraicIndependent_unique_type_iff]
  intro halg
  exact P.rep_notMem_bot (ClosedIF.mem_bot_iff.2 halg)

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

/-- The three free coordinates `(S,T,S')` chosen in the group-
configuration proof. -/
def groupReps (f : Fin 6 → Point k K) : Fin 3 → K :=
  ![(f 0).rep, (f 1).rep, (f 3).rep]

/-- The positions of `(S,T,S')` inside the displayed six-coordinate
partial quadrangle. -/
def groupCoordinateIndex : Fin 3 → Fin 6 := ![0, 1, 3]

/-- The positions `(T,S',U')` of the `T`-family member. -/
def tFamilyIndex : Fin 3 → Fin 6 := ![1, 3, 5]

/-- The positions `(S,U',T')` of the `S`-family member. -/
def sFamilyIndex : Fin 3 → Fin 6 := ![0, 5, 4]

/-- The positions `(U,S',T')` of the endpoint `U`-family member. -/
def uFamilyIndex : Fin 3 → Fin 6 := ![2, 3, 4]

/-- The common parameter coordinates inside a six-tuple. -/
def parameterIndices : Set (Fin 6) := {0, 1, 2}

/-- Common parameters together with coordinate `S'`. -/
def parameterSource3Indices : Set (Fin 6) := {0, 1, 2, 3}

/-- Common parameters together with coordinate `T'`. -/
def parameterSource4Indices : Set (Fin 6) := {0, 1, 2, 4}

/-- Common parameters together with coordinate `U'`. -/
def parameterSource5Indices : Set (Fin 6) := {0, 1, 2, 5}

omit [Field K] in
/-- Image of the three common parameter positions. -/
theorem image_parameterIndices (v : Fin 6 → K) :
    v '' parameterIndices = ({v 0, v 1, v 2} : Set K) := by
  ext z
  simp [parameterIndices]
  tauto

omit [Field K] in
/-- Image of the common parameters and position `3`. -/
theorem image_parameterSource3Indices (v : Fin 6 → K) :
    v '' parameterSource3Indices = ({v 0, v 1, v 2, v 3} : Set K) := by
  ext z
  simp [parameterSource3Indices]
  tauto

omit [Field K] in
/-- Image of the common parameters and position `4`. -/
theorem image_parameterSource4Indices (v : Fin 6 → K) :
    v '' parameterSource4Indices = ({v 0, v 1, v 2, v 4} : Set K) := by
  ext z
  simp [parameterSource4Indices]
  tauto

omit [Field K] in
/-- Image of the common parameters and position `5`. -/
theorem image_parameterSource5Indices (v : Fin 6 → K) :
    v '' parameterSource5Indices = ({v 0, v 1, v 2, v 5} : Set K) := by
  ext z
  simp [parameterSource5Indices]
  tauto

/-- The six displayed representatives of the partial quadrangle. -/
def configurationReps (f : Fin 6 → Point k K) : Fin 6 → K :=
  fun i ↦ (f i).rep

/-- The free group coordinates are algebraically independent. -/
theorem groupReps_independent (h : IsPartialQuadrangle f) :
    AlgebraicIndependent k (groupReps f) :=
  algebraicIndependent_rep_triple_of_rankEq_three (rank_STS' h)

/-- The range of the three chosen free representatives. -/
theorem groupReps_range :
    Set.range (groupReps f) =
      ({(f 0).rep, (f 1).rep, (f 3).rep} : Set K) := by
  ext x
  simp [groupReps, Matrix.range_cons, Matrix.range_empty]
  tauto

/-- Every representative in the partial quadrangle is algebraic over the
free triple `(S,T,S')`. -/
theorem configurationReps_mem_racl_groupReps
    (h : IsPartialQuadrangle f) (i : Fin 6) :
    configurationReps f i ∈ racl k (Set.range (groupReps f)) := by
  rw [groupReps_range]
  fin_cases i
  · exact subset_racl k _ (by simp [configurationReps])
  · exact subset_racl k _ (by simp [configurationReps])
  · apply racl_mono (k := k)
      (S := {(f 0).rep, (f 1).rep})
      (T := {(f 0).rep, (f 1).rep, (f 3).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      ((IsPartialQuadrangle.injective h).ne (by decide))
      (IsPartialQuadrangle.rank_STU h)
  · exact subset_racl k _ (by simp [configurationReps])
  · have hmem : (f 4).rep ∈ racl k ({(f 2).rep, (f 3).rep} : Set K) :=
      third_rep_mem_racl_pair_of_rankEq_two
        ((IsPartialQuadrangle.injective h).ne (by decide))
        (IsPartialQuadrangle.rank_S'T'U h)
    apply racl_le_of_subset_racl (k := k) _ hmem
    rintro x (rfl | rfl)
    · apply racl_mono (k := k)
        (S := {(f 0).rep, (f 1).rep})
        (T := {(f 0).rep, (f 1).rep, (f 3).rep})
        (by rintro y (rfl | rfl) <;> simp)
      exact third_rep_mem_racl_pair_of_rankEq_two
        ((IsPartialQuadrangle.injective h).ne (by decide))
        (IsPartialQuadrangle.rank_STU h)
    · exact subset_racl k _ (by simp)
  · apply racl_mono (k := k)
      (S := {(f 1).rep, (f 3).rep})
      (T := {(f 0).rep, (f 1).rep, (f 3).rep})
      (by rintro x (rfl | rfl) <;> simp)
    exact third_rep_mem_racl_pair_of_rankEq_two
      ((IsPartialQuadrangle.injective h).ne (by decide))
      (IsPartialQuadrangle.rank_S'TU' h)

/-- Restricting the six-coordinate tuple to `groupCoordinateIndex`
recovers the independent tuple `(S,T,S')`. -/
theorem configurationReps_comp_groupCoordinateIndex :
    configurationReps f ∘ groupCoordinateIndex = groupReps f := by
  funext i
  fin_cases i <;> rfl

/-- The complete partial-quadrangle locus can be relocated while fixing an
arbitrary independent replacement for `(S,T,S')`.  All six coordinates
move simultaneously, so every dependent triple and all three selected
family branches remain compatible. -/
theorem exists_configuration_relocation [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {g : Fin 3 → K}
    (hg : AlgebraicIndependent k g) :
    ∃ v : Fin 6 → K,
      idealOf k v = idealOf k (configurationReps f) ∧
        v ∘ groupCoordinateIndex = g := by
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    (groupReps_independent h) hg
    (u := configurationReps f) (e := groupCoordinateIndex)
    (fun i ↦ congrFun configurationReps_comp_groupCoordinateIndex i)
    (configurationReps_mem_racl_groupReps h)
  exact ⟨v, hv, funext hfix⟩

/-- The parameter `T` is recoverable up to finitely many choices from
the endpoints of its selected `S' → U'` branch. -/
theorem T_rep_mem_racl_endpoints (h : IsPartialQuadrangle f) :
    (f 1).rep ∈ racl k ({(f 3).rep, (f 5).rep} : Set K) :=
  third_rep_mem_racl_pair_of_rankEq_two
    (P := f 3) (Q := f 5) (R := f 1)
    ((IsPartialQuadrangle.injective h).ne (by decide)) (by
      simpa [sup_assoc, sup_comm, sup_left_comm]
        using IsPartialQuadrangle.rank_S'TU' h)

/-- The parameter `S` is recoverable up to finitely many choices from
the endpoints of its selected `U' → T'` branch. -/
theorem S_rep_mem_racl_endpoints (h : IsPartialQuadrangle f) :
    (f 0).rep ∈ racl k ({(f 5).rep, (f 4).rep} : Set K) :=
  third_rep_mem_racl_pair_of_rankEq_two
    (P := f 5) (Q := f 4) (R := f 0)
    ((IsPartialQuadrangle.injective h).ne (by decide)) (by
      simpa [sup_assoc, sup_comm, sup_left_comm]
        using IsPartialQuadrangle.rank_STU' h)

/-- The parameter `U` is recoverable up to finitely many choices from
the endpoints of its selected `S' → T'` branch. -/
theorem U_rep_mem_racl_endpoints (h : IsPartialQuadrangle f) :
    (f 2).rep ∈ racl k ({(f 3).rep, (f 4).rep} : Set K) :=
  third_rep_mem_racl_pair_of_rankEq_two
    (P := f 3) (Q := f 4) (R := f 2)
    ((IsPartialQuadrangle.injective h).ne (by decide)) (by
      simpa [sup_assoc, sup_comm, sup_left_comm]
        using IsPartialQuadrangle.rank_S'T'U h)

/-- The field generated by the independent coordinates `(S,T,S')`. -/
def groupCoordinateField (f : Fin 6 → Point k K) : IntermediateField k K :=
  adjoin k (Set.range (groupReps f))

/-- The field generated by all six partial-quadrangle representatives. -/
def configurationField (f : Fin 6 → Point k K) : IntermediateField k K :=
  adjoin k (Set.range (configurationReps f))

/-- The free coordinate field embeds in the full configuration field. -/
theorem groupCoordinateField_le_configurationField :
    groupCoordinateField f ≤ configurationField f := by
  apply adjoin.mono
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

/-- The full six-coordinate field regarded as an extension of the free
three-coordinate field. -/
def configurationOverGroupCoordinates (f : Fin 6 → Point k K) :
    IntermediateField (↥(groupCoordinateField f)) K :=
  extendScalars groupCoordinateField_le_configurationField

/-- The six-coordinate partial-quadrangle field is a finite extension of
the field generated by `(S,T,S')`. -/
theorem configurationOverGroupCoordinates_finiteDimensional
    (h : IsPartialQuadrangle f) :
    FiniteDimensional (↥(groupCoordinateField f))
      (↥(configurationOverGroupCoordinates f)) := by
  have key : configurationOverGroupCoordinates f =
      adjoin (↥(groupCoordinateField f))
        (Set.range (configurationReps f)) := by
    refine restrictScalars_injective k ?_
    unfold configurationOverGroupCoordinates groupCoordinateField
      configurationField
    rw [adjoin_adjoin_left, extendScalars_restrictScalars, adjoin_union]
    exact (sup_eq_right.2 groupCoordinateField_le_configurationField).symm
  rw [key]
  letI : Fintype (Set.range (configurationReps f)) :=
    Set.Finite.fintype (Set.finite_range (configurationReps f))
  exact finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨i, rfl⟩ := hx
    rw [groupCoordinateField]
    exact ((mem_racl_iff k).1
      (configurationReps_mem_racl_groupReps h i)).isIntegral

/-- The normal closure of the full partial-quadrangle coordinate field
over the independent three-coordinate field. -/
def configurationNormalOverGroupCoordinates (f : Fin 6 → Point k K) :
    IntermediateField (↥(groupCoordinateField f)) K :=
  FiniteCover.normalClosureOver groupCoordinateField_le_configurationField

/-- The original six-coordinate extension embeds in its normal closure. -/
theorem configurationOverGroupCoordinates_le_normal :
    configurationOverGroupCoordinates f ≤
      configurationNormalOverGroupCoordinates f :=
  FiniteCover.extendScalars_le_normalClosureOver
    groupCoordinateField_le_configurationField

/-- The full configuration normal cover remains finite over the
independent coordinates `(S,T,S')`. -/
theorem configurationNormalOverGroupCoordinates_finiteDimensional
    (h : IsPartialQuadrangle f) :
    FiniteDimensional (↥(groupCoordinateField f))
      (↥(configurationNormalOverGroupCoordinates f)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    groupCoordinateField_le_configurationField
    (configurationOverGroupCoordinates_finiteDimensional h)

/-- Inside an algebraically closed ambient field, the full configuration
cover is normal over the independent coordinates `(S,T,S')`. -/
theorem configurationNormalOverGroupCoordinates_normal [IsAlgClosed K]
    (h : IsPartialQuadrangle f) :
    Normal (↥(groupCoordinateField f))
      (↥(configurationNormalOverGroupCoordinates f)) := by
  letI := configurationOverGroupCoordinates_finiteDimensional h
  exact FiniteCover.normalClosureOver_normal
    groupCoordinateField_le_configurationField
    (Algebra.IsAlgebraic.of_finite (↥(groupCoordinateField f))
      (↥(configurationOverGroupCoordinates f)))

/-- The varying one-parameter `T`-family member `S' → U'`. -/
def tFamilyMember (h : IsPartialQuadrangle f) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 1 where
  parameter := ![(f 1).rep]
  source := (f 3).rep
  target := (f 5).rep
  parameter_independent := point_rep_singleton_independent (f 1)
  source_generic := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      point_rep_notMem_racl_rep_of_ne
        ((IsPartialQuadrangle.injective h).ne (by decide) : f 3 ≠ f 1)
  target_mem_parameter_source := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 1) (Q := f 3) (R := f 5)
        ((IsPartialQuadrangle.injective h).ne (by decide))
        (IsPartialQuadrangle.rank_S'TU' h)
  source_mem_parameter_target := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 1) (Q := f 5) (R := f 3)
        ((IsPartialQuadrangle.injective h).ne (by decide)) (by
          simpa [sup_comm (f 3).1 (f 5).1, sup_left_comm]
            using IsPartialQuadrangle.rank_S'TU' h)

/-- The varying one-parameter `S`-family member `U' → T'`. -/
def sFamilyMember (h : IsPartialQuadrangle f) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 1 where
  parameter := ![(f 0).rep]
  source := (f 5).rep
  target := (f 4).rep
  parameter_independent := point_rep_singleton_independent (f 0)
  source_generic := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      point_rep_notMem_racl_rep_of_ne
        ((IsPartialQuadrangle.injective h).ne (by decide) : f 5 ≠ f 0)
  target_mem_parameter_source := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 0) (Q := f 5) (R := f 4)
        ((IsPartialQuadrangle.injective h).ne (by decide)) (by
          simpa [sup_comm (f 4).1 (f 5).1]
            using IsPartialQuadrangle.rank_STU' h)
  source_mem_parameter_target := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 0) (Q := f 4) (R := f 5)
        ((IsPartialQuadrangle.injective h).ne (by decide)) (by
          simpa [sup_comm (f 4).1 (f 5).1, sup_left_comm]
            using IsPartialQuadrangle.rank_STU' h)

/-- The varying one-parameter `U`-family endpoint member `S' → T'`. -/
def uFamilyMember (h : IsPartialQuadrangle f) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := K) 1 where
  parameter := ![(f 2).rep]
  source := (f 3).rep
  target := (f 4).rep
  parameter_independent := point_rep_singleton_independent (f 2)
  source_generic := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      point_rep_notMem_racl_rep_of_ne
        ((IsPartialQuadrangle.injective h).ne (by decide) : f 3 ≠ f 2)
  target_mem_parameter_source := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 2) (Q := f 3) (R := f 4)
        ((IsPartialQuadrangle.injective h).ne (by decide)) (by
          simpa [sup_comm (f 2).1 (f 3).1, sup_left_comm]
            using IsPartialQuadrangle.rank_S'T'U h)
  source_mem_parameter_target := by
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using
      third_rep_mem_racl_pair_of_rankEq_two
        (P := f 2) (Q := f 4) (R := f 3)
        ((IsPartialQuadrangle.injective h).ne (by decide)) (by
          simpa only [sup_comm (f 3).1 (f 4).1]
            using IsPartialQuadrangle.rank_S'T'U h)

/-- The `T`-family tuple is the corresponding projection of the complete
partial-quadrangle tuple. -/
theorem configurationReps_comp_tFamilyIndex (h : IsPartialQuadrangle f) :
    configurationReps f ∘ tFamilyIndex = (tFamilyMember h).tuple := by
  funext i
  fin_cases i <;> rfl

/-- The `S`-family tuple is the corresponding projection of the complete
partial-quadrangle tuple. -/
theorem configurationReps_comp_sFamilyIndex (h : IsPartialQuadrangle f) :
    configurationReps f ∘ sFamilyIndex = (sFamilyMember h).tuple := by
  funext i
  fin_cases i <;> rfl

/-- The endpoint `U`-family tuple is the corresponding projection of the
complete partial-quadrangle tuple. -/
theorem configurationReps_comp_uFamilyIndex (h : IsPartialQuadrangle f) :
    configurationReps f ∘ uFamilyIndex = (uFamilyMember h).tuple := by
  funext i
  fin_cases i <;> rfl

/-- **Simultaneous compatible family relocation.**  After installing any
independent replacement for `(S,T,S')`, a single relocated six-tuple
simultaneously realizes the original `T`, `S`, and `U` family ideals.  The
three projected tuples share the same relocated `S'`, `U'`, and `T'`
coordinates, so their selected composition remains literal. -/
theorem exists_compatible_family_relocation [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {g : Fin 3 → K}
    (hg : AlgebraicIndependent k g) :
    ∃ v : Fin 6 → K,
      idealOf k v = idealOf k (configurationReps f) ∧
        v ∘ groupCoordinateIndex = g ∧
        idealOf k (v ∘ tFamilyIndex) = (tFamilyMember h).ideal ∧
        idealOf k (v ∘ sFamilyIndex) = (sFamilyMember h).ideal ∧
        idealOf k (v ∘ uFamilyIndex) = (uFamilyMember h).ideal := by
  obtain ⟨v, hv, hfix⟩ := exists_configuration_relocation h hg
  have ht := idealOf_comp_eq_of_idealOf_eq hv tFamilyIndex
  have hs := idealOf_comp_eq_of_idealOf_eq hv sFamilyIndex
  have hu := idealOf_comp_eq_of_idealOf_eq hv uFamilyIndex
  rw [configurationReps_comp_tFamilyIndex h] at ht
  rw [configurationReps_comp_sFamilyIndex h] at hs
  rw [configurationReps_comp_uFamilyIndex h] at hu
  exact ⟨v, hv, hfix, ht, hs, hu⟩

/-- Every independent parameter/source pair carries a member of the same
`T`-family locus as the selected `(T,S',U')` tuple. -/
theorem tFamily_exists_relocation [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {t : Fin 1 → K} {s' : K}
    (hts : AlgebraicIndependent k (Fin.snoc t s')) :
    ∃ u' : K,
      idealOf k (Fin.snoc (Fin.snoc t s') u') =
        (tFamilyMember h).ideal :=
  (tFamilyMember h).exists_relocation hts

/-- Every independent parameter/source pair carries a member of the same
`S`-family locus as the selected `(S,U',T')` tuple. -/
theorem sFamily_exists_relocation [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {s : Fin 1 → K} {u' : K}
    (hsu : AlgebraicIndependent k (Fin.snoc s u')) :
    ∃ t' : K,
      idealOf k (Fin.snoc (Fin.snoc s u') t') =
        (sFamilyMember h).ideal :=
  (sFamilyMember h).exists_relocation hsu

/-- Every independent parameter/source pair carries a member of the same
endpoint `U`-family locus as the selected `(U,S',T')` tuple. -/
theorem uFamily_exists_relocation [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {u : Fin 1 → K} {s' : K}
    (hus : AlgebraicIndependent k (Fin.snoc u s')) :
    ∃ t' : K,
      idealOf k (Fin.snoc (Fin.snoc u s') t') =
        (uFamilyMember h).ideal :=
  (uFamilyMember h).exists_relocation hus

/-- The individual `T` parameter field embeds in the common
`k(S,T,U)` coefficient field of the selected groupoid. -/
theorem tFamilyParameterField_le_parameterField
    (h : IsPartialQuadrangle f) :
    (tFamilyMember h).parameterField ≤ parameterField f := by
  unfold FiniteCorrespondenceFamilyMember.parameterField tFamilyMember
    parameterField
  apply adjoin.mono
  intro x hx
  have hx' : x = (f 1).rep := by
    simpa [Matrix.range_cons, Matrix.range_empty] using hx
  simp [hx']

/-- The individual `S` parameter field embeds in the common
`k(S,T,U)` coefficient field. -/
theorem sFamilyParameterField_le_parameterField
    (h : IsPartialQuadrangle f) :
    (sFamilyMember h).parameterField ≤ parameterField f := by
  unfold FiniteCorrespondenceFamilyMember.parameterField sFamilyMember
    parameterField
  apply adjoin.mono
  intro x hx
  have hx' : x = (f 0).rep := by
    simpa [Matrix.range_cons, Matrix.range_empty] using hx
  simp [hx']

/-- The individual `U` parameter field embeds in the common
`k(S,T,U)` coefficient field. -/
theorem uFamilyParameterField_le_parameterField
    (h : IsPartialQuadrangle f) :
    (uFamilyMember h).parameterField ≤ parameterField f := by
  unfold FiniteCorrespondenceFamilyMember.parameterField uFamilyMember
    parameterField
  apply adjoin.mono
  intro x hx
  have hx' : x = (f 2).rep := by
    simpa [Matrix.range_cons, Matrix.range_empty] using hx
  simp [hx']

/-- The common coefficient field generated by the first three coordinates
of a relocated six-tuple. -/
def tupleParameterField (v : Fin 6 → K) : IntermediateField k K :=
  adjoin k ({v 0, v 1, v 2} : Set K)

/-- The first five coordinates of a relocated quadrangle: the common
parameters together with the source and target of the composite branch. -/
def compositeBranchIndex : Fin 5 → Fin 6 :=
  fun i ↦ i.castSucc

@[simp] theorem compositeBranchIndex_apply (i : Fin 5) :
    compositeBranchIndex i = i.castSucc := rfl

/-- The field generated by the common parameters and the two endpoints of
the selected composite correspondence. -/
def tupleCompositeField (v : Fin 6 → K) : IntermediateField k K :=
  adjoin k (Set.range (v ∘ compositeBranchIndex))

/-- The function field generated by all six coordinates of a realization
of the partial-quadrangle locus. -/
def tupleConfigurationField (v : Fin 6 → K) : IntermediateField k K :=
  adjoin k (Set.range v)

/-- The five-coordinate composite field is contained in the full
six-coordinate configuration field. -/
theorem tupleCompositeField_le_configurationField (v : Fin 6 → K) :
    tupleCompositeField (k := k) v ≤ tupleConfigurationField (k := k) v := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  exact Set.mem_range_self (compositeBranchIndex i)

/-- Equal complete quadrangle loci canonically identify their generated
five-coordinate composite fields. -/
def relocatedCompositeEquiv {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (↥(tupleCompositeField (k := k) v)) ≃ₐ[k]
      (↥(tupleCompositeField (k := k) w)) :=
  locusFunctionFieldEquivOfIdealEq
    (idealOf_comp_eq_of_idealOf_eq (hv.trans hw.symm) compositeBranchIndex)

/-- Composite-field transport sends each of its five displayed coordinates
to the corresponding coordinate of the target realization. -/
@[simp] theorem relocatedCompositeEquiv_apply {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) (i : Fin 5) :
    relocatedCompositeEquiv hv hw
        ⟨v (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ =
      ⟨w (compositeBranchIndex i),
        subset_adjoin k _ (Set.mem_range_self i)⟩ := by
  exact locusFunctionFieldEquivOfIdealEq_apply
    (idealOf_comp_eq_of_idealOf_eq (hv.trans hw.symm) compositeBranchIndex) i

/-- Relocated composite-field transport is the identity on one
realization. -/
@[simp] theorem relocatedCompositeEquiv_refl {v : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedCompositeEquiv hv hv = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  exact relocatedCompositeEquiv_apply hv hv i

/-- Reversing relocated composite-field transport gives its inverse. -/
@[simp] theorem relocatedCompositeEquiv_symm {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedCompositeEquiv hv hw).symm =
      relocatedCompositeEquiv hw hv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    (relocatedCompositeEquiv hv hw).symm
        ⟨w (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ =
        ⟨v (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedCompositeEquiv hv hw).symm_apply_eq.mpr
        (relocatedCompositeEquiv_apply hv hw i).symm
    _ = relocatedCompositeEquiv hw hv
        ⟨w (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedCompositeEquiv_apply hw hv i).symm

/-- Composite-field transports compose coherently along relocated
realizations. -/
@[simp] theorem relocatedCompositeEquiv_trans {u v w : Fin 6 → K}
    (hu : idealOf k u = idealOf k (configurationReps f))
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedCompositeEquiv hu hv).trans
        (relocatedCompositeEquiv hv hw) =
      relocatedCompositeEquiv hu hw := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    ((relocatedCompositeEquiv hu hv).trans
        (relocatedCompositeEquiv hv hw))
        ⟨u (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ =
        relocatedCompositeEquiv hv hw
          (relocatedCompositeEquiv hu hv
            ⟨u (compositeBranchIndex i),
              subset_adjoin k _ (Set.mem_range_self i)⟩) := rfl
    _ = relocatedCompositeEquiv hv hw
        ⟨v (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ := by
      rw [relocatedCompositeEquiv_apply]
    _ = ⟨w (compositeBranchIndex i),
        subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      relocatedCompositeEquiv_apply hv hw i
    _ = relocatedCompositeEquiv hu hw
        ⟨u (compositeBranchIndex i),
          subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedCompositeEquiv_apply hu hw i).symm

/-- Equal complete quadrangle loci canonically identify their generated
six-coordinate function fields. -/
def relocatedConfigurationEquiv {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (↥(tupleConfigurationField (k := k) v)) ≃ₐ[k]
      (↥(tupleConfigurationField (k := k) w)) :=
  locusFunctionFieldEquivOfIdealEq (hv.trans hw.symm)

/-- The canonical equivalence between two relocated configuration fields
sends all six coordinates to their matching coordinates. -/
@[simp] theorem relocatedConfigurationEquiv_apply {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) (i : Fin 6) :
    relocatedConfigurationEquiv hv hw
        ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
      ⟨w i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
  locusFunctionFieldEquivOfIdealEq_apply (hv.trans hw.symm) i

/-- Relocated configuration-field transport is the identity on one
realization. -/
@[simp] theorem relocatedConfigurationEquiv_refl {v : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedConfigurationEquiv hv hv = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    relocatedConfigurationEquiv hv hv
        ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
        ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      relocatedConfigurationEquiv_apply hv hv i
    _ = AlgEquiv.refl
        ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ := rfl

/-- Reversing relocated configuration-field transport gives its inverse. -/
@[simp] theorem relocatedConfigurationEquiv_symm {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationEquiv hv hw).symm =
      relocatedConfigurationEquiv hw hv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    (relocatedConfigurationEquiv hv hw).symm
        ⟨w i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
        ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedConfigurationEquiv hv hw).symm_apply_eq.mpr
        (relocatedConfigurationEquiv_apply hv hw i).symm
    _ = relocatedConfigurationEquiv hw hv
        ⟨w i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedConfigurationEquiv_apply hw hv i).symm

/-- Canonical transport between three relocated configuration fields is
strictly coherent. -/
@[simp] theorem relocatedConfigurationEquiv_trans {u v w : Fin 6 → K}
    (hu : idealOf k u = idealOf k (configurationReps f))
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationEquiv hu hv).trans
        (relocatedConfigurationEquiv hv hw) =
      relocatedConfigurationEquiv hu hw := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    ((relocatedConfigurationEquiv hu hv).trans
        (relocatedConfigurationEquiv hv hw))
        ⟨u i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
        relocatedConfigurationEquiv hv hw
          (relocatedConfigurationEquiv hu hv
            ⟨u i, subset_adjoin k _ (Set.mem_range_self i)⟩) := rfl
    _ = relocatedConfigurationEquiv hv hw
          ⟨v i, subset_adjoin k _ (Set.mem_range_self i)⟩ := by
      rw [relocatedConfigurationEquiv_apply]
    _ = ⟨w i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      relocatedConfigurationEquiv_apply hv hw i
    _ = relocatedConfigurationEquiv hu hw
        ⟨u i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (relocatedConfigurationEquiv_apply hu hw i).symm

/-- The composite- and configuration-field transports form a commuting
equivalence of nested extensions.  Thus relocation preserves the actual
finite extension that will be normalized, not only its total field. -/
def relocatedConfigurationExtensionEquiv {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    FiniteCover.ExtensionEquiv
      (tupleCompositeField_le_configurationField (k := k) v)
      (tupleCompositeField_le_configurationField (k := k) w) where
  baseEquiv := relocatedCompositeEquiv hv hw
  totalEquiv := relocatedConfigurationEquiv hv hw
  commutes := by
    apply adjoin_algHom_ext k
    rintro _ ⟨i, rfl⟩
    change relocatedConfigurationEquiv hv hw
        ⟨v (compositeBranchIndex i), _⟩ =
      IntermediateField.inclusion
        (tupleCompositeField_le_configurationField (k := k) w)
        (relocatedCompositeEquiv hv hw
          ⟨v (compositeBranchIndex i), _⟩)
    rw [relocatedCompositeEquiv_apply, relocatedConfigurationEquiv_apply]
    rfl

/-- The base component of relocated extension transport is the canonical
five-coordinate equivalence. -/
@[simp] theorem relocatedConfigurationExtensionEquiv_baseEquiv
    {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationExtensionEquiv hv hw).baseEquiv =
      relocatedCompositeEquiv hv hw := rfl

/-- The total component of relocated extension transport is the canonical
six-coordinate equivalence. -/
@[simp] theorem relocatedConfigurationExtensionEquiv_totalEquiv
    {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationExtensionEquiv hv hw).totalEquiv =
      relocatedConfigurationEquiv hv hw := rfl

/-- Extension transport is the identity on one relocated realization. -/
@[simp] theorem relocatedConfigurationExtensionEquiv_refl
    {v : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedConfigurationExtensionEquiv hv hv =
      FiniteCover.ExtensionEquiv.refl
        (tupleCompositeField_le_configurationField (k := k) v) := by
  apply FiniteCover.ExtensionEquiv.ext
  · simp
  · simp

/-- Reversing relocated extension transport gives its inverse square. -/
@[simp] theorem relocatedConfigurationExtensionEquiv_symm
    {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationExtensionEquiv hv hw).symm =
      relocatedConfigurationExtensionEquiv hw hv := by
  apply FiniteCover.ExtensionEquiv.ext
  · simp
  · simp

/-- Relocated extension squares compose coherently on triples of
realizations. -/
@[simp] theorem relocatedConfigurationExtensionEquiv_trans
    {u v w : Fin 6 → K}
    (hu : idealOf k u = idealOf k (configurationReps f))
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedConfigurationExtensionEquiv hu hv).trans
        (relocatedConfigurationExtensionEquiv hv hw) =
      relocatedConfigurationExtensionEquiv hu hw := by
  apply FiniteCover.ExtensionEquiv.ext
  · simp
  · simp

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

/-- A tuple with the same complete ideal as the original partial
quadrangle carries the relocated selected `T : S' → U'` pair over its
common parameter field. -/
def tPairOfIdealEq (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    FiniteCorrespondencePair (↥(tupleParameterField (k := k) v)) K where
  source := v 3
  target := v 5
  source_generic := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    have ho : configurationReps f 3 ∉
        racl k (configurationReps f '' parameterIndices) := by
      rw [image_parameterIndices]
      exact S'_rep_generic_over_parameters h
    have ht := notMem_racl_image_of_idealOf_eq k hv.symm ho
    rwa [image_parameterIndices] at ht
  target_mem_source := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (tPair (k := k) h).target_mem_source
    change (f 5).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 3).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 5 ∈
        racl k (configurationReps f '' parameterSource3Indices) := by
      rw [image_parameterSource3Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 3).rep} : Set K) =
          insert (f 3).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 5).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 3).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource3Indices] at ht
    have hset : insert (v 3) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 3} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht
  source_mem_target := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (tPair (k := k) h).source_mem_target
    change (f 3).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 5).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 3 ∈
        racl k (configurationReps f '' parameterSource5Indices) := by
      rw [image_parameterSource5Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 5).rep} : Set K) =
          insert (f 5).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 3).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 5).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource5Indices] at ht
    have hset : insert (v 5) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 5} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht

/-- The relocated selected `S : U' → T'` pair over the same common
parameter field. -/
def sPairOfIdealEq (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    FiniteCorrespondencePair (↥(tupleParameterField (k := k) v)) K where
  source := v 5
  target := v 4
  source_generic := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    have ho : configurationReps f 5 ∉
        racl k (configurationReps f '' parameterIndices) := by
      rw [image_parameterIndices]
      exact U'_rep_generic_over_parameters h
    have ht := notMem_racl_image_of_idealOf_eq k hv.symm ho
    rwa [image_parameterIndices] at ht
  target_mem_source := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (sPair (k := k) h).target_mem_source
    change (f 4).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 5).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 4 ∈
        racl k (configurationReps f '' parameterSource5Indices) := by
      rw [image_parameterSource5Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 5).rep} : Set K) =
          insert (f 5).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 4).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 5).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource5Indices] at ht
    have hset : insert (v 5) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 5} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht
  source_mem_target := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (sPair (k := k) h).source_mem_target
    change (f 5).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 4).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 5 ∈
        racl k (configurationReps f '' parameterSource4Indices) := by
      rw [image_parameterSource4Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 4).rep} : Set K) =
          insert (f 4).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 5).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 4).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource4Indices] at ht
    have hset : insert (v 4) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 4} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht

/-- The relocated selected endpoint `U : S' → T'` pair over the common
parameter field. -/
def uPairOfIdealEq (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    FiniteCorrespondencePair (↥(tupleParameterField (k := k) v)) K where
  source := v 3
  target := v 4
  source_generic := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    have ho : configurationReps f 3 ∉
        racl k (configurationReps f '' parameterIndices) := by
      rw [image_parameterIndices]
      exact S'_rep_generic_over_parameters h
    have ht := notMem_racl_image_of_idealOf_eq k hv.symm ho
    rwa [image_parameterIndices] at ht
  target_mem_source := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (uPair (k := k) h).target_mem_source
    change (f 4).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 3).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 4 ∈
        racl k (configurationReps f '' parameterSource3Indices) := by
      rw [image_parameterSource3Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 3).rep} : Set K) =
          insert (f 3).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 4).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 3).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource3Indices] at ht
    have hset : insert (v 3) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 3} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht
  source_mem_target := by
    rw [tupleParameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    have ho := (uPair (k := k) h).source_mem_target
    change (f 3).rep ∈ racl
      (↥(adjoin k ({(f 0).rep, (f 1).rep, (f 2).rep} : Set K)))
      ({(f 4).rep} : Set K) at ho
    rw [mem_racl_adjoin_base_iff, Set.union_singleton] at ho
    have ho' : configurationReps f 3 ∈
        racl k (configurationReps f '' parameterSource4Indices) := by
      rw [image_parameterSource4Indices]
      have hset : ({(f 0).rep, (f 1).rep, (f 2).rep, (f 4).rep} : Set K) =
          insert (f 4).rep {(f 0).rep, (f 1).rep, (f 2).rep} := by
        ext z
        simp
        tauto
      change (f 3).rep ∈
        racl k ({(f 0).rep, (f 1).rep, (f 2).rep, (f 4).rep} : Set K)
      rw [hset]
      exact ho
    have ht := mem_racl_image_of_idealOf_eq k hv.symm ho'
    rw [image_parameterSource4Indices] at ht
    have hset : insert (v 4) ({v 0, v 1, v 2} : Set K) =
        {v 0, v 1, v 2, v 4} := by
      ext z
      simp
      tauto
    rw [hset]
    exact ht

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

/-- Every relocated tuple with the same complete partial-quadrangle ideal
gives a literal selected composition over its relocated common parameter
field. -/
theorem pairsOfIdealEq_composes (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    FiniteCorrespondenceGerm.Composes
      (FiniteCorrespondenceGerm.ofPair (tPairOfIdealEq h v hv))
      (FiniteCorrespondenceGerm.ofPair (sPairOfIdealEq h v hv))
      (FiniteCorrespondenceGerm.ofPair (uPairOfIdealEq h v hv)) := by
  refine ⟨tPairOfIdealEq h v hv, sPairOfIdealEq h v hv,
    rfl, rfl, rfl, ?_⟩
  rfl

/-- The selected composite branch field of a relocated quadrangle, viewed
over the original ground field. -/
abbrev relocatedCompositeBranchField (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    IntermediateField k K :=
  (((tPairOfIdealEq h v hv).comp
    (sPairOfIdealEq h v hv) rfl).branchField).restrictScalars k

/-- The full selected chain field of a relocated quadrangle, viewed over
the original ground field. -/
abbrev relocatedChainField (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    IntermediateField k K :=
  ((tPairOfIdealEq h v hv).chainField
    (sPairOfIdealEq h v hv)).restrictScalars k

/-- After restriction to `k`, the selected composite branch field is the
field generated by the first five coordinates of the relocated tuple. -/
theorem relocatedCompositeBranchField_restrictScalars_eq
    (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedCompositeBranchField h v hv =
      tupleCompositeField (k := k) v := by
  change (((tPairOfIdealEq h v hv).comp
      (sPairOfIdealEq h v hv) rfl).branchField).restrictScalars k = _
  rw [FiniteCorrespondencePair.branchField, restrictScalars_adjoin]
  change adjoin k
      ((tupleParameterField (k := k) v : Set K) ∪ {v 3, v 4}) =
    adjoin k (Set.range (v ∘ compositeBranchIndex))
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    rintro x (hx | hx)
    · have hparam : tupleParameterField (k := k) v ≤
          tupleCompositeField (k := k) v := by
        rw [tupleParameterField, tupleCompositeField]
        apply adjoin.mono
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Set.mem_range_self 0
        · exact Set.mem_range_self 1
        · exact Set.mem_range_self 2
      exact hparam hx
    · apply subset_adjoin k _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_range_self 3
      · exact Set.mem_range_self 4
  · apply adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · exact subset_adjoin k _ (by simp)
    · exact subset_adjoin k _ (by simp)

/-- After restriction from the relocated common parameter field to `k`,
the literal three-arrow chain field is exactly the field generated by all
six coordinates of the relocated quadrangle. -/
theorem relocatedChainField_restrictScalars_eq
    (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedChainField h v hv =
      tupleConfigurationField (k := k) v := by
  change ((tPairOfIdealEq h v hv).chainField
      (sPairOfIdealEq h v hv)).restrictScalars k = _
  rw [FiniteCorrespondencePair.chainField, restrictScalars_adjoin]
  change adjoin k
      ((tupleParameterField (k := k) v : Set K) ∪ {v 3, v 5, v 4}) =
    adjoin k (Set.range v)
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    rintro x (hx | hx)
    · have hparam : tupleParameterField (k := k) v ≤
          adjoin k (Set.range v) := by
        rw [tupleParameterField]
        apply adjoin.mono
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Set.mem_range_self 0
        · exact Set.mem_range_self 1
        · exact Set.mem_range_self 2
      exact hparam hx
    · apply subset_adjoin k _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Set.mem_range_self 3
      · exact Set.mem_range_self 5
      · exact Set.mem_range_self 4
  · apply adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · apply subset_adjoin k _
      left
      exact subset_adjoin k _ (by simp)
    · exact subset_adjoin k _ (by simp)
    · exact subset_adjoin k _ (by simp)
    · exact subset_adjoin k _ (by simp)

/-- The selected composite branch is contained in the selected chain after
both are restricted to `k`. -/
theorem relocatedChainExtensionInclusion (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedCompositeBranchField h v hv ≤ relocatedChainField h v hv :=
  (tPairOfIdealEq h v hv).compositeBranchField_le_chainField
    (sPairOfIdealEq h v hv) rfl

/-- Equal-locus relocation transports the actual selected composite/chain
extension.  The equality transports identify it with the canonical
five-in-six-coordinate extension, where the square is coordinatewise. -/
def relocatedChainExtensionEquiv (h : IsPartialQuadrangle f)
    {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    FiniteCover.ExtensionEquiv
      (relocatedChainExtensionInclusion h v hv)
      (relocatedChainExtensionInclusion h w hw) :=
  ((FiniteCover.ExtensionEquiv.ofEq
      (h := relocatedChainExtensionInclusion h v hv)
      (h' := tupleCompositeField_le_configurationField (k := k) v)
      (relocatedCompositeBranchField_restrictScalars_eq h v hv)
      (relocatedChainField_restrictScalars_eq h v hv)).trans
    (relocatedConfigurationExtensionEquiv hv hw)).trans
      (FiniteCover.ExtensionEquiv.ofEq
        (h := relocatedChainExtensionInclusion h w hw)
        (h' := tupleCompositeField_le_configurationField (k := k) w)
        (relocatedCompositeBranchField_restrictScalars_eq h w hw)
        (relocatedChainField_restrictScalars_eq h w hw)).symm

/-- Equal-locus transport lifts from the selected finite extensions to
their canonical normal closures.  The lift is compatible with the base
equivalence; chosen lifts can be composed, reversed, and identified by the
`NormalExtensionEquiv` operations. -/
noncomputable def relocatedChainNormalExtensionEquiv
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    FiniteCover.NormalExtensionEquiv
      (relocatedChainExtensionInclusion h v hv)
      (relocatedChainExtensionInclusion h w hw) :=
  (relocatedChainExtensionEquiv h hv hw).normalLift

/-- The normal-closure lift retains exactly the underlying relocated
finite-extension equivalence. -/
@[simp] theorem relocatedChainNormalExtensionEquiv_toExtensionEquiv
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedChainNormalExtensionEquiv h hv hw).toExtensionEquiv =
      relocatedChainExtensionEquiv h hv hw := by
  simp [relocatedChainNormalExtensionEquiv]

/-- Over an algebraically closed ambient field, the concrete normal covers
of two relocated chains are isomorphic as fields.  The construction passes
from each ambient cover to its canonical model, uses the compatible
normal-extension lift, and returns to the target ambient cover. -/
noncomputable def relocatedChainNormalCoverEquiv [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (↥(FiniteCover.normalClosureOver
      (relocatedChainExtensionInclusion h v hv))) ≃+*
      (↥(FiniteCover.normalClosureOver
        (relocatedChainExtensionInclusion h w hw))) := by
  have hfinv : FiniteDimensional
      (↥(relocatedCompositeBranchField h v hv))
      (↥(extendScalars (relocatedChainExtensionInclusion h v hv))) := by
    exact (tPairOfIdealEq h v hv).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h v hv) rfl
  have hfinw : FiniteDimensional
      (↥(relocatedCompositeBranchField h w hw))
      (↥(extendScalars (relocatedChainExtensionInclusion h w hw))) := by
    exact (tPairOfIdealEq h w hw).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h w hw) rfl
  let cv := FiniteCover.normalClosureOverEquivCanonical
    (relocatedChainExtensionInclusion h v hv)
    (Algebra.IsAlgebraic.of_finite
      (↥(relocatedCompositeBranchField h v hv))
      (↥(extendScalars (relocatedChainExtensionInclusion h v hv))))
  let cw := FiniteCover.normalClosureOverEquivCanonical
    (relocatedChainExtensionInclusion h w hw)
    (Algebra.IsAlgebraic.of_finite
      (↥(relocatedCompositeBranchField h w hw))
      (↥(extendScalars (relocatedChainExtensionInclusion h w hw))))
  exact cv.toRingEquiv |>.trans
    (relocatedChainNormalExtensionEquiv h hv hw).normalEquiv |>.trans
      cw.symm.toRingEquiv

/-- The concrete normal-cover equivalence is semilinear over the relocated
composite-branch equivalence. -/
@[simp] theorem relocatedChainNormalCoverEquiv_algebraMap [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f))
    (x : relocatedCompositeBranchField h v hv) :
    relocatedChainNormalCoverEquiv h hv hw
        (algebraMap (↥(relocatedCompositeBranchField h v hv))
          (↥(FiniteCover.normalClosureOver
            (relocatedChainExtensionInclusion h v hv))) x) =
      algebraMap (↥(relocatedCompositeBranchField h w hw))
        (↥(FiniteCover.normalClosureOver
          (relocatedChainExtensionInclusion h w hw)))
        ((relocatedChainExtensionEquiv h hv hw).baseEquiv x) := by
  simp [relocatedChainNormalCoverEquiv]

/-- The compatible equivalences of the base, chain, and concrete normal
cover transport every conjugate branch of one relocated chain to a
conjugate branch of the other. -/
noncomputable def relocatedChainBranchEquiv [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    FiniteCoverBranch (relocatedChainExtensionInclusion h v hv) ≃
      FiniteCoverBranch (relocatedChainExtensionInclusion h w hw) := by
  let e := relocatedChainExtensionEquiv h hv hw
  let n := relocatedChainNormalCoverEquiv h hv hw
  apply finiteCoverBranchEquivOfExtensionEquiv
    (relocatedChainExtensionInclusion h v hv)
    (relocatedChainExtensionInclusion h w hw) e n
  apply RingHom.ext
  intro x
  exact relocatedChainNormalCoverEquiv_algebraMap h hv hw x

/-- Correcting the raw transported branch by a target deck transformation
gives an equivariant transport which preserves the literal relocated chain.
The same correction conjugates the deck-transformation equivalence. -/
noncomputable def relocatedChainBasedBranchEquiv [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    FiniteCoverBasedBranchEquiv
      (relocatedChainExtensionInclusion h v hv)
      (relocatedChainExtensionInclusion h w hw) := by
  have hfinw : FiniteDimensional
      (↥(relocatedCompositeBranchField h w hw))
      (↥(extendScalars (relocatedChainExtensionInclusion h w hw))) :=
    (tPairOfIdealEq h w hw).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h w hw) rfl
  apply finiteCoverBasedBranchEquivOfExtensionEquiv
    (relocatedChainExtensionInclusion h v hv)
    (relocatedChainExtensionInclusion h w hw) hfinw
    (relocatedChainExtensionEquiv h hv hw)
    (relocatedChainNormalCoverEquiv h hv hw)
  apply RingHom.ext
  intro x
  exact relocatedChainNormalCoverEquiv_algebraMap h hv hw x

/-- The based relocated branch transport sends the distinguished source
chain exactly to the distinguished target chain. -/
@[simp] theorem relocatedChainBasedBranchEquiv_selected [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedChainBasedBranchEquiv h hv hw).branchEquiv
        (finiteCoverSelectedBranch
          (relocatedChainExtensionInclusion h v hv)) =
      finiteCoverSelectedBranch
        (relocatedChainExtensionInclusion h w hw) :=
  (relocatedChainBasedBranchEquiv h hv hw).map_selected

/-- Above every independent replacement of `(S,T,S')` there is a single
compatible six-tuple whose three actual finite-correspondence pairs over
the common parameter field compose literally. -/
theorem exists_relocated_correspondence_groupoid [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {g : Fin 3 → K}
    (hg : AlgebraicIndependent k g) :
    ∃ (v : Fin 6 → K)
      (hv : idealOf k v = idealOf k (configurationReps f)),
      v ∘ groupCoordinateIndex = g ∧
        FiniteCorrespondenceGerm.Composes
          (FiniteCorrespondenceGerm.ofPair (tPairOfIdealEq h v hv))
          (FiniteCorrespondenceGerm.ofPair (sPairOfIdealEq h v hv))
          (FiniteCorrespondenceGerm.ofPair (uPairOfIdealEq h v hv)) := by
  obtain ⟨v, hv, hfix⟩ := exists_configuration_relocation h hg
  exact ⟨v, hv, hfix, pairsOfIdealEq_composes h v hv⟩

/-- Base-changing the individual `T`-family member to the common
`k(S,T,U)` coefficient field selects the `T` branch of the groupoid. -/
theorem tFamily_map_le_selectedPair (h : IsPartialQuadrangle f) :
    Ideal.map
        (MvPolynomial.map (IntermediateField.inclusion
          (tFamilyParameterField_le_parameterField h)))
        (tFamilyMember h).toPair.ideal ≤ (tPair h).ideal := by
  change Ideal.map
      (MvPolynomial.map (IntermediateField.inclusion
        (tFamilyParameterField_le_parameterField h)))
      (idealOf (↥(tFamilyMember h).parameterField)
        ![(f 3).rep, (f 5).rep]) ≤
    idealOf (↥(parameterField f)) ![(f 3).rep, (f 5).rep]
  exact idealOf_map_le_of_intermediateField_le
    (tFamilyParameterField_le_parameterField h)
    ![(f 3).rep, (f 5).rep]

/-- Base-changing the individual `S`-family member selects the `S`
branch of the common groupoid. -/
theorem sFamily_map_le_selectedPair (h : IsPartialQuadrangle f) :
    Ideal.map
        (MvPolynomial.map (IntermediateField.inclusion
          (sFamilyParameterField_le_parameterField h)))
        (sFamilyMember h).toPair.ideal ≤ (sPair h).ideal := by
  change Ideal.map
      (MvPolynomial.map (IntermediateField.inclusion
        (sFamilyParameterField_le_parameterField h)))
      (idealOf (↥(sFamilyMember h).parameterField)
        ![(f 5).rep, (f 4).rep]) ≤
    idealOf (↥(parameterField f)) ![(f 5).rep, (f 4).rep]
  exact idealOf_map_le_of_intermediateField_le
    (sFamilyParameterField_le_parameterField h)
    ![(f 5).rep, (f 4).rep]

/-- Base-changing the individual endpoint `U`-family member selects the
composite `U` branch of the common groupoid. -/
theorem uFamily_map_le_selectedPair (h : IsPartialQuadrangle f) :
    Ideal.map
        (MvPolynomial.map (IntermediateField.inclusion
          (uFamilyParameterField_le_parameterField h)))
        (uFamilyMember h).toPair.ideal ≤ (uPair h).ideal := by
  change Ideal.map
      (MvPolynomial.map (IntermediateField.inclusion
        (uFamilyParameterField_le_parameterField h)))
      (idealOf (↥(uFamilyMember h).parameterField)
        ![(f 3).rep, (f 4).rep]) ≤
    idealOf (↥(parameterField f)) ![(f 3).rep, (f 4).rep]
  exact idealOf_map_le_of_intermediateField_le
    (uFamilyParameterField_le_parameterField h)
    ![(f 3).rep, (f 4).rep]

/-- The selected three-object groupoid composition identity
`S ∘ T = U`. -/
theorem selected_correspondence_composes (h : IsPartialQuadrangle f) :
    FiniteCorrespondenceGerm.Composes
      (FiniteCorrespondenceGerm.ofPair (tPair h))
      (FiniteCorrespondenceGerm.ofPair (sPair h))
      (FiniteCorrespondenceGerm.ofPair (uPair h)) := by
  refine ⟨tPair h, sPair h, rfl, rfl, rfl, ?_⟩
  rfl

/-- The literal `S' → U' → T'` chain has a common joint function field
finite over the `T` branch, the `S` branch, and the selected `U` endpoint
branch. -/
theorem selected_chain_field_finite_covers (h : IsPartialQuadrangle f) :
    let P := tPair h
    let Q := sPair h
    FiniteDimensional (↥P.branchField) (↥(P.chainOverLeft Q)) ∧
      FiniteDimensional (↥Q.branchField) (↥(P.chainOverRight Q rfl)) ∧
      FiniteDimensional (↥(P.comp Q rfl).branchField)
        (↥(P.chainOverComposite Q rfl)) := by
  dsimp only
  exact
    ⟨(tPair h).chainOverLeft_finiteDimensional (sPair h) rfl,
      (tPair h).chainOverRight_finiteDimensional (sPair h) rfl,
      (tPair h).chainOverComposite_finiteDimensional (sPair h) rfl⟩

/-- In an algebraically closed ambient field, the partial-quadrangle
chain embeds in a finite normal closure over its selected `U` endpoint
branch. -/
theorem selected_chain_normal_cover [IsAlgClosed K]
    (h : IsPartialQuadrangle f) :
    let P := tPair h
    let Q := sPair h
    FiniteDimensional (↥(P.comp Q rfl).branchField)
        (↥(P.chainNormalOverComposite Q rfl)) ∧
      Normal (↥(P.comp Q rfl).branchField)
        (↥(P.chainNormalOverComposite Q rfl)) ∧
      P.chainOverComposite Q rfl ≤ P.chainNormalOverComposite Q rfl := by
  dsimp only
  exact
    ⟨(tPair h).chainNormalOverComposite_finiteDimensional (sPair h) rfl,
      (tPair h).chainNormalOverComposite_normal (sPair h) rfl,
      (tPair h).chainOverComposite_le_normal (sPair h) rfl⟩

/-- On the normal cover, the literal partial-quadrangle branch is a
selected embedding.  Its conjugate branches and the automorphisms of the
normal cover form finite types. -/
theorem selected_chain_component_on_normal_cover
    (h : IsPartialQuadrangle f) :
    let P := tPair h
    let Q := sPair h
    let hle := P.compositeBranchField_le_chainField Q rfl
    (P.chainNormalOverComposite Q rfl).val.comp
          (FiniteCover.selectedEmbedding hle) =
        (P.chainOverComposite Q rfl).val ∧
      Finite ((↥(P.chainOverComposite Q rfl)) →ₐ[
        ↥(P.comp Q rfl).branchField] K) ∧
      Finite ((↥(P.chainNormalOverComposite Q rfl)) ≃ₐ[
        ↥(P.comp Q rfl).branchField]
          (↥(P.chainNormalOverComposite Q rfl))) := by
  dsimp only
  exact
    ⟨FiniteCover.normalClosure_val_comp_selectedEmbedding _,
      FiniteCover.finite_ambientEmbeddings _
        ((tPair h).chainOverComposite_finiteDimensional (sPair h) rfl),
      FiniteCover.finite_normalAutomorphisms _
        ((tPair h).chainOverComposite_finiteDimensional (sPair h) rfl)⟩

/-- Ambient embeddings of the partial-quadrangle normal cover are exactly
its automorphisms over the selected `U` endpoint branch. -/
noncomputable def selectedChainEmbeddingEquivAut [IsAlgClosed K]
    (h : IsPartialQuadrangle f) :
    let P := tPair h
    let Q := sPair h
    ((↥(P.chainNormalOverComposite Q rfl)) →ₐ[
        ↥(P.comp Q rfl).branchField] K) ≃
      ((↥(P.chainNormalOverComposite Q rfl)) ≃ₐ[
        ↥(P.comp Q rfl).branchField]
          (↥(P.chainNormalOverComposite Q rfl))) := by
  dsimp only
  let P := tPair h
  let Q := sPair h
  let hle := P.compositeBranchField_le_chainField Q rfl
  change ((↥(FiniteCover.normalClosureOver hle)) →ₐ[
      ↥(P.comp Q rfl).branchField] K) ≃
    ((↥(FiniteCover.normalClosureOver hle)) ≃ₐ[
      ↥(P.comp Q rfl).branchField]
        (↥(FiniteCover.normalClosureOver hle)))
  letI : FiniteDimensional (↥(P.comp Q rfl).branchField)
      (↥(extendScalars hle)) :=
    P.chainOverComposite_finiteDimensional Q rfl
  letI : Normal (↥(P.comp Q rfl).branchField)
      (↥(FiniteCover.normalClosureOver hle)) :=
    FiniteCover.normalClosureOver_normal hle
      (Algebra.IsAlgebraic.of_finite
        (↥(P.comp Q rfl).branchField) (↥(extendScalars hle)))
  exact FiniteCover.normalEmbeddingEquivAut hle

/-- The genuine action groupoid of all conjugate components of the
selected partial-quadrangle chain on its finite normal cover. -/
abbrev selectedChainBranchGroupoid (h : IsPartialQuadrangle f) :=
  finiteCoverBranchGroupoid
    ((tPair h).compositeBranchField_le_chainField (sPair h) rfl)

/-- The literal `S' → U' → T'` component as the distinguished object of
its normal-cover branch groupoid. -/
def selectedChainBranchObject (h : IsPartialQuadrangle f) :
    selectedChainBranchGroupoid h :=
  finiteCoverSelectedObject
    ((tPair h).compositeBranchField_le_chainField (sPair h) rfl)

/-- The partial-quadrangle normal cover has only finitely many conjugate
selected-chain components. -/
theorem finite_selectedChainBranches (h : IsPartialQuadrangle f) :
    Finite
      (FiniteCoverBranch
        ((tPair h).compositeBranchField_le_chainField (sPair h) rfl)) :=
  finite_coverBranches _
    ((tPair h).chainOverComposite_finiteDimensional (sPair h) rfl)

/-- Over an algebraically closed ambient field, deck transformations act
transitively on the conjugate partial-quadrangle components, so their
action category is a connected genuine groupoid. -/
theorem selectedChainBranchGroupoid_isConnected [IsAlgClosed K]
    (h : IsPartialQuadrangle f) :
    CategoryTheory.IsConnected (selectedChainBranchGroupoid h) :=
  finiteCoverBranchGroupoid_isConnected _
    ((tPair h).chainOverComposite_finiteDimensional (sPair h) rfl)

/-- The genuine conjugate-branch groupoid attached to any relocated
partial-quadrangle chain.  Its coefficient field and branch fields vary
with the relocated tuple. -/
abbrev relocatedChainBranchGroupoid (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :=
  finiteCoverBranchGroupoid (relocatedChainExtensionInclusion h v hv)

/-- The literal relocated chain as the distinguished object in its
finite-cover branch groupoid. -/
def relocatedChainBranchObject (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    relocatedChainBranchGroupoid h v hv :=
  finiteCoverSelectedObject (relocatedChainExtensionInclusion h v hv)

/-- Equal-locus relocation gives an equivalence of the genuine finite
branch groupoids, with the deck action and literal selected chain both
preserved. -/
noncomputable def relocatedChainBranchGroupoidEquivalence [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    relocatedChainBranchGroupoid h v hv ≌
      relocatedChainBranchGroupoid h w hw :=
  (relocatedChainBasedBranchEquiv h hv hw).groupoidEquivalence

/-- The relocated groupoid equivalence sends the literal source chain to
the literal target chain. -/
theorem relocatedChainBranchGroupoidEquivalence_obj_selected
    [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f)) :
    (relocatedChainBranchGroupoidEquivalence h hv hw).functor.obj
        (relocatedChainBranchObject h v hv) =
      relocatedChainBranchObject h w hw :=
  (relocatedChainBasedBranchEquiv h hv hw).groupoidEquivalence_obj_selected

/-- Equal-locus relocation identifies every based arrow family by
transporting its deck label.  This is the hom-set interface used by the
difference chart above the varying realization locus. -/
noncomputable def relocatedChainBasedArrowEquiv [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f))
    (b : relocatedChainBranchGroupoid h v hv) :
    (relocatedChainBranchObject h v hv ⟶ b) ≃
      (relocatedChainBranchObject h w hw ⟶
        ((relocatedChainBasedBranchEquiv h hv hw).branchEquiv b.back :
          relocatedChainBranchGroupoid h w hw)) :=
  (relocatedChainBasedBranchEquiv h hv hw).arrowEquiv b

/-- On based arrows, relocated transport sends the deck label through the
corrected deck-group equivalence. -/
@[simp] theorem relocatedChainBasedArrowEquiv_val [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f))
    (b : relocatedChainBranchGroupoid h v hv)
    (a : relocatedChainBranchObject h v hv ⟶ b) :
    (relocatedChainBasedArrowEquiv h hv hw b a).val =
      (relocatedChainBasedBranchEquiv h hv hw).deckEquiv a.val := rfl

/-- Relocated based-arrow transport preserves difference-chart
multiplication on the nose. -/
theorem relocatedChainBasedArrowEquiv_differenceProduct [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f))
    (b : relocatedChainBranchGroupoid h v hv)
    (e a c : relocatedChainBranchObject h v hv ⟶ b) :
    relocatedChainBasedArrowEquiv h hv hw b
        (groupoidDifferenceProduct e a c) =
      groupoidDifferenceProduct
        (relocatedChainBasedArrowEquiv h hv hw b e)
        (relocatedChainBasedArrowEquiv h hv hw b a)
        (relocatedChainBasedArrowEquiv h hv hw b c) :=
  (relocatedChainBasedBranchEquiv h hv hw).arrowEquiv_differenceProduct
    b e a c

/-- Relocated based-arrow transport preserves difference-chart inverse on
the nose. -/
theorem relocatedChainBasedArrowEquiv_differenceInverse [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {v w : Fin 6 → K}
    (hv : idealOf k v = idealOf k (configurationReps f))
    (hw : idealOf k w = idealOf k (configurationReps f))
    (b : relocatedChainBranchGroupoid h v hv)
    (e a : relocatedChainBranchObject h v hv ⟶ b) :
    relocatedChainBasedArrowEquiv h hv hw b
        (groupoidDifferenceInverse e a) =
      groupoidDifferenceInverse
        (relocatedChainBasedArrowEquiv h hv hw b e)
        (relocatedChainBasedArrowEquiv h hv hw b a) :=
  (relocatedChainBasedBranchEquiv h hv hw).arrowEquiv_differenceInverse
    b e a

/-- Every relocated chain has only finitely many conjugate branches on
its selected finite normal cover. -/
theorem finite_relocatedChainBranches (h : IsPartialQuadrangle f)
    (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    Finite
      (FiniteCoverBranch
        ((tPairOfIdealEq h v hv).compositeBranchField_le_chainField
          (sPairOfIdealEq h v hv) rfl)) :=
  finite_coverBranches _
    ((tPairOfIdealEq h v hv).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h v hv) rfl)

/-- Over an algebraically closed ambient field, the branch groupoid of
every relocated chain is connected. -/
theorem relocatedChainBranchGroupoid_isConnected [IsAlgClosed K]
    (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f)) :
    CategoryTheory.IsConnected (relocatedChainBranchGroupoid h v hv) :=
  finiteCoverBranchGroupoid_isConnected _
    ((tPairOfIdealEq h v hv).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h v hv) rfl)

/-- Based arrows from the literal relocated chain to any conjugate branch
carry a rational group chunk.  This is the finite branch-groupoid fiber of
the varying parameter-family construction. -/
def relocatedChainArrowChunk [IsAlgClosed K]
    (h : IsPartialQuadrangle f) (v : Fin 6 → K)
    (hv : idealOf k v = idealOf k (configurationReps f))
    (b : relocatedChainBranchGroupoid h v hv) :
    RationalGroupChunk (relocatedChainBranchObject h v hv ⟶ b) :=
  finiteCoverArrowChunk _
    ((tPairOfIdealEq h v hv).chainOverComposite_finiteDimensional
      (sPairOfIdealEq h v hv) rfl) b

/-- Every independent replacement of `(S,T,S')` therefore carries a
compatible relocated correspondence chain together with a connected
finite branch groupoid above that chain. -/
theorem exists_relocated_connected_branch_groupoid [IsAlgClosed K]
    (h : IsPartialQuadrangle f) {g : Fin 3 → K}
    (hg : AlgebraicIndependent k g) :
    ∃ (v : Fin 6 → K)
      (hv : idealOf k v = idealOf k (configurationReps f)),
      v ∘ groupCoordinateIndex = g ∧
        FiniteCorrespondenceGerm.Composes
          (FiniteCorrespondenceGerm.ofPair (tPairOfIdealEq h v hv))
          (FiniteCorrespondenceGerm.ofPair (sPairOfIdealEq h v hv))
          (FiniteCorrespondenceGerm.ofPair (uPairOfIdealEq h v hv)) ∧
        CategoryTheory.IsConnected (relocatedChainBranchGroupoid h v hv) := by
  obtain ⟨v, hv, hfix, hcomp⟩ :=
    exists_relocated_correspondence_groupoid h hg
  exact ⟨v, hv, hfix, hcomp,
    relocatedChainBranchGroupoid_isConnected h v hv⟩

end IsPartialQuadrangle

end
end AclGeom
