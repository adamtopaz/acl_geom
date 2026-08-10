/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family
import AclGeom.Geometry.FiniteRank

/-!
# Rank-two finite-correspondence multiplication

This module packages a six-coordinate prime locus as a generically finite
multiplication relation on rank-two parameter tuples.  Each pair among the
left input, right input, and output is algebraically independent, while the
remaining two coordinates are algebraic over that pair.  Consequently the
same locus supports multiplication and both division relocations.

The operation remains relational: no uniqueness of any relocated output is
asserted.
-/

namespace AclGeom

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Concatenate two rank-two parameter tuples. -/
def rankTwoPairTuple (a b : Fin 2 → Ω) : Fin 4 → Ω :=
  ![a 0, a 1, b 0, b 1]

/-- Concatenate three rank-two parameter tuples. -/
def rankTwoTripleTuple (a b c : Fin 2 → Ω) : Fin 6 → Ω :=
  ![a 0, a 1, b 0, b 1, c 0, c 1]

/-- Concatenate four rank-two parameter tuples. -/
def rankTwoFourTuple (a b c d : Fin 2 → Ω) : Fin 8 → Ω :=
  ![a 0, a 1, b 0, b 1, c 0, c 1, d 0, d 1]

omit [Field Ω] in
/-- The range of a concatenated pair is the union of the two block
ranges. -/
theorem rankTwoPairTuple_range (a b : Fin 2 → Ω) :
    Set.range (rankTwoPairTuple a b) = Set.range a ∪ Set.range b := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_union_left _ (Set.mem_range_self 0)
    · exact Set.mem_union_left _ (Set.mem_range_self 1)
    · exact Set.mem_union_right _ (Set.mem_range_self 0)
    · exact Set.mem_union_right _ (Set.mem_range_self 1)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩

omit [Field Ω] in
/-- The range of a concatenated four-tuple is the union of its four block
ranges. -/
theorem rankTwoFourTuple_range (a b c d : Fin 2 → Ω) :
    Set.range (rankTwoFourTuple a b c d) =
      Set.range a ∪ Set.range b ∪ Set.range c ∪ Set.range d := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_range_self 0)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_range_self 1)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_range_self 0)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_range_self 1)))
    · exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_range_self 0))
    · exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_range_self 1))
    · exact Set.mem_union_right _ (Set.mem_range_self 0)
    · exact Set.mem_union_right _ (Set.mem_range_self 1)
  · rintro (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · fin_cases i
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    · fin_cases i
      · exact ⟨6, rfl⟩
      · exact ⟨7, rfl⟩

/-- Equality of relative algebraic closures is stable under adjoining the
same set of generators. -/
theorem racl_union_congr_left {S T : Set Ω}
    (h : racl k S = racl k T) (U : Set Ω) :
    racl k (S ∪ U) = racl k (T ∪ U) := by
  calc
    racl k (S ∪ U) = racl k ((racl k S : Set Ω) ∪ U) :=
      (racl_union_left S U).symm
    _ = racl k ((racl k T : Set Ω) ∪ U) := by rw [h]
    _ = racl k (T ∪ U) := racl_union_left T U

/-- Algebraic independence is preserved when an equally sized tuple
generates the same relative algebraic closure. -/
theorem algebraicIndependent_of_racl_range_eq {n : ℕ}
    {v w : Fin n → Ω} (hv : AlgebraicIndependent k v)
    (h : racl k (Set.range v) = racl k (Set.range w)) :
    AlgebraicIndependent k w := by
  apply algebraicIndependent_of_rankEq_iSup_point
  exact (rankEq_iSup_point hv).congr (iSup_point_congr h)

/-- A generically finite ternary correspondence on rank-two parameter
tuples.  Every displayed pair has rank four and the omitted parameter tuple
is coordinatewise algebraic over it. -/
structure RankTwoFiniteCorrespondenceMultiplication where
  /-- The left rank-two input. -/
  left : Fin 2 → Ω
  /-- The right rank-two input. -/
  right : Fin 2 → Ω
  /-- The rank-two output. -/
  output : Fin 2 → Ω
  /-- The two input tuples are jointly independent. -/
  leftRight_independent :
    AlgebraicIndependent k (rankTwoPairTuple left right)
  /-- The left-input/output tuples are jointly independent. -/
  leftOutput_independent :
    AlgebraicIndependent k (rankTwoPairTuple left output)
  /-- The right-input/output tuples are jointly independent. -/
  rightOutput_independent :
    AlgebraicIndependent k (rankTwoPairTuple right output)
  /-- Every output coordinate is algebraic over the two inputs. -/
  output_mem_left_right : ∀ i,
    output i ∈ racl k (Set.range (rankTwoPairTuple left right))
  /-- Every right-input coordinate is algebraic over the left input and
  output. -/
  right_mem_left_output : ∀ i,
    right i ∈ racl k (Set.range (rankTwoPairTuple left output))
  /-- Every left-input coordinate is algebraic over the right input and
  output. -/
  left_mem_right_output : ∀ i,
    left i ∈ racl k (Set.range (rankTwoPairTuple right output))

namespace RankTwoFiniteCorrespondenceMultiplication

variable (M : RankTwoFiniteCorrespondenceMultiplication
  (k := k) (Ω := Ω))

/-- The generic six-coordinate tuple of the relation. -/
def tuple : Fin 6 → Ω := rankTwoTripleTuple M.left M.right M.output

/-- The complete prime ideal of the rank-two multiplication locus. -/
def ideal : Ideal (MvPolynomial (Fin 6) k) := idealOf k M.tuple

/-- Three rank-two tuples realize the selected multiplication locus. -/
def IsRealization (a b c : Fin 2 → Ω) : Prop :=
  idealOf k (rankTwoTripleTuple a b c) = M.ideal

namespace IsRealization

variable {M : RankTwoFiniteCorrespondenceMultiplication
  (k := k) (Ω := Ω)} {a b c : Fin 2 → Ω}
  (h : M.IsRealization a b c)

include h

/-- Every realization retains independence of its two input tuples. -/
theorem leftRight_independent :
    AlgebraicIndependent k (rankTwoPairTuple a b) := by
  let e : Fin 4 → Fin 6 := ![0, 1, 2, 3]
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.leftRight_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- Every realization retains independence of its left-input/output
tuples. -/
theorem leftOutput_independent :
    AlgebraicIndependent k (rankTwoPairTuple a c) := by
  let e : Fin 4 → Fin 6 := ![0, 1, 4, 5]
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.leftOutput_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- Every realization retains independence of its right-input/output
tuples. -/
theorem rightOutput_independent :
    AlgebraicIndependent k (rankTwoPairTuple b c) := by
  let e : Fin 4 → Fin 6 := ![2, 3, 4, 5]
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.rightOutput_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- In every realization, each output coordinate is algebraic over the
two input tuples. -/
theorem output_mem_left_right (i : Fin 2) :
    c i ∈ racl k (Set.range (rankTwoPairTuple a b)) := by
  let e : Fin 2 → Fin 6 := ![4, 5]
  let S : Set (Fin 6) := {0, 1, 2, 3}
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have himageM : M.tuple '' S =
      Set.range (rankTwoPairTuple M.left M.right) := by
    ext z
    simp [S, tuple, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  have ho : M.tuple (e i) ∈ racl k (M.tuple '' S) := by
    rw [himageM]
    fin_cases i
    · exact M.output_mem_left_right 0
    · exact M.output_mem_left_right 1
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : rankTwoTripleTuple a b c '' S =
      Set.range (rankTwoPairTuple a b) := by
    ext z
    simp [S, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  rw [himage] at ht
  fin_cases i <;> simpa [e, rankTwoTripleTuple] using ht

/-- In every realization, each right-input coordinate is algebraic over
the left input and output tuples. -/
theorem right_mem_left_output (i : Fin 2) :
    b i ∈ racl k (Set.range (rankTwoPairTuple a c)) := by
  let e : Fin 2 → Fin 6 := ![2, 3]
  let S : Set (Fin 6) := {0, 1, 4, 5}
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have himageM : M.tuple '' S =
      Set.range (rankTwoPairTuple M.left M.output) := by
    ext z
    simp [S, tuple, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  have ho : M.tuple (e i) ∈ racl k (M.tuple '' S) := by
    rw [himageM]
    fin_cases i
    · exact M.right_mem_left_output 0
    · exact M.right_mem_left_output 1
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : rankTwoTripleTuple a b c '' S =
      Set.range (rankTwoPairTuple a c) := by
    ext z
    simp [S, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  rw [himage] at ht
  fin_cases i <;> simpa [e, rankTwoTripleTuple] using ht

/-- In every realization, each left-input coordinate is algebraic over
the right input and output tuples. -/
theorem left_mem_right_output (i : Fin 2) :
    a i ∈ racl k (Set.range (rankTwoPairTuple b c)) := by
  let e : Fin 2 → Fin 6 := ![0, 1]
  let S : Set (Fin 6) := {2, 3, 4, 5}
  have hfull : M.ideal = idealOf k (rankTwoTripleTuple a b c) := h.symm
  have himageM : M.tuple '' S =
      Set.range (rankTwoPairTuple M.right M.output) := by
    ext z
    simp [S, tuple, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  have ho : M.tuple (e i) ∈ racl k (M.tuple '' S) := by
    rw [himageM]
    fin_cases i
    · exact M.left_mem_right_output 0
    · exact M.left_mem_right_output 1
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : rankTwoTripleTuple a b c '' S =
      Set.range (rankTwoPairTuple b c) := by
    ext z
    simp [S, rankTwoTripleTuple, rankTwoPairTuple]
    tauto
  rw [himage] at ht
  fin_cases i <;> simpa [e, rankTwoTripleTuple] using ht

/-- Replacing the output tuple by the right input does not change the
relative algebraic closure generated by a realization. -/
theorem racl_leftRight_eq_leftOutput :
    racl k (Set.range (rankTwoPairTuple a b)) =
      racl k (Set.range (rankTwoPairTuple a c)) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact h.right_mem_left_output 0
    · exact h.right_mem_left_output 1
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact h.output_mem_left_right 0
    · exact h.output_mem_left_right 1

/-- Replacing the left input by the output does not change the relative
algebraic closure generated by a realization. -/
theorem racl_leftRight_eq_rightOutput :
    racl k (Set.range (rankTwoPairTuple a b)) =
      racl k (Set.range (rankTwoPairTuple b c)) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · exact h.left_mem_right_output 0
    · exact h.left_mem_right_output 1
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
    · exact h.output_mem_left_right 0
    · exact h.output_mem_left_right 1

/-- In a surrounding four-block tuple, a realization permits replacing
its right input by its output without changing relative algebraic
closure. -/
theorem racl_four_leftRight_eq_leftOutput (p q : Fin 2 → Ω) :
    racl k (Set.range (rankTwoFourTuple a b p q)) =
      racl k (Set.range (rankTwoFourTuple a c p q)) := by
  have hp := h.racl_leftRight_eq_leftOutput
  rw [rankTwoPairTuple_range, rankTwoPairTuple_range] at hp
  have hu := racl_union_congr_left hp (Set.range p ∪ Set.range q)
  rw [rankTwoFourTuple_range, rankTwoFourTuple_range]
  simpa only [Set.union_assoc] using hu

/-- In a surrounding four-block tuple, a realization permits replacing
its output by its left input while retaining the right input. -/
theorem racl_four_outputRight_eq_leftRight (p q : Fin 2 → Ω) :
    racl k (Set.range (rankTwoFourTuple p c b q)) =
      racl k (Set.range (rankTwoFourTuple p a b q)) := by
  have hp := h.racl_leftRight_eq_rightOutput.symm
  rw [rankTwoPairTuple_range, rankTwoPairTuple_range] at hp
  have hp' :
      racl k (Set.range c ∪ Set.range b) =
        racl k (Set.range a ∪ Set.range b) := by
    rw [Set.union_comm (Set.range c) (Set.range b)]
    exact hp
  have hu := racl_union_congr_left hp' (Set.range p ∪ Set.range q)
  rw [rankTwoFourTuple_range, rankTwoFourTuple_range]
  simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hu

/-- In a surrounding four-block tuple, a realization permits replacing
its right input in the fourth position by its output. -/
theorem racl_four_firstRight_eq_firstOutput (p q : Fin 2 → Ω) :
    racl k (Set.range (rankTwoFourTuple a p q b)) =
      racl k (Set.range (rankTwoFourTuple a p q c)) := by
  have hp := h.racl_leftRight_eq_leftOutput
  rw [rankTwoPairTuple_range, rankTwoPairTuple_range] at hp
  have hu := racl_union_congr_left hp (Set.range p ∪ Set.range q)
  rw [rankTwoFourTuple_range, rankTwoFourTuple_range]
  simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hu

end IsRealization

/-- The locus has an output above every independent generic pair of
rank-two inputs. -/
theorem exists_output [IsAlgClosed Ω] {a b : Fin 2 → Ω}
    (hab : AlgebraicIndependent k (rankTwoPairTuple a b)) :
    ∃ c : Fin 2 → Ω, M.IsRealization a b c := by
  classical
  let e : Fin 4 → Fin 6 := ![0, 1, 2, 3]
  have he (i : Fin 4) :
      M.tuple (e i) = rankTwoPairTuple M.left M.right i := by
    fin_cases i <;> rfl
  have hmem (j : Fin 6) :
      M.tuple j ∈
        racl k (Set.range (rankTwoPairTuple M.left M.right)) := by
    fin_cases j
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
    · exact M.output_mem_left_right 0
    · exact M.output_mem_left_right 1
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    M.leftRight_independent hab he hmem
  let c : Fin 2 → Ω := ![v 4, v 5]
  refine ⟨c, ?_⟩
  have hvtuple : v = rankTwoTripleTuple a b c := by
    funext i
    fin_cases i
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (0 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (1 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (2 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (3 : Fin 4)
    · rfl
    · rfl
  change idealOf k (rankTwoTripleTuple a b c) = idealOf k M.tuple
  rw [← hvtuple]
  exact hv

/-- The locus solves right division above every independent generic
left-input/output pair. -/
theorem exists_right [IsAlgClosed Ω] {a c : Fin 2 → Ω}
    (hac : AlgebraicIndependent k (rankTwoPairTuple a c)) :
    ∃ b : Fin 2 → Ω, M.IsRealization a b c := by
  classical
  let e : Fin 4 → Fin 6 := ![0, 1, 4, 5]
  have he (i : Fin 4) :
      M.tuple (e i) = rankTwoPairTuple M.left M.output i := by
    fin_cases i <;> rfl
  have hmem (j : Fin 6) :
      M.tuple j ∈
        racl k (Set.range (rankTwoPairTuple M.left M.output)) := by
    fin_cases j
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact M.right_mem_left_output 0
    · exact M.right_mem_left_output 1
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    M.leftOutput_independent hac he hmem
  let b : Fin 2 → Ω := ![v 2, v 3]
  refine ⟨b, ?_⟩
  have hvtuple : v = rankTwoTripleTuple a b c := by
    funext i
    fin_cases i
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (0 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (1 : Fin 4)
    · rfl
    · rfl
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (2 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (3 : Fin 4)
  change idealOf k (rankTwoTripleTuple a b c) = idealOf k M.tuple
  rw [← hvtuple]
  exact hv

/-- The locus solves left division above every independent generic
right-input/output pair. -/
theorem exists_left [IsAlgClosed Ω] {b c : Fin 2 → Ω}
    (hbc : AlgebraicIndependent k (rankTwoPairTuple b c)) :
    ∃ a : Fin 2 → Ω, M.IsRealization a b c := by
  classical
  let e : Fin 4 → Fin 6 := ![2, 3, 4, 5]
  have he (i : Fin 4) :
      M.tuple (e i) = rankTwoPairTuple M.right M.output i := by
    fin_cases i <;> rfl
  have hmem (j : Fin 6) :
      M.tuple j ∈
        racl k (Set.range (rankTwoPairTuple M.right M.output)) := by
    fin_cases j
    · exact M.left_mem_right_output 0
    · exact M.left_mem_right_output 1
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    M.rightOutput_independent hbc he hmem
  let a : Fin 2 → Ω := ![v 0, v 1]
  refine ⟨a, ?_⟩
  have hvtuple : v = rankTwoTripleTuple a b c := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (0 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (1 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (2 : Fin 4)
    · simpa [e, rankTwoPairTuple, rankTwoTripleTuple] using hfix (3 : Fin 4)
  change idealOf k (rankTwoTripleTuple a b c) = idealOf k M.tuple
  rw [← hvtuple]
  exact hv

/-- The four multiplication/division edges of the rank-two difference
chart.  The notation is relational: the selected output tuples need not be
unique. -/
structure FourArrowDifferenceDiagram
    (s a b e : Fin 2 → Ω) where
  /-- A selected output of `s · e`. -/
  u : Fin 2 → Ω
  /-- A selected left quotient solving `sA · a = u`. -/
  sA : Fin 2 → Ω
  /-- A selected output of `s · b`. -/
  uB : Fin 2 → Ω
  /-- The selected difference output solving `sA · c = uB`. -/
  c : Fin 2 → Ω
  /-- The edge `u = s · e`. -/
  se_u : M.IsRealization s e u
  /-- The edge `sA · a = u`. -/
  sA_a_u : M.IsRealization sA a u
  /-- The edge `uB = s · b`. -/
  s_b_uB : M.IsRealization s b uB
  /-- The edge `sA · c = uB`. -/
  sA_c_uB : M.IsRealization sA c uB

/-- Four independent generic rank-two inputs admit the complete four-arrow
difference diagram.  Each of the first three edges replaces one
interalgebraic two-coordinate block in the ambient eight-tuple.  Its
relative algebraic closure and exact rank therefore remain unchanged, so
the final left-input/output pair is an independent generic pair and the
last division edge can be relocated. -/
theorem exists_fourArrowDifferenceDiagram [IsAlgClosed Ω]
    {s e a b : Fin 2 → Ω}
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Nonempty (M.FourArrowDifferenceDiagram s a b e) := by
  classical
  have hse : AlgebraicIndependent k (rankTwoPairTuple s e) := by
    let f : Fin 4 → Fin 8 := ![0, 1, 2, 3]
    have ht := AlgebraicIndependent.comp hind f (by decide)
    convert ht using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨u, hu⟩ := M.exists_output hse
  have hRu : M.IsRealization s e u := hu
  have hq1 : AlgebraicIndependent k (rankTwoFourTuple s u a b) :=
    algebraicIndependent_of_racl_range_eq hind
      (hRu.racl_four_leftRight_eq_leftOutput a b)
  have hau : AlgebraicIndependent k (rankTwoPairTuple a u) := by
    let f : Fin 4 → Fin 8 := ![4, 5, 2, 3]
    have ht := AlgebraicIndependent.comp hq1 f (by decide)
    convert ht using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨sA, hsA⟩ := M.exists_left hau
  have hRsA : M.IsRealization sA a u := hsA
  have hq2 : AlgebraicIndependent k (rankTwoFourTuple s sA a b) :=
    algebraicIndependent_of_racl_range_eq hq1
      (hRsA.racl_four_outputRight_eq_leftRight s b)
  have hsb : AlgebraicIndependent k (rankTwoPairTuple s b) := by
    let f : Fin 4 → Fin 8 := ![0, 1, 6, 7]
    have ht := AlgebraicIndependent.comp hq2 f (by decide)
    convert ht using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨uB, huB⟩ := M.exists_output hsb
  have hRuB : M.IsRealization s b uB := huB
  have hq3 : AlgebraicIndependent k (rankTwoFourTuple s sA a uB) :=
    algebraicIndependent_of_racl_range_eq hq2
      (hRuB.racl_four_firstRight_eq_firstOutput sA a)
  have hsa_uB : AlgebraicIndependent k (rankTwoPairTuple sA uB) := by
    let f : Fin 4 → Fin 8 := ![2, 3, 6, 7]
    have ht := AlgebraicIndependent.comp hq3 f (by decide)
    convert ht using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨c, hc⟩ := M.exists_right hsa_uB
  exact ⟨{
    u := u
    sA := sA
    uB := uB
    c := c
    se_u := hRu
    sA_a_u := hRsA
    s_b_uB := hRuB
    sA_c_uB := hc }⟩

end RankTwoFiniteCorrespondenceMultiplication

end

end AclGeom
