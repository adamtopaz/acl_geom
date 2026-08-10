/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family

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

end RankTwoFiniteCorrespondenceMultiplication

end

end AclGeom
