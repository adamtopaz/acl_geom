/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.GenericNegation

/-!
# The true existence half of the literal total nonzero addition

Blueprint Lemma `total-nonzero-add` asserts that for `x, y, x + y ∉ acl_k(a)` the detour
`JAddTotalNZ(j(x, a), j(y, a), w)` has the single output `w = j(x + y, a)`.  Uniqueness fails for
the literal predicates (`blueprintJAddTotalNZ_not_functional`).  The existence of the sum output
is true under exactly the stated hypotheses, with no joint independence of `x` and `y`
(`blueprintJAddTotalNZ_of_pairs`).

The detour follows the source.  For `z` outside `acl_k(x, y, a)`, the negation
`JNeg(j(z, a), j(-z, a))` and the three generic additions `x + z`, `y - z` and
`(x + z) + (y - z) = x + y` witness `JAddTotalNZ(j(x, a), j(y, a), j(x + y, a))`.  The last
addition is generic because `x + y ∉ acl_k(a)`: otherwise exchange would put `z` in
`acl_k(x, y, a)`.  All auxiliary tuples lie in the Frobenius class of any `j(x₀, a)`.

The fresh element raises the rank by one over `x, y, a`, within the rank-five bound.  The base and
ambient fields are arbitrary; no perfection, infinite base or completeness input is used.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the existence half of Lemma `total-nonzero-add` is proved (#8, #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The literal total nonzero addition has the sum output** (blueprint Lemma
`total-nonzero-add`, existence).  For `x, y, x + y` independent from `a`, the detour relates
`j(x, a)` and `j(y, a)` to `j(x + y, a)` on the Frobenius class of any semantic base tuple
`j(x₀, a)`, at rank five over arbitrary fields.  No joint independence of `x` and `y` is
assumed. -/
theorem blueprintJAddTotalNZ_of_pairs (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {x₀ x y a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hx : AlgebraicIndependent k ![x, a]) (hy : AlgebraicIndependent k ![y, a])
    (hxy : AlgebraicIndependent k ![x + y, a]) :
    BlueprintJAddTotalNZ (jTupleOf x₀ a h₀) (jTupleOf x a hx) (jTupleOf y a hy)
      (jTupleOf (x + y) a hxy) := by
  classical
  obtain ⟨z, hz⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  have hz' : z ∉ racl k ({x, y, a} : Set K) := by simpa using hz
  have hxF : x ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (Set.mem_insert x _)
  have hyF : y ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem x (Set.mem_insert y _))
  have haF : a ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem x (Set.mem_insert_of_mem y rfl))
  have hsub : ∀ {p : K}, p ∈ racl k ({x, y, a} : Set K) → z ∉ racl k ({p, a} : Set K) :=
    fun hp hm ↦ hz' (racl_le_of_subset_racl (by
      rintro w (rfl | rfl)
      · exact hp
      · exact haF) hm)
  have hm1 : (-1 : k) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- The addition triples `(x, z, a)`, `(y, -z, a)` and `(x + z, y - z, a)`.
  have T₁ : AlgebraicIndependent k ![x, z, a] := AlgebraicIndependent.insert_middle hx (hsub hxF)
  have hza : AlgebraicIndependent k ![z, a] := AlgebraicIndependent.pair_one_two T₁
  have T₂ : AlgebraicIndependent k ![y, algebraMap k K (-1) * z, a] := by
    refine AlgebraicIndependent.insert_middle hy fun h ↦ hsub hyF ?_
    exact mem_racl_of_eq (show z = algebraMap k K (-1) * (algebraMap k K (-1) * z) by
      rw [map_neg, map_one]; ring) (mul_mem (IntermediateField.algebraMap_mem _ (-1 : k)) h)
  have hr : AlgebraicIndependent k ![x + z, a] := JArith.pair_add_a T₁
  have hs : AlgebraicIndependent k ![y + algebraMap k K (-1) * z, a] := JArith.pair_add_a T₂
  have T₃ : AlgebraicIndependent k ![x + z, y + algebraMap k K (-1) * z, a] := by
    refine AlgebraicIndependent.insert_middle hr fun h ↦ hz' ?_
    -- Otherwise `x + y` lies in `racl_k {x + z, a}`, and exchange puts `x + z`, hence `z`,
    -- in `racl_k {x, y, a}`.
    have hsum : x + y ∈ racl k (insert (x + z) ({a} : Set K)) :=
      mem_racl_of_eq (show x + y = (y + algebraMap k K (-1) * z) + (x + z) by
          rw [map_neg, map_one]; ring)
        (add_mem h (subset_racl k _ (Set.mem_insert _ _)))
    have hle : racl k (insert (x + y) ({a} : Set K)) ≤ racl k ({x, y, a} : Set K) :=
      racl_le_of_subset_racl (by
        rintro w (rfl | rfl)
        · exact add_mem hxF hyF
        · exact haF)
    exact mem_racl_of_eq (show z = x + z - x by ring)
      (sub_mem (hle (racl_exchange hsum (AlgebraicIndependent.notMem_racl_pair' hxy))) hxF)
  -- The three generic additions, with their outputs packaged and normalized.
  obtain ⟨r, _, A₁, hreq⟩ : ∃ (r : K) (hr' : AlgebraicIndependent k ![r, a]),
      BlueprintJAdd (jTupleOf x a hx) (jTupleOf z a hza) (jTupleOf r a hr') ∧
        r = algebraMap k K 1 * x + z :=
    ⟨_, _, blueprintJAdd_kappa T₁ htr one_ne_zero, rfl⟩
  rw [map_one, one_mul] at hreq
  subst hreq
  obtain ⟨s, _, A₂, hseq⟩ : ∃ (s : K) (hs' : AlgebraicIndependent k ![s, a]),
      BlueprintJAdd (jTupleOf y a hy)
        (jTupleOf (algebraMap k K (-1) * z) a (AlgebraicIndependent.smul_left hza hm1))
        (jTupleOf s a hs') ∧ s = algebraMap k K 1 * y + algebraMap k K (-1) * z :=
    ⟨_, _, blueprintJAdd_kappa T₂ htr one_ne_zero, rfl⟩
  rw [map_one, one_mul] at hseq
  subst hseq
  obtain ⟨w, _, A₃, hweq⟩ : ∃ (w : K) (hw : AlgebraicIndependent k ![w, a]),
      BlueprintJAdd (jTupleOf (x + z) a hr) (jTupleOf (y + algebraMap k K (-1) * z) a hs)
        (jTupleOf w a hw) ∧ w = algebraMap k K 1 * (x + z) + (y + algebraMap k K (-1) * z) :=
    ⟨_, _, blueprintJAdd_kappa T₃ htr one_ne_zero, rfl⟩
  rw [show algebraMap k K 1 * (x + z) + (y + algebraMap k K (-1) * z) = x + y by
    rw [map_neg, map_one]; ring] at hweq
  subst hweq
  -- The four auxiliary tuples and the detour.
  exact ⟨jTupleOf z a hza,
    jTupleOf (algebraMap k K (-1) * z) a (AlgebraicIndependent.smul_left hza hm1),
    jTupleOf (x + z) a hr, jTupleOf (y + algebraMap k K (-1) * z) a hs,
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    blueprintJNeg_smul htr h₀ hza hm1, A₁, A₂, A₃⟩

end AclGeom
