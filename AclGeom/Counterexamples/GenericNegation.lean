/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.GenericArithmetic
import AclGeom.Interpretation.JArithSem

/-!
# The blueprint's negation and total nonzero addition are not functional

Validation for issue #23, continuing `AclGeom.Counterexamples.GenericArithmetic`.  On the
Frobenius class `J₁ = [j(x₀, a)]`, the blueprint generic-arithmetic section (`sec:genericops`)
defines a negation detour through two literal additions,
`JNeg(u, v) ⇔ ∃ z r ∈ J₁, JAdd(u, z, r) ∧ JAdd(v, r, z)`,
and claims `JNeg(j(x, a), j(y, a)) ⇔ y = -x`.  Its Lemma `total-nonzero-add` claims, for
`x, y, x + y ∉ acl_k(a)`, that the detour
`JAddTotalNZ(u, v, w) ⇔ ∃ z nz r s, JNeg(z, nz) ∧ JAdd(u, z, r) ∧ JAdd(v, nz, s) ∧ JAdd(r, s, w)`
has the single output `j(x + y, a)`.

Both claims fail, because the literal `JAdd` accepts the output `j(κp + q, a)` for every
`κ ∈ kˣ` (`blueprintJAdd_kappa`):

* with `z` fresh and `r = -cx + z`, the additions `JAdd(j(x, a), j(z, a), j(r, a))` (`κ = -c`)
  and `JAdd(j(cx, a), j(r, a), j(z, a))` (`κ = 1`) witness `JNeg(j(x, a), j(cx, a))` for every
  `c ∈ kˣ` (`blueprintJNeg_smul`).  For `c ≠ -1` the tuples `j(cx, a)` and `j(-x, a)` differ
  (`blueprintJNeg_not_functional`).  If `2 ≠ 0` in `k`, then `c = 1` makes every generic
  `j(x, a)` its own literal negation (`blueprintJNeg_self`);
* with `z` fresh, `nz = j(-z, a)`, `r = j(κx + z, a)` and `s = j(y - z, a)`, the detour outputs
  `j(κx + y, a)` for every `κ ∈ kˣ` (`blueprintJAddTotalNZ_kappa`).  This differs from
  `j(x + y, a)` for `κ ≠ 1` (`blueprintJAddTotalNZ_not_functional`).

The blueprint defines `JAdd` only on `J₁`, so `BlueprintJAddTotalNZ` requires its four auxiliary
tuples to lie in `J₁`, and `BlueprintJNeg` requires its two witnesses to lie there, as displayed.
Every tuple used here is `j(t, a)` for the literal parameter `a`, so class membership follows
from `frobEq_jTupleOf_of_common`.  Only rank-five soundness is used; no completeness input
appears. The scalar families and conditional counterexamples for a specified scalar work
over arbitrary base fields at rank five. The existential `_on_class` counterexamples use
an infinite base to choose a nontrivial scalar. The corrected counterparts `JNegTotalRel`
and `JAddTotalNZRel` are in `AclGeom.Interpretation.TotalOps`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (refutation for issue #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Defs

/-- The negation graph of the blueprint generic-arithmetic section, stated literally relative to
the Frobenius class `J₁ = [b]`: `JNeg(u, v)` when there are `z, r ∈ J₁` with `JAdd(u, z, r)` and
`JAdd(v, r, z)`.  It is not functional (`blueprintJNeg_not_functional`). -/
def BlueprintJNeg (b u v : Fin 5 → Point k K) : Prop :=
  ∃ z r : Fin 5 → Point k K, FrobEq b z ∧ FrobEq b r ∧ BlueprintJAdd u z r ∧ BlueprintJAdd v r z

/-- The total nonzero addition of the blueprint generic-arithmetic section, stated literally
relative to the Frobenius class `J₁ = [b]`.  The blueprint defines `JAdd` only on `J₁`, so the
four auxiliary tuples are required to lie in `J₁`.  It is not functional
(`blueprintJAddTotalNZ_not_functional`). -/
def BlueprintJAddTotalNZ (b u v w : Fin 5 → Point k K) : Prop :=
  ∃ z nz r s : Fin 5 → Point k K, FrobEq b z ∧ FrobEq b nz ∧ FrobEq b r ∧ FrobEq b s ∧
    BlueprintJNeg b z nz ∧ BlueprintJAdd u z r ∧ BlueprintJAdd v nz s ∧ BlueprintJAdd r s w

end Defs

/-- Rescaling the first entry of an independent triple by a nonzero constant keeps it
independent. -/
private theorem triple_smul_left {x y a : K} (hind : AlgebraicIndependent k ![x, y, a])
    {κ : k} (hκ : κ ≠ 0) : AlgebraicIndependent k ![algebraMap k K κ * x, y, a] := by
  refine (algebraicIndependent_congr_racl (v := ![x, y, a])
    (w := ![algebraMap k K κ * x, y, a]) fun i ↦ ?_).1 hind
  fin_cases i
  · exact (racl_algebraMap_mul hκ x).symm
  · rfl
  · rfl

variable [Infinite k] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)

include htr

section Negation

omit [Infinite k] in
/-- **The κ-family satisfies the blueprint negation**: for every `c ∈ kˣ`,
`JNeg(j(x, a), j(cx, a))` on the class of any `j(x₀, a)`. -/
theorem blueprintJNeg_smul {x₀ x a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hx : AlgebraicIndependent k ![x, a]) {c : k} (hc : c ≠ 0) :
    BlueprintJNeg (jTupleOf x₀ a h₀) (jTupleOf x a hx)
      (jTupleOf (algebraMap k K c * x) a (AlgebraicIndependent.smul_left hx hc)) := by
  classical
  obtain ⟨z, hz⟩ := fresh_four_of_five_le_trdeg htr {x, a}
    (Finset.card_le_two.trans (by norm_num))
  have hz' : z ∉ racl k ({x, a} : Set K) := by simpa using hz
  have hxm : x ∈ racl k ({x, a} : Set K) := subset_racl k _ (Set.mem_insert x _)
  -- The two addition triples `(x, z, a)` and `(cx, -cx + z, a)`.
  have T₁ : AlgebraicIndependent k ![x, z, a] := AlgebraicIndependent.insert_middle hx hz'
  have T₂ : AlgebraicIndependent k ![algebraMap k K c * x, algebraMap k K (-c) * x + z, a] := by
    refine AlgebraicIndependent.insert_middle (AlgebraicIndependent.smul_left hx hc)
      fun h ↦ hz' ?_
    have hle : racl k ({algebraMap k K c * x, a} : Set K) ≤ racl k ({x, a} : Set K) :=
      racl_le_of_subset_racl (by
        rintro w (rfl | rfl)
        · exact mul_mem (IntermediateField.algebraMap_mem _ c) hxm
        · exact subset_racl k _ (Set.mem_insert_of_mem x rfl))
    exact mem_racl_of_eq (show z = algebraMap k K (-c) * x + z - algebraMap k K (-c) * x by ring)
      (sub_mem (hle h) (mul_mem (IntermediateField.algebraMap_mem _ (-c)) hxm))
  refine ⟨jTupleOf z a (AlgebraicIndependent.pair_one_two T₁),
    jTupleOf (algebraMap k K (-c) * x + z) a (AlgebraicIndependent.pair_one_two T₂),
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    blueprintJAdd_kappa T₁ htr (neg_ne_zero.2 hc), ?_⟩
  convert blueprintJAdd_kappa T₂ htr one_ne_zero using 1
  exact jTupleOf_congr _ _ (by rw [map_one, map_neg]; ring)

omit [Infinite k] in
/-- **The blueprint negation is not functional** (issue #23): for `c ∉ {0, -1}`, both `j(cx, a)`
and `j(-x, a)` are `JNeg`-partners of `j(x, a)`, and they are distinct.  This refutes the claim
`JNeg(j(x, a), j(y, a)) ⇔ y = -x`. -/
theorem blueprintJNeg_not_functional {x₀ x a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hx : AlgebraicIndependent k ![x, a]) {c : k} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    BlueprintJNeg (jTupleOf x₀ a h₀) (jTupleOf x a hx)
        (jTupleOf (algebraMap k K c * x) a (AlgebraicIndependent.smul_left hx hc)) ∧
      BlueprintJNeg (jTupleOf x₀ a h₀) (jTupleOf x a hx)
        (jTupleOf (algebraMap k K (-1) * x) a
          (AlgebraicIndependent.smul_left hx (neg_ne_zero.2 one_ne_zero))) ∧
      jTupleOf (algebraMap k K c * x) a (AlgebraicIndependent.smul_left hx hc) ≠
        jTupleOf (algebraMap k K (-1) * x) a
          (AlgebraicIndependent.smul_left hx (neg_ne_zero.2 one_ne_zero)) := by
  refine ⟨blueprintJNeg_smul htr h₀ hx hc,
    blueprintJNeg_smul htr h₀ hx (neg_ne_zero.2 one_ne_zero), fun h ↦ ?_⟩
  have h1 := congrArg (fun t ↦ (t 1).1) h
  simp only [jTupleOf_one] at h1
  have hx0 : x ∉ racl k (∅ : Set K) := fun h' ↦
    AlgebraicIndependent.notMem_racl_pair' hx (racl_mono (Set.empty_subset _) h')
  have hxx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
  refine point_ne_of_sub (κ := c + 1) (r := x) (fun h' ↦ hc1 (eq_neg_of_add_eq_zero_left h'))
    ?_ hx0 (fun h' ↦ ?_) h1
  · rw [map_add, map_neg, map_one]
    ring
  · exact AlgebraicIndependent.notMem_racl_pair hx (mem_racl_of_eq
      (show a = algebraMap k K (-1) * x + a - x + (x + x) by rw [map_neg, map_one]; ring)
      (add_mem h' (add_mem hxx hxx)))

omit [Infinite k] in
/-- **Every generic tuple is its own blueprint negation** when `2 ≠ 0` in `k`:
`JNeg(j(x, a), j(x, a))` holds although `j(x, a) ≠ j(-x, a)`. -/
theorem blueprintJNeg_self {x₀ x a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hx : AlgebraicIndependent k ![x, a]) (h2 : (2 : k) ≠ 0) :
    BlueprintJNeg (jTupleOf x₀ a h₀) (jTupleOf x a hx) (jTupleOf x a hx) ∧
      jTupleOf x a hx ≠ jTupleOf (algebraMap k K (-1) * x) a
        (AlgebraicIndependent.smul_left hx (neg_ne_zero.2 one_ne_zero)) := by
  obtain ⟨h1, -, h3⟩ := blueprintJNeg_not_functional htr h₀ hx one_ne_zero
    fun h ↦ h2 (by linear_combination h)
  have e : jTupleOf (algebraMap k K 1 * x) a (AlgebraicIndependent.smul_left hx one_ne_zero) =
      jTupleOf x a hx :=
    jTupleOf_congr _ _ (by rw [map_one, one_mul])
  rw [e] at h1 h3
  exact ⟨h1, h3⟩

/-- **The blueprint negation is not functional on one Frobenius class**: there are `u, v₁, v₂`
all Frobenius-equivalent to `u` (so in the class `J₁ = [u]`) with `JNeg(u, v₁)`, `JNeg(u, v₂)`
and `v₁ ≠ v₂`. -/
theorem blueprintJNeg_not_functional_on_class :
    ∃ u v₁ v₂ : Fin 5 → Point k K, FrobEq u u ∧ FrobEq u v₁ ∧ FrobEq u v₂ ∧
      BlueprintJNeg u u v₁ ∧ BlueprintJNeg u u v₂ ∧ v₁ ≠ v₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  have hx := AlgebraicIndependent.pair_zero_two hind
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, -1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨h1, h2, h3⟩ := blueprintJNeg_not_functional htr hx hx hc.1 hc.2
  exact ⟨_, _, _, frobEq_jTupleOf_of_common htr hx hx, frobEq_jTupleOf_of_common htr hx _,
    frobEq_jTupleOf_of_common htr hx _, h1, h2, h3⟩

end Negation

section TotalNonzeroAddition

omit [Infinite k] in
/-- **The κ-family satisfies the blueprint total nonzero addition**: for independent `x, y, a`
and every `κ ∈ kˣ`, `JAddTotalNZ(j(x, a), j(y, a), j(κx + y, a))` on the class of any
`j(x₀, a)`. -/
theorem blueprintJAddTotalNZ_kappa {x₀ x y a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (hind : AlgebraicIndependent k ![x, y, a]) {κ : k} (hκ : κ ≠ 0) :
    BlueprintJAddTotalNZ (jTupleOf x₀ a h₀) (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
      (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
      (jTupleOf (algebraMap k K κ * x + y) a (JArith.pair_add_a (triple_smul_left hind hκ))) := by
  classical
  obtain ⟨z, hz⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  have hz' : z ∉ racl k ({x, y, a} : Set K) := by simpa using hz
  have hx : x ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (Set.mem_insert x _)
  have hy : y ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem x (Set.mem_insert y _))
  have ha : a ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem x (Set.mem_insert_of_mem y rfl))
  have hsub : ∀ {p q : K}, p ∈ racl k ({x, y, a} : Set K) → q ∈ racl k ({x, y, a} : Set K) →
      z ∉ racl k ({p, q} : Set K) := fun hp hq hm ↦ hz' (racl_le_of_subset_racl (by
        rintro w (rfl | rfl)
        · exact hp
        · exact hq) hm)
  have hm1 : (-1 : k) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- The three addition triples `(x, z, a)`, `(y, -z, a)` and `(κx + z, y - z, a)`.
  have T₁ : AlgebraicIndependent k ![x, z, a] :=
    AlgebraicIndependent.insert_middle (AlgebraicIndependent.pair_zero_two hind) (hsub hx ha)
  have hza : AlgebraicIndependent k ![z, a] := AlgebraicIndependent.pair_one_two T₁
  have T₂ : AlgebraicIndependent k ![y, algebraMap k K (-1) * z, a] := by
    refine AlgebraicIndependent.insert_middle (AlgebraicIndependent.pair_one_two hind)
      fun h ↦ hsub hy ha ?_
    simpa using mul_mem (IntermediateField.algebraMap_mem _ (-1 : k)) h
  have hr : AlgebraicIndependent k ![algebraMap k K κ * x + z, a] :=
    JArith.pair_add_a (triple_smul_left T₁ hκ)
  have hw : AlgebraicIndependent k ![algebraMap k K κ * x + y, a] :=
    JArith.pair_add_a (triple_smul_left hind hκ)
  have T₃ : AlgebraicIndependent k
      ![algebraMap k K κ * x + z, algebraMap k K 1 * y + algebraMap k K (-1) * z, a] := by
    refine AlgebraicIndependent.insert_middle hr fun h ↦ hz' ?_
    -- Otherwise `κx + y = r + s` lies in `racl_k {r, a}`, and exchange puts `r`, hence `z`,
    -- in `racl_k {x, y, a}`.
    have hsum : algebraMap k K κ * x + y ∈
        racl k (insert (algebraMap k K κ * x + z) ({a} : Set K)) :=
      mem_racl_of_eq (show algebraMap k K κ * x + y =
          (algebraMap k K 1 * y + algebraMap k K (-1) * z) + (algebraMap k K κ * x + z) by
            rw [map_neg, map_one]; ring)
        (add_mem h (subset_racl k _ (Set.mem_insert _ _)))
    have hle : racl k (insert (algebraMap k K κ * x + y) ({a} : Set K)) ≤
        racl k ({x, y, a} : Set K) :=
      racl_le_of_subset_racl (by
        rintro w (rfl | rfl)
        · exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ κ) hx) hy
        · exact ha)
    exact mem_racl_of_eq (show z = algebraMap k K κ * x + z - algebraMap k K κ * x by ring)
      (sub_mem (hle (racl_exchange hsum (AlgebraicIndependent.notMem_racl_pair' hw)))
        (mul_mem (IntermediateField.algebraMap_mem _ κ) hx))
  refine ⟨jTupleOf z a hza,
    jTupleOf (algebraMap k K (-1) * z) a (AlgebraicIndependent.smul_left hza hm1),
    jTupleOf (algebraMap k K κ * x + z) a hr,
    jTupleOf (algebraMap k K 1 * y + algebraMap k K (-1) * z) a
      (AlgebraicIndependent.pair_one_two T₃),
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    blueprintJNeg_smul htr h₀ hza hm1, blueprintJAdd_kappa T₁ htr hκ,
    blueprintJAdd_kappa T₂ htr one_ne_zero, ?_⟩
  convert blueprintJAdd_kappa T₃ htr one_ne_zero using 1
  exact jTupleOf_congr _ _ (by rw [map_neg, map_one]; ring)

omit [Infinite k] in
/-- **Blueprint Lemma `total-nonzero-add` fails** (issue #23): for independent `x, y, a` and
`κ ∉ {0, 1}`, both `j(κx + y, a)` and `j(x + y, a)` are `JAddTotalNZ`-outputs of
`(j(x, a), j(y, a))`, and they are distinct. -/
theorem blueprintJAddTotalNZ_not_functional {x₀ x y a : K}
    (h₀ : AlgebraicIndependent k ![x₀, a]) (hind : AlgebraicIndependent k ![x, y, a]) {κ : k}
    (hκ : κ ≠ 0) (hκ1 : κ ≠ 1) :
    BlueprintJAddTotalNZ (jTupleOf x₀ a h₀) (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K κ * x + y) a (JArith.pair_add_a (triple_smul_left hind hκ))) ∧
      BlueprintJAddTotalNZ (jTupleOf x₀ a h₀)
        (jTupleOf x a (AlgebraicIndependent.pair_zero_two hind))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two hind))
        (jTupleOf (algebraMap k K 1 * x + y) a
          (JArith.pair_add_a (triple_smul_left hind one_ne_zero))) ∧
      jTupleOf (algebraMap k K κ * x + y) a (JArith.pair_add_a (triple_smul_left hind hκ)) ≠
        jTupleOf (algebraMap k K 1 * x + y) a
          (JArith.pair_add_a (triple_smul_left hind one_ne_zero)) :=
  ⟨blueprintJAddTotalNZ_kappa htr h₀ hind hκ, blueprintJAddTotalNZ_kappa htr h₀ hind one_ne_zero,
    (blueprintJAdd_not_functional hind htr hκ hκ1).2.2⟩

/-- **The blueprint total nonzero addition is not functional on one Frobenius class**: there are
`u, v, w₁, w₂` all Frobenius-equivalent to `u` (so in the class `J₁ = [u]`) with
`JAddTotalNZ(u, v, w₁)`, `JAddTotalNZ(u, v, w₂)` and `w₁ ≠ w₂`.  The inputs are `j(x, a)` and
`j(y, a)` for independent `x, y, a`, so they satisfy the hypotheses of Lemma
`total-nonzero-add`. -/
theorem blueprintJAddTotalNZ_not_functional_on_class :
    ∃ u v w₁ w₂ : Fin 5 → Point k K, FrobEq u u ∧ FrobEq u v ∧ FrobEq u w₁ ∧ FrobEq u w₂ ∧
      BlueprintJAddTotalNZ u u v w₁ ∧ BlueprintJAddTotalNZ u u v w₂ ∧ w₁ ≠ w₂ := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  have hx := AlgebraicIndependent.pair_zero_two hind
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hκ
  obtain ⟨h1, h2, h3⟩ := blueprintJAddTotalNZ_not_functional htr hx hind hκ.1 hκ.2
  exact ⟨_, _, _, _, frobEq_jTupleOf_of_common htr hx hx, frobEq_jTupleOf_of_common htr hx _,
    frobEq_jTupleOf_of_common htr hx _, frobEq_jTupleOf_of_common htr hx _, h1, h2, h3⟩

end TotalNonzeroAddition

end AclGeom
