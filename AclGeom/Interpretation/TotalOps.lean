/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Ratio

/-!
# Corrected total operations on the fixed Frobenius class: negation and nonzero addition

Blueprint §genericops avoids the non-point `[0]` and defines negation on the fixed class
`J₁ = [j(x₀, a)]_FrobEq` by a detour through two generic additions,
`JNeg(u, v) ⇔ ∃ z r ∈ J₁, JAdd(u, z, r) ∧ JAdd(v, r, z)`, asserting
`JNeg(j(x, a), j(y, a)) ⇔ y = -x`.  That detour is a preserved historical proposal built on the
literal `JAdd`, whose generic semantics is refuted (#23); its own status stays open.  Here the
corrected counterpart `JNegTotalRel` uses the coupled sum `JAddRel` with the blueprint's genericity
clause `PointTripleIndependent` for each addition, and the witnesses are class members.

`jNegTotalRel_iff`: for class members `u, v`, `JNegTotalRel j₀ u v` holds exactly when
`μ(v) = -μ(u)`.

* Forward, for every witness: the two additions say `μ(r) = μ(u) + μ(z)` and
  `μ(z) = μ(v) + μ(r)` (`JAddRel.jClassEquiv_add`), so `μ(v) = -μ(u)`.
* Converse: for `u = j(x, a)` and `v = j(-x, a)`, take `z` outside `racl_k {a, x}` and `r = x + z`.
  The triples `(x, z, a)` and `(-x, x + z, a)` are independent (`insert_middle`, then a birational
  change `triple_of_mem`), so both additions are generic.

`K` is perfect of rank at least five, and completeness over `k̄ ⊆ K̄` (`hcomp`) stays explicit.

`JAddTotalNZRel` follows the nonzero-addition detour: fresh `z` gives the three generic sums
`x + z`, `y - z` and their sum. Its forward direction derives output class membership; its
converse assumes only membership and the coordinate equality, without input genericity.
The class corresponds to `K \ racl k {a}`, so the output condition is stronger than merely
being nonzero in `K`.

**Status:** both corrected geometric detours have exact coordinate semantics under explicit
perfection, rank-five and ACF J-completeness inputs (#23). `Field` proves corrected total
geometric graphs, a named transported field structure and the actual decoding ring equivalence
on the ratio carrier under the same inputs. Graph naturality and reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open ClosedIF JArith

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Corrected geometric negation on the fixed class** (the corrected counterpart of the
blueprint's `JNeg` detour): there are class members `z, r` with `u + z = r` and `v + r = z`, both
coupled additions generic. -/
def JNegTotalRel (j₀ u v : Fin 5 → Point k K) : Prop :=
  ∃ z r : Fin 5 → Point k K, FrobEq j₀ z ∧ FrobEq j₀ r ∧
    (JAddRel u z r ∧ PointTripleIndependent (u 0) (z 0) (u 4)) ∧
    (JAddRel v r z ∧ PointTripleIndependent (v 0) (r 0) (v 4))

/-- **Negation semantics, forward**: any witness of the corrected negation relation between class
members forces `μ(v) = -μ(u)`. -/
theorem JNegTotalRel.neg_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (h : JNegTotalRel (jTupleOf x₀ a h₀) u v) :
    (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) = -(jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) := by
  obtain ⟨z, r, hz, hr, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩⟩ := h
  obtain ⟨_hr', e₁⟩ := JAddRel.jClassEquiv_add q htr hcomp h₀ hu hz g₁ m₁
  obtain ⟨_hz', e₂⟩ := JAddRel.jClassEquiv_add q htr hcomp h₀ hv hr g₂ m₂
  have e₁' : (jClassEquiv q htr hcomp h₀ ⟨r, hr⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨z, hz⟩ : K) := e₁
  have e₂' : (jClassEquiv q htr hcomp h₀ ⟨z, hz⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨r, hr⟩ : K) := e₂
  linear_combination -e₁' - e₂'

/-- **Negation semantics, converse**: class members with `μ(v) = -μ(u)` satisfy the corrected
negation relation.  One element fresh over the parameter and `μ(u)` supplies both witnesses. -/
theorem jNegTotalRel_of_neg_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (h : (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) = -(jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K)) :
    JNegTotalRel (jTupleOf x₀ a h₀) u v := by
  classical
  -- Present both class members with the literal parameter `a`; then `y = -x`.
  obtain ⟨x, hx, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hu
  obtain ⟨y, hy, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hv
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf] at h
  -- A fresh `z` over `a, x`.
  obtain ⟨z, hz⟩ := fresh_three_of_five_le_trdeg htr {a, x}
    (Finset.card_le_two.trans (by norm_num))
  have hz' : z ∉ racl k ({x, a} : Set K) := by
    rw [Set.pair_comm]
    simpa using hz
  -- The two generic triples `(x, z, a)` and `(-x, x + z, a)`.
  have T₁ : AlgebraicIndependent k ![x, z, a] := AlgebraicIndependent.insert_middle hx hz'
  have T₂ : AlgebraicIndependent k ![-x, x + z, a] := by
    refine AlgebraicIndependent.triple_of_mem T₁ (fun i ↦ ?_) (fun i ↦ ?_)
    · have hr := fun i ↦ subset_racl k (Set.range ![x, z, a]) (Set.mem_range_self i)
      fin_cases i
      · exact neg_mem (hr 0)
      · exact add_mem (hr 0) (hr 1)
      · exact hr 2
    · have hr := fun i ↦ subset_racl k (Set.range ![-x, x + z, a]) (Set.mem_range_self i)
      fin_cases i
      · change x ∈ _
        exact mem_racl_of_eq (neg_neg x).symm (neg_mem (hr 0))
      · change z ∈ _
        exact mem_racl_of_eq (by ring)
          (add_mem (hr 1) (hr 0) : x + z + -x ∈ racl k (Set.range ![-x, x + z, a]))
      · exact hr 2
  -- The witnesses `j(z, a)` and `j(x + z, a)`.
  have e₂ : jTupleOf (-x + (x + z)) a (pair_add_a T₂) =
      jTupleOf z a (AlgebraicIndependent.pair_one_two T₁) :=
    jTupleOf_congr _ _ (by ring)
  have ev : jTupleOf y a hy = jTupleOf (-x) a (AlgebraicIndependent.pair_zero_two T₂) :=
    jTupleOf_congr _ _ h
  rw [ev]
  exact ⟨jTupleOf z a (AlgebraicIndependent.pair_one_two T₁), jTupleOf (x + z) a (pair_add_a T₁),
    frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _,
    ⟨jAddRel_jTupleOf T₁, pointTripleIndependent_jTupleOf T₁⟩,
    ⟨e₂ ▸ jAddRel_jTupleOf T₂, pointTripleIndependent_jTupleOf T₂⟩⟩

/-- **The corrected negation semantics** (the corrected counterpart of the blueprint's
`JNeg(j(x, a), j(y, a)) ⇔ y = -x`): for class members, the corrected negation relation holds
exactly when `μ(v) = -μ(u)`. -/
theorem jNegTotalRel_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v) :
    JNegTotalRel (jTupleOf x₀ a h₀) u v ↔
      (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) = -(jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) :=
  ⟨JNegTotalRel.neg_eq q htr hcomp h₀ hu hv, jNegTotalRel_of_neg_eq q htr hcomp h₀ hu hv⟩

/-- **Corrected total nonzero addition on the fixed class** (the corrected counterpart of the
blueprint's `JAddTotalNZ` detour): there are class members `z, nz, r, s` with `nz = -z` (corrected
negation), `u + z = r`, `v + nz = s` and `r + s = w`, each coupled addition generic.  No genericity
between `u` and `v` is required, and the output `w` is not assumed to be a class member. -/
def JAddTotalNZRel (j₀ u v w : Fin 5 → Point k K) : Prop :=
  ∃ z nz r s : Fin 5 → Point k K,
    FrobEq j₀ z ∧ FrobEq j₀ nz ∧ FrobEq j₀ r ∧ FrobEq j₀ s ∧ JNegTotalRel j₀ z nz ∧
    (JAddRel u z r ∧ PointTripleIndependent (u 0) (z 0) (u 4)) ∧
    (JAddRel v nz s ∧ PointTripleIndependent (v 0) (nz 0) (v 4)) ∧
    (JAddRel r s w ∧ PointTripleIndependent (r 0) (s 0) (r 4))

/-- **Total addition semantics, forward**: any witness of the corrected total addition of class
members `u, v` puts the output `w` in the class, with coordinate `μ(u) + μ(v)`. -/
theorem JAddTotalNZRel.exists_mem_add [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (h : JAddTotalNZRel (jTupleOf x₀ a h₀) u v w) :
    ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
      (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
        (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) := by
  obtain ⟨z, nz, r, s, hz, hnz, hr, hs, hneg, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ⟨m₃, g₃⟩⟩ := h
  have en := JNegTotalRel.neg_eq q htr hcomp h₀ hz hnz hneg
  obtain ⟨_hr', e₁⟩ := JAddRel.jClassEquiv_add q htr hcomp h₀ hu hz g₁ m₁
  obtain ⟨_hs', e₂⟩ := JAddRel.jClassEquiv_add q htr hcomp h₀ hv hnz g₂ m₂
  obtain ⟨hw, e₃⟩ := JAddRel.jClassEquiv_add q htr hcomp h₀ hr hs g₃ m₃
  have e₁' : (jClassEquiv q htr hcomp h₀ ⟨r, hr⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨z, hz⟩ : K) := e₁
  have e₂' : (jClassEquiv q htr hcomp h₀ ⟨s, hs⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨nz, hnz⟩ : K) := e₂
  exact ⟨hw, by linear_combination e₃ + e₁' + e₂' + en⟩

/-- **Total addition semantics, converse**: for class members `u, v, w` with
`μ(w) = μ(u) + μ(v)`, the corrected total addition holds.  One element fresh over the parameter
and the two input coordinates supplies all witnesses. -/
theorem jAddTotalNZRel_of_add_eq [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v)
    (hw : FrobEq (jTupleOf x₀ a h₀) w)
    (h : (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
      (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K)) :
    JAddTotalNZRel (jTupleOf x₀ a h₀) u v w := by
  classical
  -- Present the three class members with the literal parameter `a`; then `c = x + y`.
  obtain ⟨x, hx, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hu
  obtain ⟨y, hy, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hv
  obtain ⟨c, hc, rfl⟩ := (frobEq_jTupleOf_iff q htr hcomp h₀).1 hw
  rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf] at h
  -- A fresh `z` over `a, x, y`.
  obtain ⟨z, hz⟩ := fresh_three_of_five_le_trdeg htr {a, x, y} Finset.card_le_three
  have hz' : z ∉ racl k ({a, x, y} : Set K) := by simpa using hz
  have haR : a ∈ racl k ({a, x, y} : Set K) := subset_racl k _ (by simp)
  have hxR : x ∈ racl k ({a, x, y} : Set K) := subset_racl k _ (by simp)
  have hyR : y ∈ racl k ({a, x, y} : Set K) := subset_racl k _ (by simp)
  have hcR : c ∈ racl k ({a, x, y} : Set K) := by
    rw [h]
    exact add_mem hxR hyR
  have hsub : ∀ {p : K}, p ∈ racl k ({a, x, y} : Set K) →
      ({p, a} : Set K) ⊆ racl k ({a, x, y} : Set K) := fun hp ↦
    Set.insert_subset_iff.2 ⟨hp, Set.singleton_subset_iff.2 haR⟩
  -- The generic triples `(x, z, a)`, `(y, -z, a)`, `(c, x + z, a)` and `(x + z, y - z, a)`.
  have T₁ : AlgebraicIndependent k ![x, z, a] :=
    AlgebraicIndependent.insert_middle hx fun h' ↦ hz' (racl_le_of_subset_racl (hsub hxR) h')
  have T₂ : AlgebraicIndependent k ![y, -z, a] :=
    AlgebraicIndependent.insert_middle hy fun h' ↦ hz'
      (mem_racl_of_eq (neg_neg z).symm (neg_mem (racl_le_of_subset_racl (hsub hyR) h')))
  have T₃ : AlgebraicIndependent k ![c, x + z, a] :=
    AlgebraicIndependent.insert_middle hc fun h' ↦ hz'
      (mem_racl_of_eq (by ring)
        (sub_mem (racl_le_of_subset_racl (hsub hcR) h') hxR :
          x + z - x ∈ racl k ({a, x, y} : Set K)))
  have T₄ : AlgebraicIndependent k ![x + z, y + -z, a] := by
    refine AlgebraicIndependent.triple_of_mem T₃ (fun i ↦ ?_) (fun i ↦ ?_)
    · have hr := fun i ↦ subset_racl k (Set.range ![c, x + z, a]) (Set.mem_range_self i)
      fin_cases i
      · exact hr 1
      · change y + -z ∈ _
        exact mem_racl_of_eq (by rw [h]; ring)
          (sub_mem (hr 0) (hr 1) : c - (x + z) ∈ racl k (Set.range ![c, x + z, a]))
      · exact hr 2
    · have hr := fun i ↦ subset_racl k (Set.range ![x + z, y + -z, a]) (Set.mem_range_self i)
      fin_cases i
      · change c ∈ _
        exact mem_racl_of_eq (by rw [h]; ring)
          (add_mem (hr 0) (hr 1) : x + z + (y + -z) ∈ racl k (Set.range ![x + z, y + -z, a]))
      · exact hr 0
      · exact hr 2
  -- The witnesses `j(z, a)`, `j(-z, a)`, `j(x + z, a)` and `j(y - z, a)`.
  have hzT := frobEq_jTupleOf_of_common htr h₀ (AlgebraicIndependent.pair_one_two T₁)
  have hnzT := frobEq_jTupleOf_of_common htr h₀ (AlgebraicIndependent.pair_one_two T₂)
  have hneg := jNegTotalRel_of_neg_eq q htr hcomp h₀ hzT hnzT
    (by rw [jClassEquiv_jTupleOf, jClassEquiv_jTupleOf])
  have ew : jTupleOf (x + z + (y + -z)) a (pair_add_a T₄) = jTupleOf c a hc :=
    jTupleOf_congr _ _ (by rw [h]; ring)
  exact ⟨jTupleOf z a (AlgebraicIndependent.pair_one_two T₁),
    jTupleOf (-z) a (AlgebraicIndependent.pair_one_two T₂),
    jTupleOf (x + z) a (pair_add_a T₁), jTupleOf (y + -z) a (pair_add_a T₂),
    hzT, hnzT, frobEq_jTupleOf_of_common htr h₀ _, frobEq_jTupleOf_of_common htr h₀ _, hneg,
    ⟨jAddRel_jTupleOf T₁, pointTripleIndependent_jTupleOf T₁⟩,
    ⟨jAddRel_jTupleOf T₂, pointTripleIndependent_jTupleOf T₂⟩,
    ⟨ew ▸ jAddRel_jTupleOf T₄, pointTripleIndependent_jTupleOf T₄⟩⟩

/-- **The corrected total nonzero addition semantics** (the corrected counterpart of blueprint
Lemma `total-nonzero-add`): for class members `u, v` and an arbitrary tuple `w`, the corrected
total addition holds exactly when `w` is a class member with coordinate `μ(u) + μ(v)`. -/
theorem jAddTotalNZRel_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) {u v w : Fin 5 → Point k K}
    (hu : FrobEq (jTupleOf x₀ a h₀) u) (hv : FrobEq (jTupleOf x₀ a h₀) v) :
    JAddTotalNZRel (jTupleOf x₀ a h₀) u v w ↔
      ∃ hw : FrobEq (jTupleOf x₀ a h₀) w,
        (jClassEquiv q htr hcomp h₀ ⟨w, hw⟩ : K) =
          (jClassEquiv q htr hcomp h₀ ⟨u, hu⟩ : K) + (jClassEquiv q htr hcomp h₀ ⟨v, hv⟩ : K) :=
  ⟨JAddTotalNZRel.exists_mem_add q htr hcomp h₀ hu hv,
    fun ⟨hw, h⟩ ↦ jAddTotalNZRel_of_add_eq q htr hcomp h₀ hu hv hw h⟩

end

end AclGeom
