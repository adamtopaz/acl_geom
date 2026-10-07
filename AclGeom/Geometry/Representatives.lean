/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.FiniteRank
import AclGeom.Transfer.Transcendence

/-!
# The finite representative calculus

Blueprint Lemma `finite-representative-calculus` (Lemma 4.2), for tuples
`v₁, …, vₙ ∈ K`:

* (a) independence is the absence of closure membership among the entries —
  `algebraicIndependent_iff_forall_notMem_racl` (`AclGeom.Closure.Basic`);
* (b) replacing each entry by an interalgebraic one preserves independence
  (`algebraicIndependent_congr_racl`), the closure of the tuple
  (`racl_range_congr`), its matroid rank (`eRk_range_congr`) and the join of
  its points (`iSup_point_congr`, `AclGeom.Geometry.FiniteRank`);
* (c) rank below the transcendence degree leaves room for fresh elements:
  `exists_notMem_racl_of_eRk_lt` and the two-step
  `exists_two_fresh_of_eRk_add_two_le`; the cardinality forms used by the
  configuration layer are `exists_notMem_racl_of_card_lt_trdeg`,
  `fresh_three_of_five_le_trdeg` and `fresh_four_of_five_le_trdeg`
  (`AclGeom.Transfer.Transcendence`);
* (d) a change of coordinates whose new and old entries generate each other
  algebraically preserves independence
  (`AlgebraicIndependent.of_racl_range_eq`); the three changes listed in the
  blueprint are `algebraicIndependent_mul_mul_left`,
  `algebraicIndependent_mul_one_add` and `algebraicIndependent_mul_left`.

Many concrete instances of (b) and (d) are already proved where they are
used, for the witness tables (`qtable_indep_*`, `mtable_indep_*`); they are
not restated here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (blueprint Lemma 4.2). Other foundational carryovers remain
tracked separately in issue #24.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Congr

variable {ι : Type*} {v w : ι → K}

/-- Membership of an element in a closure depends only on its principal
closure. -/
theorem mem_racl_congr_left {x y : K} (h : racl k {x} = racl k {y}) {S : Set K} :
    x ∈ racl k S ↔ y ∈ racl k S := by
  have key : ∀ {z : K}, z ∈ racl k S ↔ racl k {z} ≤ racl k S := fun {z} ↦
    ⟨fun hz ↦ racl_le_of_subset_racl (Set.singleton_subset_iff.2 hz),
      fun hz ↦ hz (subset_racl k _ rfl)⟩
  rw [key, key, h]

/-- **Lemma 4.2(b), closures**: entrywise interalgebraic families generate
the same closure on every index set. -/
theorem racl_image_congr (h : ∀ i, racl k {v i} = racl k {w i}) (s : Set ι) :
    racl k (v '' s) = racl k (w '' s) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact (mem_racl_congr_left (h i)).2 (subset_racl k _ ⟨i, hi, rfl⟩)
  · rintro _ ⟨i, hi, rfl⟩
    exact (mem_racl_congr_left (h i)).1 (subset_racl k _ ⟨i, hi, rfl⟩)

/-- **Lemma 4.2(b), closures of the whole family**: entrywise
interalgebraic families generate the same closure. -/
theorem racl_range_congr (h : ∀ i, racl k {v i} = racl k {w i}) :
    racl k (Set.range v) = racl k (Set.range w) := by
  rw [← Set.image_univ, ← Set.image_univ]
  exact racl_image_congr h Set.univ

/-- **Lemma 4.2(b), independence**: replacing each entry of a family by an
interalgebraic one preserves algebraic independence. -/
theorem algebraicIndependent_congr_racl (h : ∀ i, racl k {v i} = racl k {w i}) :
    AlgebraicIndependent k v ↔ AlgebraicIndependent k w := by
  rw [algebraicIndependent_iff_forall_notMem_racl,
    algebraicIndependent_iff_forall_notMem_racl]
  refine forall_congr' fun i ↦ not_congr ?_
  rw [racl_image_congr h, mem_racl_congr_left (h i)]

/-- **Lemma 4.2(b), rank**: replacing each entry by an interalgebraic one
preserves the rank of the family in the algebraic matroid. -/
theorem eRk_range_congr (h : ∀ i, racl k {v i} = racl k {w i}) :
    (AlgebraicIndependent.matroid k K).eRk (Set.range v) =
      (AlgebraicIndependent.matroid k K).eRk (Set.range w) := by
  set M := AlgebraicIndependent.matroid k K
  rw [← M.eRk_closure_eq, ← M.eRk_closure_eq (Set.range w),
    algebraicMatroid_closure_eq_racl, algebraicMatroid_closure_eq_racl,
    racl_range_congr h]

end Congr

section Fresh

/-- **Lemma 4.2(c), one step**: a set of finite rank below the
transcendence degree is not closure-dense. -/
theorem exists_notMem_racl_of_eRk_lt {n : ℕ} (htr : (n : Cardinal) < Algebra.trdeg k K)
    {S : Set K} (hS : (AlgebraicIndependent.matroid k K).eRk S ≤ n) :
    ∃ t : K, t ∉ racl k S := by
  classical
  set M := AlgebraicIndependent.matroid k K
  obtain ⟨I, hI⟩ := M.exists_isBasis S (by simp [M])
  have hIcard : I.encard ≤ n := hI.encard_eq_eRk ▸ hS
  have hIfin : I.Finite := Set.finite_of_encard_le_coe hIcard
  obtain ⟨t, ht⟩ := exists_notMem_racl_of_card_lt_trdeg htr hIfin.toFinset (by
    rw [← Nat.cast_le (α := ℕ∞), ← hIfin.encard_eq_coe_toFinset_card]
    exact hIcard)
  refine ⟨t, fun htS ↦ ht ?_⟩
  have hcl : (racl k (hIfin.toFinset : Set K) : Set K) = (racl k S : Set K) := by
    rw [Set.Finite.coe_toFinset, ← algebraicMatroid_closure_eq_racl,
      ← algebraicMatroid_closure_eq_racl, hI.closure_eq_closure]
  rw [← SetLike.mem_coe, hcl]
  exact htS

/-- **Lemma 4.2(c), two steps**: if the rank of `S` is at most `n` and
`n + 2` is at most the transcendence degree, there are successive fresh
elements `s`, `t` raising the rank by two. -/
theorem exists_two_fresh_of_eRk_add_two_le {n : ℕ}
    (htr : ((n + 1 : ℕ) : Cardinal) < Algebra.trdeg k K) {S : Set K}
    (hS : (AlgebraicIndependent.matroid k K).eRk S ≤ n) :
    ∃ s t : K, s ∉ racl k S ∧ t ∉ racl k (insert s S) ∧
      (AlgebraicIndependent.matroid k K).eRk (insert t (insert s S)) =
        (AlgebraicIndependent.matroid k K).eRk S + 2 := by
  set M := AlgebraicIndependent.matroid k K
  have hcl : ∀ T : Set K, M.closure T = (racl k T : Set K) :=
    algebraicMatroid_closure_eq_racl
  have htr' : (n : Cardinal) < Algebra.trdeg k K :=
    lt_of_le_of_lt (by exact_mod_cast Nat.le_succ n) htr
  obtain ⟨s, hs⟩ := exists_notMem_racl_of_eRk_lt htr' hS
  have h1 : M.eRk (insert s S) = M.eRk S + 1 :=
    M.eRk_insert_eq_add_one ⟨Set.mem_univ s, by rw [hcl]; exact hs⟩
  obtain ⟨t, ht⟩ := exists_notMem_racl_of_eRk_lt (S := insert s S) htr (by
    rw [h1]
    push_cast
    exact add_le_add hS le_rfl)
  have h2 : M.eRk (insert t (insert s S)) = M.eRk (insert s S) + 1 :=
    M.eRk_insert_eq_add_one ⟨Set.mem_univ t, by rw [hcl]; exact ht⟩
  refine ⟨s, t, hs, ht, ?_⟩
  rw [h2, h1, add_assoc]
  rfl

end Fresh

section Birational

/-- **Lemma 4.2(d), general form**: an `n`-tuple generating the same
closure as an independent `n`-tuple is itself independent.  This covers
every birational (indeed every algebraic) change of coordinates. -/
theorem AlgebraicIndependent.of_racl_range_eq {n : ℕ} {v w : Fin n → K}
    (hv : AlgebraicIndependent k v)
    (h : racl k (Set.range v) = racl k (Set.range w)) :
    AlgebraicIndependent k w := by
  refine algebraicIndependent_of_rankEq_iSup_point ?_
  have hv' := rankEq_iSup_point hv
  refine hv'.congr (iSup_point_congr h)

/-- Mutual membership of the entries gives equal closures. -/
theorem racl_range_eq_of_mem {n m : ℕ} {v : Fin n → K} {w : Fin m → K}
    (hw : ∀ j, w j ∈ racl k (Set.range v)) (hv : ∀ i, v i ∈ racl k (Set.range w)) :
    racl k (Set.range v) = racl k (Set.range w) :=
  racl_congr_of_subset_racl (by rintro _ ⟨i, rfl⟩; exact hv i)
    (by rintro _ ⟨j, rfl⟩; exact hw j)

variable {x y a : K}

/-- The three entries of a vector lie in its range. -/
private theorem mem_range_three {α : Type*} {u₀ u₁ u₂ : α} :
    u₀ ∈ Set.range ![u₀, u₁, u₂] ∧ u₁ ∈ Set.range ![u₀, u₁, u₂] ∧
      u₂ ∈ Set.range ![u₀, u₁, u₂] :=
  ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩

/-- Lemma 4.2(d): `(x, y, a) ↦ (xa, ya, a)` preserves independence.
The needed `a ≠ 0` follows from the original independence. -/
theorem algebraicIndependent_mul_mul_left
    (h : AlgebraicIndependent k ![x, y, a]) :
    AlgebraicIndependent k ![x * a, y * a, a] := by
  have ha : a ≠ 0 := by
    intro h0
    exact h.transcendental 2 (h0.symm ▸ isAlgebraic_zero)
  refine AlgebraicIndependent.of_racl_range_eq h (racl_range_eq_of_mem ?_ ?_)
  · obtain ⟨h0, h1, h2⟩ := (mem_range_three (u₀ := x) (u₁ := y) (u₂ := a))
    intro j
    fin_cases j
    · exact mul_mem (subset_racl k _ h0) (subset_racl k _ h2)
    · exact mul_mem (subset_racl k _ h1) (subset_racl k _ h2)
    · exact subset_racl k _ h2
  · obtain ⟨h0, h1, h2⟩ := (mem_range_three (u₀ := x * a) (u₁ := y * a) (u₂ := a))
    have hai : a⁻¹ ∈ racl k (Set.range ![x * a, y * a, a]) := inv_mem (subset_racl k _ h2)
    intro i
    fin_cases i
    · simpa [mul_inv_cancel_right₀ ha] using mul_mem (subset_racl k _ h0) hai
    · simpa [mul_inv_cancel_right₀ ha] using mul_mem (subset_racl k _ h1) hai
    · exact subset_racl k _ h2

/-- Lemma 4.2(d): `(x, y, a) ↦ (x(1+a), y(1+a), a)` preserves
independence. The needed `1 + a ≠ 0` follows from the original independence. -/
theorem algebraicIndependent_mul_one_add
    (h : AlgebraicIndependent k ![x, y, a]) :
    AlgebraicIndependent k ![x * (1 + a), y * (1 + a), a] := by
  have ha : 1 + a ≠ 0 := by
    intro h0
    have ha' : a = -1 := by linear_combination h0
    exact h.transcendental 2 (ha'.symm ▸ isAlgebraic_one.neg)
  refine AlgebraicIndependent.of_racl_range_eq h (racl_range_eq_of_mem ?_ ?_)
  · obtain ⟨h0, h1, h2⟩ := (mem_range_three (u₀ := x) (u₁ := y) (u₂ := a))
    have ha1 : 1 + a ∈ racl k (Set.range ![x, y, a]) := add_mem (one_mem _) (subset_racl k _ h2)
    intro j
    fin_cases j
    · exact mul_mem (subset_racl k _ h0) ha1
    · exact mul_mem (subset_racl k _ h1) ha1
    · exact subset_racl k _ h2
  · obtain ⟨h0, h1, h2⟩ :=
      (mem_range_three (u₀ := x * (1 + a)) (u₁ := y * (1 + a)) (u₂ := a))
    have hai : (1 + a)⁻¹ ∈ racl k (Set.range ![x * (1 + a), y * (1 + a), a]) :=
      inv_mem (add_mem (one_mem _) (subset_racl k _ h2))
    intro i
    fin_cases i
    · simpa [mul_inv_cancel_right₀ ha] using mul_mem (subset_racl k _ h0) hai
    · simpa [mul_inv_cancel_right₀ ha] using mul_mem (subset_racl k _ h1) hai
    · exact subset_racl k _ h2

/-- Lemma 4.2(d): `(x, y, a) ↦ (xy, y, a)` preserves independence.
The needed `y ≠ 0` follows from the original independence. -/
theorem algebraicIndependent_mul_left
    (h : AlgebraicIndependent k ![x, y, a]) :
    AlgebraicIndependent k ![x * y, y, a] := by
  have hy : y ≠ 0 := by
    intro h0
    exact h.transcendental 1 (h0.symm ▸ isAlgebraic_zero)
  refine AlgebraicIndependent.of_racl_range_eq h (racl_range_eq_of_mem ?_ ?_)
  · obtain ⟨h0, h1, h2⟩ := (mem_range_three (u₀ := x) (u₁ := y) (u₂ := a))
    intro j
    fin_cases j
    · exact mul_mem (subset_racl k _ h0) (subset_racl k _ h1)
    · exact subset_racl k _ h1
    · exact subset_racl k _ h2
  · obtain ⟨h0, h1, h2⟩ := (mem_range_three (u₀ := x * y) (u₁ := y) (u₂ := a))
    intro i
    fin_cases i
    · simpa [mul_inv_cancel_right₀ hy] using
        mul_mem (subset_racl k _ h0) (inv_mem (subset_racl k _ h1))
    · exact subset_racl k _ h1
    · exact subset_racl k _ h2

end Birational

section Triples

/-! Sub-pairs of independent triples and insertion of fresh elements, used by the direct-link
soundness proofs (`AclGeom.Interpretation.FrobLinkSoundness`).  Moved from
`AclGeom.Counterexamples.GenericArithmetic`; `insert_middle` now proves `range_pair` inline, which
lives in `AclGeom.Config.Quadrangle`. -/

/-- A pair taken from the entries of an independent triple is independent. -/
theorem AlgebraicIndependent.pair_of_triple {u v w : K}
    (h : AlgebraicIndependent k ![u, v, w]) {i j : Fin 3} (hij : i ≠ j) :
    AlgebraicIndependent k ![![u, v, w] i, ![u, v, w] j] := by
  have hinj : Function.Injective ![i, j] := by
    intro m n hmn
    fin_cases m <;> fin_cases n <;> simp_all [eq_comm]
  have := h.comp ![i, j] hinj
  convert this using 1
  ext m
  fin_cases m <;> rfl

/-- The entries `0, 2` of an independent triple are independent. -/
theorem AlgebraicIndependent.pair_zero_two {p q r : K} (h : AlgebraicIndependent k ![p, q, r]) :
    AlgebraicIndependent k ![p, r] :=
  AlgebraicIndependent.pair_of_triple h (i := 0) (j := 2) (by decide)

/-- The entries `1, 2` of an independent triple are independent. -/
theorem AlgebraicIndependent.pair_one_two {p q r : K} (h : AlgebraicIndependent k ![p, q, r]) :
    AlgebraicIndependent k ![q, r] :=
  AlgebraicIndependent.pair_of_triple h (i := 1) (j := 2) (by decide)

/-- `1 + r` is nonzero for the last entry `r` of an independent triple. -/
theorem AlgebraicIndependent.one_add_ne_zero_two {p q r : K}
    (hind : AlgebraicIndependent k ![p, q, r]) : 1 + r ≠ 0 := fun h ↦ hind.transcendental 2 (by
  change IsAlgebraic k r
  rw [show r = algebraMap k K (-1) by rw [map_neg, map_one]; linear_combination h]
  exact isAlgebraic_algebraMap _)

/-- Two triples generating the same closure are simultaneously independent. -/
theorem AlgebraicIndependent.triple_of_mem {u v w u' v' w' : K}
    (h : AlgebraicIndependent k ![u, v, w])
    (h₁ : ∀ i, ![u', v', w'] i ∈ racl k (Set.range ![u, v, w]))
    (h₂ : ∀ i, ![u, v, w] i ∈ racl k (Set.range ![u', v', w'])) :
    AlgebraicIndependent k ![u', v', w'] :=
  AlgebraicIndependent.of_racl_range_eq h (racl_range_eq_of_mem h₁ h₂)

/-- Insert a fresh element in the middle of an independent pair. -/
theorem AlgebraicIndependent.insert_middle {p q t : K} (h : AlgebraicIndependent k ![p, q])
    (ht : t ∉ racl k ({p, q} : Set K)) : AlgebraicIndependent k ![p, t, q] := by
  have h3 : AlgebraicIndependent k ![p, q, t] := by
    have hr : Set.range ![p, q] = ({p, q} : Set K) := by
      ext z
      simp [Matrix.range_cons, Matrix.range_empty]
      tauto
    have hs := algebraicIndependent_snoc h (z := t) (by rwa [hr])
    convert hs using 1
    funext i
    fin_cases i <;> rfl
  have := h3.comp ![0, 2, 1] (by decide)
  convert this using 1
  funext i
  fin_cases i <;> rfl

/-- Insert a fresh element in front of an independent pair. -/
theorem AlgebraicIndependent.insert_left {p q t : K} (h : AlgebraicIndependent k ![p, q])
    (ht : t ∉ racl k ({p, q} : Set K)) : AlgebraicIndependent k ![t, p, q] := by
  have := (AlgebraicIndependent.insert_middle h ht).comp ![1, 0, 2] (by decide)
  convert this using 1
  funext i
  fin_cases i <;> rfl

/-- A nonzero power of both entries keeps a pair independent. -/
theorem AlgebraicIndependent.pair_pow {x a : K} {m : ℕ} (hm : m ≠ 0)
    (h : AlgebraicIndependent k ![x, a]) : AlgebraicIndependent k ![x ^ m, a ^ m] :=
  (algebraicIndependent_congr_racl (v := ![x, a]) (w := ![x ^ m, a ^ m])
    (Fin.forall_fin_two.2 ⟨(racl_pow x hm).symm, (racl_pow a hm).symm⟩)).1 h

end Triples


end

end AclGeom
