/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Soundness

/-!
# The coordinate check for the multiplication diagram

The forward half of blueprint Lemma mul-diagram: for algebraically
independent `x, y, a`, the eight points

`X = [x], Y = [y], V = [x/y], E = [xy], A₀ = [a], B₀ = [ax], C₀ = [ay],
D₀ = [axy]`

satisfy `MulDiagram`. Every displayed line follows from one rational
identity (`ax = a·x`, `axy = (ax)·y = x·(ay) = a·(xy)`,
`x/y = (ax)/(ay)`), verified with the rank bridge; this file provides
the entry kit, the line-pair independences, and the rank clauses.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G4 forward half).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section MulTable

variable {x y a : K} (hind : AlgebraicIndependent k ![x, y, a])

include hind

/-! ### Generator projections -/

theorem mtable_x_notMem_empty : x ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 0
    (isAlgebraic_of_mem_racl_empty h)

theorem mtable_y_notMem_empty : y ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 1
    (isAlgebraic_of_mem_racl_empty h)

theorem mtable_a_notMem_empty : a ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 2
    (isAlgebraic_of_mem_racl_empty h)

theorem mtable_x_ne_zero : x ≠ 0 := by
  intro h0
  have h := mtable_x_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

theorem mtable_y_ne_zero : y ≠ 0 := by
  intro h0
  have h := mtable_y_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

theorem mtable_a_ne_zero : a ≠ 0 := by
  intro h0
  have h := mtable_a_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

theorem mtable_y_notMem_x : y ∉ racl k ({x} : Set K) := by
  have h : AlgebraicIndependent k ![x, y] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

theorem mtable_x_notMem_y : x ∉ racl k ({y} : Set K) := by
  have h : AlgebraicIndependent k ![x, y] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem mtable_a_notMem_x : a ∉ racl k ({x} : Set K) := by
  have h : AlgebraicIndependent k ![x, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

theorem mtable_a_notMem_y : a ∉ racl k ({y} : Set K) := by
  have h : AlgebraicIndependent k ![y, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 1) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

theorem mtable_a_notMem_xy : a ∉ racl k ({x, y} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1}) (i := 2) (by decide)
  simpa [Set.image_insert_eq] using h

theorem mtable_x_notMem_ay : x ∉ racl k ({a, y} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {2, 1}) (i := 0) (by decide)
  simpa [Set.image_insert_eq] using h

theorem mtable_y_notMem_ax : y ∉ racl k ({a, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {2, 0}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

/-! ### Transcendence of the composite entries -/

/-- `x/y` is a point. -/
theorem mtable_div_notMem_bot : x / y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {y} ?_ (mtable_x_notMem_y hind)
  have hq : x / y ∈ racl k (insert (x / y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hy : y ∈ racl k (insert (x / y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hq hy
  rwa [div_mul_cancel₀ x (mtable_y_ne_zero hind)] at h

/-- `xy` is a point. -/
theorem mtable_mul_notMem_bot : x * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {y} ?_ (mtable_x_notMem_y hind)
  have hm : x * y ∈ racl k (insert (x * y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hy : y ∈ racl k (insert (x * y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hm (inv_mem hy)
  rwa [mul_inv_cancel_right₀ (mtable_y_ne_zero hind)] at h

/-- `ax` is a point. -/
theorem mtable_ax_notMem_bot : a * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover (w := x) {a} ?_ ?_
  · have hm : a * x ∈ racl k (insert (a * x) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert _ _)
    have ha : a ∈ racl k (insert (a * x) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    have h := MulMemClass.mul_mem (inv_mem ha) hm
    rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h
  · intro h
    have h2 : AlgebraicIndependent k ![a, x] := by
      simpa using AlgebraicIndependent.comp_pair hind
        (i := 2) (j := 0) (by decide)
    exact AlgebraicIndependent.notMem_racl_pair h2 h

/-- `ay` is a point. -/
theorem mtable_ay_notMem_bot : a * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover (w := y) {a} ?_ ?_
  · have hm : a * y ∈ racl k (insert (a * y) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert _ _)
    have ha : a ∈ racl k (insert (a * y) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    have h := MulMemClass.mul_mem (inv_mem ha) hm
    rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h
  · intro h
    have h2 : AlgebraicIndependent k ![a, y] := by
      simpa using AlgebraicIndependent.comp_pair hind
        (i := 2) (j := 1) (by decide)
    exact AlgebraicIndependent.notMem_racl_pair h2 h

/-- `axy` is a point. -/
theorem mtable_axy_notMem_bot : a * x * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, y} ?_ (mtable_x_notMem_ay hind)
  set S : Set K := insert (a * x * y) {a, y} with hS
  have hm : a * x * y ∈ racl k S := subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hy : y ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hy)) hm
  have harith : (a * y)⁻¹ * (a * x * y) = x := by
    have hr : a * x * y = a * y * x := by ring
    rw [hr, inv_mul_cancel_left₀ (mul_ne_zero (mtable_a_ne_zero hind)
      (mtable_y_ne_zero hind))]
  rwa [harith] at h

/-! ### Independence of the line pairs -/

theorem mtable_indep_xa : AlgebraicIndependent k ![x, a] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 0) (j := 2) (by decide)

theorem mtable_indep_ay : AlgebraicIndependent k ![a, y] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 2) (j := 1) (by decide)

theorem mtable_indep_xy : AlgebraicIndependent k ![x, y] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 0) (j := 1) (by decide)

theorem mtable_indep_a_xy : AlgebraicIndependent k ![a, x * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({x * y} : Set K) ≤ racl k ({x, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem hx hy
    exact mtable_a_notMem_xy hind (hsub h)
  · intro h
    have hm0 : x * y ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_mul_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : x * y ∈ racl k (insert a (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hm0
    have h3 : a ∈ racl k ({x * y} : Set K) := by simpa using h2
    have hsub : racl k ({x * y} : Set K) ≤ racl k ({x, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem hx hy
    exact mtable_a_notMem_xy hind (hsub h3)

theorem mtable_indep_ax_y : AlgebraicIndependent k ![a * x, y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hax0 : a * x ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_ax_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : a * x ∈ racl k (insert y (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hax0
    have h3 : y ∈ racl k ({a * x} : Set K) := by simpa using h2
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    exact mtable_y_notMem_ax hind (hsub h3)
  · intro h
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    exact mtable_y_notMem_ax hind (hsub h)

theorem mtable_indep_x_ay : AlgebraicIndependent k ![x, a * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    exact mtable_x_notMem_ay hind (hsub h)
  · intro h
    have hay0 : a * y ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_ay_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : a * y ∈ racl k (insert x (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hay0
    have h3 : x ∈ racl k ({a * y} : Set K) := by simpa using h2
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    exact mtable_x_notMem_ay hind (hsub h3)

theorem mtable_indep_ax_ay : AlgebraicIndependent k ![a * x, a * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    have h2 := hsub h
    have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, y} : Set K) := by
      have h3 := MulMemClass.mul_mem (inv_mem ha) h2
      rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h3
    exact mtable_x_notMem_ay hind hx
  · intro h
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    have h2 := hsub h
    have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({a, x} : Set K) := by
      have h3 := MulMemClass.mul_mem (inv_mem ha) h2
      rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h3
    exact mtable_y_notMem_ax hind hy

end MulTable

end

end AclGeom
