/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Psi

/-!
# The soundness witness table

The explicit witness of blueprint table 7.1: given five algebraically
independent elements `a, b, c, d, x`, the twenty-one points of the
`Q`-configuration are the principal closures of rational monomial
expressions in them. This file provides the *entry kit*: every table
entry is transcendental over the base (hence a point of the geometry),
via the uniform recovery principle `notMem_bot_of_recover` — if some
element recoverable from `z` and a side set `S` is not algebraic over
`S` alone, then `z` is transcendental.

The witness structure itself and the verification of the Ψ clauses
build on this kit (blueprint Thm q-correct, soundness direction).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section Recovery

/-- The recovery principle: if `w` is algebraic over `S` together with
`z` but not over `S` alone, then `z` is transcendental over the base. -/
theorem notMem_bot_of_recover {z : K} (S : Set K) {w : K}
    (hrec : w ∈ racl k (insert z S)) (hw : w ∉ racl k S) :
    z ∉ (⊥ : ClosedIF k K) := by
  intro hz
  have hz' : z ∈ racl k S := by
    have h0 : z ∈ racl k (∅ : Set K) :=
      mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 hz)
    exact racl_mono (Set.empty_subset _) h0
  rw [racl_insert_of_mem hz'] at hrec
  exact hw hrec

/-- Transcendental elements are nonzero, in lattice form. -/
theorem ne_zero_of_notMem_bot {z : K} (hz : z ∉ (⊥ : ClosedIF k K)) :
    z ≠ 0 := by
  intro h0
  refine hz ?_
  rw [h0]
  exact ClosedIF.mem_bot_iff.2 isAlgebraic_zero

end Recovery

section QTable

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

/-! ### Independence projections

Named projections of the five-tuple independence, in the pair and side-set
forms consumed by the entry kit. -/

include hind

theorem qtable_a_notMem_bot : a ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 0 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_b_notMem_bot : b ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 1 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_c_notMem_bot : c ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 2 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_d_notMem_bot : d ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 3 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_x_notMem_bot : x ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 4 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_a_ne_zero : a ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_a_notMem_bot hind)

theorem qtable_b_ne_zero : b ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_b_notMem_bot hind)

theorem qtable_c_ne_zero : c ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_c_notMem_bot hind)

theorem qtable_x_ne_zero : x ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_x_notMem_bot hind)

theorem qtable_c_notMem_a : c ∉ racl k ({a} : Set K) := by
  have h : AlgebraicIndependent k ![c, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 2) (j := 0) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_x_notMem_a : x ∉ racl k ({a} : Set K) := by
  have h : AlgebraicIndependent k ![x, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 4) (j := 0) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_c_notMem_b : c ∉ racl k ({b} : Set K) := by
  have h : AlgebraicIndependent k ![c, b] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 2) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_a_notMem_b : a ∉ racl k ({b} : Set K) := by
  have h : AlgebraicIndependent k ![a, b] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_b_notMem_c : b ∉ racl k ({c} : Set K) := by
  have h : AlgebraicIndependent k ![b, c] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 1) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_d_notMem_bc : d ∉ racl k ({b, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {1, 2}) (i := 3) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_b_notMem_ax : b ∉ racl k ({a, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 4}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_x_notMem_ab : x ∉ racl k ({a, b} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1}) (i := 4) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_x_notMem_ac : x ∉ racl k ({a, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 2}) (i := 4) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_b_notMem_ac : b ∉ racl k ({a, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 2}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_c_notMem_abx : c ∉ racl k ({a, b, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1, 4}) (i := 2) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_d_notMem_abcx : d ∉ racl k ({a, b, c, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1, 2, 4}) (i := 3) (by decide)
  simpa [Set.image_insert_eq] using h

/-! ### Transcendence of the table entries

Each composite entry of table 7.1 is transcendental over the base, by the
recovery principle: dividing or subtracting away the side factors recovers
a generator not algebraic over the side set. -/

/-- The entry `C₁ = [ac]`. -/
theorem qtable_mul_ac_notMem_bot : a * c ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a} ?_ (qtable_c_notMem_a hind)
  have hac : a * c ∈ racl k (insert (a * c) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem ha) hac
  rwa [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h

/-- The entry `D = [ax]`. -/
theorem qtable_mul_ax_notMem_bot : a * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a} ?_ (qtable_x_notMem_a hind)
  have hax : a * x ∈ racl k (insert (a * x) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem ha) hax
  rwa [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h

/-- The entry `G = [bc]`. -/
theorem qtable_mul_bc_notMem_bot : b * c ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b} ?_ (qtable_c_notMem_b hind)
  have hbc : b * c ∈ racl k (insert (b * c) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (b * c) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem hb) hbc
  rwa [inv_mul_cancel_left₀ (qtable_b_ne_zero hind)] at h

/-- The entry `U' = [cb]`. -/
theorem qtable_mul_cb_notMem_bot : c * b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {c} ?_ (qtable_b_notMem_c hind)
  have hcb : c * b ∈ racl k (insert (c * b) ({c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hc : c ∈ racl k (insert (c * b) ({c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem hc) hcb
  rwa [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h

/-- The entry `H = [a/b]`. -/
theorem qtable_div_ab_notMem_bot : a / b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b} ?_ (qtable_a_notMem_b hind)
  have hq : a / b ∈ racl k (insert (a / b) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (a / b) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hq hb
  rwa [div_mul_cancel₀ a (qtable_b_ne_zero hind)] at h

/-- The entry `C₂ = [bc + d]`. -/
theorem qtable_bcd_notMem_bot : b * c + d ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b, c} ?_ (qtable_d_notMem_bc hind)
  have hbcd : b * c + d ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := sub_mem hbcd (MulMemClass.mul_mem hb hc)
  rwa [add_sub_cancel_left] at h

/-- The entry `Y = [ax + b]`. -/
theorem qtable_Y_notMem_bot : a * x + b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, x} ?_ (qtable_b_notMem_ax hind)
  have hY : a * x + b ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hx : x ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := sub_mem hY (MulMemClass.mul_mem ha hx)
  rwa [add_sub_cancel_left] at h

/-- The entry `I = [ax/b]`. -/
theorem qtable_axb_notMem_bot : a * x / b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b} ?_ (qtable_x_notMem_ab hind)
  have hI : a * x / b ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem (inv_mem ha) (MulMemClass.mul_mem hI hb)
  have harith : a⁻¹ * (a * x / b * b) = x := by
    rw [div_mul_cancel₀ _ (qtable_b_ne_zero hind),
      inv_mul_cancel_left₀ (qtable_a_ne_zero hind)]
  rwa [harith] at h

/-- The entry `F = [acx]`. -/
theorem qtable_acx_notMem_bot : a * c * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, c} ?_ (qtable_x_notMem_ac hind)
  have hF : a * c * x ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) hF
  have harith : (a * c)⁻¹ * (a * c * x) = x :=
    inv_mul_cancel_left₀
      (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) x
  rwa [harith] at h

/-- The entry `T' = [acb]`. -/
theorem qtable_acb_notMem_bot : a * c * b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, c} ?_ (qtable_b_notMem_ac hind)
  have hT : a * c * b ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) hT
  have harith : (a * c)⁻¹ * (a * c * b) = b :=
    inv_mul_cancel_left₀
      (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) b
  rwa [harith] at h

/-- The entry `E = [c(ax + b)]`. -/
theorem qtable_E_notMem_bot : c * (a * x + b) ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b, x} ?_ (qtable_c_notMem_abx hind)
  set S : Set K := insert (c * (a * x + b)) {a, b, x} with hS
  have hE : c * (a * x + b) ∈ racl k S := subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hx : x ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ rfl)))
  have hY : a * x + b ∈ racl k S :=
    add_mem (MulMemClass.mul_mem ha hx) hb
  have hY0 : a * x + b ≠ 0 :=
    ne_zero_of_notMem_bot (qtable_Y_notMem_bot hind)
  have h := MulMemClass.mul_mem hE (inv_mem hY)
  rwa [mul_inv_cancel_right₀ hY0] at h

/-- The entry `Z = [c(ax + b) + d]`. -/
theorem qtable_Z_notMem_bot :
    c * (a * x + b) + d ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b, c, x} ?_ (qtable_d_notMem_abcx hind)
  set S : Set K := insert (c * (a * x + b) + d) {a, b, c, x} with hS
  have hZ : c * (a * x + b) + d ∈ racl k S :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hc : c ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hx : x ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  have h := sub_mem hZ (MulMemClass.mul_mem hc
    (add_mem (MulMemClass.mul_mem ha hx) hb))
  rwa [add_sub_cancel_left] at h

end QTable

end

end AclGeom
