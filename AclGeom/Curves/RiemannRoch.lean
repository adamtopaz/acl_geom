/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Divisors

/-!
# Riemann–Roch spaces

The space `L(D)` of a divisor: elements whose principal divisor is
bounded below by `-D`. This file provides the definitional layer of the
Riemann–Roch machinery (issue #13, P3): `L(D)` is a `k`-submodule of `F`,
monotone in the divisor, containing the constants at effective divisors.
The dimension bounds and Riemann's inequality build on this layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The **Riemann–Roch space** of a divisor `D`: the `k`-submodule of
elements whose order at every place is at least `-D`. -/
noncomputable def RiemannSpace (D : Divisor k F) : Submodule k F where
  carrier := {f : F | f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa using hf
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · exact Or.inl hfg
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    rcases hg with rfl | hg
    · exact absurd rfl hg0
    refine Or.inr fun P ↦ ?_
    exact le_trans (le_min (hf P) (hg P)) (P.min_ord_le_ord_add hf0 hg0 hfg)
  smul_mem' := by
    intro c f hf
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (zero_smul k f)
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl (smul_zero c)
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    refine Or.inr fun P ↦ ?_
    have h1 : P.ord (c • f) = P.ord f := by
      rw [Algebra.smul_def,
        P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hf0,
        P.ord_algebraMap hc0, zero_add]
    rw [h1]
    exact hf P

theorem mem_riemannSpace_iff {D : Divisor k F} {f : F} :
    f ∈ RiemannSpace D ↔
      f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f := Iff.rfl

theorem zero_mem_riemannSpace (D : Divisor k F) :
    (0 : F) ∈ RiemannSpace D := Or.inl rfl

/-- Monotonicity of the Riemann–Roch space in the divisor. -/
theorem riemannSpace_mono {D E : Divisor k F} (h : D ≤ E) :
    RiemannSpace D ≤ RiemannSpace E := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  refine Or.inr fun P ↦ le_trans ?_ (hf P)
  have h1 : D P ≤ E P := h P
  omega

/-- Nonzero constants lie in `L(D)` for effective `D`. -/
theorem algebraMap_mem_riemannSpace {D : Divisor k F} (hD : 0 ≤ D)
    (c : k) : algebraMap k F c ∈ RiemannSpace D := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]
    exact Or.inl rfl
  refine Or.inr fun P ↦ ?_
  rw [Place.ord_algebraMap P hc0]
  have h1 : (0 : ℤ) ≤ D P := hD P
  omega

/-- Membership of a nonzero element forces effectivity where it has
poles; in particular `L(D) = 0` when `D` has somewhere-negative degree
data pointwise. Elementary sanity lemma: if `D ≤ 0` and `D ≠ 0`, any
nonzero `f ∈ L(D)` has a zero at a place where `D` is negative. -/
theorem ord_pos_of_mem_riemannSpace {D : Divisor k F} {f : F}
    (hf : f ∈ RiemannSpace D) (hf0 : f ≠ 0) {P : Place k F}
    (hP : D P < 0) : 0 < P.ord f := by
  rcases hf with rfl | hf
  · exact absurd rfl hf0
  have h1 := hf P
  omega

end

end AclGeom
