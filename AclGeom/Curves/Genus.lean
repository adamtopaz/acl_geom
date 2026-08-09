/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.DegreeBound
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Riemann's inequality and the genus

The **defect** of a divisor is `deg D + 1 − ℓ(D)`. It is monotone in the
divisor (the subtraction bound) and invariant under adding principal
divisors (degree-zero-ness of `div z` plus the multiplication gauge on
`L`-spaces). Riemann's bound (`exists_forall_defect_le`) caps it
uniformly: every divisor is dominated, up to a principal divisor, by a
multiple of the pole divisor `A = (x)_∞` of a fixed transcendental `x`,
and on multiples of `A` the counting family pins the defect below
`deg C + 1 − [F : k(x)]`. The **genus** is the supremum of the defect,
and Riemann's inequality `ℓ(D) ≥ deg D + 1 − g` holds by construction.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The **defect** of a divisor: `deg D + 1 − ℓ(D)`. Riemann's bound
caps it uniformly; its supremum is the genus. -/
noncomputable def Divisor.defect (D : Divisor k F) : ℤ :=
  D.deg + 1 - Module.finrank k (RiemannSpace D)

/-- The defect is monotone: this is the subtraction bound rearranged. -/
theorem Divisor.defect_mono {D E : Divisor k F} (hDE : D ≤ E) :
    D.defect ≤ E.defect := by
  have h := finrank_riemannSpace_le_of_le hDE
  rw [Divisor.defect, Divisor.defect]
  omega

/-- The defect is invariant under adding a principal divisor. -/
theorem Divisor.defect_add_divisorOf (D : Divisor k F) {z : F}
    (hz : z ≠ 0) :
    (D + divisorOf k z).defect = D.defect := by
  rw [Divisor.defect, Divisor.defect, Divisor.deg_add,
    deg_divisorOf_eq_zero', add_zero,
    finrank_riemannSpace_add_divisorOf D hz]

/-- **Riemann's bound**: the defect `deg D + 1 − ℓ(D)` is bounded above
uniformly in the divisor `D`. -/
theorem exists_forall_defect_le :
    ∃ γ : ℤ, ∀ D : Divisor k F, D.defect ≤ γ := by
  classical
  obtain ⟨x, hxtr, hxfin⟩ :=
    IsFunctionFieldOneVar.exists_transcendental_finite (k := k) (F := F)
  haveI := hxfin
  set n := Module.finrank (↥(adjoin k ({x} : Set F))) F with hn
  have hnpos : 0 < n := Module.finrank_pos
  obtain ⟨C, hC0, hbound⟩ := exists_effective_riemannSpace_lower_bound hxtr
  set A : Divisor k F := poleDivisor k x with hA
  have hdegA : A.deg = (n : ℤ) := deg_poleDivisor_eq_finrank hxtr
  -- On multiples of `A`, the counting family bounds `ℓ` from below.
  have hlow : ∀ N : ℕ, ((N : ℤ) + 1) * (n : ℤ) - C.deg ≤
      (Module.finrank k (RiemannSpace ((N : ℤ) • A)) : ℤ) := by
    intro N
    have hb : ((N : ℤ) + 1) * (n : ℤ) ≤
        (Module.finrank k (RiemannSpace ((N : ℤ) • A + C)) : ℤ) := by
      exact_mod_cast hbound N
    have hle1 : (N : ℤ) • A ≤ (N : ℤ) • A + C := by
      intro P
      rw [Finsupp.add_apply]
      have h1 : 0 ≤ C P := by simpa using hC0 P
      omega
    have hsub := finrank_riemannSpace_le_of_le hle1
    have hdeg1 : ((N : ℤ) • A + C).deg = ((N : ℤ) • A).deg + C.deg :=
      Divisor.deg_add _ _
    linarith [hb, hsub, hdeg1]
  refine ⟨C.deg + 1 - n, fun D ↦ ?_⟩
  -- Reduce to the effective part.
  have h1 : D.defect ≤ D.pos.defect := Divisor.defect_mono (Divisor.le_pos D)
  set E : Divisor k F := D.pos with hE
  have hE0 : 0 ≤ E := Divisor.pos_nonneg D
  -- A high multiple of `A` dominates `E` up to a principal divisor.
  set m : ℕ := (C.deg + E.deg).toNat + 1 with hm
  have hkey : (0 : ℤ) <
      Module.finrank k (RiemannSpace ((m : ℤ) • A - E)) := by
    have hle2 : (m : ℤ) • A - E ≤ (m : ℤ) • A := by
      intro P
      rw [Finsupp.sub_apply]
      have h2 : 0 ≤ E P := by simpa using hE0 P
      omega
    have hsub2 := finrank_riemannSpace_le_of_le hle2
    have hdegsub : ((m : ℤ) • A - E).deg = ((m : ℤ) • A).deg - E.deg :=
      Divisor.deg_sub _ _
    have hlowm := hlow m
    have hmbig : (C.deg + E.deg : ℤ) < (m : ℤ) := by
      rw [hm]
      push_cast
      omega
    have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
    have hmn : ((m : ℤ) + 1) * 1 ≤ ((m : ℤ) + 1) * (n : ℤ) :=
      mul_le_mul_of_nonneg_left hn1 (by positivity)
    linarith [hsub2, hdegsub, hlowm, hmbig, hmn]
  obtain ⟨z, hzmem, hz0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (p := RiemannSpace ((m : ℤ) • A - E))
      (by
        intro hbot
        rw [hbot, finrank_bot] at hkey
        simp at hkey)
  -- `E ≤ m·A + div z`.
  have hle3 : E ≤ (m : ℤ) • A + divisorOf k z := by
    intro P
    rw [mem_riemannSpace_iff] at hzmem
    rcases hzmem with rfl | hzord
    · exact absurd rfl hz0
    have h2 := hzord P
    rw [Finsupp.sub_apply] at h2
    rw [Finsupp.add_apply, divisorOf_apply hz0]
    omega
  -- Chain the comparisons.
  have h4 : E.defect ≤ ((m : ℤ) • A + divisorOf k z).defect :=
    Divisor.defect_mono hle3
  have h5 : ((m : ℤ) • A + divisorOf k z).defect = ((m : ℤ) • A).defect :=
    Divisor.defect_add_divisorOf _ hz0
  have h6 : ((m : ℤ) • A).defect ≤ C.deg + 1 - n := by
    rw [Divisor.defect]
    have hlowm := hlow m
    have hdegmA : ((m : ℤ) • A).deg = (m : ℤ) * (n : ℤ) := by
      rw [Divisor.deg_smul, hdegA]
    have hexp : ((m : ℤ) + 1) * (n : ℤ) = (m : ℤ) * (n : ℤ) + n := by
      ring
    linarith [hlowm, hdegmA, hexp]
  omega

variable (k F) in
/-- The **genus** of the function field: the supremum of the defect
`deg D + 1 − ℓ(D)` over all divisors. Well-defined by Riemann's bound,
realized as `0` at `D = 0`, hence nonnegative. -/
noncomputable def genus : ℤ :=
  sSup (Set.range fun D : Divisor k F ↦ D.defect)

/-- Every defect is at most the genus. -/
theorem defect_le_genus (D : Divisor k F) : D.defect ≤ genus k F := by
  obtain ⟨γ, hγ⟩ := exists_forall_defect_le (k := k) (F := F)
  exact le_csSup ⟨γ, by rintro r ⟨D', rfl⟩; exact hγ D'⟩ ⟨D, rfl⟩

/-- **Riemann's inequality**: `ℓ(D) ≥ deg D + 1 − g`. -/
theorem riemann_inequality (D : Divisor k F) :
    D.deg + 1 - genus k F ≤ (Module.finrank k (RiemannSpace D) : ℤ) := by
  have h := defect_le_genus D
  rw [Divisor.defect] at h
  omega

/-- The genus is nonnegative: the zero divisor has defect zero. -/
theorem genus_nonneg : 0 ≤ genus k F := by
  have h := defect_le_genus (0 : Divisor k F)
  rw [Divisor.defect, Divisor.deg_zero, riemannSpace_zero] at h
  have h1 : Module.finrank k
      (LinearMap.range (Algebra.linearMap k F)) = 1 := by
    rw [LinearMap.finrank_range_of_inj
      (show Function.Injective (Algebra.linearMap k F) from
        (algebraMap k F).injective), Module.finrank_self]
  rw [h1] at h
  omega

end

end AclGeom
