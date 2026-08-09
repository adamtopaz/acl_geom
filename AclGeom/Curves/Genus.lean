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

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- A one-dimensional extension is trivial: an intermediate field over
which the ambient field has dimension one is everything. -/
theorem intermediateField_eq_top_of_finrank_eq_one
    {K : IntermediateField k F} [FiniteDimensional (↥K) F]
    (h1 : Module.finrank (↥K) F = 1) : K = ⊤ := by
  have hspan : Submodule.span (↥K) ({(1 : F)} : Set F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (one_ne_zero (α := F)), h1]
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span (↥K) ({(1 : F)} : Set F) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
  have hc1 : c • (1 : F) = (c : F) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [← hc, hc1]
  exact c.2

/-- **The genus-zero checkpoint** (blueprint Section 8, curve input; cf.
Stichtenoth 1.6.3): a genus-zero one-variable function field over an
algebraically closed base is rational, with a generator whose pole
divisor is any prescribed place. From `ℓ(P) ≥ deg P + 1 − g = 2` there
is a non-constant `t ∈ L(P)`; its only pole is `P` with order one, so
`[F : k(t)] = deg (t)_∞ = 1` and `t` generates. -/
theorem exists_generator_of_genus_eq_zero (hg : genus k F = 0)
    (P : Place k F) :
    ∃ t : F, Transcendental k t ∧
      poleDivisor k t = Finsupp.single P 1 ∧
      adjoin k ({t} : Set F) = ⊤ := by
  classical
  have hdeg1 : Divisor.deg (Finsupp.single P 1 : Divisor k F) = 1 := by
    rw [Divisor.deg, Finsupp.sum_single_index rfl]
  -- `ℓ(P) ≥ 2`.
  have hl2 := riemann_inequality (Finsupp.single P 1 : Divisor k F)
  rw [hg, hdeg1] at hl2
  have hmono : RiemannSpace (0 : Divisor k F) ≤
      RiemannSpace (Finsupp.single P 1) := by
    apply riemannSpace_mono
    intro Q
    rcases eq_or_ne Q P with rfl | hQ
    · simp [Finsupp.single_eq_same]
    · simp [Finsupp.single_eq_of_ne hQ]
  have hfr0 : Module.finrank k (RiemannSpace (0 : Divisor k F)) = 1 := by
    rw [riemannSpace_zero, LinearMap.finrank_range_of_inj
      (show Function.Injective (Algebra.linearMap k F) from
        (algebraMap k F).injective), Module.finrank_self]
  -- A non-constant element of `L(P)`.
  obtain ⟨t, htmem, htnc⟩ : ∃ t, t ∈ RiemannSpace (Finsupp.single P 1) ∧
      t ∉ RiemannSpace (0 : Divisor k F) := by
    by_contra hcon
    push Not at hcon
    have heq : RiemannSpace (Finsupp.single P 1 : Divisor k F) =
        RiemannSpace (0 : Divisor k F) :=
      le_antisymm (fun t ht ↦ hcon t ht) hmono
    rw [heq, hfr0] at hl2
    omega
  have htc : ∀ c : k, algebraMap k F c ≠ t := by
    intro c hc
    apply htnc
    rw [riemannSpace_zero]
    exact LinearMap.mem_range.2 ⟨c, hc⟩
  have htr : Transcendental k t := by
    intro halg
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic halg
    exact htc c hc
  have ht0 : t ≠ 0 := fun h ↦ htc 0 (by rw [map_zero, h])
  rw [mem_riemannSpace_iff] at htmem
  rcases htmem with rfl | hord
  · exact absurd rfl ht0
  -- `t` has a pole, necessarily at `P` of order one.
  have hpole : ∃ Q : Place k F, Q.ord t < 0 := by
    by_contra hnp
    push Not at hnp
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_valuation_le_one
      fun Q ↦ (Q.ord_nonneg_iff ht0).1 (hnp Q)
    exact htc c hc
  obtain ⟨Q, hQ⟩ := hpole
  have hQP : Q = P := by
    by_contra hne
    have h1 := hord Q
    rw [Finsupp.single_eq_of_ne hne] at h1
    omega
  subst hQP
  have hordP : Q.ord t = -1 := by
    have h1 := hord Q
    rw [Finsupp.single_eq_same] at h1
    omega
  have hpd : poleDivisor k t = Finsupp.single Q 1 := by
    ext R
    rw [poleDivisor_apply ht0]
    rcases eq_or_ne R Q with rfl | hR
    · rw [Finsupp.single_eq_same, hordP]
      rw [show -(-1 : ℤ) = 1 by norm_num, max_eq_left (by norm_num)]
    · have h1 := hord R
      rw [Finsupp.single_eq_of_ne hR] at h1
      rw [Finsupp.single_eq_of_ne hR, max_eq_right (by omega)]
  -- `[F : k(t)] = deg (t)_∞ = 1`, so `t` generates.
  have hfr1 : Module.finrank (↥(adjoin k ({t} : Set F))) F = 1 := by
    have h1 := deg_poleDivisor_eq_finrank htr
    rw [hpd, hdeg1] at h1
    exact_mod_cast h1.symm
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
  exact ⟨t, htr, hpd, intermediateField_eq_top_of_finrank_eq_one hfr1⟩

end

end AclGeom
