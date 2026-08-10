/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Differentials

/-!
# The duality theorem and the canonical class

For a nonzero Weil differential with maximal level `W`, the
multiplication pairing `L(W − D) → Ω(D)` is bijective: injectivity is
the cancellation of multiplication, surjectivity combines the
proportionality theorem with the shift of the maximal level. Hence
`i(D) = ℓ(W − D)` — the duality theorem (Stichtenoth 1.5.15) — and
evaluating at `D = 0` and `D = W` pins the canonical class:
`ℓ(W) = g` and `deg W = 2g − 2`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- `L(0)` is one-dimensional: the constants. -/
theorem finrank_riemannSpace_zero :
    Module.finrank k (RiemannSpace (0 : Divisor k F)) = 1 := by
  rw [riemannSpace_zero, LinearMap.finrank_range_of_inj
    (show Function.Injective (Algebra.linearMap k F) from
      (algebraMap k F).injective), Module.finrank_self]

/-- **The duality theorem** (Stichtenoth 1.5.15): for a nonzero
differential with maximal level `W`, the multiplication pairing
identifies `L(W − D)` with the level-`D` differentials, so
`i(D) = ℓ(W − D)` for every divisor `D`. -/
theorem specialtyIndex_eq_finrank_riemannSpace
    {ω : Module.Dual k ↥(adeleSubmodule k F)} (hω0 : ω ≠ 0)
    {W : Divisor k F} (hW : ω ∈ weilDifferentialsAt W)
    (hmax : ∀ D, ω ∈ weilDifferentialsAt D → D ≤ W)
    (D : Divisor k F) :
    specialtyIndex D =
      (Module.finrank k (RiemannSpace (W - D)) : ℤ) := by
  have hle : D + (W - D) ≤ W := le_of_eq (by abel)
  set μ := differentialPairing hW hle with hμ
  have hinj : Function.Injective μ := by
    intro f g hfg
    have h1 : ω ∘ₗ adeleSMul (f : F) = ω ∘ₗ adeleSMul (g : F) :=
      congrArg Subtype.val hfg
    by_contra hne
    have hsub : (f : F) - (g : F) ≠ 0 :=
      fun h0 ↦ hne (Subtype.ext (sub_eq_zero.1 h0))
    have h2 : ω ∘ₗ adeleSMul ((f : F) - (g : F)) = 0 := by
      rw [adeleSMul_sub, LinearMap.comp_sub, h1, sub_self]
    exact comp_adeleSMul_ne_zero hsub hω0 h2
  have hsurj : Function.Surjective μ := by
    rintro ⟨ω', hω'⟩
    rcases eq_or_ne ω' 0 with rfl | hω'0
    · exact ⟨0, Subtype.ext (by rw [map_zero]; rfl)⟩
    · obtain ⟨f, hf0, hf⟩ :=
        exists_eq_comp_adeleSMul hω0 hω'0 hW hω'
      have hmem : f ∈ RiemannSpace (W - D) := by
        have h3 := (isGreatest_level_comp hW hmax hf0).2 D (hf ▸ hω')
        rw [mem_riemannSpace_iff]
        refine Or.inr fun P ↦ ?_
        have h4 := h3 P
        rw [Finsupp.add_apply, divisorOf_apply hf0] at h4
        rw [Finsupp.sub_apply]
        omega
      exact ⟨⟨f, hmem⟩, Subtype.ext hf.symm⟩
  have hequiv := LinearEquiv.ofBijective μ ⟨hinj, hsurj⟩
  have h5 := hequiv.finrank_eq
  have h6 := finrank_weilDifferentialsAt (k := k) (F := F) D
  omega

/-- The divisor of every nonzero Weil differential has degree
`2g - 2`: any greatest level represents the canonical class. -/
theorem deg_eq_two_mul_genus_sub_two_of_isGreatest_level
    {ω : Module.Dual k ↥(adeleSubmodule k F)} (hω0 : ω ≠ 0)
    {W : Divisor k F} (hW : ω ∈ weilDifferentialsAt W)
    (hmax : ∀ D, ω ∈ weilDifferentialsAt D → D ≤ W) :
    W.deg = 2 * genus k F - 2 := by
  have hdual := specialtyIndex_eq_finrank_riemannSpace hω0 hW hmax
  have h0 : specialtyIndex (0 : Divisor k F) = genus k F := by
    have h := finrank_riemannSpace_eq_add_specialtyIndex
      (0 : Divisor k F)
    rw [finrank_riemannSpace_zero, Divisor.deg_zero] at h
    omega
  have hlW : (Module.finrank k (RiemannSpace W) : ℤ) = genus k F := by
    have h := hdual 0
    rw [sub_zero, h0] at h
    omega
  have hiW : specialtyIndex W = 1 := by
    have h := hdual W
    rw [sub_self, finrank_riemannSpace_zero] at h
    omega
  have hRR := finrank_riemannSpace_eq_add_specialtyIndex W
  omega

/-- **The canonical class** (Stichtenoth 1.5.15–1.5.17): a divisor `W`
with `i(D) = ℓ(W − D)` for every `D`, of degree `2g − 2` and dimension
`ℓ(W) = g`. With it, Riemann–Roch reads
`ℓ(D) = deg D + 1 − g + ℓ(W − D)`. -/
theorem exists_canonicalDivisor :
    ∃ W : Divisor k F,
      (∀ D : Divisor k F, specialtyIndex D =
        (Module.finrank k (RiemannSpace (W - D)) : ℤ)) ∧
      W.deg = 2 * genus k F - 2 ∧
      (Module.finrank k (RiemannSpace W) : ℤ) = genus k F := by
  obtain ⟨D₁, ω, hω, hω0⟩ :=
    exists_ne_zero_mem_weilDifferentialsAt (k := k) (F := F)
  obtain ⟨W, hW, hmax⟩ := exists_isGreatest_level hω0 hω
  have hdual := specialtyIndex_eq_finrank_riemannSpace hω0 hW hmax
  have h0 : specialtyIndex (0 : Divisor k F) = genus k F := by
    have h := finrank_riemannSpace_eq_add_specialtyIndex
      (0 : Divisor k F)
    rw [finrank_riemannSpace_zero, Divisor.deg_zero] at h
    omega
  have hlW : (Module.finrank k (RiemannSpace W) : ℤ) = genus k F := by
    have h := hdual 0
    rw [sub_zero, h0] at h
    omega
  have hiW : specialtyIndex W = 1 := by
    have h := hdual W
    rw [sub_self, finrank_riemannSpace_zero] at h
    omega
  have hRR := finrank_riemannSpace_eq_add_specialtyIndex W
  exact ⟨W, hdual, by omega, hlW⟩

end

end AclGeom
