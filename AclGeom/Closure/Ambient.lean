/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic

/-!
# Ambient invariance of the relative algebraic closure

The opening line of the blueprint's descent proof (§9.1): the closure
relation on tuples from a subextension `N` is unchanged when computed in
the ambient field — `x ∈ racl k S` inside `N` iff `x ∈ racl k S` inside
`Ω`. Consequently the point geometry of `N/k` embeds in that of `Ω/k`.

The workhorse is the ambient-coefficient polynomial characterization of
closure membership, `mem_racl_iff_exists_poly`, which transports along the
inclusion `N.val` in both directions.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5 descent, foundation).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Membership in `racl k S` via an ambient-coefficient annihilator: `x` is
in the closure iff some nonzero polynomial over `Ω` with coefficients in
`k(S)` vanishes at `x`. -/
theorem mem_racl_iff_exists_poly {S : Set Ω} {x : Ω} :
    x ∈ racl k S ↔ ∃ p : Polynomial Ω, p ≠ 0 ∧ p.eval x = 0 ∧
      ∀ n, p.coeff n ∈ adjoin k S := by
  constructor
  · intro hx
    obtain ⟨g, hg0, hgx⟩ := (mem_racl_iff k).1 hx
    refine ⟨g.map (algebraMap (adjoin k S) Ω), ?_, ?_, fun n ↦ ?_⟩
    · exact (Polynomial.map_ne_zero_iff
        (algebraMap (adjoin k S) Ω).injective).2 hg0
    · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hgx]
    · rw [Polynomial.coeff_map]
      exact (g.coeff n).2
  · rintro ⟨p, hp0, hpx, hpc⟩
    exact (mem_racl_iff k).2 (isAlgebraic_of_coeff_mem hp0 hpx hpc)

/-- **Ambient invariance of `racl`** (blueprint §9.1, opening line): for a
subextension `N` of `Ω/k`, membership in the closure of a subset of `N` is
the same computed in `N` or in `Ω`. -/
theorem coe_mem_racl_image_iff {N : IntermediateField k Ω} {S : Set N}
    {x : N} :
    (x : Ω) ∈ racl k ((↑) '' S : Set Ω) ↔ x ∈ racl k S := by
  constructor
  · intro hx
    obtain ⟨p, hp0, hpx, hpc⟩ := mem_racl_iff_exists_poly.1 hx
    -- The coefficients lie in `N`, so the annihilator lifts to `N[X]`.
    have hadj : adjoin k (((↑) : N → Ω) '' S) =
        (adjoin k S).map N.val := (adjoin_map k S N.val).symm
    have hN : ∀ n, p.coeff n ∈ N := fun n ↦ by
      have h1 := hpc n
      rw [hadj] at h1
      obtain ⟨c₀, -, hc⟩ := h1
      rw [← hc]
      exact c₀.2
    obtain ⟨q₀, hq₀⟩ := (Polynomial.mem_lifts
        (f := algebraMap N Ω) p).1 <|
      (Polynomial.lifts_iff_coeff_lifts p).2 fun n ↦ ⟨⟨p.coeff n, hN n⟩, rfl⟩
    refine mem_racl_iff_exists_poly.2 ⟨q₀, ?_, ?_, fun n ↦ ?_⟩
    · intro h0
      rw [h0, Polynomial.map_zero] at hq₀
      exact hp0 hq₀.symm
    · have h1 : algebraMap N Ω (q₀.eval x) = p.eval (x : Ω) := by
        rw [← hq₀, Polynomial.eval_map,
          show ((x : Ω)) = algebraMap N Ω x from rfl,
          Polynomial.eval₂_at_apply]
      rw [hpx] at h1
      exact (algebraMap N Ω).injective (by rw [h1, map_zero])
    · have h1 : (q₀.coeff n : Ω) = p.coeff n := by
        rw [← hq₀, Polynomial.coeff_map]
        rfl
      have h2 := hpc n
      rw [hadj, ← h1] at h2
      obtain ⟨c₀, hc₀, hc⟩ := h2
      have h3 : c₀ = q₀.coeff n := Subtype.ext hc
      rwa [← h3]
  · intro hx
    obtain ⟨q₀, hq0, hqx, hqc⟩ :=
      (mem_racl_iff_exists_poly (S := S) (x := x)).1 hx
    refine mem_racl_iff_exists_poly.2
      ⟨q₀.map (algebraMap N Ω), ?_, ?_, fun n ↦ ?_⟩
    · exact (Polynomial.map_ne_zero_iff (algebraMap N Ω).injective).2 hq0
    · rw [Polynomial.eval_map,
        show ((x : Ω)) = algebraMap N Ω x from rfl,
        Polynomial.eval₂_at_apply, hqx, map_zero]
    · rw [Polynomial.coeff_map]
      have h1 : (algebraMap N Ω) (q₀.coeff n) ∈ (adjoin k S).map N.val :=
        ⟨q₀.coeff n, hqc n, rfl⟩
      rwa [adjoin_map k S N.val] at h1

/-- Ambient invariance, singleton form. -/
theorem coe_mem_racl_singleton_iff {N : IntermediateField k Ω} {w x : N} :
    (x : Ω) ∈ racl k ({(w : Ω)} : Set Ω) ↔ x ∈ racl k ({w} : Set N) := by
  simpa [Set.image_singleton] using
    coe_mem_racl_image_iff (S := ({w} : Set N)) (x := x)

/-- Ambient invariance, empty-set form: algebraicity over the base is
absolute. -/
theorem coe_mem_racl_empty_iff {N : IntermediateField k Ω} {x : N} :
    (x : Ω) ∈ racl k (∅ : Set Ω) ↔ x ∈ racl k (∅ : Set N) := by
  simpa [Set.image_empty] using
    coe_mem_racl_image_iff (S := (∅ : Set N)) (x := x)

/-- Ambient invariance, pair form. -/
theorem coe_mem_racl_pair_iff {N : IntermediateField k Ω} {w₁ w₂ x : N} :
    (x : Ω) ∈ racl k ({(w₁ : Ω), (w₂ : Ω)} : Set Ω) ↔
      x ∈ racl k ({w₁, w₂} : Set N) := by
  simpa [Set.image_pair] using
    coe_mem_racl_image_iff (S := ({w₁, w₂} : Set N)) (x := x)

/-- **Base insensitivity of the closure** (blueprint §9.1: closures over
`k` and over `k̄` agree): enlarging the base field by elements algebraic
over it does not change `racl`. -/
theorem mem_racl_base_iff_of_algebraic {K₀ : IntermediateField k Ω}
    (halg : ∀ y ∈ K₀, IsAlgebraic k y) {S : Set Ω} {z : Ω} :
    z ∈ racl (↥K₀) S ↔ z ∈ racl k S := by
  constructor
  · intro hz
    -- Transport the annihilator to the `k`-closure of `↑K₀ ∪ S`, then
    -- absorb the algebraic generators.
    have h1 : IsAlgebraic (adjoin (↥K₀) S) z := (mem_racl_iff (↥K₀)).1 hz
    have h2 : z ∈ racl k ((K₀ : Set Ω) ∪ S) := by
      refine mem_racl_iff_exists_poly.2 ?_
      obtain ⟨p, hp0, hpz⟩ := h1
      refine ⟨p.map (algebraMap (adjoin (↥K₀) S) Ω),
        (Polynomial.map_ne_zero_iff
          (algebraMap (adjoin (↥K₀) S) Ω).injective).2 hp0,
        ?_, fun n ↦ ?_⟩
      · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpz]
      · rw [Polynomial.coeff_map]
        have h3 : ((p.coeff n : ↥(adjoin (↥K₀) S)) : Ω) ∈
            (adjoin (↥K₀) S).restrictScalars k :=
          (mem_restrictScalars k).2 (p.coeff n).2
        rwa [restrictScalars_adjoin] at h3
    refine racl_le_of_subset_racl ?_ h2
    rintro y (hy | hy)
    · exact racl_mono (Set.empty_subset S)
        (mem_racl_empty_of_isAlgebraic (halg y hy))
    · exact subset_racl k S hy
  · intro hz
    exact racl_subset_racl_base K₀ S hz

/-- Pair independence is insensitive to algebraic base enlargement: an
independent pair over `k` stays independent over any subextension of
algebraic elements. -/
theorem algebraicIndependent_pair_base_of_algebraic
    {K₀ : IntermediateField k Ω} (halg : ∀ y ∈ K₀, IsAlgebraic k y)
    {x a : Ω} (hind : AlgebraicIndependent k ![x, a]) :
    AlgebraicIndependent (↥K₀) ![x, a] := by
  refine algebraicIndependent_pair ?_ ?_
  · rw [mem_racl_base_iff_of_algebraic halg]
    exact AlgebraicIndependent.notMem_racl_pair' hind
  · rw [mem_racl_base_iff_of_algebraic halg]
    exact AlgebraicIndependent.notMem_racl_pair hind

/-- Equivariance of ambient closure membership under automorphisms of a
subextension: interalgebraicity relations between elements of `N` are
preserved by any `k`-automorphism of `N`, viewed in `Ω`. -/
theorem coe_mem_racl_singleton_map {N : IntermediateField k Ω}
    (σ : N ≃ₐ[k] N) {z w : N}
    (h : (z : Ω) ∈ racl k ({(w : Ω)} : Set Ω)) :
    (σ z : Ω) ∈ racl k ({(σ w : Ω)} : Set Ω) := by
  rw [coe_mem_racl_singleton_iff] at h ⊢
  simpa [Set.image_singleton] using mem_racl_map σ h

/-- Equivariance of ambient transcendence under automorphisms of a
subextension. -/
theorem coe_notMem_racl_empty_map {N : IntermediateField k Ω}
    (σ : N ≃ₐ[k] N) {z : N}
    (h : (z : Ω) ∉ racl k (∅ : Set Ω)) :
    (σ z : Ω) ∉ racl k (∅ : Set Ω) := by
  intro hmem
  rw [coe_mem_racl_empty_iff] at hmem
  have h2 := mem_racl_map σ.symm hmem
  rw [Set.image_empty, AlgEquiv.symm_apply_apply] at h2
  exact h ((coe_mem_racl_empty_iff (N := N)).2 h2)

end

end AclGeom
