/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Multiplicative

/-!
# Quotients of multiplicative coset equations

Two pairs `(x₁, y₁)`, `(x₂, y₂)` satisfying multiplicative coset equations with common nonzero
exponents, `x₁^a y₁^b = c₁` and `x₂^a y₂^b = c₂`, have interalgebraic coordinate quotients:
`(y₁/y₂)^b = (c₁/c₂) (x₁/x₂)^{-a}` (`interalgebraic_div_of_coset_equations`).  This is pure algebra,
with no closure hypothesis on the base.

With the multiplicative correspondence theorem (`MulCorrSetup.exists_coset_equations`), whose
inputs are an algebraically closed base, an algebraically closed ambient field and a fresh element,
it gives `MulCorrSetup.interalgebraic_div`.  Its #25 consumer is the step (★) of the Q′ refutation:
for `x₁ = s`, `x₂ = s t²` and the semantic representatives `y₁ = x₀`, `y₂ = y₀`, the quotient
`x₀/y₀` is interalgebraic with `s/(s t²) = t⁻²`, hence with `t`.

The reusable integer-power helper `MulCorrSetup.zpow_mem_racl` is public in
`AclGeom.Correspondence.Multiplicative`; it avoids a slow instance search. This module consumes
that helper directly, with no duplicate copy.

**Status:** the displayed prerequisite lemmas are proved. The specific Q/Q′ refutations
remain open (#25).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **Quotients of coset equations.**  Two pairs with multiplicative coset equations of common
nonzero exponents have interalgebraic quotients: `y₁/y₂` and `x₁/x₂` lie in each other's
closure. -/
theorem interalgebraic_div_of_coset_equations {x₁ y₁ x₂ y₂ : Ω} {a b : ℤ} {c₁ c₂ : k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (h₁ : x₁ ^ a * y₁ ^ b = algebraMap k Ω c₁) (h₂ : x₂ ^ a * y₂ ^ b = algebraMap k Ω c₂) :
    y₁ / y₂ ∈ racl k {x₁ / x₂} ∧ x₁ / x₂ ∈ racl k {y₁ / y₂} := by
  have hX : (x₁ / x₂) ^ a ≠ 0 := zpow_ne_zero a (div_ne_zero hx₁ hx₂)
  have hY : (y₁ / y₂) ^ b ≠ 0 := zpow_ne_zero b (div_ne_zero hy₁ hy₂)
  have hq : (x₁ / x₂) ^ a * (y₁ / y₂) ^ b = algebraMap k Ω (c₁ / c₂) := by
    rw [div_zpow, div_zpow, div_mul_div_comm, h₁, h₂, map_div₀]
  -- `(y₁/y₂)^b` lies over `x₁/x₂`, and `(x₁/x₂)^a` lies over `y₁/y₂`.
  have hYb : (y₁ / y₂) ^ b ∈ racl k {x₁ / x₂} := by
    have h : (y₁ / y₂) ^ b = algebraMap k Ω (c₁ / c₂) / (x₁ / x₂) ^ a :=
      (eq_div_iff hX).2 (by rw [mul_comm]; exact hq)
    rw [h]
    exact div_mem (IntermediateField.algebraMap_mem _ _)
      (MulCorrSetup.zpow_mem_racl (subset_racl k {x₁ / x₂} rfl) a)
  have hXa : (x₁ / x₂) ^ a ∈ racl k {y₁ / y₂} := by
    have h : (x₁ / x₂) ^ a = algebraMap k Ω (c₁ / c₂) / (y₁ / y₂) ^ b := (eq_div_iff hY).2 hq
    rw [h]
    exact div_mem (IntermediateField.algebraMap_mem _ _)
      (MulCorrSetup.zpow_mem_racl (subset_racl k {y₁ / y₂} rfl) b)
  constructor
  · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hYb) (mem_racl_singleton_zpow hb)
  · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hXa) (mem_racl_singleton_zpow ha)

/-- **The quotient of a multiplicative correspondence pair.**  Under the hypotheses of the
multiplicative correspondence theorem the quotients `y₁/y₂` and `x₁/x₂` are interalgebraic.  That
theorem needs an algebraically closed base `k`, an algebraically closed `Ω`, and an element `s`
fresh over the two generic points. -/
theorem MulCorrSetup.interalgebraic_div [IsAlgClosed k] [IsAlgClosed Ω] (S : MulCorrSetup k Ω)
    {s : Ω} (hs : s ∉ racl k {S.x₁, S.x₂}) :
    S.y₁ / S.y₂ ∈ racl k {S.x₁ / S.x₂} ∧ S.x₁ / S.x₂ ∈ racl k {S.y₁ / S.y₂} := by
  obtain ⟨a, b, c₁, c₂, ha, hb, -, -, h₁, h₂⟩ := S.exists_coset_equations hs
  exact interalgebraic_div_of_coset_equations ha hb S.x₁_ne S.x₂_ne S.y₁_ne S.y₂_ne h₁ h₂

end AclGeom
