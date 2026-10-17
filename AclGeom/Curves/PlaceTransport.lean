/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.PlaceAction

/-!
# Orders at transported places and the order filtration

Transporting a place along a `k`-automorphism `σ` transports its normalized order:
`(P.comap σ).ord x = P.ord (σ x)` (`Place.ord_comap`). The proof compares the two
integer-valued homomorphisms through their common nonnegativity set. The comparison factor is
positive (a uniformizer lies in the maximal ideal) and divides one, so it equals one.

The elements of order at least `m`, together with `0`, form a `k`-subspace
(`Place.ordFiltration`).

Named consumers: the semicontinuity of orders along a regular scheme action and the order
profiles of boundary places, toward the fixed-boundary step of blueprint `lem:affine-action`.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
  [IsFunctionFieldOneVar k F]

/-- The junk order of zero. -/
theorem ord_zero (P : Place k F) : P.ord 0 = 0 := by
  rw [ord, dite_eq_left rfl]

/-- **Orders transport along automorphisms.** -/
theorem ord_comap (σ : F ≃ₐ[k] F) (P : Place k F) (x : F) :
    (P.comap σ).ord x = P.ord (σ x) := by
  have hσ : ∀ {y : F}, y ≠ 0 → σ y ≠ 0 := fun hy ↦ (map_ne_zero σ).2 hy
  -- Both orders have the same nonnegativity set, the valuation ring of `P.comap σ`.
  have key : ∀ y : F, y ≠ 0 → (0 ≤ P.ord (σ y) ↔ 0 ≤ (P.comap σ).ord y) := by
    intro y hy
    rw [P.ord_nonneg_iff (hσ hy), (P.comap σ).ord_nonneg_iff hy,
      P.val.valuation_le_one_iff, (P.comap σ).val.valuation_le_one_iff]
    exact Iff.rfl
  -- Elements of order zero for `P.comap σ` have order zero after transport.
  have hzero : ∀ y : F, y ≠ 0 → (P.comap σ).ord y = 0 → P.ord (σ y) = 0 := by
    intro y hy h0
    have h1 := (key y hy).2 (le_of_eq h0.symm)
    have h2 := (key y⁻¹ (inv_ne_zero hy)).2
      (le_of_eq (by rw [(P.comap σ).ord_inv hy, h0, neg_zero]))
    rw [map_inv₀, P.ord_inv (hσ hy)] at h2
    exact le_antisymm (neg_nonneg.1 h2) h1
  have hpi := (P.comap σ).pi_ne_zero
  -- The comparison factor is positive.
  have hpos : 0 < P.ord (σ (P.comap σ).pi) := by
    refine lt_iff_not_ge.2 fun hle ↦ ?_
    have h1 : 0 ≤ P.ord (σ (P.comap σ).pi⁻¹) := by
      rw [map_inv₀, P.ord_inv (hσ hpi)]
      exact neg_nonneg.2 hle
    have h2 := (key _ (inv_ne_zero hpi)).1 h1
    rw [(P.comap σ).ord_inv hpi, (P.comap σ).ord_pi] at h2
    exact absurd h2 (by norm_num)
  -- The comparison factor divides one, through the transported uniformizer of `P`.
  have hz : σ.symm P.pi ≠ 0 := (map_ne_zero σ.symm).2 P.pi_ne_zero
  have hw0 : (P.comap σ).pi ^ (-(P.comap σ).ord (σ.symm P.pi)) * σ.symm P.pi ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hpi) hz
  have hwQ : (P.comap σ).ord
      ((P.comap σ).pi ^ (-(P.comap σ).ord (σ.symm P.pi)) * σ.symm P.pi) = 0 := by
    rw [(P.comap σ).ord_mul (zpow_ne_zero _ hpi) hz, (P.comap σ).ord_zpow hpi,
      (P.comap σ).ord_pi]
    ring
  have hwP := hzero _ hw0 hwQ
  rw [map_mul, map_zpow₀, AlgEquiv.apply_symm_apply,
    P.ord_mul (zpow_ne_zero _ (hσ hpi)) P.pi_ne_zero, P.ord_zpow (hσ hpi), P.ord_pi] at hwP
  have hd : P.ord (σ (P.comap σ).pi) = 1 := by
    have h : P.ord (σ (P.comap σ).pi) * (P.comap σ).ord (σ.symm P.pi) = 1 := by
      linear_combination -hwP
    exact Int.eq_one_of_mul_eq_one_right hpos.le h
  -- Conclude for an arbitrary element.
  by_cases hx : x = 0
  · rw [hx, map_zero, ord_zero, ord_zero]
  have hu0 : (P.comap σ).pi ^ (-(P.comap σ).ord x) * x ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hpi) hx
  have huQ : (P.comap σ).ord ((P.comap σ).pi ^ (-(P.comap σ).ord x) * x) = 0 := by
    rw [(P.comap σ).ord_mul (zpow_ne_zero _ hpi) hx, (P.comap σ).ord_zpow hpi,
      (P.comap σ).ord_pi]
    ring
  have huP := hzero _ hu0 huQ
  rw [map_mul, map_zpow₀, P.ord_mul (zpow_ne_zero _ (hσ hpi)) (hσ hx),
    P.ord_zpow (hσ hpi), hd] at huP
  linarith

/-- The elements of order at least `m` at a place, together with `0`, form a `k`-subspace. -/
def ordFiltration (P : Place k F) (m : ℤ) : Submodule k F where
  carrier := {w | w = 0 ∨ m ≤ P.ord w}
  add_mem' {a b} ha hb := by
    change a + b = 0 ∨ m ≤ P.ord (a + b)
    by_cases ha0 : a = 0
    · rw [ha0, zero_add]
      exact hb
    by_cases hb0 : b = 0
    · rw [hb0, add_zero]
      exact ha
    by_cases hab : a + b = 0
    · exact Or.inl hab
    exact Or.inr ((le_min (Or.resolve_left ha ha0) (Or.resolve_left hb hb0)).trans
      (P.min_ord_le_ord_add ha0 hb0 hab))
  zero_mem' := Or.inl rfl
  smul_mem' c {w} hw := by
    change c • w = 0 ∨ m ≤ P.ord (c • w)
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Or.inl rfl
    by_cases hw0 : w = 0
    · rw [hw0, smul_zero]
      exact Or.inl rfl
    refine Or.inr ?_
    rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).2 hc) hw0, P.ord_algebraMap hc, zero_add]
    exact Or.resolve_left hw hw0

/-- Membership of a nonzero element in the order filtration is the order inequality. -/
theorem mem_ordFiltration (P : Place k F) {m : ℤ} {w : F} (hw : w ≠ 0) :
    w ∈ P.ordFiltration m ↔ m ≤ P.ord w :=
  ⟨fun h ↦ Or.resolve_left h hw, Or.inr⟩

end Place

end AclGeom
