/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Derivations
import AclGeom.Curves.Genus

/-!
# Genus zero from two independent regular derivations

A function field of one variable over an algebraically closed field `K` which has two
`K`-linearly independent everywhere-regular `K`-derivations has genus zero
(`genus_eq_zero_of_linearIndependent_derivations`).

In genus at least two every regular derivation vanishes
(`derivation_eq_zero_of_two_le_genus`). In genus one, a suitable nonzero combination of the
two derivations vanishes at a chosen place: its value at a uniformizer has residue zero, and
then it maps the whole valuation ring into the maximal ideal. Such a derivation is zero
(`derivation_eq_zero_of_genus_eq_one`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
  [IsFunctionFieldOneVar K E]

omit [IsAlgClosed K] [IsFunctionFieldOneVar K E] in
/-- A derivation preserving every proper valuation subring containing `K` is regular. -/
theorem derivationIsRegular_of_forall_valuationSubring {D : Derivation K E E}
    (h : ∀ V : ValuationSubring E, (∀ c : K, algebraMap K E c ∈ V) → V ≠ ⊤ →
      ∀ x ∈ V, D x ∈ V) :
    DerivationIsRegular D := fun P x hx ↦
  Place.mem_toSubmodule_iff.2 ((P.val.valuation_le_one_iff _).2
    (h P.val P.algebraMap_mem P.ne_top x
      ((P.val.valuation_le_one_iff x).1 (Place.mem_toSubmodule_iff.1 hx))))

private theorem mem_orderSubmodule_one_of_valuation_lt_one (P : Place K E) {x : E}
    (hx : P.val.valuation x < 1) : x ∈ P.orderSubmodule 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact Or.inl rfl
  · have := (P.ord_pos_iff hx0).2 hx
    exact Or.inr (by omega)

omit [IsAlgClosed K] [IsFunctionFieldOneVar K E] in
private theorem derivationIsRegular_add_smul {D₀ D₁ : Derivation K E E}
    (h₀ : DerivationIsRegular D₀) (h₁ : DerivationIsRegular D₁) (a b : K) :
    DerivationIsRegular (a • D₀ + b • D₁) := fun P x hx ↦ by
  rw [Derivation.add_apply, Derivation.smul_apply, Derivation.smul_apply]
  exact add_mem (Submodule.smul_mem _ a (h₀ P x hx)) (Submodule.smul_mem _ b (h₁ P x hx))

/-- **First-order expansion.** A regular derivation whose value at a uniformizer lies in the
maximal ideal vanishes at the place: write `x = c + π * y` with `c` a constant and `y`
integral. -/
private theorem derivationVanishesAt_of_pi {D : Derivation K E E}
    (hreg : DerivationIsRegular D) (P : Place K E) (hπ : D P.pi ∈ P.orderSubmodule 1) :
    DerivationVanishesAt D P := by
  intro x hx
  obtain ⟨c, hc⟩ := P.exists_residue (Place.mem_toSubmodule_iff.1 hx)
  have hxc := mem_orderSubmodule_one_of_valuation_lt_one P hc
  have hpinv : P.pi⁻¹ ∈ P.orderSubmodule (-1) :=
    Or.inr (by rw [P.ord_inv P.pi_ne_zero, P.ord_pi])
  obtain ⟨y, hy⟩ : ∃ y, y = (x - algebraMap K E c) * P.pi⁻¹ := ⟨_, rfl⟩
  have hyO : y ∈ P.toSubmodule := by
    rw [← P.orderSubmodule_zero, hy]
    simpa using P.mul_mem_orderSubmodule hxc hpinv
  have hxy : x = algebraMap K E c + P.pi * y := by
    rw [hy, mul_left_comm, mul_inv_cancel₀ P.pi_ne_zero, mul_one]
    ring
  have hpi : P.pi ∈ P.orderSubmodule 1 := by
    simpa using P.pow_pi_mem_orderSubmodule 1
  rw [hxy, map_add, Derivation.map_algebraMap, zero_add, Derivation.leibniz, smul_eq_mul,
    smul_eq_mul]
  refine add_mem ?_ ?_
  · have hDy : D y ∈ P.orderSubmodule 0 := by
      rw [P.orderSubmodule_zero]
      exact hreg P y hyO
    simpa using P.mul_mem_orderSubmodule hpi hDy
  · have hy0 : y ∈ P.orderSubmodule 0 := by
      rw [P.orderSubmodule_zero]
      exact hyO
    simpa using P.mul_mem_orderSubmodule hy0 hπ

/-- **Genus zero from two independent regular derivations.** A function field of one variable
over an algebraically closed field with two linearly independent everywhere-regular
derivations has genus zero. -/
theorem genus_eq_zero_of_linearIndependent_derivations (D : Fin 2 → Derivation K E E)
    (hD : LinearIndependent K D) (hreg : ∀ i, DerivationIsRegular (D i)) :
    genus K E = 0 := by
  have hD' : LinearIndependent K ![D 0, D 1] := by
    have hD2 : D = ![D 0, D 1] := by
      ext i : 1
      fin_cases i <;> rfl
    rw [← hD2]
    exact hD
  have hg0 : 0 ≤ genus K E := genus_nonneg
  by_contra hne
  rcases (show genus K E = 1 ∨ 2 ≤ genus K E by omega) with h1 | h2
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Place K E))
    have hpi : P.pi ∈ P.toSubmodule := Place.mem_toSubmodule_iff.2 P.pi_valuation_lt_one.le
    obtain ⟨c₀, hc₀⟩ := P.exists_residue (Place.mem_toSubmodule_iff.1 (hreg 0 P P.pi hpi))
    obtain ⟨c₁, hc₁⟩ := P.exists_residue (Place.mem_toSubmodule_iff.1 (hreg 1 P P.pi hpi))
    obtain ⟨a, b, hab, hne0⟩ : ∃ a b : K, a * c₀ + b * c₁ = 0 ∧ (a ≠ 0 ∨ b ≠ 0) := by
      by_cases hc : c₀ = 0
      · exact ⟨1, 0, by rw [hc]; ring, Or.inl one_ne_zero⟩
      · exact ⟨c₁, -c₀, by ring, Or.inr (neg_ne_zero.2 hc)⟩
    have hreg' := derivationIsRegular_add_smul (hreg 0) (hreg 1) a b
    have hπ : (a • D 0 + b • D 1) P.pi ∈ P.orderSubmodule 1 := by
      have hid : (a • D 0 + b • D 1) P.pi =
          a • (D 0 P.pi - algebraMap K E c₀) + b • (D 1 P.pi - algebraMap K E c₁) := by
        have h := congrArg (algebraMap K E) hab
        rw [map_add, map_mul, map_mul, map_zero] at h
        simp only [Derivation.add_apply, Derivation.smul_apply, Algebra.smul_def]
        linear_combination h
      rw [hid]
      exact add_mem
        (Submodule.smul_mem _ a (mem_orderSubmodule_one_of_valuation_lt_one P hc₀))
        (Submodule.smul_mem _ b (mem_orderSubmodule_one_of_valuation_lt_one P hc₁))
    have hzero := derivation_eq_zero_of_genus_eq_one _ hreg' h1 P
      (derivationVanishesAt_of_pi hreg' P hπ)
    obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.1 hD' a b hzero
    rcases hne0 with h | h
    · exact h ha
    · exact h hb
  · exact hD.ne_zero 0 (derivation_eq_zero_of_two_le_genus (D 0) (hreg 0) h2)

/-- `genus_eq_zero_of_linearIndependent_derivations`, with regularity stated for every proper
valuation subring containing `K`. -/
theorem genus_eq_zero_of_linearIndependent_regular (D : Fin 2 → Derivation K E E)
    (hD : LinearIndependent K D)
    (hreg : ∀ i (V : ValuationSubring E), (∀ c : K, algebraMap K E c ∈ V) → V ≠ ⊤ →
      ∀ x ∈ V, D i x ∈ V) :
    genus K E = 0 :=
  genus_eq_zero_of_linearIndependent_derivations D hD fun i ↦
    derivationIsRegular_of_forall_valuationSubring (hreg i)

end

end AclGeom
