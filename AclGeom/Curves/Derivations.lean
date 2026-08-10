/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.GlobalResidue
import Mathlib.RingTheory.Derivation.Basic

/-!
# Regular derivations of one-variable function fields

Everywhere-regular derivations are the function-field incarnation of
global vector fields on the nonsingular projective curve.  Residue
differentials and their greatest levels bound such derivations locally;
the negative degree of the tangent divisor then forces rigidity in
genus at least two, and after one prescribed zero in genus one.

This module is part of the formalization of the
Evans–Hrushovski–Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The local `k`-subspace of elements whose order at `P` is at least
`r`, together with zero. -/
noncomputable def Place.orderSubmodule (P : Place k F) (r : ℤ) :
    Submodule k F where
  carrier := {x | x = 0 ∨ r ≤ P.ord x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simpa using hx
    rcases eq_or_ne (x + y) 0 with hxy | hxy
    · exact Or.inl hxy
    refine Or.inr ?_
    have hmin := P.min_ord_le_ord_add hx0 hy0 hxy
    have hx' := hx.resolve_left hx0
    have hy' := hy.resolve_left hy0
    omega
  smul_mem' := by
    intro c x hx
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (zero_smul k x)
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl (smul_zero c)
    refine Or.inr ?_
    rw [Algebra.smul_def,
      P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hx0,
      P.ord_algebraMap hc0, zero_add]
    exact hx.resolve_left hx0

theorem Place.mem_orderSubmodule_iff {P : Place k F} {r : ℤ} {x : F} :
    x ∈ P.orderSubmodule r ↔ x = 0 ∨ r ≤ P.ord x := Iff.rfl

/-- Increasing the required order shrinks the local order subspace. -/
theorem Place.orderSubmodule_antitone (P : Place k F) {r s : ℤ}
    (h : r ≤ s) : P.orderSubmodule s ≤ P.orderSubmodule r := by
  intro x hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (h.trans hx)

/-- Orders add under multiplication, including the zero cases. -/
theorem Place.mul_mem_orderSubmodule (P : Place k F) {a b : F}
    {r s : ℤ} (ha : a ∈ P.orderSubmodule r)
    (hb : b ∈ P.orderSubmodule s) :
    a * b ∈ P.orderSubmodule (r + s) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (zero_mul b)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inl (mul_zero a)
  refine Or.inr ?_
  rw [P.ord_mul ha0 hb0]
  have ha' := ha.resolve_left ha0
  have hb' := hb.resolve_left hb0
  omega

/-- Order zero is the valuation ring. -/
theorem Place.orderSubmodule_zero (P : Place k F) :
    P.orderSubmodule 0 = P.toSubmodule := by
  rw [← P.filtration_zero]
  ext x
  rw [Place.mem_orderSubmodule_iff, Place.mem_filtration_iff_ord]
  simp only [Nat.cast_zero, neg_zero]

/-- A uniformizer power has its expected local order. -/
theorem Place.pow_pi_mem_orderSubmodule (P : Place k F) (n : ℕ) :
    P.pi ^ n ∈ P.orderSubmodule (n : ℤ) := by
  right
  rw [P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]

/-- A derivation is regular at `P` when it preserves the valuation
ring. -/
def DerivationIsRegularAt (D : Derivation k F F)
    (P : Place k F) : Prop :=
  ∀ x ∈ P.toSubmodule, D x ∈ P.toSubmodule

/-- A derivation is regular everywhere when it preserves every
valuation ring. -/
def DerivationIsRegular (D : Derivation k F F) : Prop :=
  ∀ P : Place k F, DerivationIsRegularAt D P

/-- A regular vector field vanishes at `P` when the image of its
valuation ring lies in the maximal ideal (order at least one). -/
def DerivationVanishesAt (D : Derivation k F F)
    (P : Place k F) : Prop :=
  ∀ x ∈ P.toSubmodule, D x ∈ P.orderSubmodule 1

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem DerivationIsRegular.at {D : Derivation k F F}
    (hD : DerivationIsRegular D) (P : Place k F) :
    DerivationIsRegularAt D P := hD P

/-- Vanishing at a place implies regularity there. -/
theorem DerivationVanishesAt.isRegularAt {D : Derivation k F F}
    {P : Place k F} (hD : DerivationVanishesAt D P) :
    DerivationIsRegularAt D P := by
  intro x hx
  rw [← P.orderSubmodule_zero]
  exact P.orderSubmodule_antitone (by omega) (hD x hx)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The derivative of a scalar multiple of a power, with the natural
coefficient expressed in the base field. -/
theorem derivation_smul_pow (D : Derivation k F F) (c : k) (x : F)
    (n : ℕ) :
    D (c • x ^ n) = ((n : k) * c) • (x ^ (n - 1) * D x) := by
  rw [Derivation.map_smul, Derivation.leibniz_pow]
  simp only [Algebra.smul_def]
  change algebraMap k F c * ((n : F) * (x ^ (n - 1) * D x)) =
    algebraMap k F ((n : k) * c) * (x ^ (n - 1) * D x)
  rw [map_mul, map_natCast]
  ring

/-- Taylor coefficients are detected by the monomial residue table.
The residue against `π⁻ⁱ` selects exactly the `i`-th coefficient;
the Taylor tail vanishes by the mirror threshold. -/
theorem Place.residue_zpow_neg_eq_taylorCoeff (P : Place k F)
    {t : F} {n : ℕ} (c : Fin n → k) {b : F}
    (hb : b ∈ P.toSubmodule)
    (ht : t = (∑ j, c j • P.pi ^ (j : ℕ)) + P.pi ^ n * b)
    (i : Fin n) :
    P.residue ((P.pi : F) ^ (-((i : ℕ) : ℤ))) t =
      (i : k) * c i := by
  classical
  let ρ : F →ₗ[k] k :=
    { toFun := fun g ↦ P.residue ((P.pi : F) ^ (-((i : ℕ) : ℤ))) g
      map_add' := fun g h ↦ P.residue_add_right _ _ _
      map_smul' := fun a g ↦ by
        rw [P.residue_smul_right]
        rfl }
  have htail : ρ (P.pi ^ n * b) = 0 := by
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [mul_zero, map_zero]
    apply P.residue_eq_zero_of_ord_ge_mirror (m := (i : ℕ))
    · exact zpow_ne_zero _ P.pi_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hb0
    · rw [P.ord_zpow P.pi_ne_zero, P.ord_pi, mul_one]
    · rw [P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hb0,
        P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
      have hbOrd : 0 ≤ P.ord b :=
        (P.ord_nonneg_iff hb0).2 (Place.mem_toSubmodule_iff.1 hb)
      have hi := i.isLt
      omega
  have hdiag : ρ (c i • P.pi ^ (i : ℕ)) = (i : k) * c i := by
    rw [map_smul]
    change c i *
      P.residue ((P.pi : F) ^ (-((i : ℕ) : ℤ)))
        ((P.pi : F) ^ (i : ℕ)) = (i : k) * c i
    rw [← zpow_natCast, P.residue_zpow_pi_self (by omega)]
    simp only [Int.toNat_natCast]
    ring
  have hoff : ∀ j : Fin n, j ≠ i →
      ρ (c j • P.pi ^ (j : ℕ)) = 0 := by
    intro j hji
    rw [map_smul]
    change c j *
      P.residue ((P.pi : F) ^ (-((i : ℕ) : ℤ)))
        ((P.pi : F) ^ (j : ℕ)) = 0
    rw [← zpow_natCast,
      P.residue_zpow_pi_zpow_eq_zero (by
        intro hzero
        apply hji
        apply Fin.ext
        omega), mul_zero]
  change ρ t = (i : k) * c i
  rw [ht, map_add, map_sum, htail, add_zero]
  rw [Finset.sum_eq_single i]
  · exact hdiag
  · intro j _ hji
    exact hoff j hji
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The integral-place derivation bound with prescribed depth**: if
`D` sends the valuation ring into elements of order at least `r`, then
for integral `t` one has `ord_P(Dt) ≥ W(P) + r`, where `W` is the
greatest level of the residue differential `ω_t`. -/
theorem order_derivation_ge_level_of_mem_of_depth
    (D : Derivation k F F) (P : Place k F) {r : ℤ}
    (hdepth : ∀ x ∈ P.toSubmodule, D x ∈ P.orderSubmodule r)
    {t : F} (htP : t ∈ P.toSubmodule) {W : Divisor k F}
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ P.orderSubmodule (W P + r) := by
  rcases le_or_gt 0 (W P) with hW0 | hWneg
  · set n : ℕ := (W P).toNat + 2 with hn
    have hnInt : (n : ℤ) = W P + 2 := by
      rw [hn, Nat.cast_add, Nat.cast_ofNat, Int.toNat_of_nonneg hW0]
    obtain ⟨c, b, hb, htaylor⟩ := P.exists_taylor htP n
    have hcoeff : ∀ i : Fin n, (i : ℤ) ≤ W P →
        (i : k) * c i = 0 := by
      intro i hi
      have hlocal :=
        (local_behavior_of_isGreatest_level hW hmax P).1
          ((P.pi : F) ^ (-((i : ℕ) : ℤ))) (Or.inr (by
            rw [P.ord_zpow P.pi_ne_zero, P.ord_pi, mul_one]
            omega))
      rw [residueFunctional_adeleSingle,
        P.residue_zpow_neg_eq_taylorCoeff c hb htaylor i] at hlocal
      exact hlocal
    have hDpi : D P.pi ∈ P.orderSubmodule r := by
      apply hdepth
      rw [Place.mem_toSubmodule_iff]
      exact P.pi_valuation_lt_one.le
    have hDb : D b ∈ P.orderSubmodule r := hdepth b hb
    rw [htaylor, map_add, map_sum]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [derivation_smul_pow]
      by_cases hi : (i : ℤ) ≤ W P
      · rw [hcoeff i hi, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hprod := P.mul_mem_orderSubmodule
          (P.pow_pi_mem_orderSubmodule ((i : ℕ) - 1)) hDpi
        refine P.orderSubmodule_antitone
          (s := ((((i : ℕ) - 1 : ℕ) : ℤ) + r)) (by omega) ?_
        · exact hprod
    · rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      refine Submodule.add_mem _ ?_ ?_
      · have hprod := P.mul_mem_orderSubmodule
          (P.pow_pi_mem_orderSubmodule n) hDb
        refine P.orderSubmodule_antitone (s := (n : ℤ) + r)
          (by omega) ?_
        · exact hprod
      · have hDpow : D (P.pi ^ n) ∈
            P.orderSubmodule (((n - 1 : ℕ) : ℤ) + r) := by
          have hform := derivation_smul_pow D (1 : k) P.pi n
          simp only [one_smul, mul_one] at hform
          rw [hform]
          refine Submodule.smul_mem _ _ ?_
          simpa using P.mul_mem_orderSubmodule
            (P.pow_pi_mem_orderSubmodule (n - 1)) hDpi
        have hb0 : b ∈ P.orderSubmodule 0 := by
          rw [P.orderSubmodule_zero]
          exact hb
        have hprod := P.mul_mem_orderSubmodule hb0 hDpow
        refine P.orderSubmodule_antitone
          (s := 0 + (((n - 1 : ℕ) : ℤ) + r)) (by omega) ?_
        · exact hprod
  · exact P.orderSubmodule_antitone (s := r) (by omega) (hdepth t htP)

/-- **The integral-place derivation bound** for a regular derivation. -/
theorem order_derivation_ge_level_of_mem (D : Derivation k F F)
    (P : Place k F) (hreg : DerivationIsRegularAt D P)
    {t : F} (htP : t ∈ P.toSubmodule) {W : Divisor k F}
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ P.orderSubmodule (W P) := by
  have h := order_derivation_ge_level_of_mem_of_depth D P (r := 0)
    (fun x hx ↦ by rw [P.orderSubmodule_zero]; exact hreg x hx)
    htP hW hmax
  simpa using h

/-- **Pole-place transport with prescribed depth**: the integral-place
bound for `t⁻¹` transports to `t` through `Dt = -t²D(t⁻¹)` and
the inverse-level shift. -/
theorem order_derivation_ge_level_of_ord_neg_of_depth
    (D : Derivation k F F) (P : Place k F) {r : ℤ}
    (hdepth : ∀ x ∈ P.toSubmodule, D x ∈ P.orderSubmodule r)
    {t : F} (ht : t ≠ 0) (htP : P.ord t < 0)
    {W : Divisor k F}
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0)
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ P.orderSubmodule (W P + r) := by
  have htinv : t⁻¹ ≠ 0 := inv_ne_zero ht
  have hωinv0 : residueFunctional (k := k) (F := F) t⁻¹ ≠ 0 := by
    intro hzero
    apply hω0
    rw [residueFunctional_eq_neg_comp_inv ht, hzero,
      LinearMap.zero_comp, neg_zero]
  obtain ⟨Winv, hWinv, hmaxinv⟩ := exists_isGreatest_level hωinv0
    (residueFunctional_mem_weilDifferentialsAt htinv)
  have htinvP : t⁻¹ ∈ P.toSubmodule := by
    rw [Place.mem_toSubmodule_iff, ← P.ord_nonneg_iff htinv,
      P.ord_inv ht]
    omega
  have hDinv := order_derivation_ge_level_of_mem_of_depth D P hdepth
    htinvP hWinv hmaxinv
  have hlevel := isGreatest_level_residueFunctional_inv_apply ht
    hW hmax hWinv hmaxinv P
  have ht2 : t ^ 2 ∈ P.orderSubmodule (2 * P.ord t) := by
    right
    rw [P.ord_pow ht]
    norm_num
  have hprod := P.mul_mem_orderSubmodule ht2 hDinv
  have hDt : D t = -(t ^ 2 * D t⁻¹) := by
    have h := D.leibniz_of_mul_eq_one (mul_inv_cancel₀ ht)
    simp only [smul_eq_mul] at h
    rw [h]
    ring
  rw [hDt]
  apply Submodule.neg_mem
  rw [hlevel]
  simpa [add_assoc, add_comm, add_left_comm] using hprod

/-- **Pole-place transport** for a regular derivation. -/
theorem order_derivation_ge_level_of_ord_neg (D : Derivation k F F)
    (P : Place k F) (hreg : DerivationIsRegularAt D P)
    {t : F} (ht : t ≠ 0) (htP : P.ord t < 0)
    {W : Divisor k F}
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0)
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ P.orderSubmodule (W P) := by
  have h := order_derivation_ge_level_of_ord_neg_of_depth D P (r := 0)
    (fun x hx ↦ by rw [P.orderSubmodule_zero]; exact hreg x hx)
    ht htP hω0 hW hmax
  simpa using h

/-- The local integral and pole bounds assemble to
`Dt ∈ L(-W_t)` for an everywhere-regular derivation. -/
theorem derivation_mem_riemannSpace_neg_level
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    {t : F} (ht : t ≠ 0) {W : Divisor k F}
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0)
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ RiemannSpace (-W) := by
  rw [mem_riemannSpace_iff]
  rcases eq_or_ne (D t) 0 with hDt | hDt
  · exact Or.inl hDt
  refine Or.inr fun P ↦ ?_
  rw [Finsupp.neg_apply, neg_neg]
  have hlocal : D t ∈ P.orderSubmodule (W P) := by
    rcases le_or_gt 0 (P.ord t) with htP | htP
    · apply order_derivation_ge_level_of_mem D P (hreg P) _ hW hmax
      rw [Place.mem_toSubmodule_iff, ← P.ord_nonneg_iff ht]
      exact htP
    · exact order_derivation_ge_level_of_ord_neg D P (hreg P)
        ht htP hω0 hW hmax
  exact hlocal.resolve_left hDt

/-- A regular derivation kills every `t` whose residue differential is
nonzero when the genus is at least two. -/
theorem derivation_apply_eq_zero_of_two_le_genus
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    (hgenus : 2 ≤ genus k F) {t : F} (ht : t ≠ 0)
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0) :
    D t = 0 := by
  obtain ⟨W, hW, hmax⟩ := exists_isGreatest_level hω0
    (residueFunctional_mem_weilDifferentialsAt ht)
  have hmem := derivation_mem_riemannSpace_neg_level D hreg ht hω0
    hW hmax
  have hdegW := deg_eq_two_mul_genus_sub_two_of_isGreatest_level
    hω0 hW hmax
  have hdeg : (-W).deg < 0 := by
    rw [Divisor.deg_neg, hdegW]
    omega
  rw [riemannSpace_eq_bot_of_deg_neg hdeg] at hmem
  exact hmem

/-- If a regular derivation additionally vanishes at `P₀`, then the
global bound gains that point: `Dt ∈ L(-W_t-P₀)`. -/
theorem derivation_mem_riemannSpace_neg_level_sub_single
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    (P₀ : Place k F) (hvan : DerivationVanishesAt D P₀)
    {t : F} (ht : t ≠ 0) {W : Divisor k F}
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0)
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ E, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt E → E ≤ W) :
    D t ∈ RiemannSpace (-W - Finsupp.single P₀ 1) := by
  rw [mem_riemannSpace_iff]
  rcases eq_or_ne (D t) 0 with hDt | hDt
  · exact Or.inl hDt
  refine Or.inr fun Q ↦ ?_
  rw [Finsupp.sub_apply, Finsupp.neg_apply]
  rcases eq_or_ne Q P₀ with rfl | hQ
  · rw [Finsupp.single_eq_same]
    have hlocal : D t ∈ Place.orderSubmodule Q (W Q + 1) := by
      rcases le_or_gt 0 (Q.ord t) with htP | htP
      · apply order_derivation_ge_level_of_mem_of_depth D Q
          (r := 1) hvan _ hW hmax
        rw [Place.mem_toSubmodule_iff, ← Q.ord_nonneg_iff ht]
        exact htP
      · exact order_derivation_ge_level_of_ord_neg_of_depth D Q
          (r := 1) hvan ht htP hω0 hW hmax
    have := hlocal.resolve_left hDt
    omega
  · rw [Finsupp.single_eq_of_ne hQ]
    have hlocal : D t ∈ Q.orderSubmodule (W Q) := by
      rcases le_or_gt 0 (Q.ord t) with htQ | htQ
      · apply order_derivation_ge_level_of_mem D Q (hreg Q) _ hW hmax
        rw [Place.mem_toSubmodule_iff, ← Q.ord_nonneg_iff ht]
        exact htQ
      · exact order_derivation_ge_level_of_ord_neg D Q (hreg Q)
          ht htQ hω0 hW hmax
    have := hlocal.resolve_left hDt
    omega

/-- In genus one, a regular derivation that vanishes at one prescribed
place kills every element with nonzero residue differential. -/
theorem derivation_apply_eq_zero_of_genus_eq_one
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    (hgenus : genus k F = 1) (P₀ : Place k F)
    (hvan : DerivationVanishesAt D P₀)
    {t : F} (ht : t ≠ 0)
    (hω0 : residueFunctional (k := k) (F := F) t ≠ 0) :
    D t = 0 := by
  obtain ⟨W, hW, hmax⟩ := exists_isGreatest_level hω0
    (residueFunctional_mem_weilDifferentialsAt ht)
  have hmem := derivation_mem_riemannSpace_neg_level_sub_single
    D hreg P₀ hvan ht hω0 hW hmax
  have hdegW := deg_eq_two_mul_genus_sub_two_of_isGreatest_level
    hω0 hW hmax
  have hdeg : (-W - Finsupp.single P₀ 1).deg < 0 := by
    rw [deg_sub_single, Divisor.deg_neg, hdegW, hgenus]
    norm_num
  rw [riemannSpace_eq_bot_of_deg_neg hdeg] at hmem
  exact hmem

/-- Perturbing a uniformizer by a scalar multiple of an element on
which `D` is nonzero can simultaneously keep the derivative and the
residue differential nonzero.  Each failure condition excludes at
most one scalar, while the algebraically closed base field is
infinite. -/
theorem exists_uniformizer_add_smul_derivation_residue_ne_zero
    (D : Derivation k F F) {u : F} (hDu : D u ≠ 0)
    (P : Place k F) :
    ∃ c : k, D (P.pi + c • u) ≠ 0 ∧
      residueFunctional (k := k) (F := F) (P.pi + c • u) ≠ 0 := by
  classical
  let badD : Set k := {c | D (P.pi + c • u) = 0}
  let badω : Set k :=
    {c | residueFunctional (k := k) (F := F) (P.pi + c • u) = 0}
  have hbadDsub : badD.Subsingleton := by
    intro a ha b hb
    change D (P.pi + a • u) = 0 at ha
    change D (P.pi + b • u) = 0 at hb
    rw [map_add, Derivation.map_smul] at ha hb
    have hab : a • D u = b • D u :=
      add_left_cancel (ha.trans hb.symm)
    exact smul_left_injective k hDu hab
  have hωpi : residueFunctional (k := k) (F := F) P.pi ≠ 0 :=
    residueFunctional_pi_ne_zero P
  have hbadωsub : badω.Subsingleton := by
    intro a ha b hb
    change residueFunctional (k := k) (F := F) (P.pi + a • u) = 0 at ha
    change residueFunctional (k := k) (F := F) (P.pi + b • u) = 0 at hb
    rw [residueFunctional_add, residueFunctional_smul] at ha hb
    rcases eq_or_ne (residueFunctional (k := k) (F := F) u) 0
      with hωu | hωu
    · rw [hωu, smul_zero, add_zero] at ha
      exact (hωpi ha).elim
    · have hab : a • residueFunctional (k := k) (F := F) u =
          b • residueFunctional (k := k) (F := F) u :=
        add_left_cancel (ha.trans hb.symm)
      exact smul_left_injective k hωu hab
  have hbad : (badD ∪ badω).Finite :=
    hbadDsub.finite.union hbadωsub.finite
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hbad.toFinset
  have hc' : c ∉ badD ∪ badω := by
    simpa only [Set.Finite.mem_toFinset] using hc
  rw [Set.mem_union] at hc'
  push Not at hc'
  exact ⟨c, hc'.1, hc'.2⟩

/-- **Automorphism rigidity in genus at least two**: every
everywhere-regular `k`-derivation of the function field is zero.  This
is the vector-field core of blueprint Lemma 8.4. -/
theorem derivation_eq_zero_of_two_le_genus
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    (hgenus : 2 ≤ genus k F) : D = 0 := by
  ext u
  by_contra hDu
  obtain ⟨P⟩ := (inferInstance : Nonempty (Place k F))
  obtain ⟨c, hDt, hωt⟩ :=
    exists_uniformizer_add_smul_derivation_residue_ne_zero D hDu P
  have ht : P.pi + c • u ≠ 0 := by
    intro ht
    rw [ht, map_zero] at hDt
    exact hDt rfl
  exact hDt (derivation_apply_eq_zero_of_two_le_genus D hreg hgenus
    ht hωt)

/-- **Fixed-point rigidity in genus one**: an everywhere-regular
derivation that vanishes at one place is zero. -/
theorem derivation_eq_zero_of_genus_eq_one
    (D : Derivation k F F) (hreg : DerivationIsRegular D)
    (hgenus : genus k F = 1) (P₀ : Place k F)
    (hvan : DerivationVanishesAt D P₀) : D = 0 := by
  ext u
  by_contra hDu
  obtain ⟨c, hDt, hωt⟩ :=
    exists_uniformizer_add_smul_derivation_residue_ne_zero D hDu P₀
  have ht : P₀.pi + c • u ≠ 0 := by
    intro ht
    rw [ht, map_zero] at hDt
    exact hDt rfl
  exact hDt (derivation_apply_eq_zero_of_genus_eq_one D hreg hgenus
    P₀ hvan ht hωt)

end

end AclGeom
