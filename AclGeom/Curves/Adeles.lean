/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Genus

/-!
# Adeles of a function field

The places-indexed adele space: families `α P` of field elements that
are integral at all but finitely many places, filtered by the divisor
bounds `A(D)` (`adeleSpace`). The Riemann–Roch space is the pullback of
`A(D)` along the diagonal, and the one-point decomposition
`A(D + P) = A(D) ⊔ span {monomial}` is the local counting device of the
duality theory (Stichtenoth 1.5): unlike its `L(D)`-counterpart the
spanning monomial always exists, concentrated at the single place `P`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

variable (k F) in
/-- The **adele space** of the function field: families of field
elements integral at all but finitely many places. -/
noncomputable def adeleSubmodule : Submodule k ((P : Place k F) → F) where
  carrier := {α | {P : Place k F | α P ≠ 0 ∧ P.ord (α P) < 0}.Finite}
  zero_mem' := by
    refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    exact absurd rfl hP.1
  add_mem' := by
    intro α β hα hβ
    refine Set.Finite.subset (hα.union hβ) fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hP
    obtain ⟨hne, hlt⟩ := hP
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases eq_or_ne (α P) 0 with h0 | h0
    · rw [h0, zero_add] at hne hlt
      exact absurd (h2 hne) (by omega)
    rcases eq_or_ne (β P) 0 with h0' | h0'
    · rw [h0', add_zero] at hne hlt
      exact absurd (h1 h0) (by omega)
    have h3 := P.min_ord_le_ord_add h0 h0' hne
    have h4 := h1 h0
    have h5 := h2 h0'
    rcases min_cases (P.ord (α P)) (P.ord (β P)) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
      rw [hm] at h3 <;> omega
  smul_mem' := by
    intro c α hα
    rcases eq_or_ne c 0 with rfl | hc0
    · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
      simp only [Set.mem_setOf_eq, Pi.smul_apply, zero_smul] at hP
      exact absurd rfl hP.1
    · refine Set.Finite.subset hα fun P hP ↦ ?_
      simp only [Set.mem_setOf_eq, Pi.smul_apply] at hP ⊢
      obtain ⟨hne, hlt⟩ := hP
      have h0 : α P ≠ 0 := fun h ↦ hne (by rw [h, smul_zero])
      refine ⟨h0, ?_⟩
      have h1 : P.ord (c • α P) = P.ord (α P) := by
        rw [Algebra.smul_def,
          P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) h0,
          P.ord_algebraMap hc0, zero_add]
      rw [h1] at hlt
      exact hlt

theorem mem_adeleSubmodule_iff {α : (P : Place k F) → F} :
    α ∈ adeleSubmodule k F ↔
      {P : Place k F | α P ≠ 0 ∧ P.ord (α P) < 0}.Finite := Iff.rfl

/-- The divisor-bounded adele space `A(D)`: families whose order at
each place `P` is at least `-D P`. -/
noncomputable def adeleSpace (D : Divisor k F) :
    Submodule k ((P : Place k F) → F) where
  carrier := {α | ∀ P : Place k F, α P = 0 ∨ -(D P) ≤ P.ord (α P)}
  zero_mem' := fun _ ↦ Or.inl rfl
  add_mem' := by
    intro α β hα hβ P
    rcases eq_or_ne (α P) 0 with h0 | h0
    · have h : (α + β) P = β P := by rw [Pi.add_apply, h0, zero_add]
      rw [h]
      exact hβ P
    rcases eq_or_ne (β P) 0 with h0' | h0'
    · have h : (α + β) P = α P := by rw [Pi.add_apply, h0', add_zero]
      rw [h]
      exact hα P
    rcases eq_or_ne ((α + β) P) 0 with h0'' | h0''
    · exact Or.inl h0''
    have h1 := (hα P).resolve_left h0
    have h2 := (hβ P).resolve_left h0'
    refine Or.inr ?_
    rw [Pi.add_apply] at h0'' ⊢
    exact le_trans (le_min h1 h2) (P.min_ord_le_ord_add h0 h0' h0'')
  smul_mem' := by
    intro c α hα P
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (by rw [Pi.smul_apply, zero_smul])
    rcases eq_or_ne (α P) 0 with h0 | h0
    · exact Or.inl (by rw [Pi.smul_apply, h0, smul_zero])
    have h1 := (hα P).resolve_left h0
    refine Or.inr ?_
    rw [Pi.smul_apply, Algebra.smul_def,
      P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) h0,
      P.ord_algebraMap hc0, zero_add]
    exact h1

theorem mem_adeleSpace_iff {D : Divisor k F} {α : (P : Place k F) → F} :
    α ∈ adeleSpace D ↔
      ∀ P : Place k F, α P = 0 ∨ -(D P) ≤ P.ord (α P) := Iff.rfl

/-- Monotonicity of the bounded adele spaces. -/
theorem adeleSpace_mono {D E : Divisor k F} (h : D ≤ E) :
    adeleSpace D ≤ adeleSpace (E : Divisor k F) := by
  intro α hα P
  rcases hα P with h0 | h0
  · exact Or.inl h0
  · have := h P
    exact Or.inr (by omega)

/-- Bounded adeles are adeles: the exceptional places lie in the
support of the divisor. -/
theorem adeleSpace_le_adeleSubmodule (D : Divisor k F) :
    adeleSpace D ≤ adeleSubmodule k F := by
  intro α hα
  refine Set.Finite.subset D.hasFiniteSupport fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq] at hP
  obtain ⟨hne, hlt⟩ := hP
  have h1 := (hα P).resolve_left hne
  rw [Function.mem_support]
  omega

variable (k F) in
/-- The diagonal embedding of the function field into place-indexed
families. -/
noncomputable def adeleDiagonal : F →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun _ ↦ LinearMap.id

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
@[simp]
theorem adeleDiagonal_apply (f : F) (P : Place k F) :
    adeleDiagonal k F f P = f := rfl

/-- Diagonal families are adeles: the exceptional places are the poles. -/
theorem adeleDiagonal_mem_adeleSubmodule (f : F) :
    adeleDiagonal k F f ∈ adeleSubmodule k F := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [map_zero]
    exact zero_mem _
  refine Set.Finite.subset (finite_setOf_one_lt_valuation hf0)
    fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq, adeleDiagonal_apply] at hP ⊢
  obtain ⟨-, hlt⟩ := hP
  by_contra hle
  push Not at hle
  exact absurd ((P.ord_nonneg_iff hf0).2 hle) (by omega)

/-- The Riemann–Roch space is the diagonal pullback of the bounded
adele space. -/
theorem adeleDiagonal_mem_adeleSpace_iff {D : Divisor k F} {f : F} :
    adeleDiagonal k F f ∈ adeleSpace D ↔ f ∈ RiemannSpace D := by
  rw [mem_adeleSpace_iff, mem_riemannSpace_iff]
  constructor
  · intro h
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    refine Or.inr fun P ↦ ?_
    have h1 := h P
    rw [adeleDiagonal_apply] at h1
    exact h1.resolve_left hf0
  · intro h P
    rcases h with rfl | h
    · exact Or.inl (by rw [map_zero, Pi.zero_apply])
    · exact Or.inr (by rw [adeleDiagonal_apply]; exact h P)

section OnePoint

variable (P : Place k F)

open Classical in
/-- The **monomial adele**: the uniformizer power `π_P ^ n`
concentrated at the single place `P`. -/
noncomputable def adeleMonomial (n : ℤ) : (Q : Place k F) → F :=
  fun Q ↦ if Q = P then P.pi ^ n else 0

theorem adeleMonomial_apply_self (n : ℤ) :
    adeleMonomial P n P = P.pi ^ n := if_pos rfl

theorem adeleMonomial_apply_ne {Q : Place k F} (hQ : Q ≠ P) (n : ℤ) :
    adeleMonomial P n Q = 0 := if_neg hQ

theorem ord_pi_zpow (n : ℤ) : P.ord (P.pi ^ n) = n := by
  rw [P.ord_zpow P.pi_ne_zero, P.ord_pi, mul_one]

/-- The monomial adele lies in `A(D)` as soon as its order clears the
bound at `P`. -/
theorem adeleMonomial_mem_adeleSpace {D : Divisor k F} {n : ℤ}
    (h : -(D P) ≤ n) : adeleMonomial P n ∈ adeleSpace D := by
  intro Q
  rcases eq_or_ne Q P with rfl | hQ
  · refine Or.inr ?_
    rw [adeleMonomial_apply_self, ord_pi_zpow]
    exact h
  · exact Or.inl (adeleMonomial_apply_ne P hQ n)

/-- **The one-point decomposition of adele spaces**: `A(D + P)` is
spanned over `A(D)` by the monomial adele of exact order `-D P - 1`
at `P` — the local gauge is the residue of `α P / π ^ (-D P - 1)`. -/
theorem adeleSpace_add_single (D : Divisor k F) :
    adeleSpace (D + Finsupp.single P 1) =
      adeleSpace D ⊔
        Submodule.span k {adeleMonomial P (-(D P) - 1)} := by
  classical
  have hDP : (D + Finsupp.single P 1 : Divisor k F) P = D P + 1 := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  have hDQ : ∀ Q : Place k F, Q ≠ P →
      (D + Finsupp.single P 1 : Divisor k F) Q = D Q := by
    intro Q hQ
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hQ]
  have hpi0 : P.pi ^ (-(D P) - 1) ≠ 0 := zpow_ne_zero _ P.pi_ne_zero
  refine le_antisymm ?_ ?_
  · intro α hα
    -- If the bound at `P` already clears `-D P`, no gauge is needed.
    by_cases hP : α P = 0 ∨ -(D P) ≤ P.ord (α P)
    · refine Submodule.mem_sup_left fun Q ↦ ?_
      rcases eq_or_ne Q P with rfl | hQ
      · exact hP
      · have h1 := hα Q
        rw [hDQ Q hQ] at h1
        exact h1
    -- Otherwise the order at `P` is exactly `-D P - 1`; gauge it away.
    push Not at hP
    obtain ⟨hne, hlt⟩ := hP
    have hord : P.ord (α P) = -(D P) - 1 := by
      have h1 := (hα P).resolve_left hne
      rw [hDP] at h1
      omega
    have hu0 : α P / P.pi ^ (-(D P) - 1) ≠ 0 := div_ne_zero hne hpi0
    have hu_le : P.val.valuation (α P / P.pi ^ (-(D P) - 1)) ≤ 1 := by
      rw [← P.ord_nonneg_iff hu0, div_eq_mul_inv,
        P.ord_mul hne (inv_ne_zero hpi0), P.ord_inv hpi0, ord_pi_zpow]
      omega
    obtain ⟨c, hc⟩ := P.exists_residue hu_le
    have hdecomp : α = (α - c • adeleMonomial P (-(D P) - 1)) +
        c • adeleMonomial P (-(D P) - 1) := by abel
    have hg : α - c • adeleMonomial P (-(D P) - 1) ∈ adeleSpace D := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · have h3 : (α - c • adeleMonomial Q (-(D Q) - 1)) Q =
            (α Q / Q.pi ^ (-(D Q) - 1) - algebraMap k F c) *
              Q.pi ^ (-(D Q) - 1) := by
          rw [Pi.sub_apply, Pi.smul_apply, adeleMonomial_apply_self,
            Algebra.smul_def]
          field_simp
        rcases eq_or_ne ((α - c • adeleMonomial Q (-(D Q) - 1)) Q) 0
          with h0 | h0
        · exact Or.inl h0
        refine Or.inr ?_
        have hd0 : α Q / Q.pi ^ (-(D Q) - 1) - algebraMap k F c ≠ 0 := by
          intro h4
          rw [h3, h4, zero_mul] at h0
          exact h0 rfl
        have h5 : 0 < Q.ord (α Q / Q.pi ^ (-(D Q) - 1) -
            algebraMap k F c) := (Q.ord_pos_iff hd0).2 hc
        rw [h3, Q.ord_mul hd0 hpi0, ord_pi_zpow]
        omega
      · have h6 : (α - c • adeleMonomial P (-(D P) - 1)) Q = α Q := by
          rw [Pi.sub_apply, Pi.smul_apply, adeleMonomial_apply_ne P hQ,
            smul_zero, sub_zero]
        rw [h6]
        have h7 := hα Q
        rw [hDQ Q hQ] at h7
        exact h7
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hg)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))
  · refine sup_le (adeleSpace_mono fun Q ↦ ?_) ?_
    · rcases eq_or_ne Q P with rfl | hQ
      · rw [hDP]
        omega
      · rw [hDQ Q hQ]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact adeleMonomial_mem_adeleSpace P (by rw [hDP]; omega)

/-- **The dichotomy**: the spanning monomial of `A(D + P)` is absorbed
into `A(D) + F` exactly when `L(D + P)` exceeds `L(D)` — the adelic
index and the Riemann–Roch dimension trade off point by point. -/
theorem adeleMonomial_mem_sup_iff (D : Divisor k F) :
    adeleMonomial P (-(D P) - 1) ∈
        adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) ↔
      ∃ f, f ∈ RiemannSpace (D + Finsupp.single P 1) ∧
        f ∉ RiemannSpace D := by
  have hpi0 : P.pi ^ (-(D P) - 1) ≠ 0 := zpow_ne_zero _ P.pi_ne_zero
  have hDP : (D + Finsupp.single P 1 : Divisor k F) P = D P + 1 := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  have hDQ : ∀ Q : Place k F, Q ≠ P →
      (D + Finsupp.single P 1 : Divisor k F) Q = D Q := by
    intro Q hQ
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hQ]
  constructor
  · -- From the decomposition, the diagonal part is the sought element.
    intro hmem
    obtain ⟨β, hβ, γ, ⟨f, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hmem
    have h1 : β P + f = P.pi ^ (-(D P) - 1) := by
      have h := congrFun hsum P
      rwa [Pi.add_apply, adeleDiagonal_apply,
        adeleMonomial_apply_self] at h
    -- The diagonal entry has exact order `-D P - 1` at `P`.
    have hford : f ≠ 0 ∧ P.ord f = -(D P) - 1 := by
      rcases eq_or_ne (β P) 0 with h0 | h0
      · rw [h0, zero_add] at h1
        exact ⟨h1 ▸ hpi0, by rw [h1, ord_pi_zpow]⟩
      · have hbord : -(D P) ≤ P.ord (β P) := (hβ P).resolve_left h0
        have h2 : f = P.pi ^ (-(D P) - 1) + -(β P) := by
          have h3 := eq_sub_of_add_eq' h1
          rwa [sub_eq_add_neg] at h3
        have h3 : P.ord (P.pi ^ (-(D P) - 1)) < P.ord (-(β P)) := by
          rw [ord_pi_zpow, P.ord_neg h0]
          omega
        have h4 := P.ord_add_eq_left hpi0 (neg_ne_zero.2 h0) h3
        rw [← h2, ord_pi_zpow] at h4
        refine ⟨?_, h4⟩
        intro hf0
        rw [hf0] at h2
        have h5 : P.pi ^ (-(D P) - 1) = β P := by
          have h6 := h2.symm
          rw [← sub_eq_add_neg] at h6
          exact sub_eq_zero.1 h6
        rw [← h5, ord_pi_zpow] at hbord
        omega
    refine ⟨f, ?_, ?_⟩
    · rw [mem_riemannSpace_iff]
      refine Or.inr fun Q ↦ ?_
      rcases eq_or_ne Q P with rfl | hQ
      · rw [hDP, hford.2]
        omega
      · have h6 : β Q + f = 0 := by
          have h := congrFun hsum Q
          rwa [Pi.add_apply, adeleDiagonal_apply,
            adeleMonomial_apply_ne P hQ] at h
        have h7 : f = -(β Q) := by
          rw [add_comm] at h6
          exact eq_neg_of_add_eq_zero_left h6
        have hβQ0 : β Q ≠ 0 := by
          intro h0
          rw [h0, neg_zero] at h7
          exact hford.1 h7
        rw [hDQ Q hQ, h7, Q.ord_neg hβQ0]
        exact (hβ Q).resolve_left hβQ0
    · intro hf
      rcases hf with rfl | hall
      · exact hford.1 rfl
      · have h8 := hall P
        rw [hford.2] at h8
        omega
  · -- Gauge the monomial by the residue of `π^m / f`.
    rintro ⟨f, hfE, hfD⟩
    have hf0 : f ≠ 0 := fun h ↦ hfD (h ▸ zero_mem _)
    have hfEord : ∀ Q : Place k F,
        -((D + Finsupp.single P 1 : Divisor k F) Q) ≤ Q.ord f := by
      rcases hfE with h | h
      · exact absurd h hf0
      · exact h
    have hford : P.ord f = -(D P) - 1 := by
      rw [mem_riemannSpace_iff, not_or] at hfD
      obtain ⟨-, h2⟩ := hfD
      push Not at h2
      obtain ⟨Q₀, hQ₀⟩ := h2
      rcases eq_or_ne Q₀ P with rfl | hQ
      · have h3 := hfEord Q₀
        rw [hDP] at h3
        omega
      · have h3 := hfEord Q₀
        rw [hDQ Q₀ hQ] at h3
        omega
    have hu0 : P.pi ^ (-(D P) - 1) / f ≠ 0 := div_ne_zero hpi0 hf0
    have hu_le : P.val.valuation (P.pi ^ (-(D P) - 1) / f) ≤ 1 := by
      rw [← P.ord_nonneg_iff hu0, div_eq_mul_inv,
        P.ord_mul hpi0 (inv_ne_zero hf0), P.ord_inv hf0, ord_pi_zpow,
        hford]
      omega
    obtain ⟨c, hc⟩ := P.exists_residue hu_le
    have hg : adeleMonomial P (-(D P) - 1) - c • adeleDiagonal k F f ∈
        adeleSpace D := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · have h3 : (adeleMonomial Q (-(D Q) - 1) -
            c • adeleDiagonal k F f) Q =
            (Q.pi ^ (-(D Q) - 1) / f - algebraMap k F c) * f := by
          rw [Pi.sub_apply, Pi.smul_apply, adeleDiagonal_apply,
            adeleMonomial_apply_self, Algebra.smul_def]
          field_simp
        rcases eq_or_ne ((adeleMonomial Q (-(D Q) - 1) -
            c • adeleDiagonal k F f) Q) 0 with h0 | h0
        · exact Or.inl h0
        refine Or.inr ?_
        have hd0 : Q.pi ^ (-(D Q) - 1) / f - algebraMap k F c ≠ 0 := by
          intro h4
          rw [h3, h4, zero_mul] at h0
          exact h0 rfl
        have h5 : 0 < Q.ord (Q.pi ^ (-(D Q) - 1) / f -
            algebraMap k F c) := (Q.ord_pos_iff hd0).2 hc
        rw [h3, Q.ord_mul hd0 hf0, hford]
        omega
      · rcases eq_or_ne c 0 with rfl | hc0
        · refine Or.inl ?_
          rw [Pi.sub_apply, Pi.smul_apply, adeleDiagonal_apply,
            adeleMonomial_apply_ne P hQ, zero_smul, sub_zero]
        · refine Or.inr ?_
          have h6 : (adeleMonomial P (-(D P) - 1) -
              c • adeleDiagonal k F f) Q = -(algebraMap k F c * f) := by
            rw [Pi.sub_apply, Pi.smul_apply, adeleDiagonal_apply,
              adeleMonomial_apply_ne P hQ, Algebra.smul_def, zero_sub]
          have hcf0 : algebraMap k F c * f ≠ 0 :=
            mul_ne_zero ((map_ne_zero _).2 hc0) hf0
          rw [h6, Q.ord_neg hcf0,
            Q.ord_mul ((map_ne_zero _).2 hc0) hf0,
            Q.ord_algebraMap hc0, zero_add]
          have h7 := hfEord Q
          rw [hDQ Q hQ] at h7
          exact h7
    have hdecomp : adeleMonomial P (-(D P) - 1) =
        (adeleMonomial P (-(D P) - 1) - c • adeleDiagonal k F f) +
          c • adeleDiagonal k F f := by abel
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hg)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ ⟨f, rfl⟩))

/-- When the Riemann–Roch space jumps at `P`, the adelic sup does not:
absorption of the one-point step. -/
theorem adeleSpace_add_single_sup_diagonal_eq (D : Divisor k F)
    (hjump : ∃ f, f ∈ RiemannSpace (D + Finsupp.single P 1) ∧
      f ∉ RiemannSpace D) :
    adeleSpace (D + Finsupp.single P 1) ⊔
        LinearMap.range (adeleDiagonal k F) =
      adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := by
  refine le_antisymm ?_ (sup_le_sup_right (adeleSpace_mono fun Q ↦ ?_) _)
  · rw [adeleSpace_add_single P D]
    refine sup_le (sup_le le_sup_left ?_) le_sup_right
    rw [Submodule.span_singleton_le_iff_mem]
    exact (adeleMonomial_mem_sup_iff P D).2 hjump
  · rcases eq_or_ne Q P with rfl | hQ
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hQ]

end OnePoint

section Surjectivity

/-- Along genus-attaining divisors the adelic sup is constant: every
one-point step is absorbed, because the Riemann–Roch dimension grows by
exactly one per point there. -/
theorem adeleSpace_sup_diagonal_eq_of_defect_eq_genus {D E : Divisor k F}
    (hD : D.defect = genus k F) (hDE : D ≤ E) :
    adeleSpace E ⊔ LinearMap.range (adeleDiagonal k F) =
      adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := by
  classical
  induction hmeas : ((E - D).deg).toNat using Nat.strong_induction_on
    generalizing E with
  | _ n ih =>
  rcases eq_or_ne D E with rfl | hne
  · rfl
  · have hED : 0 ≤ E - D := by
      intro P
      have h1 := hDE P
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
      omega
    obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.2
      (sub_ne_zero.2 (Ne.symm hne))
    have hPpos : 0 < (E - D) P := by
      have h1 : (E - D) P ≠ 0 := Finsupp.mem_support_iff.1 hP
      have h2 : (0 : ℤ) ≤ (E - D) P := by simpa using hED P
      omega
    have hsub : (E - D) P = E P - D P := Finsupp.sub_apply E D P
    have hDE' : D ≤ E - Finsupp.single P 1 := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Finsupp.sub_apply, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ, sub_zero]
        exact hDE Q
    have hdeg1 : E - Finsupp.single P 1 - D =
        E - D - Finsupp.single P 1 := by abel
    have hdegP : (E - D) P ≤ (E - D).deg := by
      rw [Divisor.deg, Finsupp.sum]
      exact Finset.single_le_sum (fun Q _ ↦ by simpa using hED Q) hP
    have hmeas' : ((E - Finsupp.single P 1 - D).deg).toNat < n := by
      rw [hdeg1, deg_sub_single]
      omega
    have hih := ih _ hmeas' hDE' rfl
    -- The one-point step from `E - P` to `E` is absorbed.
    have hE' : E - Finsupp.single P 1 + Finsupp.single P 1 = E := by abel
    have hattain : (E - Finsupp.single P 1).defect = genus k F :=
      defect_eq_genus_of_le hD hDE'
    have hattainE : E.defect = genus k F := defect_eq_genus_of_le hD hDE
    have hjump : ∃ f, f ∈ RiemannSpace
        (E - Finsupp.single P 1 + Finsupp.single P 1) ∧
        f ∉ RiemannSpace (E - Finsupp.single P 1) := by
      rw [hE']
      have h1 := finrank_riemannSpace_eq_of_defect_eq_genus hattain
      have h2 := finrank_riemannSpace_eq_of_defect_eq_genus hattainE
      rw [deg_sub_single] at h1
      have hlt : RiemannSpace (E - Finsupp.single P 1) <
          RiemannSpace E := by
        refine lt_of_le_of_ne (riemannSpace_mono (sub_single_le E P)) ?_
        intro heq
        rw [heq] at h1
        omega
      exact SetLike.exists_of_lt hlt
    have hstep := adeleSpace_add_single_sup_diagonal_eq P
      (E - Finsupp.single P 1) hjump
    rw [hE'] at hstep
    rw [hstep]
    exact hih

/-- Every adele is bounded by a divisor above any prescribed one. -/
theorem exists_le_mem_adeleSpace {α : (P : Place k F) → F}
    (hα : α ∈ adeleSubmodule k F) (D : Divisor k F) :
    ∃ E : Divisor k F, D ≤ E ∧ α ∈ adeleSpace E := by
  classical
  set B : Divisor k F :=
    ∑ P ∈ hα.toFinset, Finsupp.single P (-(P.ord (α P))) with hB
  have hBapp : ∀ Q : Place k F, Q ∈ hα.toFinset → B Q = -(Q.ord (α Q)) := by
    intro Q hQ
    rw [hB, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single Q]
    · rw [Finsupp.single_eq_same]
    · intro R _ hR
      exact Finsupp.single_eq_of_ne (Ne.symm hR)
    · intro h
      exact absurd hQ h
  have hBnonneg : 0 ≤ B := by
    intro Q
    have h0 : (0 : Divisor k F) Q = 0 := rfl
    rw [h0, hB, Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun R _ ↦ ?_
    rcases eq_or_ne R Q with rfl | hR
    · rw [Finsupp.single_eq_same]
      rcases (Set.Finite.mem_toFinset hα).1 ‹R ∈ hα.toFinset› with ⟨-, h⟩
      omega
    · rw [Finsupp.single_eq_of_ne (Ne.symm hR)]
  refine ⟨D.pos + B, fun Q ↦ ?_, fun Q ↦ ?_⟩
  · rw [Finsupp.add_apply]
    have h1 : D Q ≤ D.pos Q := Divisor.le_pos D Q
    have h2 : 0 ≤ B Q := by simpa using hBnonneg Q
    omega
  · rcases eq_or_ne (α Q) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    rw [Finsupp.add_apply]
    have h1 : 0 ≤ D.pos Q := by simpa using Divisor.pos_nonneg D Q
    rcases le_or_gt 0 (Q.ord (α Q)) with h2 | h2
    · have h3 : 0 ≤ B Q := by simpa using hBnonneg Q
      omega
    · have hQmem : Q ∈ hα.toFinset :=
        (Set.Finite.mem_toFinset hα).2 ⟨h0, h2⟩
      rw [hBapp Q hQmem]
      omega

/-- **Adelic surjectivity at genus-attaining divisors** (Stichtenoth
1.5.8): once the divisor attains the genus, every adele is congruent to
a diagonal element modulo `A(D)` — the space `𝔸 / (A(D) + F)` whose
dimension is the index of specialty vanishes. -/
theorem adeleSubmodule_eq_sup_of_defect_eq_genus {D : Divisor k F}
    (hD : D.defect = genus k F) :
    adeleSubmodule k F =
      adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := by
  refine le_antisymm ?_
    (sup_le (adeleSpace_le_adeleSubmodule D) ?_)
  · intro α hα
    obtain ⟨E, hDE, hαE⟩ := exists_le_mem_adeleSpace hα D
    rw [← adeleSpace_sup_diagonal_eq_of_defect_eq_genus hD hDE]
    exact Submodule.mem_sup_left hαE
  · rintro γ ⟨f, rfl⟩
    exact adeleDiagonal_mem_adeleSubmodule f

end Surjectivity

end

end AclGeom
