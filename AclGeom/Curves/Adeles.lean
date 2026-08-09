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

end OnePoint

end

end AclGeom
