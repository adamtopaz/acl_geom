/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Residues

/-!
# Riemann–Roch spaces

The space `L(D)` of a divisor: elements whose principal divisor is
bounded below by `-D`. This file provides the definitional layer of the
Riemann–Roch machinery (issue #13, P3): `L(D)` is a `k`-submodule of `F`,
monotone in the divisor, containing the constants at effective divisors.
The dimension bounds and Riemann's inequality build on this layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The **Riemann–Roch space** of a divisor `D`: the `k`-submodule of
elements whose order at every place is at least `-D`. -/
noncomputable def RiemannSpace (D : Divisor k F) : Submodule k F where
  carrier := {f : F | f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa using hf
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · exact Or.inl hfg
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    rcases hg with rfl | hg
    · exact absurd rfl hg0
    refine Or.inr fun P ↦ ?_
    exact le_trans (le_min (hf P) (hg P)) (P.min_ord_le_ord_add hf0 hg0 hfg)
  smul_mem' := by
    intro c f hf
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (zero_smul k f)
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl (smul_zero c)
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    refine Or.inr fun P ↦ ?_
    have h1 : P.ord (c • f) = P.ord f := by
      rw [Algebra.smul_def,
        P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hf0,
        P.ord_algebraMap hc0, zero_add]
    rw [h1]
    exact hf P

theorem mem_riemannSpace_iff {D : Divisor k F} {f : F} :
    f ∈ RiemannSpace D ↔
      f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f := Iff.rfl

theorem zero_mem_riemannSpace (D : Divisor k F) :
    (0 : F) ∈ RiemannSpace D := Or.inl rfl

/-- Monotonicity of the Riemann–Roch space in the divisor. -/
theorem riemannSpace_mono {D E : Divisor k F} (h : D ≤ E) :
    RiemannSpace D ≤ RiemannSpace E := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  refine Or.inr fun P ↦ le_trans ?_ (hf P)
  have h1 : D P ≤ E P := h P
  omega

/-- Nonzero constants lie in `L(D)` for effective `D`. -/
theorem algebraMap_mem_riemannSpace {D : Divisor k F} (hD : 0 ≤ D)
    (c : k) : algebraMap k F c ∈ RiemannSpace D := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]
    exact Or.inl rfl
  refine Or.inr fun P ↦ ?_
  rw [Place.ord_algebraMap P hc0]
  have h1 : (0 : ℤ) ≤ D P := hD P
  omega

/-- Membership of a nonzero element forces effectivity where it has
poles; in particular `L(D) = 0` when `D` has somewhere-negative degree
data pointwise. Elementary sanity lemma: if `D ≤ 0` and `D ≠ 0`, any
nonzero `f ∈ L(D)` has a zero at a place where `D` is negative. -/
theorem ord_pos_of_mem_riemannSpace {D : Divisor k F} {f : F}
    (hf : f ∈ RiemannSpace D) (hf0 : f ≠ 0) {P : Place k F}
    (hP : D P < 0) : 0 < P.ord f := by
  rcases hf with rfl | hf
  · exact absurd rfl hf0
  have h1 := hf P
  omega

section OneStep

/-- Removing one point from the divisor: the pointwise comparison. -/
theorem sub_single_le (D : Divisor k F) (P : Place k F) :
    D - Finsupp.single P 1 ≤ D := by
  intro Q
  rcases eq_or_ne Q P with rfl | hQ
  · simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
    omega
  · simp [Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ]

/-- **The one-step decomposition** (the dimension engine of the
Riemann–Roch layer): removing one point from a divisor either does not
change the space, or drops it by exactly a line — `L(D)` is the sup of
`L(D − P)` and the span of any element of exact order `-D P` at `P`.
The gauge is division by that element followed by the residue theorem. -/
theorem riemannSpace_eq_or_eq_sup (D : Divisor k F) (P : Place k F) :
    RiemannSpace D = RiemannSpace (D - Finsupp.single P 1) ∨
    ∃ f₀ : F, f₀ ∈ RiemannSpace D ∧
      RiemannSpace D =
        RiemannSpace (D - Finsupp.single P 1) ⊔
          Submodule.span k {f₀} := by
  classical
  have hD'P : (D - Finsupp.single P 1 : Divisor k F) P = D P - 1 := by
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
  have hD'Q : ∀ Q : Place k F, Q ≠ P →
      (D - Finsupp.single P 1 : Divisor k F) Q = D Q := by
    intro Q hQ
    simp [Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ]
  by_cases hex : ∃ f₀ ∈ RiemannSpace D,
      f₀ ∉ RiemannSpace (D - Finsupp.single P 1)
  case neg =>
    left
    push Not at hex
    exact le_antisymm (fun f hf ↦ hex f hf)
      (riemannSpace_mono (sub_single_le D P))
  case pos =>
    right
    obtain ⟨f₀, hf₀D, hf₀D'⟩ := hex
    refine ⟨f₀, hf₀D, ?_⟩
    have hf₀0 : f₀ ≠ 0 := fun h ↦ hf₀D' (h ▸ zero_mem _)
    have hf₀mem : ∀ Q : Place k F, -(D Q) ≤ Q.ord f₀ := by
      rcases hf₀D with h | h
      · exact absurd h hf₀0
      · exact h
    -- The witness has exact order `-D P` at `P`.
    have hf₀ord : P.ord f₀ = -(D P) := by
      rw [mem_riemannSpace_iff, not_or] at hf₀D'
      obtain ⟨-, h2⟩ := hf₀D'
      push Not at h2
      obtain ⟨Q₀, hQ₀⟩ := h2
      rcases eq_or_ne Q₀ P with rfl | hQ
      · rw [hD'P] at hQ₀
        have := hf₀mem Q₀
        omega
      · rw [hD'Q Q₀ hQ] at hQ₀
        exact absurd (hf₀mem Q₀) (by omega)
    refine le_antisymm ?_ ?_
    · -- Every element decomposes through the residue of `f / f₀`.
      intro f hfD
      rcases eq_or_ne f 0 with rfl | hf0
      · exact zero_mem _
      have hfmem : ∀ Q : Place k F, -(D Q) ≤ Q.ord f := by
        rcases hfD with h | h
        · exact absurd h hf0
        · exact h
      have hquot0 : f / f₀ ≠ 0 := div_ne_zero hf0 hf₀0
      have hquot_le : P.val.valuation (f / f₀) ≤ 1 := by
        rw [← P.ord_nonneg_iff hquot0, div_eq_mul_inv,
          P.ord_mul hf0 (inv_ne_zero hf₀0), P.ord_inv hf₀0]
        have := hfmem P
        omega
      obtain ⟨c, hc⟩ := P.exists_residue hquot_le
      have hdecomp : f = (f - algebraMap k F c * f₀) +
          algebraMap k F c * f₀ := by ring
      have hg : f - algebraMap k F c * f₀ ∈
          RiemannSpace (D - Finsupp.single P 1) := by
        rcases eq_or_ne (f - algebraMap k F c * f₀) 0 with hgz | hgz
        · rw [hgz]
          exact zero_mem _
        refine Or.inr fun Q ↦ ?_
        rcases eq_or_ne Q P with rfl | hQ
        · -- At `P`: the residue gains one order.
          rw [hD'P]
          have h3 : f - algebraMap k F c * f₀ =
              (f / f₀ - algebraMap k F c) * f₀ := by
            field_simp
          have hd0 : f / f₀ - algebraMap k F c ≠ 0 := by
            intro h0
            rw [h3, h0, zero_mul] at hgz
            exact hgz rfl
          have h4 : 0 < Q.ord (f / f₀ - algebraMap k F c) :=
            (Q.ord_pos_iff hd0).2 hc
          rw [h3, Q.ord_mul hd0 hf₀0, hf₀ord]
          omega
        · -- Elsewhere: ultrametric superadditivity.
          rw [hD'Q Q hQ]
          rcases eq_or_ne c 0 with rfl | hc0
          · rw [map_zero, zero_mul, sub_zero]
            exact hfmem Q
          have hcf₀ : algebraMap k F c * f₀ ≠ 0 :=
            mul_ne_zero ((map_ne_zero (algebraMap k F)).2 hc0) hf₀0
          have h5 := Q.min_ord_le_ord_add (f := f)
            (g := -(algebraMap k F c * f₀)) hf0 (neg_ne_zero.2 hcf₀)
            (by rwa [← sub_eq_add_neg])
          rw [← sub_eq_add_neg, Q.ord_neg hcf₀,
            Q.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hf₀0,
            Q.ord_algebraMap hc0, zero_add] at h5
          have h6 := hfmem Q
          have h7 := hf₀mem Q
          rcases min_cases (Q.ord f) (Q.ord f₀) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
            rw [hm] at h5 <;> omega
      rw [hdecomp]
      refine Submodule.add_mem _ (Submodule.mem_sup_left hg)
        (Submodule.mem_sup_right ?_)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f₀)
    · refine sup_le (riemannSpace_mono (sub_single_le D P)) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact hf₀D

end OneStep

end

end AclGeom
