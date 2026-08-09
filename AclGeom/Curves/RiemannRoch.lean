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

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
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

section Dimension

/-- `L(0)` is exactly the constants: elements without poles descend to
the base field. -/
theorem riemannSpace_zero :
    RiemannSpace (0 : Divisor k F) =
      LinearMap.range (Algebra.linearMap k F) := by
  ext f
  constructor
  · intro hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, map_zero _⟩
    have hle : ∀ P : Place k F, P.val.valuation f ≤ 1 := by
      intro P
      rw [← P.ord_nonneg_iff hf0]
      rcases hf with h | h
      · exact absurd h hf0
      · have h1 := h P
        simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at h1
        exact h1
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_valuation_le_one hle
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact algebraMap_mem_riemannSpace le_rfl c

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The degree is additive across the one-point decrement. -/
theorem deg_sub_single (D : Divisor k F) (P : Place k F) :
    Divisor.deg (D - Finsupp.single P 1) = Divisor.deg D - 1 := by
  classical
  rw [Divisor.deg, Divisor.deg, Finsupp.sum_sub_index (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index rfl]

/-- **Finiteness and the elementary dimension bound** for effective
divisors: `ℓ(D) ≤ deg D + 1`, by induction along one-point decrements
from `L(0) = k`. -/
theorem finiteDimensional_riemannSpace_of_nonneg
    {D : Divisor k F} (hD : 0 ≤ D) :
    FiniteDimensional k (RiemannSpace D) ∧
      (Module.finrank k (RiemannSpace D) : ℤ) ≤ Divisor.deg D + 1 := by
  classical
  induction hmeas : (Divisor.deg D).toNat using Nat.strong_induction_on
    generalizing D with
  | _ n ih =>
  have hdeg0 : 0 ≤ Divisor.deg D := by
    rw [Divisor.deg]
    exact Finsupp.sum_nonneg fun P _ ↦ hD P
  rcases eq_or_ne D 0 with rfl | hD0
  · constructor
    · rw [riemannSpace_zero]
      infer_instance
    · rw [riemannSpace_zero]
      have h1 : Module.finrank k
          (LinearMap.range (Algebra.linearMap k F)) = 1 := by
        rw [LinearMap.finrank_range_of_inj
          (show Function.Injective (Algebra.linearMap k F) from
            (algebraMap k F).injective), Module.finrank_self]
      have h2 : Divisor.deg (0 : Divisor k F) = 0 := by
        rw [Divisor.deg, Finsupp.sum_zero_index]
      rw [h1, h2]
      norm_num
  · -- Pick a point in the support and step down.
    obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.2 hD0
    have hDP : 0 < D P := by
      have h1 : (0 : ℤ) ≤ D P := by simpa using hD P
      have h2 : D P ≠ 0 := Finsupp.mem_support_iff.1 hP
      omega
    have hD' : 0 ≤ D - Finsupp.single P 1 := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply,
          Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply,
          Finsupp.single_eq_of_ne hQ, sub_zero]
        exact hD Q
    have hdeg' : Divisor.deg (D - Finsupp.single P 1) =
        Divisor.deg D - 1 := deg_sub_single D P
    have hdegP : D P ≤ Divisor.deg D := by
      rw [Divisor.deg, Finsupp.sum]
      exact Finset.single_le_sum (fun Q _ ↦ by simpa using hD Q) hP
    have hmeas' : (Divisor.deg (D - Finsupp.single P 1)).toNat < n := by
      omega
    obtain ⟨ihfd, ihrk⟩ := ih _ hmeas' hD' rfl
    rcases riemannSpace_eq_or_eq_sup D P with heq | ⟨f₀, hf₀, heq⟩
    · rw [heq]
      refine ⟨ihfd, ?_⟩
      omega
    · haveI := ihfd
      rcases eq_or_ne f₀ 0 with rfl | hf₀0
      · rw [heq]
        have hspan : Submodule.span k ({0} : Set F) = ⊥ :=
          Submodule.span_zero_singleton k
        rw [hspan, sup_bot_eq]
        exact ⟨ihfd, by omega⟩
      constructor
      · rw [heq]
        infer_instance
      · rw [heq]
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq
          (RiemannSpace (D - Finsupp.single P 1))
          (Submodule.span k {f₀})
        have h2 : Module.finrank k (Submodule.span k {f₀}) = 1 :=
          finrank_span_singleton hf₀0
        rw [h2] at h1
        have h4 : Module.finrank k
            ↥(RiemannSpace (D - Finsupp.single P 1) ⊔
              Submodule.span k {f₀}) ≤
            Module.finrank k
              ↥(RiemannSpace (D - Finsupp.single P 1)) + 1 := by
          omega
        have h5 : ((Module.finrank k
            ↥(RiemannSpace (D - Finsupp.single P 1) ⊔
              Submodule.span k {f₀})) : ℤ) ≤
            ((Module.finrank k
              ↥(RiemannSpace (D - Finsupp.single P 1))) : ℤ) + 1 := by
          exact_mod_cast h4
        omega

/-- The positive part of a divisor. -/
noncomputable def Divisor.pos (D : Divisor k F) : Divisor k F :=
  D.mapRange (fun m ↦ max m 0) (by simp)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Divisor.le_pos (D : Divisor k F) : D ≤ D.pos := fun P ↦ by
  rw [Divisor.pos, Finsupp.mapRange_apply]
  exact le_max_left _ _

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Divisor.pos_nonneg (D : Divisor k F) : 0 ≤ D.pos := fun P ↦ by
  rw [Divisor.pos, Finsupp.mapRange_apply]
  exact le_max_right (D P) 0

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The join of two divisors, computed pointwise. -/
theorem Divisor.add_sub_pos_apply (D E : Divisor k F) (P : Place k F) :
    (D + (E - D).pos) P = max (D P) (E P) := by
  rw [Finsupp.add_apply, Divisor.pos, Finsupp.mapRange_apply,
    Finsupp.sub_apply]
  rcases le_total (E P) (D P) with h | h
  · rw [max_eq_right (by omega : E P - D P ≤ 0), max_eq_left h]
    omega
  · rw [max_eq_left (by omega : (0 : ℤ) ≤ E P - D P), max_eq_right h]
    omega

/-- **Riemann–Roch spaces are finite-dimensional.** -/
instance finiteDimensional_riemannSpace (D : Divisor k F) :
    FiniteDimensional k (RiemannSpace D) := by
  haveI := (finiteDimensional_riemannSpace_of_nonneg
    (Divisor.pos_nonneg D)).1
  exact Submodule.finiteDimensional_of_le
    (riemannSpace_mono (Divisor.le_pos D))

end Dimension

section PoleDivisor

variable (k) in
/-- The **pole divisor** `(f)_∞` of an element: the positive part of the
negated principal divisor. -/
noncomputable def poleDivisor (f : F) : Divisor k F :=
  (-(divisorOf k f)).pos

theorem poleDivisor_apply {f : F} (hf : f ≠ 0) (P : Place k F) :
    poleDivisor k f P = max (-(P.ord f)) 0 := by
  rw [poleDivisor, Divisor.pos, Finsupp.mapRange_apply, Finsupp.neg_apply,
    divisorOf_apply hf]

theorem poleDivisor_nonneg (f : F) : 0 ≤ poleDivisor k f :=
  Divisor.pos_nonneg _

/-- Every nonzero element lies in the Riemann–Roch space of its own pole
divisor. -/
theorem mem_riemannSpace_poleDivisor {g : F} (hg : g ≠ 0) :
    g ∈ RiemannSpace (poleDivisor k g) := by
  rw [mem_riemannSpace_iff]
  refine Or.inr fun P ↦ ?_
  rw [poleDivisor_apply hg]
  rcases le_total (-(P.ord g)) 0 with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

/-- Products lie in the Riemann–Roch space of the sum of divisors. -/
theorem mul_mem_riemannSpace {D E : Divisor k F} {g h : F}
    (hg : g ∈ RiemannSpace D) (hh : h ∈ RiemannSpace E) :
    g * h ∈ RiemannSpace (D + E) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [zero_mul]
    exact zero_mem_riemannSpace _
  rcases eq_or_ne h 0 with rfl | hh0
  · rw [mul_zero]
    exact zero_mem_riemannSpace _
  rw [mem_riemannSpace_iff] at hg hh ⊢
  refine Or.inr fun P ↦ ?_
  rcases hg with rfl | hg
  · exact absurd rfl hg0
  rcases hh with rfl | hh
  · exact absurd rfl hh0
  rw [Finsupp.add_apply, P.ord_mul hg0 hh0]
  have h1 := hg P
  have h2 := hh P
  omega

/-- Powers up to `N` lie in `L(N · (f)_∞)`. -/
theorem pow_mem_riemannSpace_smul_poleDivisor {f : F} (hf : f ≠ 0)
    {N j : ℕ} (hj : j ≤ N) :
    f ^ j ∈ RiemannSpace ((N : ℤ) • poleDivisor k f) := by
  rw [mem_riemannSpace_iff]
  refine Or.inr fun P ↦ ?_
  rw [Finsupp.smul_apply, poleDivisor_apply hf, P.ord_pow hf,
    smul_eq_mul]
  have hjN : (j : ℤ) ≤ (N : ℤ) := by exact_mod_cast hj
  rcases le_total 0 (P.ord f) with hord | hord
  · rw [max_eq_right (neg_nonpos.mpr hord), mul_zero, neg_zero]
    exact mul_nonneg (Int.natCast_nonneg j) hord
  · rw [max_eq_left (neg_nonneg.mpr hord), mul_neg, neg_neg]
    exact mul_le_mul_of_nonpos_right hjN hord

end PoleDivisor

section RiemannBound

/-- **The subtraction bound**: enlarging a divisor grows the dimension
by at most the added degree — the one-point decomposition iterated. -/
theorem finrank_riemannSpace_le_of_le {D E : Divisor k F} (hDE : D ≤ E) :
    (Module.finrank k (RiemannSpace E) : ℤ) ≤
      (Module.finrank k (RiemannSpace D) : ℤ) + E.deg - D.deg := by
  classical
  induction hmeas : ((E - D).deg).toNat using Nat.strong_induction_on
    generalizing E with
  | _ n ih =>
  rcases eq_or_ne D E with rfl | hne
  · omega
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
    have hone : Module.finrank k (RiemannSpace E) ≤
        Module.finrank k (RiemannSpace (E - Finsupp.single P 1)) + 1 := by
      rcases riemannSpace_eq_or_eq_sup E P with heq | ⟨f₀, hf₀, heq⟩
      · rw [heq]
        omega
      · rcases eq_or_ne f₀ 0 with rfl | hf₀0
        · have hspan : Submodule.span k ({0} : Set F) = ⊥ :=
            Submodule.span_zero_singleton k
          rw [heq, hspan, sup_bot_eq]
          omega
        · rw [heq]
          have h1 := Submodule.finrank_sup_add_finrank_inf_eq
            (RiemannSpace (E - Finsupp.single P 1))
            (Submodule.span k {f₀})
          rw [finrank_span_singleton hf₀0] at h1
          omega
    have hdegE' : (E - Finsupp.single P 1).deg = E.deg - 1 :=
      deg_sub_single E P
    have hcast : (Module.finrank k (RiemannSpace E) : ℤ) ≤
        (Module.finrank k (RiemannSpace (E - Finsupp.single P 1)) : ℤ) +
          1 := by
      exact_mod_cast hone
    omega

/-- Adding one point grows the Riemann–Roch dimension by at most one. -/
theorem finrank_riemannSpace_add_single_le (D : Divisor k F)
    (P : Place k F) :
    Module.finrank k (RiemannSpace (D + Finsupp.single P 1)) ≤
      Module.finrank k (RiemannSpace D) + 1 := by
  have hDD : D + Finsupp.single P 1 - Finsupp.single P 1 = D := by abel
  have h := riemannSpace_eq_or_eq_sup (D + Finsupp.single P 1) P
  rw [hDD] at h
  rcases h with heq | ⟨f₀, hf₀, heq⟩
  · rw [heq]
    omega
  · rcases eq_or_ne f₀ 0 with rfl | hf₀0
    · have hspan : Submodule.span k ({0} : Set F) = ⊥ :=
        Submodule.span_zero_singleton k
      rw [heq, hspan, sup_bot_eq]
      omega
    · rw [heq]
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq
        (RiemannSpace D) (Submodule.span k {f₀})
      rw [finrank_span_singleton hf₀0] at h1
      omega

/-- Multiplication by `z` embeds `L(E + div z)` into `L(E)`. -/
theorem finrank_riemannSpace_add_divisorOf_le (E : Divisor k F) {z : F}
    (hz : z ≠ 0) :
    Module.finrank k (RiemannSpace (E + divisorOf k z)) ≤
      Module.finrank k (RiemannSpace E) := by
  have hmem : ∀ w ∈ RiemannSpace (E + divisorOf k z),
      w * z ∈ RiemannSpace E := by
    intro w hw
    rw [mem_riemannSpace_iff] at hw ⊢
    rcases eq_or_ne w 0 with rfl | hw0
    · exact Or.inl (zero_mul z)
    rcases hw with rfl | hw
    · exact absurd rfl hw0
    refine Or.inr fun P ↦ ?_
    have h1 := hw P
    rw [Finsupp.add_apply, divisorOf_apply hz] at h1
    rw [P.ord_mul hw0 hz]
    omega
  have hinj : Function.Injective
      (LinearMap.codRestrict (RiemannSpace E)
        ((LinearMap.mulRight k z).comp
          (RiemannSpace (E + divisorOf k z)).subtype)
        fun w ↦ hmem w w.2) := by
    intro w w' h
    have h1 : (w : F) * z = (w' : F) * z := congrArg Subtype.val h
    exact Subtype.ext (mul_right_cancel₀ hz h1)
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **Linear-equivalence invariance** of the Riemann–Roch dimension:
`ℓ(D + div z) = ℓ(D)`, by multiplication with `z` in both directions. -/
theorem finrank_riemannSpace_add_divisorOf (D : Divisor k F) {z : F}
    (hz : z ≠ 0) :
    Module.finrank k (RiemannSpace (D + divisorOf k z)) =
      Module.finrank k (RiemannSpace D) := by
  refine le_antisymm (finrank_riemannSpace_add_divisorOf_le D hz) ?_
  have h := finrank_riemannSpace_add_divisorOf_le (D + divisorOf k z)
    (inv_ne_zero hz)
  rwa [divisorOf_inv hz,
    show D + divisorOf k z + -divisorOf k z = D by abel] at h

end RiemannBound

end

end AclGeom
