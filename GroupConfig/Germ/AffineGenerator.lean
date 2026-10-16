/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.SLLift
import GroupConfig.Constructible.SLClassification
import GroupConfig.BaseNesting

/-!
# An affine generator for the actual rank-two HW action

`GroupConfig.Germ.IsHWBij.exists_affine_generator` starts with actual HW bijection data, a
finite rank-one source locus and a difference germ of ordinary canonical-base rank exactly
two. It internally chooses a transcendental generator of the original K-function field in
which every actual group element acts by `u ↦ a*u+b`, with `a ≠ 0`, in every characteristic.

The actual constructible determinant-one lift supplies the subgroup and its rank. Its Borel
classification supplies the matrix `A`, and the fractional linear change `u = φ_A(t)` turns
each lift `m` into `A*m*A⁻¹`. The generator and all coordinate data are conclusions, with no
caller-supplied classification, fixed-point or coordinate certificate.

`exists_affine_generator_parameters` also records coefficients. The generator is a fraction
`A / B` of polynomials over an internally chosen small algebraically closed field `M`, and `B`
is nonzero at every point generic over `M`. Over `M`, the affine coefficients `a, b` of every
member generate the same closure as its canonical base. `exists_affine_generator` is the
projection forgetting these coefficients. The coefficient form feeds the initial affine chart
`GroupConfig.exists_initial_chart_generic` (#27).

This is an auxiliary actual-action consumer for `lem:affine-action` in `sources/blueprint.tex`.
The original scheme action, connected normal subgroup, algebraization and original-field
chart/action descent are not conclusions. Rank exactly two is essential to this statement.

**Status:** the complete actual rank-two HW affine generator is proved (#21). Original
scheme/action and reconstruction obligations remain open.
-/

namespace GroupConfig

open AclGeom Set Matrix
open scoped MatrixGroups

noncomputable section

section Moebius

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The fractional linear expression of a matrix in an element. -/
private def moebiusVal (X : SL(2, K)) (s : L) : L :=
  (algebraMap K L (X 0 0) * s + algebraMap K L (X 0 1)) /
    (algebraMap K L (X 1 0) * s + algebraMap K L (X 1 1))

/-- Fractional linear expressions compose like matrices. -/
private theorem moebiusVal_mul {s : L} (hs : Transcendental K s) (X Y : SL(2, K)) :
    moebiusVal X (moebiusVal Y s) = moebiusVal (X * Y) s := by
  have hY := sl2_denom_ne_zero hs Y
  have hXY := sl2_denom_ne_zero hs (X * Y)
  obtain ⟨φ, hφdef⟩ : ∃ φ, φ = moebiusVal Y s := ⟨_, rfl⟩
  have hφ : φ * (algebraMap K L (Y 1 0) * s + algebraMap K L (Y 1 1)) =
      algebraMap K L (Y 0 0) * s + algebraMap K L (Y 0 1) := by
    rw [hφdef]
    exact div_mul_cancel₀ _ hY
  rw [← hφdef]
  have hX : algebraMap K L (X 1 0) * φ + algebraMap K L (X 1 1) ≠ 0 := by
    intro h
    apply hXY
    have hprod : (algebraMap K L (X 1 0) * φ + algebraMap K L (X 1 1)) *
        (algebraMap K L (Y 1 0) * s + algebraMap K L (Y 1 1)) =
        algebraMap K L ((X * Y) 1 0) * s + algebraMap K L ((X * Y) 1 1) := by
      simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, map_add, map_mul]
      linear_combination (algebraMap K L (X 1 0)) * hφ
    rw [← hprod, h, zero_mul]
  unfold moebiusVal
  rw [div_eq_div_iff hX hXY]
  simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, map_add, map_mul]
  linear_combination (algebraMap K L (X 0 0) * algebraMap K L (X 1 1) -
    algebraMap K L (X 0 1) * algebraMap K L (X 1 0)) * hφ

/-- The identity matrix acts trivially. -/
private theorem moebiusVal_one (s : L) : moebiusVal (1 : SL(2, K)) s = s := by
  simp [moebiusVal]

/-- A `K`-algebra automorphism commutes with fractional linear expressions. -/
private theorem moebiusVal_algEquiv (σ : L ≃ₐ[K] L) (X : SL(2, K)) (s : L) :
    σ (moebiusVal X s) = moebiusVal X (σ s) := by
  simp only [moebiusVal, map_div₀, map_add, map_mul, AlgEquiv.commutes]

/-- A fractional linear change `φ_A(s)` of a transcendental generator `s` of `L / K` is again a
transcendental generator. -/
private theorem moebiusVal_generator {s : L} (hs : Transcendental K s)
    (htop : IntermediateField.adjoin K ({s} : Set L) = ⊤) (A : SL(2, K)) :
    Transcendental K (moebiusVal A s) ∧
      IntermediateField.adjoin K ({moebiusVal A s} : Set L) = ⊤ := by
  -- `s` is a fractional linear expression in `u = φ_A(s)`.
  have hsu : moebiusVal A⁻¹ (moebiusVal A s) = s := by
    rw [moebiusVal_mul hs, inv_mul_cancel, moebiusVal_one]
  have hsmem : s ∈ IntermediateField.adjoin K ({moebiusVal A s} : Set L) := by
    have h : moebiusVal A⁻¹ (moebiusVal A s) ∈
        IntermediateField.adjoin K ({moebiusVal A s} : Set L) := by
      obtain ⟨u, hudef⟩ : ∃ u, u = moebiusVal A s := ⟨_, rfl⟩
      rw [← hudef]
      have hu := IntermediateField.mem_adjoin_simple_self K u
      unfold moebiusVal
      exact div_mem
        (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hu)
          (IntermediateField.algebraMap_mem _ _))
        (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hu)
          (IntermediateField.algebraMap_mem _ _))
    rwa [hsu] at h
  refine ⟨fun halg ↦ ?_, top_unique (htop ▸ IntermediateField.adjoin_simple_le_iff.2 hsmem)⟩
  -- `u` is transcendental: otherwise `s` would be algebraic.
  have : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({moebiusVal A s} : Set L)) :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  exact hs (IntermediateField.isAlgebraic_iff.1
    (Algebra.IsAlgebraic.isAlgebraic (⟨s, hsmem⟩ :
      IntermediateField.adjoin K ({moebiusVal A s} : Set L))))

end Moebius

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K]

namespace Germ.IsHWBij

universe w

/-! ### The coefficient field of the affine generator -/

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- Conjugation by a matrix whose entries and inverse entries lie in `F` does not change the
closure of the entries over `F`. -/
private theorem racl_union_entries_conj {F : Set K} {A : SL(2, K)} (hA : ∀ i j, A i j ∈ F)
    (hA' : ∀ i j, A⁻¹ i j ∈ F) (m : SL(2, K)) :
    racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ (A * m * A⁻¹) ij.1 ij.2) =
      racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) := by
  have key : ∀ B X : SL(2, K), (∀ i j, B i j ∈ F) → (∀ i j, B⁻¹ i j ∈ F) →
      racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ (B * X * B⁻¹) ij.1 ij.2) ≤
        racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ X ij.1 ij.2) := by
    intro B X hB hB'
    have hF : ∀ c ∈ F, c ∈ racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ X ij.1 ij.2) :=
      fun c hc ↦ subset_racl k _ (Or.inl hc)
    refine racl_le_of_subset_racl (union_subset hF ?_)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact sl_mul_entries_mem _ (sl_mul_entries_mem _ (fun i j ↦ hF _ (hB i j))
      (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩))) (fun i j ↦ hF _ (hB' i j)) i j
  refine le_antisymm (key A m hA hA') ?_
  have h := key A⁻¹ (A * m * A⁻¹) hA' (by simpa only [inv_inv] using hA)
  rwa [show A⁻¹ * (A * m * A⁻¹) * A⁻¹⁻¹ = m by group] at h

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- For an upper triangular `n` of determinant one, the affine coefficients `n₀₀/n₁₁` and
`n₀₁/n₁₁` generate the same closure over `F` as the entries of `n`. -/
private theorem racl_union_affineCoeffs {F : Set K} {n : SL(2, K)} (hn : n 1 0 = 0) :
    racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) =
      racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ n ij.1 ij.2) := by
  have hdet : n 0 0 * n 1 1 = 1 := by
    have h := n.det_coe
    rw [Matrix.det_fin_two, hn, mul_zero, sub_zero] at h
    exact h
  have h11 : n 1 1 = (n 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have h11ne : n 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  refine le_antisymm (racl_le_of_subset_racl (union_subset
    (fun c hc ↦ subset_racl k _ (Or.inl hc)) ?_)) (racl_le_of_subset_racl (union_subset
    (fun c hc ↦ subset_racl k _ (Or.inl hc)) ?_))
  · have he : ∀ i j, n i j ∈ racl k (F ∪ range fun ij : Fin 2 × Fin 2 ↦ n ij.1 ij.2) :=
      fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)
    rintro _ (rfl | rfl)
    · exact div_mem (he 0 0) (he 1 1)
    · exact div_mem (he 0 1) (he 1 1)
  · have ha : n 0 0 / n 1 1 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) :=
      subset_racl k _ (Or.inr (Or.inl rfl))
    have hb : n 0 1 / n 1 1 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) :=
      subset_racl k _ (Or.inr (Or.inr rfl))
    have hsq : n 0 0 ^ 2 = n 0 0 / n 1 1 := by
      rw [h11, div_inv_eq_mul, sq]
    have h00 : n 0 0 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) := by
      rw [mem_racl_iff k] at ha ⊢
      exact IsAlgebraic.of_pow two_pos (by rw [hsq]; exact ha)
    have h11m : n 1 1 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) := by
      have h := inv_mem h00
      rwa [← h11] at h
    have h01 : n 0 1 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) := by
      have h := mul_mem hb h11m
      rwa [div_mul_cancel₀ _ h11ne] at h
    have h10 : n 1 0 ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) := by
      rw [hn]
      exact zero_mem _
    have hall : ∀ i j, n i j ∈ racl k (F ∪ {n 0 0 / n 1 1, n 0 1 / n 1 1}) :=
      Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨h00, h01⟩, Fin.forall_fin_two.2 ⟨h10, h11m⟩⟩
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact hall i j

/-- The action on `u = φ_A(t)` of a member with lift `m`, when `n = A m A⁻¹` is upper
triangular, is `u ↦ (n₀₀/n₁₁) u + n₀₁/n₁₁`. -/
private theorem functionFieldAction_moebiusVal_of_triangular {ι : Type*} [Finite ι]
    {v : ι → K} {g₀ : Germ k v v} (hw : IsHW g₀) (hv : erk k ∅ (range v) = 1)
    {t : LocusFunctionField k v} (ht : Transcendental K t) (A : SL(2, K))
    {γ : ↥hw.prodSubgroup} {m : SL(2, K)} (hm : hw.IsMoebiusLift hv t γ m)
    (hn : (A * m * A⁻¹) 1 0 = 0) :
    hw.functionFieldAction hv γ (moebiusVal A t) =
      algebraMap K _ ((A * m * A⁻¹) 0 0 / (A * m * A⁻¹) 1 1) * moebiusVal A t +
        algebraMap K _ ((A * m * A⁻¹) 0 1 / (A * m * A⁻¹) 1 1) := by
  obtain ⟨hden, hm⟩ := hm
  have hσt : hw.functionFieldAction hv γ t = moebiusVal m t := by
    unfold moebiusVal
    rw [eq_div_iff hden]
    exact hm
  have hσu : hw.functionFieldAction hv γ (moebiusVal A t) =
      moebiusVal (A * m * A⁻¹) (moebiusVal A t) := by
    rw [moebiusVal_algEquiv, hσt, moebiusVal_mul ht, moebiusVal_mul ht,
      show A * m * A⁻¹ * A = A * m by group]
  obtain ⟨n, hndef⟩ : ∃ n, n = A * m * A⁻¹ := ⟨_, rfl⟩
  rw [← hndef] at hσu hn ⊢
  have hdet : n 0 0 * n 1 1 = 1 := by
    have h := n.det_coe
    rw [Matrix.det_fin_two, hn, mul_zero, sub_zero] at h
    exact h
  have h11' : algebraMap K (LocusFunctionField k v) (n 1 1) ≠ 0 :=
    (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one hdet)
  rw [hσu]
  unfold moebiusVal
  rw [hn, map_zero, zero_mul, zero_add, map_div₀, map_div₀]
  field_simp

/-- **The affine generator with its coefficient field.** Under the hypotheses of
`exists_affine_generator`, the generator `u` is a fraction of polynomials over an internally
chosen small algebraically closed field `M`, with denominator nonzero at every generic point over
`M`. The affine coefficients `a, b` of every member generate the same closure over `M` as its
canonical base. -/
theorem exists_affine_generator_parameters {ι κ : Type w} [Finite ι] [Finite κ]
    {v : ι → K} {v' : κ → K} {f₀ : Germ k v v'} (hb : f₀.IsHWBij) {δ₀ : Germ k v v}
    (hδ₀ : δ₀ ∈ f₀.diffSet) (hv : erk k ∅ (range v) = 1)
    (hr : erk k ∅ (δ₀.cb : Set K) = 2) :
    ∃ (u : LocusFunctionField k v) (M : IntermediateField k K) (_ : IsAlgClosed ↥M),
      IsSmall k (M : Set K) ∧ Transcendental K u ∧
      IntermediateField.adjoin K ({u} : Set (LocusFunctionField k v)) = ⊤ ∧
      (∃ A B : MvPolynomial ι M, (∀ y, IsGenericOver M v y → MvPolynomial.aeval y B ≠ 0) ∧
        u = LocusFunctionField.mk k v (MvPolynomial.map (algebraMap M K) A) /
          LocusFunctionField.mk k v (MvPolynomial.map (algebraMap M K) B)) ∧
      ∀ γ : ↥(hb.isHW hδ₀).prodSubgroup, ∃ a b : K, a ≠ 0 ∧
        (hb.isHW hδ₀).functionFieldAction hv γ u = algebraMap K _ a * u + algebraMap K _ b ∧
        racl (↥M) ({a, b} : Set K) = racl (↥M) (((hb.isHW hδ₀).val γ).cb : Set K) := by
  obtain ⟨t, M, iM, Γ, ht, htop, hM, hlift, hΓ, _, _, hcons, hcl, hle, hex⟩ :=
    hb.exists_constructible_slLift hδ₀ hv (by rw [hr])
  let : IsAlgClosed ↥M := iM
  let : UniversalDomain ↥M K := universalDomain_of_isSmall M hM
  have hrank (γ : ↥(hb.isHW hδ₀).prodSubgroup) (m : SpecialLinearGroup (Fin 2) K)
      (hm : (hb.isHW hδ₀).IsMoebiusLift hv t γ m) :
      erk ↥M ∅ (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
        erk ↥M ∅ (((hb.isHW hδ₀).val γ).cb : Set K) := by
    have he := congrArg (fun F : IntermediateField ↥M K ↦ erk ↥M ∅ (F : Set K)) (hcl γ m hm)
    have er (S : Set K) : erk ↥M ∅ (racl ↥M S : Set K) = erk ↥M ∅ S := by
      simpa only [empty_union] using erk_racl (↥M) (∅ : Set K) S
    simpa only [er] using he
  have hleΓ : ∀ m ∈ Γ, erk ↥M ∅ (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ≤ 2 := by
    intro m hm
    obtain ⟨γ, hγ⟩ := (hΓ m).1 hm
    rw [hrank γ m hγ]
    exact (hle γ).trans_eq hr
  have hrΓ : ∃ m ∈ Γ, erk ↥M ∅ (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) = 2 := by
    obtain ⟨γ, hγ⟩ := hex
    obtain ⟨m, hm⟩ := hlift γ
    exact ⟨m, (hΓ m).2 ⟨γ, hm⟩, (hrank γ m hm).trans (hγ.trans hr)⟩
  obtain ⟨A, hA⟩ := exists_borel_conj_of_constructible_rank_two (k := ↥M) Γ hcons hleΓ hrΓ
  obtain ⟨hu, htop'⟩ := moebiusVal_generator ht htop A
  -- The coefficient field: `M`, the entries of `A` and `A⁻¹`, and the coefficients of `u`.
  obtain ⟨C, hCfin, hC⟩ := LocusFunctionField.exists_fraction_of_subset (moebiusVal A t)
  obtain ⟨T, hTdef⟩ : ∃ T : Set K, T = (range fun ij : Fin 2 × Fin 2 ↦ A ij.1 ij.2) ∪
      (range fun ij : Fin 2 × Fin 2 ↦ A⁻¹ ij.1 ij.2) ∪ C := ⟨_, rfl⟩
  have hT : T.Finite := hTdef ▸ ((finite_range _).union (finite_range _)).union hCfin
  obtain ⟨M', hM'def⟩ : ∃ M' : IntermediateField k K, M' = racl k ((M : Set K) ∪ T) :=
    ⟨_, rfl⟩
  have iM' : IsAlgClosed ↥M' := hM'def ▸ isAlgClosed_racl _
  have hM' : IsSmall k (M' : Set K) := hM'def ▸ (hM.union (IsSmall.of_finite hT)).racl
  have hTM' : T ⊆ M' := hM'def ▸ fun c hc ↦ subset_racl k _ (Or.inr hc)
  have hAM' : ∀ i j, A i j ∈ (M' : Set K) := fun i j ↦
    hTM' (hTdef ▸ Or.inl (Or.inl ⟨(i, j), rfl⟩))
  have hA'M' : ∀ i j, A⁻¹ i j ∈ (M' : Set K) := fun i j ↦
    hTM' (hTdef ▸ Or.inl (Or.inr ⟨(i, j), rfl⟩))
  obtain ⟨P, Q, hQ, hPQ⟩ := hC M' fun c hc ↦ hTM' (hTdef ▸ Or.inr hc)
  refine ⟨moebiusVal A t, M', iM', hM', hu, htop', ⟨P, Q, hQ, hPQ⟩, fun γ ↦ ?_⟩
  obtain ⟨m, hm⟩ := hlift γ
  have hn := (hA m).1 ((hΓ m).2 ⟨γ, hm⟩)
  have hdet : (A * m * A⁻¹) 0 0 * (A * m * A⁻¹) 1 1 = 1 := by
    have h := (A * m * A⁻¹).det_coe
    rw [Matrix.det_fin_two, hn, mul_zero, sub_zero] at h
    exact h
  refine ⟨_, _, div_ne_zero (left_ne_zero_of_mul_eq_one hdet)
    (right_ne_zero_of_mul_eq_one hdet),
    functionFieldAction_moebiusVal_of_triangular (hb.isHW hδ₀) hv ht A hm hn, ?_⟩
  -- Closures over `M'`: coefficients, conjugated entries, entries, canonical base.
  have hbase : racl k ((M' : Set K) ∪ range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
      racl k ((M' : Set K) ∪ (((hb.isHW hδ₀).val γ).cb : Set K)) := by
    rw [hM'def]
    have h := congrArg (fun F : IntermediateField _ K ↦ (F : Set K))
      (racl_eq_of_racl_eq M T (hcl γ m hm))
    simp only [racl_base_coe] at h
    exact SetLike.coe_injective h
  apply SetLike.coe_injective
  rw [racl_base_coe, racl_base_coe, racl_union_affineCoeffs hn,
    racl_union_entries_conj hAM' hA'M' m, hbase]

/-- The actual rank-two Hrushovski–Weil action has a uniform affine function-field generator.
The constructible lift, triangularizing matrix and generator are chosen internally. -/
theorem exists_affine_generator {ι κ : Type w} [Finite ι] [Finite κ]
    {v : ι → K} {v' : κ → K} {f₀ : Germ k v v'} (hb : f₀.IsHWBij) {δ₀ : Germ k v v}
    (hδ₀ : δ₀ ∈ f₀.diffSet) (hv : erk k ∅ (range v) = 1)
    (hr : erk k ∅ (δ₀.cb : Set K) = 2) :
    ∃ u : LocusFunctionField k v, Transcendental K u ∧
      IntermediateField.adjoin K ({u} : Set (LocusFunctionField k v)) = ⊤ ∧
      ∀ γ : ↥(hb.isHW hδ₀).prodSubgroup, ∃ a b : K, a ≠ 0 ∧
        (hb.isHW hδ₀).functionFieldAction hv γ u = algebraMap K _ a * u + algebraMap K _ b := by
  obtain ⟨u, _, _, -, hu, htop, -, hcoef⟩ := hb.exists_affine_generator_parameters hδ₀ hv hr
  refine ⟨u, hu, htop, fun γ ↦ ?_⟩
  obtain ⟨a, b, ha, hact, -⟩ := hcoef γ
  exact ⟨a, b, ha, hact⟩

end Germ.IsHWBij

end

end GroupConfig
