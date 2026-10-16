/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.SLLift
import GroupConfig.Constructible.SLClassification

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

end Moebius

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K]

namespace Germ.IsHW

variable {ι : Type*} [Finite ι] {v : ι → K} {g₀ : Germ k v v} (hw : IsHW g₀)
  (hv : erk k ∅ (range v) = 1)

/-- **The affine generator.** Let `t` generate the function field, and suppose that for a
matrix `A ∈ SL₂(K)` every member has a lift `m` in `t` with `A m A⁻¹` upper triangular. Then
`u = φ_A(t)` is a transcendental generator of the same function field in which every member
acts by an affine transformation `u ↦ a u + b` with `a ≠ 0`. -/
private theorem affine_generator_of_triangular_lifts {t : LocusFunctionField k v}
    (ht : Transcendental K t)
    (htop : IntermediateField.adjoin K ({t} : Set (LocusFunctionField k v)) = ⊤)
    (A : SL(2, K))
    (hlift : ∀ γ : ↥hw.prodSubgroup, ∃ m : SL(2, K), hw.IsMoebiusLift hv t γ m ∧
      (A * m * A⁻¹) 1 0 = 0) :
    Transcendental K (moebiusVal A t) ∧
      IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v)) = ⊤ ∧
      ∀ γ : ↥hw.prodSubgroup, ∃ a b : K, a ≠ 0 ∧
        hw.functionFieldAction hv γ (moebiusVal A t) =
          algebraMap K _ a * moebiusVal A t + algebraMap K _ b := by
  -- `t` is a fractional linear expression in `u`.
  have htu : moebiusVal A⁻¹ (moebiusVal A t) = t := by
    rw [moebiusVal_mul ht, inv_mul_cancel, moebiusVal_one]
  have htmem : t ∈
      IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v)) := by
    have h : moebiusVal A⁻¹ (moebiusVal A t) ∈
        IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v)) := by
      obtain ⟨u, hudef⟩ : ∃ u, u = moebiusVal A t := ⟨_, rfl⟩
      rw [← hudef]
      have hu := IntermediateField.mem_adjoin_simple_self K u
      unfold moebiusVal
      exact div_mem
        (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hu)
          (IntermediateField.algebraMap_mem _ _))
        (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hu)
          (IntermediateField.algebraMap_mem _ _))
    rwa [htu] at h
  have htop' : IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v)) = ⊤ :=
    top_unique (htop ▸ IntermediateField.adjoin_simple_le_iff.2 htmem)
  -- `u` is transcendental: otherwise `t` would be algebraic.
  have hu : Transcendental K (moebiusVal A t) := by
    intro halg
    have : Algebra.IsAlgebraic K
        (IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v))) :=
      IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
    exact ht (IntermediateField.isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨t, htmem⟩ :
        IntermediateField.adjoin K ({moebiusVal A t} : Set (LocusFunctionField k v)))))
  refine ⟨hu, htop', fun γ ↦ ?_⟩
  obtain ⟨m, ⟨hden, hm⟩, hn⟩ := hlift γ
  -- The action of `γ` on `t` and on `u`.
  have hσt : hw.functionFieldAction hv γ t = moebiusVal m t := by
    unfold moebiusVal
    rw [eq_div_iff hden]
    exact hm
  have hσu : hw.functionFieldAction hv γ (moebiusVal A t) =
      moebiusVal (A * m * A⁻¹) (moebiusVal A t) := by
    rw [moebiusVal_algEquiv, hσt, moebiusVal_mul ht, moebiusVal_mul ht,
      show A * m * A⁻¹ * A = A * m by group]
  -- The conjugated matrix is upper triangular, so the action is affine.
  obtain ⟨n, hndef⟩ : ∃ n, n = A * m * A⁻¹ := ⟨_, rfl⟩
  rw [← hndef] at hσu hn
  have hdet : n 0 0 * n 1 1 = 1 := by
    have h := n.det_coe
    rw [Matrix.det_fin_two, hn, mul_zero, sub_zero] at h
    exact h
  have h00 : n 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : n 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have h11' : algebraMap K (LocusFunctionField k v) (n 1 1) ≠ 0 := (map_ne_zero _).2 h11
  refine ⟨n 0 0 / n 1 1, n 0 1 / n 1 1, div_ne_zero h00 h11, ?_⟩
  rw [hσu]
  unfold moebiusVal
  rw [hn, map_zero, zero_mul, zero_add, map_div₀, map_div₀]
  field_simp

end Germ.IsHW

namespace Germ.IsHWBij

universe w

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
  refine ⟨moebiusVal A t, ?_⟩
  apply (hb.isHW hδ₀).affine_generator_of_triangular_lifts hv ht htop A
  intro γ
  obtain ⟨m, hm⟩ := hlift γ
  exact ⟨m, hm, (hA m).1 ((hΓ m).2 ⟨γ, hm⟩)⟩

end Germ.IsHWBij

end

end GroupConfig
