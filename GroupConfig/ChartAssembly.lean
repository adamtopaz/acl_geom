/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Germ.AffineGenerator
import GroupConfig.Germ.AffineEvaluation
import GroupConfig.Constructible.SLAffineMultiplier
import GroupConfig.PsiFresh

/-!
# The initial affine chart of a Ψ witness

Let `w` be a witness of the `Q`-configuration satisfying Ψ. This module moves it by an
automorphism `σ` of `K` over `k` and chooses an intermediate field `L` independent from the moved
representatives. Over `L` the moved points are those of an affine chart in five elements
`a, b, c, d, x` (`AclGeom.QWitness.Psi.exists_initial_chart_rows`):
`A = (a, b)`, `B = (c, d)`, `C = (a c, b c + d)`, `S = a`, `T = c`, `U = a c`, `X = x`,
`Y = a x + b` and `Z = c (a x + b) + d`, each as an equality of relative algebraic closures.

The generic statement `GroupConfig.exists_initial_chart_generic` works over the base field of the
group configuration theorem. It takes actual Hrushovski–Weil data of rank two on a curve, three
difference germs `ga`, `gb`, `gc = gb ga⁻¹`, an independent generic point and three rank-one
elements over their canonical bases. Its proof combines four results:

* the affine generator `u` and its coefficient field `M`
  (`Germ.IsHWBij.exists_affine_generator_parameters`);
* an automorphism moving all data independently from `M`;
* evaluation of the affine action at the moved points (`affine_coordinate_evalGen`);
* the multiplier identification (`upper_curve_diagonal_rows`) for the upper triangular matrices
  `[[l, b/l], [0, l⁻¹]]` with `l² = a`.

The Ψ statement applies this to the conclusion of the group configuration theorem for the
rank-two configuration of `w` (`QWitness.PsiCore.exists_isMainConclusion_fresh`). It needs no
guard on `w`. Its consumer is the guarded affine-grid extraction (#27). Descent of the chart to
the original field and the remaining blueprint obligations are not conclusions here.

**Status:** both statements are proved; the supporting lemmas are private.
-/

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

universe u

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Affine coefficients of a transcendental element are unique. -/
private theorem affine_coeff_unique {L : Type*} [Field L] [Algebra K L] {z : L}
    (hz : Transcendental K z) {α β α' β' : K}
    (h : algebraMap K L α * z + algebraMap K L β = algebraMap K L α' * z + algebraMap K L β') :
    α = α' ∧ β = β' := by
  by_cases hα : α = α'
  · refine ⟨hα, ?_⟩
    subst hα
    exact (algebraMap K L).injective (add_left_cancel h)
  · exfalso
    apply hz
    have hne : algebraMap K L (α - α') ≠ 0 := (map_ne_zero _).2 (sub_ne_zero.2 hα)
    have hz' : z = algebraMap K L ((β' - β) / (α - α')) := by
      rw [map_div₀, eq_div_iff hne, map_sub, map_sub]
      linear_combination h
    rw [hz']
    exact isAlgebraic_algebraMap _

/-- An automorphism over the base moving a finite tuple independently from a small set. -/
private theorem exists_aut_indep [IsAlgClosed K] [UniversalDomain k K] {ι : Type*} [Finite ι]
    (d : ι → K) {M : Set K} (hM : IsSmall k M) :
    ∃ σ : K ≃ₐ[k] K, IndepOver k ∅ (range (⇑σ ∘ d)) M := by
  have : IsAlgClosed ↥(racl k (∅ : Set K)) := isAlgClosed_racl _
  obtain ⟨τ, hτ⟩ := exists_algEquiv_indepOver (M := racl k (∅ : Set K))
    (IsSmall.of_finite finite_empty).racl d hM
  refine ⟨τ.restrictScalars k, fun a ha hfin ↦ ?_⟩
  have h := hτ ha hfin
  rwa [erk_congr_base k (racl_union_left (k := k) ∅ M) a, erk_racl_base] at h

/-- Units of the group whose underlying germs are given members of the orbit. -/
private theorem exists_prodSubgroup_val [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    {ι : Type*} [Finite ι] {v : ι → K} {g₀ : Germ k v v} (hw : g₀.IsHW) {g : Germ k v v}
    (hg : g ∈ Germ.orbit g₀) : ∃ γ : ↥hw.prodSubgroup, hw.val γ = g := by
  have hu := hw.isUnit_of_mem hg
  refine ⟨⟨hu.unit, ?_⟩, hu.unit_spec⟩
  rw [hw.mem_prodSubgroup, hu.unit_spec]
  exact hw.mem_prodSet_of_mem hg

/-- The inverse of a group element has the same canonical base. -/
private theorem cb_val_inv [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    {ι : Type*} [Finite ι] {v : ι → K} {g₀ : Germ k v v} (hw : g₀.IsHW)
    (γ : ↥hw.prodSubgroup) : (hw.val γ⁻¹).cb = (hw.val γ).cb := by
  refine Germ.IsInverse.cb_eq ⟨?_, ?_⟩
  · change ((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ).val * (γ : (Germ k v v)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  · change (γ : (Germ k v v)ˣ).val * ((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.mul_inv]

/-- Independence of a moved tuple passes to any tuple whose values occur in it. -/
private theorem indepOver_range_comp_mono {α β : Type*} {D : α → K} {σ : K → K} {M : Set K}
    (h : IndepOver k ∅ (range (σ ∘ D)) M) (f : β → K) (hf : ∀ i, ∃ j, D j = f i) :
    IndepOver k ∅ (range (σ ∘ f)) M := by
  refine h.mono_left ?_
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hf i
  exact ⟨j, by simp only [Function.comp_apply, hj]⟩

/-- A generic point independent from a code tuple and, jointly, from `M`, is independent from
`M` together with the closure of the code. -/
private theorem indep_point_union {Y Cd F M : Set K} (hF : racl k F = racl k Cd)
    (hYC : IndepOver k ∅ Y Cd) (hjoint : IndepOver k ∅ (Cd ∪ Y) M) :
    IndepOver k ∅ Y (M ∪ F) := by
  have h2 : IndepOver k (∅ ∪ Cd) M Y := (indepOver_union_right_iff.1 hjoint.symm).2
  have h3 : IndepOver k ∅ Y (Cd ∪ M) := indepOver_union_right_iff.2 ⟨hYC, h2.symm⟩
  have h4 : IndepOver k ∅ Y (racl k (∅ ∪ (Cd ∪ M))) := indepOver_racl_right_iff.2 h3
  refine h4.mono_right (union_subset ?_ ?_)
  · exact fun z hz ↦ subset_racl k _ (Or.inr (Or.inr hz))
  · intro z hz
    have hz' : z ∈ racl k Cd := hF ▸ subset_racl k F hz
    exact racl_mono (subset_union_left.trans subset_union_right) hz'

/-- The upper triangular matrix `[[x, b/x], [0, x⁻¹]]`, whose affine data are `(x², b)`. -/
private def sqrtMat {K : Type*} [Field K] (x b : K) (hx : x ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![x, b / x; 0, x⁻¹], by simp [Matrix.det_fin_two_of, hx]⟩

/-- The entries of `sqrtMat x b` generate the closure of its affine data `(x², b)`. -/
private theorem racl_slEntries_sqrtMat {F : Type*} [Field F] [Algebra F K] {x a b : K}
    (hx : x ≠ 0) (ha : x ^ 2 = a) :
    racl F (slEntries (sqrtMat x b hx)) = racl F ({a, b} : Set K) := by
  have hsq : ({x ^ 2} : Set K) ⊆ {a, b} := singleton_subset_iff.2 (Or.inl ha)
  have hxm : x ∈ racl F ({a, b} : Set K) :=
    racl_mono hsq (mem_racl_singleton_pow (k := F) (x := x) two_ne_zero)
  have hbm : b ∈ racl F ({a, b} : Set K) := subset_racl F _ (Or.inr rfl)
  refine le_antisymm (racl_le_of_subset_racl ?_) (racl_le_of_subset_racl ?_)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact hxm
    · exact div_mem hbm hxm
    · exact zero_mem _
    · exact inv_mem hxm
  · have hx' : x ∈ racl F (slEntries (sqrtMat x b hx)) := subset_racl F _ ⟨(0, 0), rfl⟩
    have hb' : b / x ∈ racl F (slEntries (sqrtMat x b hx)) := subset_racl F _ ⟨(0, 1), rfl⟩
    rintro z (rfl | rfl)
    · rw [← ha]
      exact pow_mem hx' 2
    · have h := mul_mem hb' hx'
      rwa [div_mul_cancel₀ _ hx] at h

/-- A square root generates the same closure as its square. -/
private theorem racl_singleton_sq {F : Type*} [Field F] [Algebra F K] {x a : K}
    (ha : x ^ 2 = a) : racl F ({a} : Set K) = racl F ({x} : Set K) := by
  rw [← ha]
  exact racl_pow x two_ne_zero

/-- Ranks over the base are invariant under automorphisms. -/
private theorem erk_image_aut (σ : K ≃ₐ[k] K) (X : Set K) :
    erk k ∅ (⇑σ '' X) = erk k ∅ X := by
  have h := erk_image σ ∅ X
  rwa [image_empty] at h

/-- **The initial affine chart over a fresh coefficient field.**
From actual HW data of rank two on a curve, three difference germs `ga, gb, gc = gb ga⁻¹`,
an independent generic point `y`, and rank-one elements `s, t, w₀` algebraic over the three
canonical bases with the dependent-triple ranks, an automorphism `σ` moves all data (and an
arbitrary finite tuple `extra`) independently from the coefficient field `M` of the affine
generator. Over `M` the moved data have all nine initial chart rows. -/
theorem exists_initial_chart_generic [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    {ι κ : Type u} [Finite ι] [Finite κ] {v : ι → K} {v' : κ → K} {f₀ : Germ k v v'}
    (hb : f₀.IsHWBij) {ga gb gc : Germ k v v} (hga : ga ∈ f₀.diffSet) (hgb : gb ∈ f₀.diffSet)
    (hgc : gc ∈ f₀.diffSet) (hprod : gb = gc * ga) (hv : erk k ∅ (range v) = 1)
    (hr : erk k ∅ (ga.cb : Set K) = 2) {y : ι → K} (hy : IsGen k v y)
    (hind : IndepTriple k (ga.cb : Set K) gb.cb (range y))
    {μ : Type} [Finite μ] (extra : μ → K) {s t w₀ : K}
    (hs : s ∈ racl k (ga.cb : Set K)) (ht : t ∈ racl k (gb.cb : Set K))
    (hw₀ : w₀ ∈ racl k (gc.cb : Set K))
    (hst : erk k ∅ ({s, t} : Set K) = 2) (hsw : erk k ∅ ({s, w₀} : Set K) = 2)
    (hstw : erk k ∅ ({s, t, w₀} : Set K) = 2) :
    ∃ (σ : K ≃ₐ[k] K) (M : IntermediateField k K) (_ : IsAlgClosed ↥M),
      IsSmall k (M : Set K) ∧ IndepOver k ∅ (range (⇑σ ∘ extra)) (M : Set K) ∧
      ∃ a b c d x : K,
        racl (↥M) ({a, b} : Set K) = racl (↥M) ((ga.map σ).cb : Set K) ∧
        racl (↥M) ({c, d} : Set K) = racl (↥M) ((gb.map σ).cb : Set K) ∧
        racl (↥M) ({a * c, b * c + d} : Set K) = racl (↥M) ((gc.map σ).cb : Set K) ∧
        racl (↥M) ({a} : Set K) = racl (↥M) ({σ s} : Set K) ∧
        racl (↥M) ({c} : Set K) = racl (↥M) ({σ t} : Set K) ∧
        racl (↥M) ({a * c} : Set K) = racl (↥M) ({σ w₀} : Set K) ∧
        racl (↥M) ({x} : Set K) = racl (↥M) (range ((ga.map σ).evalGen (⇑σ ∘ y))) ∧
        racl (↥M) ({a * x + b} : Set K) = racl (↥M) (range (⇑σ ∘ y)) ∧
        racl (↥M) ({c * (a * x + b) + d} : Set K) =
          racl (↥M) (range ((gb.map σ).evalGen (⇑σ ∘ y))) := by
  classical
  have hw : ga.IsHW := hb.isHW hga
  -- The affine generator and its coefficient field.
  obtain ⟨u, M, iM, hMs, hu, -, ⟨P, Q, hQ, hPQ⟩, hcoef⟩ :=
    hb.exists_affine_generator_parameters hga hv hr
  -- Move all data independently from `M`.
  obtain ⟨σ, hσ⟩ := exists_aut_indep (Sum.elim extra (Sum.elim ![s, t, w₀]
    (Sum.elim ga.codeTuple (Sum.elim gb.codeTuple (Sum.elim gc.codeTuple y))))) hMs
  -- The moved germs as group elements.
  have horb : f₀.diffSet = Germ.orbit ga := Germ.diffSet_eq_orbit hga
  obtain ⟨γa, hγa⟩ := exists_prodSubgroup_val hw (horb ▸ Germ.map_mem_diffSet hga σ)
  obtain ⟨γb, hγb⟩ := exists_prodSubgroup_val hw (horb ▸ Germ.map_mem_diffSet hgb σ)
  obtain ⟨γc, hγc⟩ := exists_prodSubgroup_val hw (horb ▸ Germ.map_mem_diffSet hgc σ)
  have hrel : γb = γc * γa := by
    apply Subtype.ext
    apply Units.ext
    change hw.val γb = hw.val γc * hw.val γa
    rw [hγa, hγb, hγc, hprod]
    simpa only [Germ.mapHom_apply] using map_mul (Germ.mapHom σ) gc ga
  -- The affine coefficients of the inverses.
  obtain ⟨α, β, hα0, hacta, hra⟩ := hcoef γa⁻¹
  obtain ⟨α', β', hα'0, hactb, hrb⟩ := hcoef γb⁻¹
  obtain ⟨α'', β'', -, hactc, hrc⟩ := hcoef γc⁻¹
  rw [cb_val_inv, hγa] at hra
  rw [cb_val_inv, hγb] at hrb
  rw [cb_val_inv, hγc] at hrc
  have hco : α' = α'' * α ∧ β' = α'' * β + β'' := by
    have hinv : γb⁻¹ = γa⁻¹ * γc⁻¹ := by rw [hrel, _root_.mul_inv_rev]
    have e := DFunLike.congr_fun (map_mul (hw.functionFieldAction hv) γa⁻¹ γc⁻¹) u
    rw [← hinv, AlgEquiv.mul_apply, hactb, hactc, map_add, map_mul, AlgEquiv.commutes,
      AlgEquiv.commutes, hacta] at e
    refine affine_coeff_unique hu ?_
    rw [e, map_mul, map_add, map_mul]
    ring
  -- Codes, the moved independent triple, and genericity of the moved point.
  have hcodeA : racl k (((ga.map σ).cb : IntermediateField k K) : Set K) =
      racl k (range (⇑σ ∘ ga.codeTuple)) :=
    (Germ.racl_codeTuple (ga.map σ)).symm.trans (Germ.racl_codeTuple_map σ ga)
  have hcodeB : racl k (((gb.map σ).cb : IntermediateField k K) : Set K) =
      racl k (range (⇑σ ∘ gb.codeTuple)) :=
    (Germ.racl_codeTuple (gb.map σ)).symm.trans (Germ.racl_codeTuple_map σ gb)
  have hindc : IndepTriple k (range ga.codeTuple) (range gb.codeTuple) (range y) :=
    indepTriple_of_racl_eq (Germ.racl_codeTuple ga).symm (Germ.racl_codeTuple gb).symm rfl hind
  have hindσ := GroupConfiguration.IndepTriple.image σ hindc
  rw [← range_comp, ← range_comp, ← range_comp] at hindσ
  have hYA : IndepOver k ∅ (range (⇑σ ∘ y)) (range (⇑σ ∘ ga.codeTuple)) :=
    hindσ.rotate.rotate.indepOver_left (finite_range _) (finite_range _) (finite_range _)
  have hYB : IndepOver k ∅ (range (⇑σ ∘ y)) (range (⇑σ ∘ gb.codeTuple)) :=
    (hindσ.rotate.indepOver_left (finite_range _) (finite_range _) (finite_range _)).symm
  have hjA : IndepOver k ∅ (range (⇑σ ∘ ga.codeTuple) ∪ range (⇑σ ∘ y)) (M : Set K) := by
    have h := indepOver_range_comp_mono hσ (Sum.elim ga.codeTuple y) (fun i ↦ by
      cases i with
      | inl c => exact ⟨Sum.inr (Sum.inr (Sum.inl c)), rfl⟩
      | inr j => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))), rfl⟩)
    rwa [Sum.comp_elim, Sum.elim_range] at h
  have hjB : IndepOver k ∅ (range (⇑σ ∘ gb.codeTuple) ∪ range (⇑σ ∘ y)) (M : Set K) := by
    have h := indepOver_range_comp_mono hσ (Sum.elim gb.codeTuple y) (fun i ↦ by
      cases i with
      | inl c => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl c))), rfl⟩
      | inr j => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))), rfl⟩)
    rwa [Sum.comp_elim, Sum.elim_range] at h
  have hyA : IsGenericOver (racl k ((M : Set K) ∪ ((ga.map σ).cb : Set K))) v (⇑σ ∘ y) :=
    (hy.map σ).isGenericOver_racl (hMs.union (ga.map σ).isSmall_cb)
      (indep_point_union hcodeA hYA hjA)
  have hyB : IsGenericOver (racl k ((M : Set K) ∪ ((gb.map σ).cb : Set K))) v (⇑σ ∘ y) :=
    (hy.map σ).isGenericOver_racl (hMs.union (gb.map σ).isSmall_cb)
      (indep_point_union hcodeB hYB hjB)
  have hyM : IsGenericOver M v (⇑σ ∘ y) :=
    hyA.of_le fun z hz ↦ subset_racl k _ (Or.inl hz)
  -- Coordinate values at the moved points.
  have hbase : ∀ {S : Set K} {z : K}, z ∈ racl (↥M) S → z ∈ racl k ((M : Set K) ∪ S) :=
    fun hz ↦ (mem_racl_base_iff M _ _).1 hz
  have hαm : α ∈ racl k ((M : Set K) ∪ ((hw.val γa).cb : Set K)) := by
    rw [hγa]
    exact hbase (hra ▸ subset_racl (↥M) _ (Or.inl rfl))
  have hβm : β ∈ racl k ((M : Set K) ∪ ((hw.val γa).cb : Set K)) := by
    rw [hγa]
    exact hbase (hra ▸ subset_racl (↥M) _ (Or.inr rfl))
  have hα'm : α' ∈ racl k ((M : Set K) ∪ ((hw.val γb).cb : Set K)) := by
    rw [hγb]
    exact hbase (hrb ▸ subset_racl (↥M) _ (Or.inl rfl))
  have hβ'm : β' ∈ racl k ((M : Set K) ∪ ((hw.val γb).cb : Set K)) := by
    rw [hγb]
    exact hbase (hrb ▸ subset_racl (↥M) _ (Or.inr rfl))
  obtain ⟨x₀, z₀, hx₀, -, hz₀eq, hrx₀, hrz₀⟩ := affine_coordinate_evalGen hw hv hMs hu P Q hQ
    hPQ γa α β hαm hβm hacta (by rw [hγa]; exact hyA)
  obtain ⟨x₁, z₁, hx₁, -, hz₁eq, -, hrz₁⟩ := affine_coordinate_evalGen hw hv hMs hu P Q hQ
    hPQ γb α' β' hα'm hβ'm hactb (by rw [hγb]; exact hyB)
  have hx₁₀ : x₁ = x₀ := LocusFunctionField.HasValue.eq_value hyM hx₁ hx₀
  rw [hγa] at hrz₀
  rw [hγb] at hrz₁
  -- The chart coordinates and the six rows from the coordinate.
  have hY : α⁻¹ * z₀ + -(β * α⁻¹) = x₀ := by
    rw [hz₀eq, mul_add, ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
    ring
  have hZ : α' * (α⁻¹ * z₀ + -(β * α⁻¹)) + β' = z₁ := by
    rw [hY, hz₁eq, hx₁₀]
  have hAc : α⁻¹ * α' = α'' := by
    rw [hco.1, mul_comm α'' α, ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hCc : -(β * α⁻¹) * α' + β' = β'' := by
    rw [hco.1, hco.2]
    field_simp
    ring
  have hApair : racl (↥M) ({α⁻¹, -(β * α⁻¹)} : Set K) = racl (↥M) ({α, β} : Set K) := by
    have hαM : α ∈ racl (↥M) ({α, β} : Set K) := subset_racl (↥M) _ (Or.inl rfl)
    have hβM : β ∈ racl (↥M) ({α, β} : Set K) := subset_racl (↥M) _ (Or.inr rfl)
    have hiM : α⁻¹ ∈ racl (↥M) ({α⁻¹, -(β * α⁻¹)} : Set K) := subset_racl (↥M) _ (Or.inl rfl)
    have hjM : -(β * α⁻¹) ∈ racl (↥M) ({α⁻¹, -(β * α⁻¹)} : Set K) :=
      subset_racl (↥M) _ (Or.inr rfl)
    refine le_antisymm (racl_le_of_subset_racl ?_) (racl_le_of_subset_racl ?_)
    · rintro z (rfl | rfl)
      · exact inv_mem hαM
      · exact neg_mem (mul_mem hβM (inv_mem hαM))
    · rintro z (rfl | rfl)
      · have h := inv_mem hiM
        rwa [inv_inv] at h
      · have h := mul_mem (neg_mem hjM) (inv_mem hiM)
        rwa [neg_neg, inv_inv, mul_assoc, inv_mul_cancel₀ hα0, mul_one] at h
  -- The field rows from the raw multiplier identification over `M`.
  have : UniversalDomain ↥M K := universalDomain_of_isSmall M hMs
  have hαi0 : α⁻¹ ≠ 0 := inv_ne_zero hα0
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq α⁻¹ two_pos
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq α' two_pos
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hαi0 (by rw [← hl]; ring)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hα'0 (by rw [← hm]; ring)
  have hErk : ∀ {X : Set K}, X.Finite → IndepOver k ∅ X (M : Set K) →
      erk (↥M) ∅ X = erk k ∅ X := fun {X} hX hi ↦ by
    rw [erk_base_empty M X]
    have h := hi.erk_eq subset_rfl hX
    rwa [empty_union] at h
  have hrM : ∀ {X Y : Set K}, racl k X = racl k Y → racl (↥M) X = racl (↥M) Y :=
    fun h ↦ racl_base_congr M h
  have hmapcb : ∀ g : Germ k v v, (⇑σ '' (g.cb : Set K)) = ((g.map σ).cb : Set K) := fun g ↦ by
    rw [Germ.cb_map, IntermediateField.coe_map]
    rfl
  have hmemM : ∀ {z : K} {g : Germ k v v}, z ∈ racl k (g.cb : Set K) →
      σ z ∈ racl (↥M) ((g.map σ).cb : Set K) := fun hz ↦ by
    have h := mem_racl_map σ hz
    rw [hmapcb] at h
    exact (mem_racl_base_iff M _ _).2 (racl_mono subset_union_right h)
  have hDmem : ∀ {z : K}, z ∈ ({s, t, w₀} : Set K) →
      σ z ∈ range (⇑σ ∘ Sum.elim extra (Sum.elim ![s, t, w₀]
        (Sum.elim ga.codeTuple (Sum.elim gb.codeTuple (Sum.elim gc.codeTuple y))))) := by
    rintro z (rfl | rfl | rfl)
    · exact ⟨Sum.inr (Sum.inl 0), rfl⟩
    · exact ⟨Sum.inr (Sum.inl 1), rfl⟩
    · exact ⟨Sum.inr (Sum.inl 2), rfl⟩
  have hpairM : ∀ {X : Set K}, X ⊆ ({s, t, w₀} : Set K) →
      erk (↥M) ∅ (⇑σ '' X) = erk k ∅ X := fun hX ↦ by
    rw [hErk ((((toFinite ({s, t, w₀} : Set K)).subset hX).image _))
      (hσ.mono_left (by rintro _ ⟨z, hz, rfl⟩; exact hDmem (hX hz))), erk_image_aut]
  obtain ⟨g, hgdef⟩ : ∃ g, g = sqrtMat l (-(β * α⁻¹)) hl0 := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = sqrtMat m β' hm0 := ⟨_, rfl⟩
  have hg10 : g 1 0 = 0 := by rw [hgdef]; rfl
  have hh10 : h 1 0 = 0 := by rw [hhdef]; rfl
  have hg00 : g 0 0 = l := by rw [hgdef]; rfl
  have hh00 : h 0 0 = m := by rw [hhdef]; rfl
  have hg01 : g 0 1 = -(β * α⁻¹) / l := by rw [hgdef]; rfl
  have hg11 : g 1 1 = l⁻¹ := by rw [hgdef]; rfl
  have hh01 : h 0 1 = β' / m := by rw [hhdef]; rfl
  have hmul : ∀ i j, (h * g) i j = h i 0 * g 0 j + h i 1 * g 1 j := fun i j ↦ by
    rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hp00 : (h * g) 0 0 = m * l := by
    rw [hmul, hg10, mul_zero, add_zero, hg00, hh00]
  have hp01 : (h * g) 0 1 = m * (-(β * α⁻¹) / l) + β' / m * l⁻¹ := by
    rw [hmul, hh00, hg01, hh01, hg11]
  have hgE : racl (↥M) (slEntries g) = racl (↥M) ({α⁻¹, -(β * α⁻¹)} : Set K) := by
    rw [hgdef]
    exact racl_slEntries_sqrtMat hl0 hl
  have hhE : racl (↥M) (slEntries h) = racl (↥M) ({α', β'} : Set K) := by
    rw [hhdef]
    exact racl_slEntries_sqrtMat hm0 hm
  have hpE : ({α⁻¹ * α', -(β * α⁻¹) * α' + β'} : Set K) ⊆ racl (↥M) (slEntries (h * g)) := by
    have h0 : (h * g) 0 0 ∈ racl (↥M) (slEntries (h * g)) := subset_racl (↥M) _ ⟨(0, 0), rfl⟩
    have h1 : (h * g) 0 1 ∈ racl (↥M) (slEntries (h * g)) := subset_racl (↥M) _ ⟨(0, 1), rfl⟩
    have e1 : α⁻¹ * α' = (h * g) 0 0 ^ 2 := by
      rw [hp00, mul_pow, hm, hl, mul_comm]
    have e2 : -(β * α⁻¹) * α' + β' = (h * g) 0 0 * (h * g) 0 1 := by
      rw [hp00, hp01, ← hm]
      field_simp
    rintro z (rfl | rfl)
    · rw [e1]
      exact pow_mem h0 2
    · rw [e2]
      exact mul_mem h0 h1
  -- The rank-four join and the point incidences over `M`.
  have hjAB : IndepOver k ∅ (range (⇑σ ∘ ga.codeTuple) ∪ range (⇑σ ∘ gb.codeTuple))
      (M : Set K) := by
    have h' := indepOver_range_comp_mono hσ (Sum.elim ga.codeTuple gb.codeTuple) (fun i ↦ by
      cases i with
      | inl c => exact ⟨Sum.inr (Sum.inr (Sum.inl c)), rfl⟩
      | inr c => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl c))), rfl⟩)
    rwa [Sum.comp_elim, Sum.elim_range] at h'
  have hcA2 : erk k ∅ (range (⇑σ ∘ ga.codeTuple)) = 2 := by
    rw [range_comp, erk_image_aut, erk_eq_of_racl_eq (Germ.racl_codeTuple ga), hr]
  have hcB2 : erk k ∅ (range (⇑σ ∘ gb.codeTuple)) = 2 := by
    rw [range_comp, erk_image_aut, erk_eq_of_racl_eq (Germ.racl_codeTuple gb),
      Germ.erk_cb_eq_of_mem_orbit (horb ▸ hgb), hr]
  have hgh4 : erk (↥M) ∅ (slEntries g ∪ slEntries h) = 4 := by
    have hr4 : racl (↥M) (slEntries g ∪ slEntries h) =
        racl (↥M) (range (⇑σ ∘ ga.codeTuple) ∪ range (⇑σ ∘ gb.codeTuple)) :=
      racl_union_congr (hgE.trans (hApair.trans (hra.trans (hrM hcodeA))))
        (hhE.trans (hrb.trans (hrM hcodeB)))
    rw [erk_eq_of_racl_eq hr4, hErk ((finite_range _).union (finite_range _)) hjAB,
      hindσ.erk_union_left (finite_range _), hcA2, hcB2]
    norm_num
  have hs' : σ s ∈ racl (↥M) (slEntries g) := by
    rw [hgE, hApair, hra]
    exact hmemM hs
  have ht' : σ t ∈ racl (↥M) (slEntries h) := by
    rw [hhE, hrb]
    exact hmemM ht
  have hw' : σ w₀ ∈ racl (↥M) (slEntries (h * g)) := by
    have h' := hmemM hw₀
    rw [← hrc, ← hAc, ← hCc] at h'
    exact racl_le_of_subset_racl hpE h'
  have hst' : erk (↥M) ∅ ({σ s, σ t} : Set K) = 2 := by
    rw [← image_pair (⇑σ) s t, hpairM (by
      rintro z (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)), hst]
  have hsw' : erk (↥M) ∅ ({σ s, σ w₀} : Set K) = 2 := by
    rw [← image_pair (⇑σ) s w₀, hpairM (by
      rintro z (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)), hsw]
  have hstw' : erk (↥M) ∅ ({σ s, σ t, σ w₀} : Set K) = 2 := by
    rw [← image_pair (⇑σ) t w₀, ← image_insert_eq, hpairM subset_rfl, hstw]
  obtain ⟨hS, hT, hU⟩ :=
    upper_curve_diagonal_rows (k := ↥M) g h hg10 hh10 hgh4 hs' ht' hw' hst' hsw' hstw'
  rw [hg00] at hS
  rw [hh00] at hT
  rw [hp00] at hU
  refine ⟨σ, M, iM, hMs, indepOver_range_comp_mono hσ extra (fun i ↦ ⟨Sum.inl i, rfl⟩),
    α⁻¹, -(β * α⁻¹), α', β', z₀,
    hApair.trans hra, hrb, ?_, ?_, ?_, ?_, hrz₀, ?_, ?_⟩
  · rw [hAc, hCc]
    exact hrc
  · rw [racl_singleton_sq hl, hS]
  · rw [racl_singleton_sq hm, hT]
  · rw [racl_singleton_sq (x := m * l) (by rw [mul_pow, hm, hl, mul_comm]), hU]
  · rw [hY]
    exact hrx₀
  · rw [hZ]
    exact hrz₁


end

end GroupConfig

namespace GroupConfig

open AclGeom Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Closures over an intermediate field of an intermediate field agree with closures over its
restriction of scalars. -/
private theorem racl_restrictScalars_coe {F₀ : IntermediateField k K}
    (M : IntermediateField (↥F₀) K) (X : Set K) :
    ((racl (↥(M.restrictScalars k)) X : IntermediateField _ K) : Set K) =
      ((racl (↥M) X : IntermediateField _ K) : Set K) := by
  have hF : (F₀ : Set K) ⊆ (M : Set K) := fun z hz ↦ M.algebraMap_mem (⟨z, hz⟩ : F₀)
  rw [racl_base_coe (M.restrictScalars k), racl_base_coe M, racl_base_coe F₀, ← union_assoc,
    union_eq_right.2 hF, IntermediateField.coe_restrictScalars]

/-- Row equalities over `M` are row equalities over its restriction of scalars. -/
private theorem racl_restrictScalars_eq {F₀ : IntermediateField k K}
    {M : IntermediateField (↥F₀) K} {X Y : Set K} (h : racl (↥M) X = racl (↥M) Y) :
    racl (↥(M.restrictScalars k)) X = racl (↥(M.restrictScalars k)) Y := by
  apply SetLike.coe_injective
  rw [racl_restrictScalars_coe, racl_restrictScalars_coe, h]

/-- Equal closures stay equal after an automorphism. -/
private theorem racl_image_congr (σ : K ≃ₐ[k] K) {X Y : Set K} (h : racl k X = racl k Y) :
    racl k (⇑σ '' X) = racl k (⇑σ '' Y) := by
  rw [← racl_map, ← racl_map, h]

end

end GroupConfig

namespace AclGeom.QWitness

open GroupConfig Set

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

/-- **The nine initial chart rows of a Ψ witness.** For a Ψ witness `w` there are an
automorphism `σ` of `K` over `k`, an intermediate field `L` independent from the moved
representatives `σ ∘ w.repTuple`, and five elements `a, b, c, d, x` such that over `L` the moved
points `A, B, C, S, T, U, X, Y, Z` of `w` are the points of the affine chart
`(a, b), (c, d), (ac, bc + d), a, c, ac, x, ax + b, c(ax + b) + d`. -/
theorem Psi.exists_initial_chart_rows [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    {w : QWitness k K} (hw : w.Psi) :
    ∃ (σ : K ≃ₐ[k] K) (L : IntermediateField k K),
      IndepOver k ∅ (L : Set K) (range (⇑σ ∘ w.repTuple)) ∧ ∃ a b c d x : K,
        racl (↥L) (range ![σ w.A₁.rep, σ w.A₂.rep]) = racl (↥L) (range ![a, b]) ∧
        racl (↥L) (range ![σ w.B₁.rep, σ w.B₂.rep]) = racl (↥L) (range ![c, d]) ∧
        racl (↥L) (range ![σ w.C₁.rep, σ w.C₂.rep]) =
          racl (↥L) (range ![a * c, b * c + d]) ∧
        racl (↥L) ({σ w.S.rep} : Set K) = racl (↥L) ({a} : Set K) ∧
        racl (↥L) ({σ w.T.rep} : Set K) = racl (↥L) ({c} : Set K) ∧
        racl (↥L) ({σ w.U.rep} : Set K) = racl (↥L) ({a * c} : Set K) ∧
        racl (↥L) ({σ w.X.rep} : Set K) = racl (↥L) ({x} : Set K) ∧
        racl (↥L) ({σ w.Y.rep} : Set K) = racl (↥L) ({a * x + b} : Set K) ∧
        racl (↥L) ({σ w.Z.rep} : Set K) = racl (↥L) ({c * (a * x + b) + d} : Set K) := by
  classical
  obtain ⟨S', T', U', hq⟩ := hw.quad
  obtain ⟨E, -, -, hEind, hmain, haR, hxR⟩ :=
    hw.toCore.exists_isMainConclusion_fresh (W := ∅) finite_empty
  rw [union_empty] at hEind
  generalize hF₀ : racl k E = F₀ at hmain haR hxR
  obtain ⟨iF, uF, ν, ν', _, _, v, v', f₀, ga, gb, gc, y', hb, hga, hgb, hgc, hprod, hy, hind, -,
    -, hA, hB, hC, hX, hY, hZ, hvx, -, -⟩ := hmain
  -- Ranks of witness points over `F₀` are ranks over `k`.
  have hrk : ∀ {X : Set K}, X ⊆ range w.repTuple → erk (↥F₀) ∅ X = erk k ∅ X := fun hX ↦ by
    rw [erk_base_empty, ← hF₀, erk_racl_base]
    have := hEind.symm hX ((finite_range _).subset hX)
    rwa [empty_union] at this
  have hnle : ∀ {P₁ Q₁ : Point k K}, P₁ ≠ Q₁ → ¬ Q₁.1 ≤ P₁.1 := fun {P₁ Q₁} hPQ hle ↦
    hPQ (Subtype.ext ((P₁.2.le_iff_eq Q₁.2.1).1 hle).symm)
  have hpair : ∀ {P₁ Q₁ : Point k K}, P₁ ≠ Q₁ → erk k ∅ ({P₁.rep, Q₁.rep} : Set K) = 2 :=
      fun {P₁ Q₁} hPQ ↦ by
    have hr : racl k ({P₁.rep, Q₁.rep} : Set K) = (P₁.1 ⊔ Q₁.1).1 := by
      rw [← coe_sup_point₂, P₁.point_rep, Q₁.point_rep]
    have h := ClosedIF.erk_eq_of_racl_eq hr
      ((Point.rankEq_one P₁).sup_point_of_not_le (hnle hPQ))
    norm_num at h
    exact h
  have hST : w.S ≠ w.T := hq.injective.ne (by decide : (0 : Fin 6) ≠ 1)
  have hSU : w.S ≠ w.U := hq.injective.ne (by decide : (0 : Fin 6) ≠ 2)
  have hr3 : racl k ({w.S.rep, w.T.rep, w.U.rep} : Set K) = (w.S.1 ⊔ (w.T.1 ⊔ w.U.1)).1 := by
    rw [insert_eq]
    exact ClosedIF.racl_union_eq_sup (congrArg Subtype.val w.S.point_rep)
      (by rw [← coe_sup_point₂, w.T.point_rep, w.U.point_rep])
  have hsub : ({w.S.rep, w.T.rep, w.U.rep} : Set K) ⊆ range w.repTuple := by
    rintro z (rfl | rfl | rfl)
    exacts [⟨15, rfl⟩, ⟨16, rfl⟩, ⟨17, rfl⟩]
  have hst : erk (↥F₀) ∅ ({w.S.rep, w.T.rep} : Set K) = 2 := by
    rw [hrk ((show ({w.S.rep, w.T.rep} : Set K) ⊆ {w.S.rep, w.T.rep, w.U.rep} from
      insert_subset_insert (singleton_subset_iff.2 (Or.inl rfl))).trans hsub), hpair hST]
  have hsu : erk (↥F₀) ∅ ({w.S.rep, w.U.rep} : Set K) = 2 := by
    rw [hrk ((show ({w.S.rep, w.U.rep} : Set K) ⊆ {w.S.rep, w.T.rep, w.U.rep} from
      insert_subset_insert (singleton_subset_iff.2 (Or.inr rfl))).trans hsub), hpair hSU]
  have hstu : erk (↥F₀) ∅ ({w.S.rep, w.T.rep, w.U.rep} : Set K) = 2 := by
    have h := ClosedIF.erk_eq_of_racl_eq hr3 hw.rank_STU
    rw [hrk hsub]
    exact_mod_cast h
  -- The dependent triple lies on the three canonical bases.
  have hmem : ∀ {P₁ Q₁ R₁ : Point k K}, R₁.1 ≤ P₁.1 ⊔ Q₁.1 →
      R₁.rep ∈ racl k ({P₁.rep, Q₁.rep} : Set K) := fun {P₁ Q₁ R₁} h ↦ by
    have h1 : ClosedIF.point k R₁.rep ≤ ClosedIF.point k P₁.rep ⊔ ClosedIF.point k Q₁.rep := by
      rw [R₁.point_rep, P₁.point_rep, Q₁.point_rep]
      exact h
    have h2 : R₁.rep ∈
        ((ClosedIF.point k P₁.rep ⊔ ClosedIF.point k Q₁.rep).1 : IntermediateField k K) :=
      ClosedIF.point_le_iff.1 h1
    rwa [coe_sup_point₂] at h2
  have hcbA : racl (↥F₀) (ga.cb : Set K) = racl (↥F₀) ({w.A₁.rep, w.A₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, ← hA, aTuple, Matrix.range_cons_cons_empty]
  have hcbB : racl (↥F₀) (gb.cb : Set K) = racl (↥F₀) ({w.B₁.rep, w.B₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, ← hB, bTuple, Matrix.range_cons_cons_empty]
  have hcbC : racl (↥F₀) (gc.cb : Set K) = racl (↥F₀) ({w.C₁.rep, w.C₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, ← hC, cTuple, Matrix.range_cons_cons_empty]
  have hs : w.S.rep ∈ racl (↥F₀) (ga.cb : Set K) := by
    rw [hcbA]
    exact racl_subset_racl_base F₀ _ (hmem (P₁ := w.A₁) (Q₁ := w.A₂) hw.S_le)
  have ht : w.T.rep ∈ racl (↥F₀) (gb.cb : Set K) := by
    rw [hcbB]
    exact racl_subset_racl_base F₀ _ (hmem (P₁ := w.B₁) (Q₁ := w.B₂) hw.T_le)
  have hu : w.U.rep ∈ racl (↥F₀) (gc.cb : Set K) := by
    rw [hcbC]
    exact racl_subset_racl_base F₀ _ (hmem (P₁ := w.C₁) (Q₁ := w.C₂) hw.U_le)
  have hv : erk (↥F₀) ∅ (range v) = 1 := hvx.trans hxR
  have hr : erk (↥F₀) ∅ (ga.cb : Set K) = 2 := by
    rw [← erk_eq_of_racl_eq (Germ.racl_codeTuple ga), ← erk_eq_of_racl_eq hA, haR]
  -- The generic chart over `F₀`.
  obtain ⟨σ, M, -, -, hσM, a, b, c, d, x, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ :=
    exists_initial_chart_generic hb hga hgb hgc hprod hv hr hy hind w.repTuple hs ht hu hst hsu
      hstu
  -- The moved bases and points are the moved witness points.
  have hindc : IndepTriple (↥F₀) (range ga.codeTuple) (range gb.codeTuple) (range y') :=
    indepTriple_of_racl_eq (Germ.racl_codeTuple ga).symm (Germ.racl_codeTuple gb).symm rfl hind
  have hyA : IndepOver (↥F₀) ∅ (range y') (ga.cb : Set K) := by
    have h := hindc.rotate.rotate.indepOver_left (finite_range _) (finite_range _)
      (finite_range _)
    refine (indepOver_racl_right_iff.2 h).mono_right ?_
    rw [empty_union]
    exact Germ.cb_subset_racl_codeTuple ga
  have hyB : IndepOver (↥F₀) ∅ (range y') (gb.cb : Set K) := by
    have h := (hindc.rotate.indepOver_left (finite_range _) (finite_range _)
      (finite_range _)).symm
    refine (indepOver_racl_right_iff.2 h).mono_right ?_
    rw [empty_union]
    exact Germ.cb_subset_racl_codeTuple gb
  have hmapA : racl (↥F₀) ((ga.map σ).cb : Set K) =
      racl (↥F₀) ({σ w.A₁.rep, σ w.A₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, Germ.racl_codeTuple_map, range_comp, racl_image_congr σ hA.symm,
      aTuple, Matrix.range_cons_cons_empty, image_pair]
  have hmapB : racl (↥F₀) ((gb.map σ).cb : Set K) =
      racl (↥F₀) ({σ w.B₁.rep, σ w.B₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, Germ.racl_codeTuple_map, range_comp, racl_image_congr σ hB.symm,
      bTuple, Matrix.range_cons_cons_empty, image_pair]
  have hmapC : racl (↥F₀) ((gc.map σ).cb : Set K) =
      racl (↥F₀) ({σ w.C₁.rep, σ w.C₂.rep} : Set K) := by
    rw [← Germ.racl_codeTuple, Germ.racl_codeTuple_map, range_comp, racl_image_congr σ hC.symm,
      cTuple, Matrix.range_cons_cons_empty, image_pair]
  have hmapX : racl (↥F₀) (range ((ga.map σ).evalGen (⇑σ ∘ y'))) =
      racl (↥F₀) ({σ w.X.rep} : Set K) := by
    rw [Germ.evalGen_map σ ga hy hyA, range_comp, racl_image_congr σ hX.symm,
      show w.xTuple = fun _ ↦ w.X.rep from rfl,
      range_const, image_singleton]
  have hmapY : racl (↥F₀) (range (⇑σ ∘ y')) = racl (↥F₀) ({σ w.Y.rep} : Set K) := by
    rw [range_comp, racl_image_congr σ hY.symm,
      show w.yTuple = fun _ ↦ w.Y.rep from rfl, range_const, image_singleton]
  have hmapZ : racl (↥F₀) (range ((gb.map σ).evalGen (⇑σ ∘ y'))) =
      racl (↥F₀) ({σ w.Z.rep} : Set K) := by
    rw [Germ.evalGen_map σ gb hy hyB, range_comp, racl_image_congr σ hZ.symm,
      show w.zTuple = fun _ ↦ w.Z.rep from rfl,
      range_const, image_singleton]
  -- Freshness over `k`: `σ` fixes `E`, which is independent from the representatives.
  obtain ⟨σk, hσk⟩ : ∃ σk : K ≃ₐ[k] K, ⇑σk = ⇑σ := ⟨σ.restrictScalars k, rfl⟩
  have hσE : ⇑σ '' E = E := by
    have hfix : ∀ z ∈ E, σ z = z := fun z hz ↦ by
      have h : z ∈ F₀ := hF₀ ▸ subset_racl k E hz
      exact σ.commutes (⟨z, h⟩ : F₀)
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      rwa [hfix z' hz']
    · intro hz
      exact ⟨z, hz, hfix z hz⟩
  have h1 : IndepOver k ∅ (range (⇑σ ∘ w.repTuple)) E := by
    have h := hEind.image σk
    rw [image_empty, hσk, hσE, ← range_comp] at h
    exact h.symm
  have h2 : IndepOver k (∅ ∪ E) (range (⇑σ ∘ w.repTuple)) (M : Set K) := by
    have h := (indepOver_base_iff F₀ _ _).1 hσM
    exact (indepOver_congr_base (by rw [← hF₀, racl_racl, empty_union])).1 h
  have hfresh : IndepOver k ∅ (M : Set K) (range (⇑σ ∘ w.repTuple)) :=
    ((indepOver_union_right_iff.2 ⟨h1, h2⟩).mono_right subset_union_right).symm
  refine ⟨σk, M.restrictScalars k, ?_, a, b, c, d, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσk, IntermediateField.coe_restrictScalars]
    exact hfresh
  · rw [hσk, Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty]
    exact racl_restrictScalars_eq (r1.trans (racl_base_congr M hmapA)).symm
  · rw [hσk, Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty]
    exact racl_restrictScalars_eq (r2.trans (racl_base_congr M hmapB)).symm
  · rw [hσk, Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty]
    exact racl_restrictScalars_eq (r3.trans (racl_base_congr M hmapC)).symm
  · rw [hσk]
    exact racl_restrictScalars_eq r4.symm
  · rw [hσk]
    exact racl_restrictScalars_eq r5.symm
  · rw [hσk]
    exact racl_restrictScalars_eq r6.symm
  · rw [hσk]
    exact racl_restrictScalars_eq (r7.trans (racl_base_congr M hmapX)).symm
  · rw [hσk]
    exact racl_restrictScalars_eq (r8.trans (racl_base_congr M hmapY)).symm
  · rw [hσk]
    exact racl_restrictScalars_eq (r9.trans (racl_base_congr M hmapZ)).symm

end

end AclGeom.QWitness
