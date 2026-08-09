/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-potent endomorphisms and the Tate trace

An endomorphism of an arbitrary vector space is **finite-potent** if
some power has finite-dimensional range. Such an endomorphism has a
well-defined **trace**: the trace of its restriction to any *core* — a
finite-dimensional invariant subspace absorbing a power — with
independence of the core because the induced action beyond the absorbed
power is nilpotent. This is the linear algebra underlying Tate's
trace-theoretic construction of residues of differentials on curves
(Tate 1968), which the curve library consumes for the canonical-class
comparison.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6 via Tate residues).
-/

namespace AclGeom

open Module

noncomputable section

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- An endomorphism is **finite-potent** if some power has
finite-dimensional range. -/
def IsFinitePotent (θ : Module.End k V) : Prop :=
  ∃ n : ℕ, FiniteDimensional k (LinearMap.range (θ ^ n))

/-- A **core** for an endomorphism: a finite-dimensional invariant
subspace absorbing some power. The Tate trace is computed on any
core. -/
structure IsTateCore (θ : Module.End k V) (W : Submodule k V) :
    Prop where
  finite : FiniteDimensional k W
  stable : ∀ x ∈ W, θ x ∈ W
  absorbs : ∃ n : ℕ, ∀ x : V, (θ ^ n) x ∈ W

/-- Endomorphisms with finite-dimensional range are finite-potent. -/
theorem IsFinitePotent.of_finiteDimensional_range
    (θ : Module.End k V) [FiniteDimensional k (LinearMap.range θ)] :
    IsFinitePotent θ :=
  ⟨1, by rwa [pow_one]⟩

/-- Nilpotent endomorphisms are finite-potent. -/
theorem IsFinitePotent.of_isNilpotent {θ : Module.End k V}
    (h : IsNilpotent θ) : IsFinitePotent θ := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [hn, LinearMap.range_zero]
  infer_instance

/-- A finite-potent endomorphism has a core: the saturation
`θⁿV + θ(θⁿV) + ⋯` stabilizes — concretely, the span of the ranges of
all powers `≥ n` is already contained in the range of `θⁿ` summed with
finitely many images, and `θⁿV ⊔ θ^{n+1}V ⊔ ⋯` is finite-dimensional
and invariant. Here we take the invariant subspace generated inside
the finite-dimensional range. -/
theorem IsFinitePotent.exists_isTateCore {θ : Module.End k V}
    (h : IsFinitePotent θ) : ∃ W : Submodule k V, IsTateCore θ W := by
  obtain ⟨n, hn⟩ := h
  -- The image of the range of `θⁿ` under `θ` lies in the range of
  -- `θⁿ` composed once more; sum the finitely many iterates up to the
  -- dimension bound. Simplest invariant choice: the range of `θⁿ`
  -- together with all forward images, which stabilizes inside
  -- `range (θⁿ)` after one step since
  -- `θ (θⁿ x) = θⁿ (θ x) ∈ range (θⁿ)`.
  refine ⟨LinearMap.range (θ ^ n), ⟨hn, ?_, ⟨n, fun x ↦ ?_⟩⟩⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨θ y, ?_⟩
    have h1 : (θ ^ n) (θ y) = (θ ^ (n + 1)) y := by
      rw [pow_succ]
      rfl
    have h2 : θ ((θ ^ n) y) = (θ ^ (n + 1)) y := by
      rw [pow_succ']
      rfl
    rw [h1, h2]
  · exact ⟨x, rfl⟩

/-- Over a field, a nilpotent endomorphism of a finite-dimensional
space has trace zero. -/
theorem trace_eq_zero_of_isNilpotent {W : Type*} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {φ : Module.End k W}
    (h : IsNilpotent φ) : LinearMap.trace k W φ = 0 := by
  classical
  set b := Module.finBasis k W with hb
  have hmat : IsNilpotent (LinearMap.toMatrixAlgEquiv b φ) :=
    IsNilpotent.map h (LinearMap.toMatrixAlgEquiv b)
  have h0 : Matrix.trace (LinearMap.toMatrixAlgEquiv b φ) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hmat).eq_zero
  rw [LinearMap.trace_eq_matrix_trace k b φ]
  exact h0

/-- **Trace decomposes along an invariant subspace**: the trace of an
endomorphism of a finite-dimensional space is the trace of its
restriction to an invariant subspace plus the trace of the induced
quotient action — split by any complement, the cross blocks die by
`tr(AB) = tr(BA)`. -/
theorem trace_eq_trace_restrict_add_trace_mapQ {M : Type*}
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (φ : Module.End k M) {U : Submodule k M}
    (hU : ∀ x ∈ U, φ x ∈ U) :
    LinearMap.trace k M φ =
      LinearMap.trace k U (φ.restrict hU) +
        LinearMap.trace k (M ⧸ U) (U.mapQ U φ hU) := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  have h1 : φ = φ ∘ₗ U.projection C hC +
      φ ∘ₗ C.projection U hC.symm := by
    rw [← LinearMap.comp_add,
      Submodule.projection_add_projection_eq_id hC, LinearMap.comp_id]
  conv_lhs => rw [h1]
  rw [map_add]
  congr 1
  · -- The `U` block is the restriction.
    have h2 : φ ∘ₗ U.projection C hC =
        (φ ∘ₗ U.subtype) ∘ₗ U.projectionOnto C hC := rfl
    rw [h2, LinearMap.trace_comp_comm']
    congr 1
    refine LinearMap.ext fun x ↦ ?_
    apply Subtype.ext
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.restrict_apply, Submodule.subtype_apply,
      Submodule.projectionOnto_apply_of_mem_left hC
        (hU _ (SetLike.coe_mem x))]
  · -- The `C` block is the quotient action, conjugated.
    have h3 : φ ∘ₗ C.projection U hC.symm =
        (φ ∘ₗ C.subtype) ∘ₗ C.projectionOnto U hC.symm := rfl
    have h4 : LinearMap.trace k (M ⧸ U) (U.mapQ U φ hU) =
        LinearMap.trace k C
          ((U.quotientEquivOfIsCompl C hC).conj (U.mapQ U φ hU)) :=
      (LinearMap.trace_conj' _ _).symm
    rw [h3, LinearMap.trace_comp_comm', h4]
    congr 1

/-- The trace agrees on nested cores: the induced action on the
quotient is nilpotent. -/
theorem IsTateCore.trace_restrict_eq_of_le {θ : Module.End k V}
    {U W : Submodule k V} (hU : IsTateCore θ U) (hW : IsTateCore θ W)
    (hUW : U ≤ W) :
    haveI := hW.finite
    haveI := hU.finite
    LinearMap.trace k W (θ.restrict hW.stable) =
      LinearMap.trace k U (θ.restrict hU.stable) := by
  haveI := hW.finite
  haveI := hU.finite
  classical
  set ψ : Module.End k ↥W := θ.restrict hW.stable with hψ
  set U' : Submodule k ↥W := U.comap W.subtype with hU'
  have hstab : ∀ x ∈ U', ψ x ∈ U' := by
    intro x hx
    have h1 : (x : V) ∈ U := hx
    exact hU.stable _ h1
  -- The quotient action is nilpotent because a power lands in `U`.
  have hquot : IsNilpotent (U'.mapQ U' ψ hstab) := by
    obtain ⟨n, hn⟩ := hU.absorbs
    refine ⟨n, ?_⟩
    rw [← Submodule.mapQ_pow]
    refine LinearMap.ext fun q ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero]
    have h2 : ((ψ ^ n) y : V) = (θ ^ n) (y : V) := by
      rw [hψ, Module.End.pow_restrict]
      rfl
    change ((ψ ^ n) y : V) ∈ U
    rw [h2]
    exact hn _
  have hdecomp := trace_eq_trace_restrict_add_trace_mapQ ψ hstab
  rw [trace_eq_zero_of_isNilpotent hquot, add_zero] at hdecomp
  rw [hdecomp]
  -- Transport the restriction along `U' ≃ U`.
  have h6 : θ.restrict hU.stable =
      (Submodule.comapSubtypeEquivOfLe hUW).conj (ψ.restrict hstab) := by
    refine LinearMap.ext fun x ↦ ?_
    apply Subtype.ext
    rw [LinearEquiv.conj_apply, LinearMap.restrict_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    have h7 : (((Submodule.comapSubtypeEquivOfLe hUW)
        ((ψ.restrict hstab)
          ((Submodule.comapSubtypeEquivOfLe hUW).symm x)) : ↥U) : V) =
        (((ψ.restrict hstab)
          ((Submodule.comapSubtypeEquivOfLe hUW).symm x) : ↥W) : V) := by
      rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
    have h8 : (((ψ.restrict hstab)
        ((Submodule.comapSubtypeEquivOfLe hUW).symm x) : ↥W) : V) =
        θ ((((Submodule.comapSubtypeEquivOfLe hUW).symm x :
          ↥(U.comap W.subtype)) : ↥W) : V) := by
      rw [LinearMap.coe_restrict_apply, hψ, LinearMap.coe_restrict_apply]
    have h9 : ((((Submodule.comapSubtypeEquivOfLe hUW).symm x :
        ↥(U.comap W.subtype)) : ↥W) : V) = (x : V) := by
      have h10 : (((Submodule.comapSubtypeEquivOfLe hUW)
          ((Submodule.comapSubtypeEquivOfLe hUW).symm x) : ↥U) : V) =
          ((x : ↥U) : V) := by
        rw [LinearEquiv.apply_symm_apply]
      rw [Submodule.comapSubtypeEquivOfLe_apply_coe] at h10
      exact h10
    rw [h7, h8, h9]
  rw [h6, LinearMap.trace_conj']

/-- Cores are closed under joins. -/
theorem IsTateCore.sup {θ : Module.End k V} {W₁ W₂ : Submodule k V}
    (h₁ : IsTateCore θ W₁) (h₂ : IsTateCore θ W₂) :
    IsTateCore θ (W₁ ⊔ W₂) := by
  haveI := h₁.finite
  haveI := h₂.finite
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (h₁.stable a ha))
      (Submodule.mem_sup_right (h₂.stable b hb))
  · obtain ⟨n, hn⟩ := h₁.absorbs
    exact ⟨n, fun x ↦ Submodule.mem_sup_left (hn x)⟩

/-- The trace agrees on any two cores. -/
theorem IsTateCore.trace_restrict_eq {θ : Module.End k V}
    {W₁ W₂ : Submodule k V} (h₁ : IsTateCore θ W₁)
    (h₂ : IsTateCore θ W₂) :
    haveI := h₁.finite
    haveI := h₂.finite
    LinearMap.trace k W₁ (θ.restrict h₁.stable) =
      LinearMap.trace k W₂ (θ.restrict h₂.stable) := by
  have hsup := h₁.sup h₂
  have e₁ := hsup.trace_restrict_eq_of_le (hU := h₁) le_sup_left
  have e₂ := hsup.trace_restrict_eq_of_le (hU := h₂) le_sup_right
  haveI := h₁.finite
  haveI := h₂.finite
  haveI := hsup.finite
  rw [← e₁, ← e₂]

/-- **The Tate trace** of an endomorphism: the trace of its restriction
to any core, and `0` if there is none. -/
noncomputable def tateTrace (θ : Module.End k V) : k := by
  classical
  exact if h : ∃ W : Submodule k V, IsTateCore θ W then
    haveI := h.choose_spec.finite
    LinearMap.trace k h.choose (θ.restrict h.choose_spec.stable)
  else 0

/-- The Tate trace is computed on any core. -/
theorem IsTateCore.tateTrace_eq {θ : Module.End k V}
    {W : Submodule k V} (hW : IsTateCore θ W) :
    haveI := hW.finite
    tateTrace θ = LinearMap.trace k W (θ.restrict hW.stable) := by
  classical
  have hex : ∃ W : Submodule k V, IsTateCore θ W := ⟨W, hW⟩
  rw [tateTrace, dif_pos hex]
  exact hex.choose_spec.trace_restrict_eq hW

section FiniteRank

/-- The range of a finite-rank endomorphism is a core. -/
theorem isTateCore_range (θ : Module.End k V)
    [FiniteDimensional k (LinearMap.range θ)] :
    IsTateCore θ (LinearMap.range θ) :=
  ⟨inferInstance, fun x _ ↦ ⟨x, rfl⟩,
    ⟨1, fun x ↦ by rw [pow_one]; exact ⟨x, rfl⟩⟩⟩

/-- A finite-dimensional subspace containing the ranges of two
endomorphisms is a common core. -/
theorem isTateCore_of_range_le {θ : Module.End k V}
    {W : Submodule k V} [FiniteDimensional k W]
    (h : LinearMap.range θ ≤ W) : IsTateCore θ W :=
  ⟨inferInstance, fun x _ ↦ h ⟨x, rfl⟩,
    ⟨1, fun x ↦ by rw [pow_one]; exact h ⟨x, rfl⟩⟩⟩

/-- **Additivity of the Tate trace on finite-rank endomorphisms**: the
join of the ranges is a common core. -/
theorem tateTrace_add_of_finiteDimensional_range
    (θ₁ θ₂ : Module.End k V)
    [FiniteDimensional k (LinearMap.range θ₁)]
    [FiniteDimensional k (LinearMap.range θ₂)] :
    tateTrace (θ₁ + θ₂) = tateTrace θ₁ + tateTrace θ₂ := by
  set W : Submodule k V := LinearMap.range θ₁ ⊔ LinearMap.range θ₂
    with hW
  haveI : FiniteDimensional k W := by
    rw [hW]
    infer_instance
  have h₁ : IsTateCore θ₁ W := isTateCore_of_range_le le_sup_left
  have h₂ : IsTateCore θ₂ W := isTateCore_of_range_le le_sup_right
  have h₁₂ : IsTateCore (θ₁ + θ₂) W := by
    refine isTateCore_of_range_le ?_
    rintro x ⟨y, rfl⟩
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right ⟨y, rfl⟩)
  rw [h₁₂.tateTrace_eq, h₁.tateTrace_eq, h₂.tateTrace_eq]
  have hres : (θ₁ + θ₂).restrict h₁₂.stable =
      θ₁.restrict h₁.stable + θ₂.restrict h₂.stable := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  rw [hres, map_add]

/-- The Tate trace commutes with scalars. -/
theorem tateTrace_smul {θ : Module.End k V} {W : Submodule k V}
    (hW : IsTateCore θ W) (c : k) :
    tateTrace (c • θ) = c * tateTrace θ := by
  haveI := hW.finite
  have hW' : IsTateCore (c • θ) W :=
    ⟨hW.finite, fun x hx ↦ by
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (hW.stable x hx), by
      obtain ⟨n, hn⟩ := hW.absorbs
      refine ⟨n, fun x ↦ ?_⟩
      rw [smul_pow, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hn x)⟩
  rw [hW'.tateTrace_eq, hW.tateTrace_eq]
  have hres : (c • θ).restrict hW'.stable = c • θ.restrict hW.stable := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  rw [hres, map_smul, smul_eq_mul]

/-- **The trace of a product is symmetric** for finite-rank composites:
the restrictions to the two range-cores are intertwined compositions,
and `tr(ab) = tr(ba)` in finite dimensions. -/
theorem tateTrace_comp_comm (f g : Module.End k V)
    [FiniteDimensional k (LinearMap.range (f ∘ₗ g))]
    [FiniteDimensional k (LinearMap.range (g ∘ₗ f))] :
    tateTrace (f ∘ₗ g) = tateTrace (g ∘ₗ f) := by
  set U : Submodule k V := LinearMap.range (f ∘ₗ g) with hU
  set W : Submodule k V := LinearMap.range (g ∘ₗ f) with hW
  have hUcore : IsTateCore (f ∘ₗ g) U := isTateCore_range _
  have hWcore : IsTateCore (g ∘ₗ f) W := isTateCore_range _
  -- The intertwiners between the cores.
  have hga : ∀ x ∈ U, g x ∈ W := by
    rintro x ⟨y, rfl⟩
    exact ⟨g y, by rfl⟩
  have hfb : ∀ x ∈ W, f x ∈ U := by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, by rfl⟩
  set a : ↥U →ₗ[k] ↥W := g.restrict hga with ha
  set b : ↥W →ₗ[k] ↥U := f.restrict hfb with hb
  have hab : (f ∘ₗ g).restrict hUcore.stable = b ∘ₗ a := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  have hba : (g ∘ₗ f).restrict hWcore.stable = a ∘ₗ b := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  rw [hUcore.tateTrace_eq, hWcore.tateTrace_eq, hab, hba,
    LinearMap.trace_comp_comm']

/-- **Commutators of finite-rank composites are traceless.** -/
theorem tateTrace_comp_sub_comp_comm (f g : Module.End k V)
    [FiniteDimensional k (LinearMap.range (f ∘ₗ g))]
    [FiniteDimensional k (LinearMap.range (g ∘ₗ f))] :
    tateTrace (f ∘ₗ g - g ∘ₗ f) = 0 := by
  have h1 : f ∘ₗ g - g ∘ₗ f = f ∘ₗ g + (-1 : k) • (g ∘ₗ f) := by
    rw [neg_one_smul]
    abel
  haveI : FiniteDimensional k
      (LinearMap.range ((-1 : k) • (g ∘ₗ f))) := by
    have h2 : LinearMap.range ((-1 : k) • (g ∘ₗ f)) ≤
        LinearMap.range (g ∘ₗ f) := by
      rintro x ⟨y, rfl⟩
      exact ⟨(-1 : k) • y, by rw [LinearMap.smul_apply, map_smul]⟩
    exact Submodule.finiteDimensional_of_le h2
  rw [h1, tateTrace_add_of_finiteDimensional_range,
    tateTrace_smul (isTateCore_range _), tateTrace_comp_comm f g]
  ring

end FiniteRank

end

end AclGeom
