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
  /-- A core is finite-dimensional. -/
  finite : FiniteDimensional k W
  /-- A core is invariant under the endomorphism. -/
  stable : ∀ x ∈ W, θ x ∈ W
  /-- A core absorbs some power of the endomorphism. -/
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

/-- The Tate trace of the zero operator vanishes. -/
theorem tateTrace_zero : tateTrace (0 : Module.End k V) = 0 := by
  have hcore : IsTateCore (0 : Module.End k V) (⊥ : Submodule k V) :=
    ⟨inferInstance, fun x _ ↦ by
      rw [LinearMap.zero_apply]
      exact Submodule.zero_mem _,
      ⟨1, fun x ↦ by
        rw [pow_one, LinearMap.zero_apply]
        exact Submodule.zero_mem _⟩⟩
  rw [hcore.tateTrace_eq]
  have h1 : (0 : Module.End k V).restrict hcore.stable = 0 :=
    LinearMap.ext fun x ↦ Subtype.ext rfl
  rw [h1, map_zero]

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

/-- The range of any power is a core once it is finite-dimensional. -/
theorem isTateCore_range_pow (θ : Module.End k V) (n : ℕ)
    [FiniteDimensional k (LinearMap.range (θ ^ n))] :
    IsTateCore θ (LinearMap.range (θ ^ n)) := by
  refine ⟨inferInstance, ?_, ⟨n, fun x ↦ ⟨x, rfl⟩⟩⟩
  rintro x ⟨y, rfl⟩
  refine ⟨θ y, ?_⟩
  have h1 : (θ ^ n) (θ y) = (θ ^ (n + 1)) y := by
    rw [pow_succ]
    rfl
  have h2 : θ ((θ ^ n) y) = (θ ^ (n + 1)) y := by
    rw [pow_succ']
    rfl
  rw [h1, h2]

/-- **Symmetry of the trace of a product**, squared-range version: if
`(αβ)²` and `(βα)²` have finite-dimensional range — as happens for
Tate's trace-class operators — then `tr(αβ) = tr(βα)`: the squared
ranges are cores intertwined by the restricted factors. -/
theorem tateTrace_comp_comm_of_sq (α β : Module.End k V)
    [FiniteDimensional k (LinearMap.range ((α ∘ₗ β) ^ 2))]
    [FiniteDimensional k (LinearMap.range ((β ∘ₗ α) ^ 2))] :
    tateTrace (α ∘ₗ β) = tateTrace (β ∘ₗ α) := by
  have hUcore : IsTateCore (α ∘ₗ β) (LinearMap.range ((α ∘ₗ β) ^ 2)) :=
    isTateCore_range_pow (α ∘ₗ β) 2
  have hWcore : IsTateCore (β ∘ₗ α) (LinearMap.range ((β ∘ₗ α) ^ 2)) :=
    isTateCore_range_pow (β ∘ₗ α) 2
  have hβu : β ∘ₗ ((α ∘ₗ β) ^ 2 : Module.End k V) =
      ((β ∘ₗ α) ^ 2 : Module.End k V) ∘ₗ β := by
    rw [pow_two, pow_two]
    ext x
    rfl
  have hαv : α ∘ₗ ((β ∘ₗ α) ^ 2 : Module.End k V) =
      ((α ∘ₗ β) ^ 2 : Module.End k V) ∘ₗ α := by
    rw [pow_two, pow_two]
    ext x
    rfl
  have hga : ∀ x ∈ LinearMap.range ((α ∘ₗ β) ^ 2),
      β x ∈ LinearMap.range ((β ∘ₗ α) ^ 2) := by
    rintro x ⟨y, rfl⟩
    exact ⟨β y, (LinearMap.congr_fun hβu y).symm⟩
  have hfb : ∀ x ∈ LinearMap.range ((β ∘ₗ α) ^ 2),
      α x ∈ LinearMap.range ((α ∘ₗ β) ^ 2) := by
    rintro x ⟨y, rfl⟩
    exact ⟨α y, (LinearMap.congr_fun hαv y).symm⟩
  have hab : (α ∘ₗ β).restrict hUcore.stable =
      α.restrict hfb ∘ₗ β.restrict hga := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  have hba : (β ∘ₗ α).restrict hWcore.stable =
      β.restrict hga ∘ₗ α.restrict hfb := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  rw [hUcore.tateTrace_eq, hWcore.tateTrace_eq, hab, hba,
    LinearMap.trace_comp_comm']

/-- **Additivity of the Tate trace over a potent pair**: if all four
length-two words in `φ, ψ` have finite-dimensional range, the join of
those ranges is a common core — length-three word images fold back
into length-two ranges. -/
theorem tateTrace_add_of_sq (φ ψ : Module.End k V)
    [FiniteDimensional k (LinearMap.range (φ ∘ₗ φ))]
    [FiniteDimensional k (LinearMap.range (φ ∘ₗ ψ))]
    [FiniteDimensional k (LinearMap.range (ψ ∘ₗ φ))]
    [FiniteDimensional k (LinearMap.range (ψ ∘ₗ ψ))] :
    tateTrace (φ + ψ) = tateTrace φ + tateTrace ψ := by
  set W : Submodule k V :=
    LinearMap.range (φ ∘ₗ φ) ⊔ (LinearMap.range (φ ∘ₗ ψ) ⊔
      (LinearMap.range (ψ ∘ₗ φ) ⊔ LinearMap.range (ψ ∘ₗ ψ))) with hW
  haveI : FiniteDimensional k W := by
    rw [hW]
    infer_instance
  have h1 : LinearMap.range (φ ∘ₗ φ) ≤ W := le_sup_left
  have h2 : LinearMap.range (φ ∘ₗ ψ) ≤ W :=
    le_sup_left.trans le_sup_right
  have h3 : LinearMap.range (ψ ∘ₗ φ) ≤ W :=
    (le_sup_left.trans le_sup_right).trans le_sup_right
  have h4 : LinearMap.range (ψ ∘ₗ ψ) ≤ W :=
    (le_sup_right.trans le_sup_right).trans le_sup_right
  -- Left-composition folds length-three words into length-two ranges.
  have hfold : ∀ χ : Module.End k V,
      LinearMap.range (χ ∘ₗ φ) ≤ W → LinearMap.range (χ ∘ₗ ψ) ≤ W →
      ∀ x ∈ W, χ x ∈ W := by
    intro χ hχφ hχψ x hx
    have hmap : Submodule.map χ W ≤ W := by
      rw [hW, Submodule.map_sup, Submodule.map_sup, Submodule.map_sup,
        ← LinearMap.range_comp, ← LinearMap.range_comp,
        ← LinearMap.range_comp, ← LinearMap.range_comp]
      have hb : ∀ ξ ζ : Module.End k V, LinearMap.range (χ ∘ₗ ξ) ≤ W →
          LinearMap.range (χ ∘ₗ (ξ ∘ₗ ζ)) ≤ W := by
        intro ξ ζ hξ
        have hassoc : χ ∘ₗ (ξ ∘ₗ ζ) = (χ ∘ₗ ξ) ∘ₗ ζ := rfl
        rw [hassoc]
        exact (LinearMap.range_comp_le_range _ _).trans hξ
      exact sup_le (hb φ φ hχφ) (sup_le (hb φ ψ hχφ)
        (sup_le (hb ψ φ hχψ) (hb ψ ψ hχψ)))
    exact hmap ⟨x, hx, rfl⟩
  have hstepφ : ∀ x ∈ W, φ x ∈ W := hfold φ h1 h2
  have hstepψ : ∀ x ∈ W, ψ x ∈ W := hfold ψ h3 h4
  have hφ : IsTateCore φ W := by
    refine ⟨inferInstance, hstepφ, ⟨2, fun x ↦ h1 ?_⟩⟩
    exact ⟨x, by rw [pow_two]; rfl⟩
  have hψ : IsTateCore ψ W := by
    refine ⟨inferInstance, hstepψ, ⟨2, fun x ↦ h4 ?_⟩⟩
    exact ⟨x, by rw [pow_two]; rfl⟩
  have hsum : IsTateCore (φ + ψ) W := by
    refine ⟨inferInstance, fun x hx ↦ ?_, ⟨2, fun x ↦ ?_⟩⟩
    · rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (hstepφ x hx) (hstepψ x hx)
    · have hexp : ((φ + ψ) ^ 2) x =
          (φ ∘ₗ φ) x + (φ ∘ₗ ψ) x + ((ψ ∘ₗ φ) x + (ψ ∘ₗ ψ) x) := by
        rw [pow_two]
        change (φ + ψ) ((φ + ψ) x) = _
        rw [LinearMap.add_apply, LinearMap.add_apply, map_add,
          map_add]
        rfl
      rw [hexp]
      exact Submodule.add_mem _
        (Submodule.add_mem _ (h1 ⟨x, rfl⟩) (h2 ⟨x, rfl⟩))
        (Submodule.add_mem _ (h3 ⟨x, rfl⟩) (h4 ⟨x, rfl⟩))
  rw [hsum.tateTrace_eq, hφ.tateTrace_eq, hψ.tateTrace_eq]
  have hres : (φ + ψ).restrict hsum.stable =
      φ.restrict hφ.stable + ψ.restrict hψ.stable := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rfl
  rw [hres, map_add]

/-- Tate's relation `A ≺ B`: contained in `B` up to finite
dimensions. -/
def AlmostLE (A B : Submodule k V) : Prop :=
  ∃ W : Submodule k V, FiniteDimensional k W ∧ A ≤ B ⊔ W

theorem AlmostLE.of_le {A B : Submodule k V} (h : A ≤ B) :
    AlmostLE A B :=
  ⟨⊥, inferInstance, by rwa [sup_bot_eq]⟩

theorem AlmostLE.rfl {A : Submodule k V} : AlmostLE A A :=
  AlmostLE.of_le le_rfl

theorem AlmostLE.trans {A B C : Submodule k V} (h₁ : AlmostLE A B)
    (h₂ : AlmostLE B C) : AlmostLE A C := by
  obtain ⟨W₁, hW₁, hle₁⟩ := h₁
  obtain ⟨W₂, hW₂, hle₂⟩ := h₂
  refine ⟨W₂ ⊔ W₁, inferInstance, ?_⟩
  refine hle₁.trans (sup_le ?_ ?_)
  · exact hle₂.trans (sup_le le_sup_left
      ((le_sup_left : W₂ ≤ W₂ ⊔ W₁).trans le_sup_right))
  · exact (le_sup_right : W₁ ≤ W₂ ⊔ W₁).trans le_sup_right

theorem AlmostLE.mono_right {A B C : Submodule k V}
    (h : AlmostLE A B) (hBC : B ≤ C) : AlmostLE A C :=
  h.trans (AlmostLE.of_le hBC)

theorem AlmostLE.mono_left {A B C : Submodule k V} (hAB : A ≤ B)
    (h : AlmostLE B C) : AlmostLE A C :=
  (AlmostLE.of_le hAB).trans h

theorem AlmostLE.sup {A B C : Submodule k V} (h₁ : AlmostLE A C)
    (h₂ : AlmostLE B C) : AlmostLE (A ⊔ B) C := by
  obtain ⟨W₁, hW₁, hle₁⟩ := h₁
  obtain ⟨W₂, hW₂, hle₂⟩ := h₂
  refine ⟨W₁ ⊔ W₂, inferInstance, sup_le ?_ ?_⟩
  · exact hle₁.trans (sup_le le_sup_left
      ((le_sup_left : W₁ ≤ W₁ ⊔ W₂).trans le_sup_right))
  · exact hle₂.trans (sup_le le_sup_left
      ((le_sup_right : W₂ ≤ W₁ ⊔ W₂).trans le_sup_right))

theorem AlmostLE.of_finiteDimensional {A B : Submodule k V}
    [FiniteDimensional k A] : AlmostLE A B :=
  ⟨A, inferInstance, le_sup_right⟩

section TraceClass

/-- **Tate's trace class `E₀`** relative to a subspace `A`: the range
is almost inside `A`, and the image of `A` is finite-dimensional. -/
structure IsTraceClass (A : Submodule k V) (T : Module.End k V) :
    Prop where
  /-- The range is almost inside the reference subspace. -/
  range_almostLE : AlmostLE (LinearMap.range T) A
  /-- The image of the reference subspace is finite-dimensional. -/
  finite_map : FiniteDimensional k (A.map T)

theorem IsTraceClass.zero (A : Submodule k V) :
    IsTraceClass A (0 : Module.End k V) := by
  constructor
  · rw [LinearMap.range_zero]
    exact AlmostLE.of_le bot_le
  · have h1 : A.map (0 : Module.End k V) ≤ ⊥ := by
      rintro x ⟨y, -, rfl⟩
      simp
    haveI : FiniteDimensional k (⊥ : Submodule k V) := inferInstance
    exact Submodule.finiteDimensional_of_le h1

/-- Products of two trace-class operators have finite-dimensional
range. -/
theorem IsTraceClass.finiteDimensional_range_comp
    {A : Submodule k V} {T S : Module.End k V}
    (hT : IsTraceClass A T) (hS : IsTraceClass A S) :
    FiniteDimensional k (LinearMap.range (T ∘ₗ S)) := by
  obtain ⟨W, hW, hle⟩ := hS.range_almostLE
  haveI := hW
  haveI := hT.finite_map
  have h1 : LinearMap.range (T ∘ₗ S) ≤ A.map T ⊔ W.map T := by
    rw [LinearMap.range_comp]
    refine (Submodule.map_mono hle).trans ?_
    rw [Submodule.map_sup]
  exact Submodule.finiteDimensional_of_le h1

/-- The trace class is closed under addition. -/
theorem IsTraceClass.add {A : Submodule k V} {T S : Module.End k V}
    (hT : IsTraceClass A T) (hS : IsTraceClass A S) :
    IsTraceClass A (T + S) := by
  constructor
  · refine AlmostLE.mono_left ?_
      (AlmostLE.sup hT.range_almostLE hS.range_almostLE)
    rintro x ⟨y, rfl⟩
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right ⟨y, rfl⟩)
  · haveI := hT.finite_map
    haveI := hS.finite_map
    have h1 : A.map (T + S) ≤ A.map T ⊔ A.map S := by
      rintro x ⟨y, hy, rfl⟩
      exact Submodule.add_mem _
        (Submodule.mem_sup_left ⟨y, hy, rfl⟩)
        (Submodule.mem_sup_right ⟨y, hy, rfl⟩)
    exact Submodule.finiteDimensional_of_le h1

/-- The trace class is closed under negation. -/
theorem IsTraceClass.neg {A : Submodule k V} {T : Module.End k V}
    (hT : IsTraceClass A T) : IsTraceClass A (-T) := by
  constructor
  · refine AlmostLE.mono_left ?_ hT.range_almostLE
    rintro x ⟨y, rfl⟩
    exact ⟨-y, by simp⟩
  · haveI := hT.finite_map
    have h1 : A.map (-T) ≤ A.map T := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨-y, Submodule.neg_mem _ hy, by simp⟩
    exact Submodule.finiteDimensional_of_le h1

theorem IsTraceClass.sub {A : Submodule k V} {T S : Module.End k V}
    (hT : IsTraceClass A T) (hS : IsTraceClass A S) :
    IsTraceClass A (T - S) := by
  rw [sub_eq_add_neg]
  exact hT.add hS.neg

/-- The trace class absorbs left composition with operators respecting
the commensurability class. -/
theorem IsTraceClass.comp_left {A : Submodule k V}
    {T g : Module.End k V} (hT : IsTraceClass A T)
    (hg : AlmostLE (A.map g) A) : IsTraceClass A (g ∘ₗ T) := by
  obtain ⟨W, hW, hle⟩ := hT.range_almostLE
  haveI := hW
  constructor
  · have h1 : LinearMap.range (g ∘ₗ T) ≤ A.map g ⊔ W.map g := by
      rw [LinearMap.range_comp]
      refine (Submodule.map_mono hle).trans ?_
      rw [Submodule.map_sup]
    refine AlmostLE.mono_left h1 (AlmostLE.sup hg ?_)
    exact AlmostLE.of_finiteDimensional
  · haveI := hT.finite_map
    have h2 : A.map (g ∘ₗ T) = (A.map T).map g := by
      rw [Submodule.map_comp]
    rw [h2]
    infer_instance

/-- The trace class absorbs right composition with any operator whose
image of `A` is almost inside `A`. -/
theorem IsTraceClass.comp_right {A : Submodule k V}
    {T g : Module.End k V} (hT : IsTraceClass A T)
    (hg : AlmostLE (A.map g) A) : IsTraceClass A (T ∘ₗ g) := by
  constructor
  · exact AlmostLE.mono_left (LinearMap.range_comp_le_range _ _)
      hT.range_almostLE
  · obtain ⟨W, hW, hle⟩ := hg
    haveI := hW
    haveI := hT.finite_map
    have h1 : A.map (T ∘ₗ g) ≤ A.map T ⊔ W.map T := by
      rw [Submodule.map_comp]
      refine (Submodule.map_mono hle).trans ?_
      rw [Submodule.map_sup]
    exact Submodule.finiteDimensional_of_le h1

/-- Trace-class operators are finite-potent: their square has
finite-dimensional range. -/
theorem IsTraceClass.isFinitePotent {A : Submodule k V}
    {T : Module.End k V} (hT : IsTraceClass A T) :
    IsFinitePotent T := by
  refine ⟨2, ?_⟩
  have h1 : (T ^ 2 : Module.End k V) = T ∘ₗ T := by
    rw [pow_two]
    rfl
  rw [h1]
  exact hT.finiteDimensional_range_comp hT

/-- **The Tate trace of a finite-rank idempotent is its rank** (cast
into the field). -/
theorem tateTrace_of_isIdempotentElem {ρ : Module.End k V}
    (hρ : IsIdempotentElem ρ)
    [FiniteDimensional k (LinearMap.range ρ)] :
    tateTrace ρ = (Module.finrank k (LinearMap.range ρ) : k) := by
  have hcore : IsTateCore ρ (LinearMap.range ρ) := isTateCore_range ρ
  rw [hcore.tateTrace_eq]
  have hid : ρ.restrict hcore.stable = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change ρ (x : V) = (x : V)
    rw [← hy, ← Module.End.mul_apply, hρ]
  rw [hid]
  exact LinearMap.trace_id k _

end TraceClass

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

/-- Cores are stable under all powers. -/
theorem IsTateCore.pow_stable {θ : Module.End k V} {W : Submodule k V}
    (hW : IsTateCore θ W) (j : ℕ) :
    ∀ w ∈ W, (θ ^ j) w ∈ W := by
  induction j with
  | zero =>
    intro w hw
    rw [pow_zero]
    exact hw
  | succ j ih =>
    intro w hw
    have h1 : (θ ^ (j + 1)) w = θ ((θ ^ j) w) := by
      rw [pow_succ']
      rfl
    rw [h1]
    exact hW.stable _ (ih w hw)

/-- A core absorbing at exponent `n` absorbs at every larger
exponent. -/
theorem IsTateCore.pow_mem_of_le {θ : Module.End k V}
    {W : Submodule k V} (hW : IsTateCore θ W) {n : ℕ}
    (hn : ∀ x : V, (θ ^ n) x ∈ W) {m : ℕ} (hm : n ≤ m) :
    ∀ x : V, (θ ^ m) x ∈ W := by
  intro x
  have h1 : (θ ^ m) x = (θ ^ (m - n)) ((θ ^ n) x) := by
    rw [← Module.End.mul_apply, ← pow_add]
    congr 2
    omega
  rw [h1]
  exact hW.pow_stable (m - n) _ (hn x)

/-- Square-zero operators have vanishing higher powers. -/
theorem pow_eq_zero_of_comp_self_eq_zero {θ : Module.End k V}
    (hθ : θ ∘ₗ θ = 0) {n : ℕ} (hn : 2 ≤ n) :
    (θ ^ n : Module.End k V) = 0 := by
  have h2 : (θ ^ 2 : Module.End k V) = 0 := by
    have h1 : (θ ^ 2 : Module.End k V) = θ ∘ₗ θ := by
      rw [pow_two]
      rfl
    rw [h1, hθ]
  calc (θ ^ n : Module.End k V) = θ ^ (n - 2) * θ ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
    _ = 0 := by rw [h2, mul_zero]

/-- The Tate trace of a nilpotent operator vanishes: the bottom
submodule is a core. -/
theorem tateTrace_of_isNilpotent {θ : Module.End k V}
    (h : IsNilpotent θ) : tateTrace θ = 0 := by
  obtain ⟨n, hn⟩ := h
  have hcore : IsTateCore θ (⊥ : Submodule k V) :=
    ⟨inferInstance, fun x hx ↦ by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _,
      ⟨n, fun x ↦ by
        rw [hn, LinearMap.zero_apply]
        exact Submodule.zero_mem _⟩⟩
  rw [hcore.tateTrace_eq]
  have h1 : θ.restrict hcore.stable = 0 := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    have hx0 : (x : V) = 0 := (Submodule.mem_bot k).1 x.2
    change θ (x : V) = 0
    rw [hx0, map_zero]
  rw [h1, map_zero]

/-- **Traceless commutators, squared-range version**: when the squares
and the mixed products of `α ∘ β` and `β ∘ α` have finite-dimensional
range — as happens when both composites are trace-class — the
commutator is traceless. -/
theorem tateTrace_comp_sub_comp_comm_of_sq (α β : Module.End k V)
    [FiniteDimensional k (LinearMap.range ((α ∘ₗ β) ^ 2))]
    [FiniteDimensional k (LinearMap.range ((β ∘ₗ α) ^ 2))]
    [FiniteDimensional k (LinearMap.range ((α ∘ₗ β) ∘ₗ (β ∘ₗ α)))]
    [FiniteDimensional k (LinearMap.range ((β ∘ₗ α) ∘ₗ (α ∘ₗ β)))] :
    tateTrace (α ∘ₗ β - β ∘ₗ α) = 0 := by
  haveI hXX : FiniteDimensional k
      (LinearMap.range ((α ∘ₗ β) ∘ₗ (α ∘ₗ β))) := by
    have h5 : (α ∘ₗ β) ∘ₗ (α ∘ₗ β) =
        ((α ∘ₗ β) ^ 2 : Module.End k V) := by
      rw [pow_two]
      rfl
    rw [h5]
    infer_instance
  haveI hYY : FiniteDimensional k
      (LinearMap.range ((β ∘ₗ α) ∘ₗ (β ∘ₗ α))) := by
    have h5 : (β ∘ₗ α) ∘ₗ (β ∘ₗ α) =
        ((β ∘ₗ α) ^ 2 : Module.End k V) := by
      rw [pow_two]
      rfl
    rw [h5]
    infer_instance
  haveI hXnY : FiniteDimensional k
      (LinearMap.range ((α ∘ₗ β) ∘ₗ (-(β ∘ₗ α)))) := by
    rw [LinearMap.comp_neg, LinearMap.range_neg]
    infer_instance
  haveI hnYX : FiniteDimensional k
      (LinearMap.range ((-(β ∘ₗ α)) ∘ₗ (α ∘ₗ β))) := by
    rw [LinearMap.neg_comp, LinearMap.range_neg]
    infer_instance
  haveI hnYnY : FiniteDimensional k
      (LinearMap.range ((-(β ∘ₗ α)) ∘ₗ (-(β ∘ₗ α)))) := by
    rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
    exact hYY
  have hadd := tateTrace_add_of_sq (α ∘ₗ β) (-(β ∘ₗ α))
  have hflip := tateTrace_comp_comm_of_sq α β
  have hneg : tateTrace (-(β ∘ₗ α)) = -tateTrace (β ∘ₗ α) := by
    have h5 : (-(β ∘ₗ α) : Module.End k V) = (-1 : k) • (β ∘ₗ α) := by
      rw [neg_one_smul]
    rw [h5, tateTrace_smul (isTateCore_range_pow (β ∘ₗ α) 2),
      neg_one_mul]
  have hsub : α ∘ₗ β - β ∘ₗ α = α ∘ₗ β + (-(β ∘ₗ α)) :=
    sub_eq_add_neg _ _
  rw [hsub, hadd, hflip, hneg]
  ring

/-- **Compatible projections for a spanning pair**: two subspaces that
together span the module admit projections onto each whose sum is the
identity plus an operator into the intersection — project onto each
along a complement of the intersection inside the other. -/
theorem exists_projection_pair {A B : Submodule k V}
    (hsup : A ⊔ B = ⊤) :
    ∃ εA εB : Module.End k V,
      (∀ x : V, εA x ∈ A) ∧ (∀ x ∈ A, εA x = x) ∧
      (∀ x : V, εB x ∈ B) ∧ (∀ x ∈ B, εB x = x) ∧
      (∀ x : V, εA x + εB x - x ∈ A ⊓ B) := by
  classical
  obtain ⟨C₁', hC₁'⟩ :=
    Submodule.exists_isCompl ((A ⊓ B).comap B.subtype)
  obtain ⟨C₂', hC₂'⟩ :=
    Submodule.exists_isCompl ((A ⊓ B).comap A.subtype)
  set C₁ : Submodule k V := C₁'.map B.subtype with hC₁def
  set C₂ : Submodule k V := C₂'.map A.subtype with hC₂def
  have hC₁B : C₁ ≤ B := Submodule.map_subtype_le _ _
  have hC₂A : C₂ ≤ A := Submodule.map_subtype_le _ _
  have hsup₁ : (A ⊓ B) ⊔ C₁ = B := by
    have h1 := congrArg (Submodule.map B.subtype) hC₁'.sup_eq_top
    rw [Submodule.map_sup, Submodule.map_comap_subtype,
      Submodule.map_subtype_top,
      inf_eq_right.2 (inf_le_right : A ⊓ B ≤ B)] at h1
    exact h1
  have hsup₂ : (A ⊓ B) ⊔ C₂ = A := by
    have h1 := congrArg (Submodule.map A.subtype) hC₂'.sup_eq_top
    rw [Submodule.map_sup, Submodule.map_comap_subtype,
      Submodule.map_subtype_top,
      inf_eq_right.2 (inf_le_left : A ⊓ B ≤ A)] at h1
    exact h1
  have hinf₁ : (A ⊓ B) ⊓ C₁ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxAB, hxC₁⟩
    obtain ⟨c, hc, rfl⟩ := hxC₁
    have h2 : c ∈ (A ⊓ B).comap B.subtype ⊓ C₁' := ⟨hxAB, hc⟩
    rw [hC₁'.inf_eq_bot] at h2
    rw [Submodule.mem_bot] at h2 ⊢
    rw [h2]
    exact map_zero _
  have hinf₂ : (A ⊓ B) ⊓ C₂ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxAB, hxC₂⟩
    obtain ⟨c, hc, rfl⟩ := hxC₂
    have h2 : c ∈ (A ⊓ B).comap A.subtype ⊓ C₂' := ⟨hxAB, hc⟩
    rw [hC₂'.inf_eq_bot] at h2
    rw [Submodule.mem_bot] at h2 ⊢
    rw [h2]
    exact map_zero _
  have hcomplA : IsCompl A C₁ := by
    refine IsCompl.of_eq ?_ ?_
    · refine le_antisymm ?_ bot_le
      have h1 : A ⊓ C₁ ≤ (A ⊓ B) ⊓ C₁ :=
        le_inf (le_inf inf_le_left (inf_le_right.trans hC₁B))
          inf_le_right
      rw [hinf₁] at h1
      exact h1
    · rw [← hsup]
      conv_rhs => rw [← hsup₁, ← sup_assoc, sup_inf_self]
  have hcomplB : IsCompl B C₂ := by
    refine IsCompl.of_eq ?_ ?_
    · refine le_antisymm ?_ bot_le
      have h1 : B ⊓ C₂ ≤ (A ⊓ B) ⊓ C₂ :=
        le_inf (le_inf (inf_le_right.trans hC₂A) inf_le_left)
          inf_le_right
      rw [hinf₂] at h1
      exact h1
    · rw [← hsup, sup_comm A B]
      conv_rhs => rw [← hsup₂, ← sup_assoc, inf_comm A B,
        sup_inf_self]
  refine ⟨A.projection C₁ hcomplA, B.projection C₂ hcomplB,
    fun x ↦ Submodule.projection_apply_mem hcomplA x,
    fun x hx ↦ ?_, fun x ↦ Submodule.projection_apply_mem hcomplB x,
    fun x hx ↦ ?_, fun x ↦ ?_⟩
  · exact Submodule.projection_apply_left hcomplA ⟨x, hx⟩
  · exact Submodule.projection_apply_left hcomplB ⟨x, hx⟩
  · have h1 : x - A.projection C₁ hcomplA x ∈ C₁ := by
      have h2 := LinearMap.congr_fun
        (Submodule.projection_add_projection_eq_id hcomplA) x
      rw [LinearMap.add_apply, LinearMap.id_apply] at h2
      have h3 : x - A.projection C₁ hcomplA x =
          C₁.projection A hcomplA.symm x :=
        sub_eq_of_eq_add' h2.symm
      rw [h3]
      exact Submodule.projection_apply_mem hcomplA.symm x
    have h4 : x - B.projection C₂ hcomplB x ∈ C₂ := by
      have h2 := LinearMap.congr_fun
        (Submodule.projection_add_projection_eq_id hcomplB) x
      rw [LinearMap.add_apply, LinearMap.id_apply] at h2
      have h3 : x - B.projection C₂ hcomplB x =
          C₂.projection B hcomplB.symm x :=
        sub_eq_of_eq_add' h2.symm
      rw [h3]
      exact Submodule.projection_apply_mem hcomplB.symm x
    refine ⟨?_, ?_⟩
    · have h5 : A.projection C₁ hcomplA x + B.projection C₂ hcomplB x -
          x = A.projection C₁ hcomplA x -
            (x - B.projection C₂ hcomplB x) := by
        abel
      rw [h5]
      exact Submodule.sub_mem _
        (Submodule.projection_apply_mem hcomplA x) (hC₂A h4)
    · have h5 : A.projection C₁ hcomplA x + B.projection C₂ hcomplB x -
          x = B.projection C₂ hcomplB x -
            (x - A.projection C₁ hcomplA x) := by
        abel
      rw [h5]
      exact Submodule.sub_mem _
        (Submodule.projection_apply_mem hcomplB x) (hC₁B h1)

/-- Almost-stability propagates from generators to the whole monoid
of words. -/
theorem almostLE_map_closure_of {A : Submodule k V}
    {s : Set (Module.End k V)}
    (hs : ∀ w ∈ s, AlmostLE (A.map w) A) :
    ∀ w ∈ Submonoid.closure s, AlmostLE (A.map w) A := by
  intro w hw
  induction hw using Submonoid.closure_induction with
  | mem x hx => exact hs x hx
  | one =>
    have h1 : (1 : Module.End k V) = LinearMap.id := rfl
    rw [h1, Submodule.map_id]
    exact AlmostLE.rfl
  | mul x y hx hy ihx ihy =>
    have h1 : A.map (x * y) = (A.map y).map x := by
      rw [← Submodule.map_comp]
      rfl
    rw [h1]
    obtain ⟨W, hW, hle⟩ := ihy
    haveI := hW
    have h2 : (A.map y).map x ≤ A.map x ⊔ W.map x := by
      refine (Submodule.map_mono hle).trans ?_
      rw [Submodule.map_sup]
    exact AlmostLE.mono_left h2
      (AlmostLE.sup ihx AlmostLE.of_finiteDimensional)

/-- A projection commutator against an almost-stabilizing operator is
trace-class: the range decomposes over the projection target and the
image, and on the target the commutator factors through `ε − 1`, which
kills the target. -/
theorem isTraceClass_proj_commutator {A : Submodule k V}
    {ε χ : Module.End k V} (hχ : AlmostLE (A.map χ) A)
    (hεr : ∀ x : V, ε x ∈ A) (hεf : ∀ x ∈ A, ε x = x) :
    IsTraceClass A (ε ∘ₗ χ - χ ∘ₗ ε) := by
  constructor
  · have hle : LinearMap.range (ε ∘ₗ χ - χ ∘ₗ ε) ≤ A ⊔ A.map χ := by
      rintro x ⟨y, rfl⟩
      have h1 : (ε ∘ₗ χ - χ ∘ₗ ε) y = ε (χ y) - χ (ε y) := rfl
      rw [h1, sub_eq_add_neg]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hεr _))
        (Submodule.neg_mem _ (Submodule.mem_sup_right
          ⟨ε y, hεr y, rfl⟩))
    exact AlmostLE.mono_left hle (AlmostLE.sup AlmostLE.rfl hχ)
  · obtain ⟨W, hW, hle⟩ := hχ
    haveI := hW
    have h1 : A.map (ε ∘ₗ χ - χ ∘ₗ ε) ≤
        W.map (ε - LinearMap.id : Module.End k V) := by
      rintro x ⟨a, ha, rfl⟩
      have h2 : (ε ∘ₗ χ - χ ∘ₗ ε) a =
          (ε - LinearMap.id : Module.End k V) (χ a) := by
        have h3 : (ε ∘ₗ χ - χ ∘ₗ ε) a = ε (χ a) - χ a := by
          have h4 : χ (ε a) = χ a := by rw [hεf a ha]
          calc (ε ∘ₗ χ - χ ∘ₗ ε) a = ε (χ a) - χ (ε a) := rfl
            _ = ε (χ a) - χ a := by rw [h4]
        rw [h3]
        rfl
      rw [h2]
      obtain ⟨u, hu, w, hw, huw⟩ :=
        Submodule.mem_sup.1 (hle ⟨a, ha, rfl⟩)
      have h5 : (ε - LinearMap.id : Module.End k V) (χ a) =
          (ε - LinearMap.id : Module.End k V) w := by
        rw [← huw, map_add]
        have h6 : (ε - LinearMap.id : Module.End k V) u = 0 := by
          rw [LinearMap.sub_apply, LinearMap.id_apply, hεf u hu,
            sub_self]
        rw [h6, zero_add]
      rw [h5]
      exact ⟨w, hw, rfl⟩
    exact Submodule.finiteDimensional_of_le h1

/-- The residue-type commutator of a projection against a commuting
pair of almost-stabilizing operators is trace-class: it decomposes as
a projection commutator at the product minus a composed projection
commutator. -/
theorem isTraceClass_commutator_of_comm {A : Submodule k V}
    {ε μ ν : Module.End k V} (hcomm : ν ∘ₗ μ = μ ∘ₗ ν)
    (hμν : AlmostLE (A.map (μ ∘ₗ ν)) A)
    (hμ : AlmostLE (A.map μ) A) (hν : AlmostLE (A.map ν) A)
    (hεr : ∀ x : V, ε x ∈ A) (hεf : ∀ x ∈ A, ε x = x) :
    IsTraceClass A ((ε ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (ε ∘ₗ μ)) := by
  have hid : (ε ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (ε ∘ₗ μ) =
      (ε ∘ₗ (μ ∘ₗ ν) - (μ ∘ₗ ν) ∘ₗ ε) -
        ν ∘ₗ (ε ∘ₗ μ - μ ∘ₗ ε) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    have h1 := LinearMap.congr_fun hcomm (ε x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [← h1]
    abel
  rw [hid]
  exact (isTraceClass_proj_commutator hμν hεr hεf).sub
    ((isTraceClass_proj_commutator hμ hεr hεf).comp_left hν)

/-- **Tate's projection-comparison theorem**: the trace of the
commutator `[ε ∘ μ, ν]` is unchanged when the projection `ε` onto a
subspace `A` is replaced by a projection `π` onto a commensurable
overspace `A'`, provided the words in `μ, ν` almost-stabilize `A`.
The difference `θ = π − ε` kills `A` and lands in `A'`, so every
composite of `θ` against words has finite rank, and the difference of
the commutators is a traceless commutator. -/
theorem tateTrace_commutator_eq_of_projection {A A' : Submodule k V}
    {μ ν ε π : Module.End k V} (hAA' : A ≤ A') (hA'A : AlmostLE A' A)
    (hstab : ∀ w ∈ Submonoid.closure
      ({μ, ν} : Set (Module.End k V)), AlmostLE (A.map w) A)
    (hεr : ∀ x : V, ε x ∈ A) (hεf : ∀ x ∈ A, ε x = x)
    (hπr : ∀ x : V, π x ∈ A') (hπf : ∀ x ∈ A', π x = x)
    (hεtc : IsTraceClass A ((ε ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (ε ∘ₗ μ))) :
    tateTrace ((π ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (π ∘ₗ μ)) =
    tateTrace ((ε ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (ε ∘ₗ μ)) := by
  have hμ : μ ∈ Submonoid.closure ({μ, ν} : Set (Module.End k V)) :=
    Submonoid.subset_closure (Set.mem_insert _ _)
  have hν : ν ∈ Submonoid.closure ({μ, ν} : Set (Module.End k V)) :=
    Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  set θ : Module.End k V := π - ε with hθ
  have hθmem : ∀ x : V, θ x ∈ A' := fun x ↦ by
    rw [hθ, LinearMap.sub_apply]
    exact Submodule.sub_mem _ (hπr x) (hAA' (hεr x))
  have hθker : ∀ x ∈ A, θ x = 0 := fun x hx ↦ by
    rw [hθ, LinearMap.sub_apply, hπf x (hAA' hx), hεf x hx, sub_self]
  -- images of almost-`A` subspaces under `θ` are finite-dimensional
  have hfin : ∀ C : Submodule k V, AlmostLE C A →
      FiniteDimensional k (C.map θ) := by
    intro C hC
    obtain ⟨W, hW, hle⟩ := hC
    haveI := hW
    have h1 : C.map θ ≤ W.map θ := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hle hy)
      have h2 : θ y = θ w := by
        rw [← huw, map_add, hθker u hu, zero_add]
      rw [h2]
      exact ⟨w, hw, rfl⟩
    exact Submodule.finiteDimensional_of_le h1
  -- words applied to `A'` are still almost `A`
  have hstab' : ∀ w ∈ Submonoid.closure
      ({μ, ν} : Set (Module.End k V)), AlmostLE (A'.map w) A := by
    intro w hw
    obtain ⟨W, hW, hle⟩ := hA'A
    haveI := hW
    have h1 : A'.map w ≤ A.map w ⊔ W.map w := by
      refine (Submodule.map_mono hle).trans ?_
      rw [Submodule.map_sup]
    exact AlmostLE.mono_left h1
      (AlmostLE.sup (hstab w hw) AlmostLE.of_finiteDimensional)
  have hkey : ∀ (w : Module.End k V) (x : V), x ∈ A' →
      θ (w x) ∈ (A'.map w).map θ :=
    fun w x hx ↦ ⟨w x, ⟨x, hx, rfl⟩, rfl⟩
  set S : Module.End k V := θ ∘ₗ μ with hS
  -- the four squared-range instances for the commutator of `S` and `ν`
  haveI hI1 : FiniteDimensional k (LinearMap.range
      (((S ∘ₗ ν) ^ 2 : Module.End k V))) := by
    haveI := hfin _ (hstab' (μ * ν) (mul_mem hμ hν))
    refine Submodule.finiteDimensional_of_le
      (S₂ := (A'.map (μ * ν)).map θ) ?_
    rintro x ⟨y, rfl⟩
    have h1 : (((S ∘ₗ ν) ^ 2 : Module.End k V)) y =
        θ ((μ * ν) (θ ((μ * ν) y))) := by
      rw [pow_two, Module.End.mul_apply]
      rfl
    rw [h1]
    exact hkey _ _ (hθmem _)
  haveI hI2 : FiniteDimensional k (LinearMap.range
      (((ν ∘ₗ S) ^ 2 : Module.End k V))) := by
    haveI := hfin _ (hstab' (μ * ν) (mul_mem hμ hν))
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((A'.map (μ * ν)).map θ).map ν) ?_
    rintro x ⟨y, rfl⟩
    have h1 : (((ν ∘ₗ S) ^ 2 : Module.End k V)) y =
        ν (θ ((μ * ν) (θ (μ y)))) := by
      rw [pow_two, Module.End.mul_apply]
      rfl
    rw [h1]
    exact ⟨θ ((μ * ν) (θ (μ y))), hkey _ _ (hθmem _), rfl⟩
  haveI hI3 : FiniteDimensional k (LinearMap.range
      ((S ∘ₗ ν) ∘ₗ (ν ∘ₗ S))) := by
    haveI := hfin _ (hstab' (μ * ν * ν) (mul_mem (mul_mem hμ hν) hν))
    refine Submodule.finiteDimensional_of_le
      (S₂ := (A'.map (μ * ν * ν)).map θ) ?_
    rintro x ⟨y, rfl⟩
    have h1 : ((S ∘ₗ ν) ∘ₗ (ν ∘ₗ S)) y =
        θ ((μ * ν * ν) (θ (μ y))) := by
      rfl
    rw [h1]
    exact hkey _ _ (hθmem _)
  haveI hI4 : FiniteDimensional k (LinearMap.range
      ((ν ∘ₗ S) ∘ₗ (S ∘ₗ ν))) := by
    haveI := hfin _ (hstab' μ hμ)
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((A'.map μ).map θ).map ν) ?_
    rintro x ⟨y, rfl⟩
    have h1 : ((ν ∘ₗ S) ∘ₗ (S ∘ₗ ν)) y =
        ν (θ (μ (θ ((μ * ν) y)))) := by
      rfl
    rw [h1]
    exact ⟨θ (μ (θ ((μ * ν) y))), hkey _ _ (hθmem _), rfl⟩
  -- the difference of the commutators is trace-class
  have hDtc : IsTraceClass A (S ∘ₗ ν - ν ∘ₗ S) := by
    constructor
    · have hle : LinearMap.range (S ∘ₗ ν - ν ∘ₗ S) ≤
          A' ⊔ A'.map ν := by
        rintro x ⟨y, rfl⟩
        have h1 : (S ∘ₗ ν - ν ∘ₗ S) y =
            θ ((μ * ν) y) - ν (θ (μ y)) := by
          rfl
        rw [h1, sub_eq_add_neg]
        refine Submodule.add_mem _
          (Submodule.mem_sup_left (hθmem _))
          (Submodule.neg_mem _ (Submodule.mem_sup_right
            ⟨θ (μ y), hθmem _, rfl⟩))
      refine AlmostLE.mono_left hle ?_
      refine AlmostLE.sup (hA'A.trans AlmostLE.rfl) ?_
      obtain ⟨W, hW, hle'⟩ := hA'A
      haveI := hW
      have h2 : A'.map ν ≤ A.map ν ⊔ W.map ν := by
        refine (Submodule.map_mono hle').trans ?_
        rw [Submodule.map_sup]
      exact AlmostLE.mono_left h2
        (AlmostLE.sup (hstab ν hν) AlmostLE.of_finiteDimensional)
    · haveI := hfin _ (hstab' (μ * ν) (mul_mem hμ hν))
      haveI := hfin _ (hstab' μ hμ)
      refine Submodule.finiteDimensional_of_le
        (S₂ := (A'.map (μ * ν)).map θ ⊔
          ((A'.map μ).map θ).map ν) ?_
      rintro x ⟨a, ha, rfl⟩
      have h1 : (S ∘ₗ ν - ν ∘ₗ S) a =
          θ ((μ * ν) a) - ν (θ (μ a)) := by
        rfl
      rw [h1, sub_eq_add_neg]
      refine Submodule.add_mem _
        (Submodule.mem_sup_left (hkey _ _ (hAA' ha)))
        (Submodule.neg_mem _ (Submodule.mem_sup_right
          ⟨θ (μ a), hkey _ _ (hAA' ha), rfl⟩))
  have htrD : tateTrace (S ∘ₗ ν - ν ∘ₗ S) = 0 :=
    tateTrace_comp_sub_comp_comm_of_sq S ν
  have hCid : (π ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (π ∘ₗ μ) =
      ((ε ∘ₗ μ) ∘ₗ ν - ν ∘ₗ (ε ∘ₗ μ)) +
        (S ∘ₗ ν - ν ∘ₗ S) := by
    refine LinearMap.ext fun x ↦ ?_
    rw [hS, hθ]
    simp only [LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, map_sub]
    abel
  haveI := hεtc.finiteDimensional_range_comp hεtc
  haveI := hεtc.finiteDimensional_range_comp hDtc
  haveI := hDtc.finiteDimensional_range_comp hεtc
  haveI := hDtc.finiteDimensional_range_comp hDtc
  rw [hCid, tateTrace_add_of_sq, htrD, add_zero]

end

end AclGeom
