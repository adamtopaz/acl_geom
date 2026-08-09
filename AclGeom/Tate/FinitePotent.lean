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

end

end AclGeom
