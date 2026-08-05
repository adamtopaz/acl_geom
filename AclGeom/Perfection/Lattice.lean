/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Perfection.Subfield
import AclGeom.Geometry.Points
import Mathlib.FieldTheory.Perfect

/-!
# The perfected base and the pullback equation

Toward the perfection order isomorphism
`𝒢(K/k) ≃o 𝒢(K^perf/k^perf)` (blueprint Prop `perf-lattice`), this file
provides:

* `Perfection.basePerf`: the compatible perfected base `k^i` inside the
  perfection of `K` (blueprint eq. 20.1);
* `Perfection.perfIF`: `M^perf` as an intermediate field of the perfection
  over the perfected base, for a closed `M ∈ 𝒢(K/k)`;
* `Perfection.incl_mem_perfIF_iff`: the pullback equation (5.1) —
  intersecting `M^perf` with (the image of) `K` recovers `M`.

Still to come (P2, P3): relative algebraic closedness of `M^perf` in the
perfection, the order isomorphism with inverse `comap incl` (eq. 5.2), and
the integral Frobenius action fixing every atom.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M2, checklist P2).
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]
variable (π : Perfection K)

variable (k) in
/-- The compatible perfected base `k^i` (blueprint eq. 20.1): elements of the
perfection of `K` some `p`-power of which lies in the image of `k`. -/
def basePerf : Subfield π.carrier :=
  π.perfSubfield (algebraMap k K).fieldRange

theorem mem_basePerf_iff {x : π.carrier} :
    x ∈ π.basePerf k ↔ ∃ n : ℕ, ∃ c : k, x ^ π.p ^ n = π.incl (algebraMap k K c) := by
  rw [basePerf, mem_perfSubfield_iff]
  constructor
  · rintro ⟨n, m, ⟨c, rfl⟩, h⟩
    exact ⟨n, c, h⟩
  · rintro ⟨n, c, h⟩
    exact ⟨n, algebraMap k K c, ⟨c, rfl⟩, h⟩

variable (k) in
/-- The perfected subfield of a closed intermediate field contains the
perfected base. -/
theorem basePerf_le_perfSubfield (M : ClosedIF k K) :
    π.basePerf k ≤ π.perfSubfield M.1.toSubfield :=
  π.perfSubfield_mono fun _ hy ↦ by
    obtain ⟨c, rfl⟩ := hy
    exact M.1.algebraMap_mem c

variable (k) in
/-- `M^perf`, as an intermediate field of the perfection over the perfected
base (blueprint §Foundation III). -/
def perfIF (M : ClosedIF k K) : IntermediateField (π.basePerf k) π.carrier :=
  (π.perfSubfield M.1.toSubfield).toIntermediateField fun x ↦
    π.basePerf_le_perfSubfield k M x.2

theorem mem_perfIF_iff {M : ClosedIF k K} {x : π.carrier} :
    x ∈ π.perfIF k M ↔ ∃ n : ℕ, ∃ m ∈ M, x ^ π.p ^ n = π.incl m :=
  Iff.rfl

theorem perfIF_mono {M N : ClosedIF k K} (h : M ≤ N) :
    π.perfIF k M ≤ π.perfIF k N := fun _ hx ↦ by
  obtain ⟨n, m, hm, hxm⟩ := hx
  exact ⟨n, m, ClosedIF.le_iff.1 h hm, hxm⟩

/-- Equation (5.1) of the blueprint: pulling `M^perf` back along the
inclusion of `K` recovers exactly `M`, for closed `M`. This is the inverse
direction of the perfection order isomorphism. -/
theorem incl_mem_perfIF_iff {M : ClosedIF k K} {x : K} :
    π.incl x ∈ π.perfIF k M ↔ x ∈ M := by
  rw [mem_perfIF_iff]
  constructor
  · rintro ⟨n, m, hm, hx⟩
    rw [← map_pow] at hx
    have hxm : x ^ π.p ^ n ∈ M.1 := by
      rw [π.incl_injective hx]
      exact hm
    exact M.2.mem_of_pow_mem (expChar_pow_pos K π.p n).ne' hxm
  · intro hx
    exact ⟨0, x, hx, by simp⟩

/-- The perfected intermediate field determines the closed field: `perfIF` is
injective. -/
theorem perfIF_injective : Function.Injective (π.perfIF k (K := K)) := by
  intro M N h
  refine SetLike.ext fun x ↦ ?_
  rw [← π.incl_mem_perfIF_iff (M := M), ← π.incl_mem_perfIF_iff (M := N), h]

/-- `perfIF` reflects the order (via the pullback equation). -/
theorem perfIF_le_iff {M N : ClosedIF k K} :
    π.perfIF k M ≤ π.perfIF k N ↔ M ≤ N := by
  constructor
  · intro h x hx
    exact (π.incl_mem_perfIF_iff).1 (h ((π.incl_mem_perfIF_iff).2 hx))
  · exact π.perfIF_mono

end Perfection

end

end AclGeom
