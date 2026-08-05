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
  intersecting `M^perf` with (the image of) `K` recovers `M`;
* `Perfection.isRAC_perfIF` / `Perfection.perfClosed`: `M^perf` is
  relatively algebraically closed in the perfection, so perfection maps the
  closed lattice of `K/k` into that of `K^perf/k^perf`.

Still to come (P2, P3): surjectivity onto the closed lattice of the
perfection (eq. 5.2) and the order isomorphism, and the integral Frobenius
action fixing every atom.

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

/-- The perfected subfield of a closed intermediate field is relatively
algebraically closed in the perfection (blueprint Prop `perf-lattice`,
first part). The proof raises an annihilating polynomial by a common
Frobenius power to land its coefficients in `ι M`, raises once more to land
the point in `ι K`, and descends the resulting polynomial identity to `K`
along the injective inclusion. -/
theorem isRAC_perfIF (M : ClosedIF k K) : IsRAC (π.perfIF k M) := by
  classical
  intro x hx
  -- An annihilating polynomial with coefficients in `M^perf`.
  obtain ⟨q, hq0, hqx, hqc⟩ := exists_poly_of_isAlgebraic hx
  -- Choose exponents and preimages for the coefficients, then pass to the
  -- common exponent `s`.
  choose e m hm hqm using fun n ↦ π.mem_perfIF_iff.1 (hqc n)
  set s := q.support.sup e with hs
  have key : ∀ n, ∃ c ∈ M, q.coeff n ^ π.p ^ s = π.incl c := by
    intro n
    by_cases hn : n ∈ q.support
    · refine ⟨m n ^ π.p ^ (s - e n),
        ClosedIF.mem_val.1 (pow_mem (ClosedIF.mem_val.2 (hm n)) _), ?_⟩
      have hsplit : π.p ^ s = π.p ^ e n * π.p ^ (s - e n) := by
        rw [← pow_add, Nat.add_sub_cancel' (Finset.le_sup hn)]
      rw [hsplit, pow_mul, hqm n, ← map_pow]
    · refine ⟨0, zero_mem M.1, ?_⟩
      rw [Polynomial.notMem_support_iff.1 hn, map_zero,
        zero_pow (expChar_pow_pos π.carrier π.p s).ne']
  choose c hc hcq using key
  -- A power of `x` descends to `K`.
  obtain ⟨r, y, hy⟩ := π.exists_pow_incl x
  set z : K := y ^ π.p ^ s with hz
  -- The descended annihilating polynomial over `K`.
  set Q : Polynomial K := ∑ n ∈ q.support, Polynomial.monomial n (c n ^ π.p ^ r) with hQ
  have hQcoeff : ∀ j, Q.coeff j ∈ M.1 := by
    intro j
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' q.support j fun n ↦ c n ^ π.p ^ r]
    split_ifs with hj
    · exact pow_mem (ClosedIF.mem_val.2 (hc j)) _
    · exact zero_mem _
  have hcne : ∀ n ∈ q.support, c n ≠ 0 := by
    intro n hn h0
    refine Polynomial.mem_support_iff.1 hn ?_
    have := hcq n
    rw [h0, map_zero, pow_eq_zero_iff (expChar_pow_pos π.carrier π.p s).ne'] at this
    exact this
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hd : q.natDegree ∈ q.support := q.natDegree_mem_support_of_nonzero hq0
    have : Q.coeff q.natDegree = c q.natDegree ^ π.p ^ r := by
      rw [hQ, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' q.support _ fun n ↦ c n ^ π.p ^ r, if_pos hd]
    rw [h0, Polynomial.coeff_zero] at this
    exact pow_ne_zero _ (hcne _ hd) this.symm
  -- The evaluation identity, via the `p^(s+r)`-th Frobenius.
  have hQz : Q.eval z = 0 := by
    refine π.incl_injective ?_
    have hev : π.incl (Q.eval z) =
        Polynomial.eval₂ (iterateFrobenius π.carrier π.p (s + r))
          (iterateFrobenius π.carrier π.p (s + r) x) q := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, hQ]
      rw [Polynomial.eval_finsetSum, map_sum]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [Polynomial.eval_monomial, map_mul, map_pow, map_pow]
      congr 1
      · -- coefficient side: ι(c n)^(p^r) = (q.coeff n)^(p^(s+r))
        rw [← hcq n, iterateFrobenius_def, ← pow_mul, ← pow_add]
      · -- point side: ι(z)^n = (x^(p^(s+r)))^n
        rw [hz, map_pow, hy, iterateFrobenius_def,
          ← pow_mul x (π.p ^ r) (π.p ^ s), ← pow_add, Nat.add_comm r s]
    rw [hev, Polynomial.eval₂_at_apply, hqx, map_zero, map_zero]
  -- Descend: `z` is algebraic over the closed `M`, hence in `M`.
  have hzM : z ∈ M.1 := M.2 z (isAlgebraic_of_coeff_mem hQ0 hQz hQcoeff)
  refine π.mem_perfIF_iff.2 ⟨r + s, z, ClosedIF.mem_val.1 hzM, ?_⟩
  rw [hz, map_pow, hy, ← pow_mul, ← pow_add]

variable (k) in
/-- `M^perf` as a member of the closed lattice of the perfection over the
perfected base. -/
def perfClosed (M : ClosedIF k K) : ClosedIF (π.basePerf k) π.carrier :=
  ⟨π.perfIF k M, π.isRAC_perfIF M⟩

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
