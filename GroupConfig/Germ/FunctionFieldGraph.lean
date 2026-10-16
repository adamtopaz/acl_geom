/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.FunctionFieldAction

/-!
# The graph of a rational substitution in the function field

Let `r` be a representative of exponent zero of a germ on the locus of `v`, and let `C ≤ M_r`
be a coefficient field. The polynomial relations over `C` between the coordinates of the
function field and their substitutes under `r` are exactly the polynomials over `C` in the
graph ideal of `r` (`ker_aeval_graph`).

The proof evaluates at a generic point `y` over `M_r`. Every polynomial expression in the
coordinates and their substitutes has a value at `y` (`hasValue_aeval_graph`), namely its
value at the graph point `(y, r(y))`, and an element of the function field vanishes iff its
value does.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set LocusFunctionField

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

namespace Representative

variable (r : Representative k K v v)

private theorem hasValue_subst_coord (hr : r.f.e = 0) {y : ι → K} (hy : IsGenericOver r.M v y)
    (i : ι) : HasValue r.M y (r.subst hr (coord k v i)) (r.f.eval y i) :=
  ⟨r.f.num i, r.f.den i, r.isDefinedAt y hy i, r.subst_coord hr i, by
    rw [QuasiRational.eval_apply, hr, pRoot_zero]⟩

/-- Every polynomial expression over `C` in the coordinates and their substitutes has, at a
generic point `y`, its value at the graph point `(y, r(y))`. -/
private theorem hasValue_aeval_graph (hr : r.f.e = 0) {C : IntermediateField k K}
    (hCM : C ≤ r.M) {y : ι → K} (hy : IsGenericOver r.M v y) (P : MvPolynomial (ι ⊕ ι) C) :
    HasValue r.M y (aeval (Sum.elim (coord k v) fun i ↦ r.subst hr (coord k v i)) P)
      (aeval (r.graphPoint y) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, aeval_C]
    exact hasValue_algebraMap hCM c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact HasValue.add hy hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    refine HasValue.mul hp ?_
    cases j with
    | inl i => exact hasValue_coord i
    | inr i => exact r.hasValue_subst_coord hr hy i

/-- **The graph kernel.** The polynomial relations over `C ≤ M_r` between the coordinates of
the function field and their substitutes under `r` are the polynomials over `C` in the graph
ideal of `r`. -/
theorem ker_aeval_graph (hr : r.f.e = 0) (C : IntermediateField k K) (hCM : C ≤ r.M) :
    RingHom.ker (aeval (Sum.elim (coord k v) fun i ↦ r.subst hr (coord k v i)) :
        MvPolynomial (ι ⊕ ι) C →ₐ[C] LocusFunctionField k v).toRingHom =
      r.graphIdeal.comap (MvPolynomial.map (algebraMap C K)) := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall v
  ext P
  have hval := r.hasValue_aeval_graph hr hCM hy P
  have hzero : HasValue r.M y (0 : LocusFunctionField k v) 0 := by
    simpa using hasValue_mk (k := k) (v := v) (M := r.M) (y := y) 0
  have hmap : MvPolynomial.map (algebraMap C K) P = MvPolynomial.map (algebraMap r.M K)
      (MvPolynomial.map (IntermediateField.inclusion hCM).toRingHom P) := by
    rw [MvPolynomial.map_map]
    rfl
  rw [RingHom.mem_ker, Ideal.mem_comap, r.graphIdeal_eq hy, hmap, map_mem_locusIdeal_iff,
    mem_idealOf_iff, aeval_map_inclusion]
  change aeval (Sum.elim (coord k v) fun i ↦ r.subst hr (coord k v i)) P = 0 ↔ _
  constructor
  · intro h0
    rw [h0] at hval
    exact hval.eq_value hy hzero
  · intro h0
    rw [h0] at hval
    exact hval.eq hy hzero

end Representative

end

end GroupConfig
