/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.CurveGenus
import AclGeom.Curves.RationalAutomorphisms

/-!
# The Hrushovski–Weil action is fractional linear

Let `v` be a finite tuple of rank one carrying Hrushovski–Weil data whose canonical base has
rank at least two. The locus function field then has genus zero (`Germ.IsHW.genus_eq_zero`).
It therefore has a transcendental generator `t` in which every element of the function-field
action is a fractional linear transformation (`Germ.IsHW.exists_generator_moebius`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). The scheme and action bridges, the
normal-subgroup producer and the classification of the action remain obligations.
-/

namespace GroupConfig

open AclGeom Set

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

/-- **The HW action is fractional linear.** A rank-one HW locus whose canonical base has rank
at least two has a transcendental generator `t` of its function field such that every element
of the function-field action sends `t` to `(a t + b) / (c t + d)` with `a d - b c ≠ 0`. The
one-variable structure is derived from `hv`. -/
theorem Germ.IsHW.exists_generator_moebius {g₀ : Germ k v v} (hw : Germ.IsHW g₀)
    (hv : erk k ∅ (range v) = 1) (hr : 2 ≤ erk k ∅ (g₀.cb : Set K)) :
    ∃ t : LocusFunctionField k v, Transcendental K t ∧
      IntermediateField.adjoin K ({t} : Set (LocusFunctionField k v)) = ⊤ ∧
      ∀ γ : ↥hw.prodSubgroup, ∃ a b c d : K, a * d - b * c ≠ 0 ∧
        algebraMap K _ c * t + algebraMap K _ d ≠ 0 ∧
        hw.functionFieldAction hv γ t * (algebraMap K _ c * t + algebraMap K _ d) =
          algebraMap K _ a * t + algebraMap K _ b := by
  let _ := LocusFunctionField.isFunctionFieldOneVar (k := k) (v := v) hv
  obtain ⟨t, ht, htop, hσ⟩ := exists_generator_moebius_of_genus_eq_zero
    (k := K) (F := LocusFunctionField k v) (hw.genus_eq_zero hv hr)
  exact ⟨t, ht, htop, fun γ ↦ hσ (hw.functionFieldAction hv γ)⟩

end GroupConfig
