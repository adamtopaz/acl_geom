/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Transfer.Transcendence
import Mathlib.Data.Set.Finite.Basic

/-!
# Fresh sequences over infinite transcendence degree

* `exists_fresh_sequence_of_aleph0_le_trdeg`: if `ℵ₀ ≤ trdeg_k K` and `S` is finite, there is a
  sequence `t` such that each `t n` lies outside `acl(S ∪ {t m | m < n})`.  No algebraic
  closedness is needed.

The sequences supply the families of fresh inputs of the affine-grid producers: in `K` itself in
`AclGeom.Config.AffineGridInfinite`, and in an algebraically closed extension with at least
countable transcendence degree over `k` in `AclGeom.Config.AffineGridNormalization`.

**Status:** proved (#27, P5); moved here unchanged in P6.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Fresh sequences** (#27, P5).  If `K` has infinite transcendence degree over `k`, then for
a finite parameter set `S` there is a sequence whose `n`-th term is not algebraic over `S`
together with the earlier terms. -/
theorem exists_fresh_sequence_of_aleph0_le_trdeg
    (htr : Cardinal.aleph0 ≤ Algebra.trdeg k K) {S : Set K} (hS : S.Finite) :
    ∃ t : ℕ → K, ∀ n, t n ∉ racl k (S ∪ t '' Set.Iio n) := by
  refine Set.seq_of_forall_finite_exists (P := fun z T ↦ z ∉ racl k (S ∪ T)) fun T hT ↦ ?_
  have hfin := hS.union hT
  obtain ⟨z, hz⟩ := exists_notMem_racl_of_card_lt_trdeg (n := hfin.toFinset.card)
    (Cardinal.natCast_lt_aleph0.trans_le htr) hfin.toFinset le_rfl
  rw [Set.Finite.coe_toFinset] at hz
  exact ⟨z, hz⟩

end AclGeom
