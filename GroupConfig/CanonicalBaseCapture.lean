/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.CanonicalBase

/-!
# Capturing algebraicity over a canonical base

Algebraicity of a finite target tuple over an algebraically closed small field and a source
tuple is already captured by the canonical base of their joint locus. The source tuple has
finite rank, so the rank-addition law detects the algebraicity after replacing the field.

**Status:** proved (#12). Shared by the canonical-base clauses of the rank-two Ψ configuration
and the rank-one partial-quadrangle configuration.
-/

namespace GroupConfig

open AclGeom Set

variable {k K ι κ : Type*} [Field k] [Field K] [Algebra k K]

/-- Algebraicity of a finite target tuple over M and a source tuple can be
captured using the canonical base of their joint locus instead of M.
Consumers: the canonical-base clauses of the rank-two Ψ input and the rank-one
partial-quadrangle input. -/
theorem range_subset_racl_canonicalBase [IsAlgClosed K] [UniversalDomain k K]
    [Finite ι] [Finite κ] (M : IntermediateField k K) [IsAlgClosed (↥M)]
    (hM : IsSmall k (M : Set K)) (a : ι → K) (b : κ → K)
    (hb : range b ⊆ racl k ((M : Set K) ∪ range a)) :
    range b ⊆ racl k ((canonicalBase M (Sum.elim a b) : Set K) ∪ range a) := by
  let C := canonicalBase M (Sum.elim a b)
  have hrange := Sum.elim_range a b
  have htotal : erk k (C : Set K) (range a ∪ range b) =
      erk k (M : Set K) (range a) := by
    rw [← hrange, erk_canonicalBase_eq M hM, hrange]
    exact erk_union_eq_of_subset_racl k hb
  have hlow : erk k (M : Set K) (range a) ≤ erk k (C : Set K) (range a) :=
    erk_base_mono k (SetLike.coe_subset_coe.2 (canonicalBase_le M (Sum.elim a b))) _
  have hsum : erk k (C : Set K) (range a) +
      erk k ((C : Set K) ∪ range a) (range b) ≤ erk k (C : Set K) (range a) + 0 := by
    rw [← erk_union_eq, add_zero]
    exact htotal.le.trans hlow
  have hz := (ENat.add_le_add_iff_left (erk_ne_top k (finite_range a) (C : Set K))).1 hsum
  exact (erk_eq_zero_iff k).1 (bot_unique hz)


end GroupConfig
