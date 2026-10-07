/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic

/-!
# The two-generic intersection lemma

Blueprint Lemma `two-generic-intersection` (checklist R3): if `s, t` are
algebraically independent over `acl_k(x) ∩ K`, then
`acl_k(t, tx) ∩ acl_k(s, sx) = acl_k(x)` inside `K`.

The blueprint proves this through linear disjointness of rational function fields. Here it is
an infimum-equality wrapper around the existing exchange consequence
`mem_racl_of_mem_racl_insert`: for any set `X` and `t ∉ acl(X ∪ {s})`,
`acl(X ∪ {t}) ∩ acl(X ∪ {s}) = acl(X)`. Neither finiteness of `X` nor
`s ∉ acl(X)` is required. The literal pair statement recovers `x` by division by `s` or `t`.

**Status:** the intersection part of M7/R3 is proved; all-point recovery remains open (#9).
The bypassed linear-disjointness obligations remain open (#11).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Two-generic intersection, exchange form**: if `t` is generic over `X ∪ {s}`,
the closures of `X ∪ {t}` and `X ∪ {s}` meet exactly in the closure of `X`. -/
theorem racl_insert_inf_racl_insert {X : Set K} {s t : K}
    (ht : t ∉ racl k (insert s X)) :
    racl k (insert t X) ⊓ racl k (insert s X) = racl k X := by
  refine le_antisymm (fun z hz ↦ ?_)
    (le_inf (racl_mono (Set.subset_insert _ _)) (racl_mono (Set.subset_insert _ _)))
  obtain ⟨hzt, hzs⟩ := IntermediateField.mem_inf.1 hz
  exact mem_racl_of_mem_racl_insert hzs hzt ht

/-- **Two-generic intersection** (blueprint Lemma `two-generic-intersection`):
if `s` is transcendental over `acl_k(x)` and `t` is transcendental over
`acl_k(x, s)` (that is, `s, t` are algebraically independent over
`acl_k(x) ∩ K`), then `acl_k(t, tx) ∩ acl_k(s, sx) = acl_k(x)`. -/
theorem racl_pair_mul_inf_racl_pair_mul {x s t : K}
    (hs : s ∉ racl k ({x} : Set K)) (ht : t ∉ racl k ({x, s} : Set K)) :
    racl k ({t, t * x} : Set K) ⊓ racl k ({s, s * x} : Set K) =
      racl k ({x} : Set K) := by
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ zero_mem _)
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ zero_mem _)
  -- `acl(u, ux) = acl(x, u)` for `u ≠ 0`.
  have hpair : ∀ u : K, u ≠ 0 →
      racl k ({u, u * x} : Set K) = racl k (insert u ({x} : Set K)) := by
    intro u hu
    apply le_antisymm
    · apply racl_le_of_subset_racl
      intro z hz
      rcases hz with h | h
      · rw [h]
        exact subset_racl k _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact mul_mem (subset_racl k _ (Set.mem_insert _ _))
          (subset_racl k _ (Set.mem_insert_of_mem _ rfl))
    · apply racl_le_of_subset_racl
      intro z hz
      rcases hz with h | h
      · rw [h]
        exact subset_racl k _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        have hu' : u ∈ racl k ({u, u * x} : Set K) :=
          subset_racl k _ (Set.mem_insert _ _)
        have hux : u * x ∈ racl k ({u, u * x} : Set K) :=
          subset_racl k _ (Set.mem_insert_of_mem _ rfl)
        have := mul_mem (inv_mem hu') hux
        rwa [inv_mul_cancel_left₀ hu] at this
  rw [hpair t ht0, hpair s hs0]
  refine racl_insert_inf_racl_insert ?_
  rwa [Set.pair_comm] at ht

end

end AclGeom
