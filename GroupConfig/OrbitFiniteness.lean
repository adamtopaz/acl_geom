/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConjugateSet

/-!
# Finite orbits

Blueprint `sources/group_configuration/01-universal-domain.tex`, `lem:orbit`.

For an intermediate field `L`, the orbit of `x` under the automorphisms of `K` over `L` is
finite exactly when `x` is algebraic over `L` (`finite_orbit_iff`); the finiteness of orbits of
algebraic elements is `GroupConfig.finite_conjugates`. The orbit of an element transcendental
over `L` is the set of all elements transcendental over `L` (`orbit_eq_of_transcendental`).
For a finite tuple the orbit is finite exactly when every coordinate is algebraic over `L`
(`finite_orbit_tuple_iff`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:orbit` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]

/-- `lem:orbit`: the orbit of an element transcendental over `L` is the set of all elements
transcendental over `L`. -/
theorem orbit_eq_of_transcendental {L : IntermediateField k K} {x : K}
    (hx : Transcendental (↥L) x) :
    range (fun σ : K ≃ₐ[↥L] K ↦ σ x) = {x' | Transcendental (↥L) x'} := by
  ext x'
  constructor
  · rintro ⟨σ, rfl⟩ halg
    apply hx
    simpa using halg.algHom σ.symm.toAlgHom
  · intro hx'
    have hx'' : Transcendental (↥L) x' := hx'
    have hideal : idealOf (↥L) (fun _ : Unit ↦ x) = idealOf (↥L) (fun _ : Unit ↦ x') := by
      rw [(idealOf_eq_bot_iff (↥L)).2 (algebraicIndependent_unique_type_iff.2 hx),
        (idealOf_eq_bot_iff (↥L)).2 (algebraicIndependent_unique_type_iff.2 hx'')]
    obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq hideal
    exact ⟨σ, hσ ()⟩

/-- `lem:orbit`: the orbit of `x` under the automorphisms over `L` is finite exactly when `x`
lies in the relative algebraic closure of `L`. -/
theorem finite_orbit_iff (L : IntermediateField k K) (x : K) :
    (range fun σ : K ≃ₐ[↥L] K ↦ σ x).Finite ↔ x ∈ racl k (L : Set K) := by
  rw [mem_racl_iff, adjoin_self]
  constructor
  · intro hfin
    by_contra hx
    have hxt : Transcendental (↥L) x := hx
    rw [orbit_eq_of_transcendental hxt] at hfin
    -- The positive powers of `x` are pairwise distinct and transcendental.
    have hinj : Function.Injective fun n : ℕ ↦ x ^ (n + 1) := by
      intro i j hij
      have h := (transcendental_iff_injective.1 hxt)
        (show Polynomial.aeval x (Polynomial.X ^ (i + 1)) =
          Polynomial.aeval x (Polynomial.X ^ (j + 1)) by simpa using hij)
      simpa using congrArg Polynomial.natDegree h
    exact Set.infinite_of_injective_forall_mem hinj (fun n ↦ hxt.pow n.succ_pos) hfin
  · intro hx
    have h := finite_conjugates (L := L) (z := fun _ : Unit ↦ x) fun _ ↦ hx.isIntegral
    refine (h.image fun z ↦ z ()).subset ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, ⟨σ, rfl⟩, rfl⟩

/-- `lem:orbit` for tuples: the orbit of a finite tuple under the automorphisms over `L` is
finite exactly when every coordinate lies in the relative algebraic closure of `L`. -/
theorem finite_orbit_tuple_iff (L : IntermediateField k K) {μ : Type*} [Finite μ] (z : μ → K) :
    (range fun σ : K ≃ₐ[↥L] K ↦ ⇑σ ∘ z).Finite ↔ ∀ i, z i ∈ racl k (L : Set K) := by
  constructor
  · intro hfin i
    refine (finite_orbit_iff L (z i)).1 ((hfin.image fun w ↦ w i).subset ?_)
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, ⟨σ, rfl⟩, rfl⟩
  · intro hz
    refine finite_conjugates fun i ↦ ?_
    have h := hz i
    rw [mem_racl_iff, adjoin_self] at h
    exact h.isIntegral

end

end GroupConfig
