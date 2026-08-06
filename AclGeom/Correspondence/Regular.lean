/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Toward regularity: tensor products of field extensions

Blueprint Lemma `generic-extension` (8.1(a)) asserts that over an
algebraically closed base `k`, the tensor product `E ⊗[k] F` of two field
extensions is a domain. This is the load-bearing fact for the hard kernel
(independent generic points, correspondence composition, the stabilizer
argument). See the tracking issue for the full plan.

This file provides the first reduction:

* `isDomain_tensorProduct_of_fg`: it suffices to prove domain-ness when the
  left factor is finitely generated — zero divisors live in a finitely
  generated leg, and tensoring with `F` preserves the inclusion by flatness.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, toward checklist C2/C3 prerequisites).
-/

namespace AclGeom

open TensorProduct IntermediateField

noncomputable section

variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

/-- The canonical map `E' ⊗[k] F → E ⊗[k] F` induced by an intermediate
field `E' ≤ E` is injective (`F` is flat over the field `k`). -/
theorem tensorProduct_map_val_injective (E' : IntermediateField k E) :
    Function.Injective
      (Algebra.TensorProduct.map E'.val (AlgHom.id k F)) := by
  have hinj : Function.Injective (E'.val.toLinearMap) := Subtype.val_injective
  have h := Module.Flat.rTensor_preserves_injective_linearMap
    (M := F) E'.val.toLinearMap hinj
  exact h

/-- Reduction of domain-ness of `E ⊗[k] F` to finitely generated
subextensions of `E` (first step of blueprint Lemma 8.1(a)): a zero divisor
has finitely many tensor legs, hence lives in a finitely generated leg. -/
theorem isDomain_tensorProduct_of_fg
    (h : ∀ E' : IntermediateField k E, E'.FG → IsDomain (E' ⊗[k] F)) :
    IsDomain (E ⊗[k] F) := by
  classical
  haveI : Nontrivial (E ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k E F
      (algebraMap k E).injective (algebraMap k F).injective
  -- No zero divisors: any relation lives in a finitely generated leg.
  haveI : NoZeroDivisors (E ⊗[k] F) := by
    refine ⟨fun {x y} hxy ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hy0⟩ := hcon
    -- Write both elements with finitely many tensor legs.
    obtain ⟨sx, hsx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hsy⟩ := TensorProduct.exists_finset y
    -- The finitely generated subextension containing all left legs.
    set T : Finset E := sx.image Prod.fst ∪ sy.image Prod.fst with hT
    set E' : IntermediateField k E := adjoin k (T : Set E) with hE'
    haveI hdom : IsDomain (E' ⊗[k] F) := h E' ⟨T, rfl⟩
    set φ := Algebra.TensorProduct.map E'.val (AlgHom.id k F) with hφ
    have hφinj : Function.Injective φ := tensorProduct_map_val_injective E'
    -- Both elements are in the image of `E' ⊗[k] F`.
    have hmem : ∀ (s : Finset (E × F)), (↑(s.image Prod.fst) : Set E) ⊆ T →
        ∃ z : E' ⊗[k] F, φ z = ∑ p ∈ s, p.1 ⊗ₜ[k] p.2 := by
      intro s hs
      refine ⟨∑ p ∈ s.attach, (⟨p.1.1, subset_adjoin k _ (hs (by
        simpa using Finset.mem_image_of_mem Prod.fst p.2))⟩ : E') ⊗ₜ[k] p.1.2, ?_⟩
      rw [map_sum, ← Finset.sum_attach s fun p ↦ p.1 ⊗ₜ[k] p.2]
      exact Finset.sum_congr rfl fun p _ ↦ rfl
    obtain ⟨x', hx'⟩ := hmem sx (by intro e he; simp only [hT, Finset.coe_union]; left; exact he)
    obtain ⟨y', hy'⟩ := hmem sy (by intro e he; simp only [hT, Finset.coe_union]; right; exact he)
    rw [← hsx] at hx'
    rw [← hsy] at hy'
    -- Transport the relation and contradict.
    have hxy' : x' * y' = 0 := by
      refine hφinj ?_
      rw [map_mul, hx', hy', hxy, map_zero]
    rcases mul_eq_zero.1 hxy' with h0 | h0
    · exact hx0 (by rw [← hx', h0, map_zero])
    · exact hy0 (by rw [← hy', h0, map_zero])
  exact NoZeroDivisors.to_isDomain _

end

end AclGeom
