/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Extending a finite generic-point isomorphism to the ambient field

The second clause of blueprint Lemma `generic-extension` (b) follows in
an algebraically closed common ambient for finite coordinate tuples.
The existing generated-field isomorphism extends to an ambient algebra
automorphism. Finite generation makes the cancelled transcendence-degree
summand finite, even when the ambient transcendence degree is infinite.
No algebraic closedness of the base field or complement-basis oracle is needed.

This module is part of the formalization of the reconstruction theorem;
the source of truth is `sources/blueprint.tex`.

**Status:** the finite-tuple field content of generic-extension (b) is proved
in a common algebraically closed ambient, with no enlargement there.
An actual consumer passes a nonclosed ambient to its algebraic closure.
Explicit rank/dimension, the packaged variety-level lemma, correspondence
composition and reconstruction completeness remain open (#5).
-/

namespace AclGeom

open IntermediateField

noncomputable section

/-- Equal loci of finite tuples in an algebraically closed ambient give an
ambient automorphism extending their existing generated-field isomorphism,
with the prescribed images of every coordinate (blueprint generic-extension (b)). -/
theorem exists_ambientAutomorphism_of_idealOf_eq
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {ι : Type*} [Finite ι] {a b : ι → Ω} (h : idealOf k a = idealOf k b) :
    ∃ σ : Ω ≃ₐ[k] Ω,
      (∀ z : ↥(adjoin k (Set.range a)),
        σ (z : Ω) = (locusFunctionFieldEquivOfIdealEq h z : Ω)) ∧
      ∀ i, σ (a i) = b i := by
  classical
  let F : IntermediateField k Ω := adjoin k (Set.range a)
  let G : IntermediateField k Ω := adjoin k (Set.range b)
  let φ : F ≃ₐ[k] G := locusFunctionFieldEquivOfIdealEq h
  let : Algebra.EssFiniteType k F :=
    essFiniteType_iff.mpr (fg_adjoin_of_finite (Set.finite_range a))
  have hf : Algebra.trdeg k F < Cardinal.aleph0 := trdeg_lt_aleph0 k F
  have hfg : Algebra.trdeg k F = Algebra.trdeg k G := φ.trdeg_eq
  have hc : Algebra.trdeg F Ω = Algebra.trdeg G Ω := by
    have ht := (trdeg_add_eq k F (A := Ω)).trans (trdeg_add_eq k G (A := Ω)).symm
    rw [← hfg] at ht
    apply (Cardinal.add_right_inj_of_lt_aleph0 hf).1
    simpa only [add_comm] using ht
  obtain ⟨α, x, hx⟩ := exists_isTranscendenceBasis' F Ω
  obtain ⟨β, y, hy⟩ := exists_isTranscendenceBasis' G Ω
  let e : α ≃ β :=
    (Cardinal.eq.1 (hx.cardinalMk_eq_trdeg.trans
      (hc.trans hy.cardinalMk_eq_trdeg.symm))).some
  have hy' : IsTranscendenceBasis G (y ∘ e) := hy.comp_equiv e
  let S : IntermediateField F Ω := adjoin F (Set.range x)
  let T : IntermediateField G Ω := adjoin G (Set.range (y ∘ e))
  let ψ : S ≃ₐ[k] T := adjoinIndependentEquivOfEquiv φ hx.1 hy'.1
  let : IsAlgClosure S Ω := ⟨inferInstance, hx.isAlgebraic_field⟩
  let : IsAlgClosure T Ω := ⟨inferInstance, hy'.isAlgebraic_field⟩
  let σ₀ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω ψ.toRingEquiv
  have hσ (z : F) : σ₀ (z : Ω) = (φ z : Ω) := by
    calc
      σ₀ (z : Ω) = algebraMap T Ω (ψ (algebraMap F S z)) :=
        IsAlgClosure.equivOfEquiv_algebraMap Ω Ω ψ.toRingEquiv (algebraMap F S z)
      _ = (φ z : Ω) := by
        change algebraMap T Ω
          (adjoinIndependentEquivOfEquiv φ hx.1 hy'.1 (algebraMap F S z)) = _
        rw [adjoinIndependentEquivOfEquiv_algebraMap]
        rfl
  let σ : Ω ≃ₐ[k] Ω :=
    { σ₀ with
      commutes' := fun c ↦ by
        change σ₀ ((algebraMap k F c : F) : Ω) = algebraMap k Ω c
        rw [hσ, φ.commutes]
        rfl }
  refine ⟨σ, hσ, ?_⟩
  intro i
  calc
    σ (a i) = (φ ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ : Ω) :=
      hσ ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩
    _ = b i := congrArg Subtype.val (locusFunctionFieldEquivOfIdealEq_apply h i)

end

end AclGeom
