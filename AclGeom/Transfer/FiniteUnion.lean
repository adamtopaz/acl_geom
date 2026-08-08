/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.GroupTheory.CosetCover
import Mathlib.FieldTheory.Finite.Basic

/-!
# A field is not a finite union of proper subfields

Via Mathlib's B. H. Neumann coset-cover theorem applied to the additive
subgroups, with the finite-field case handled by cyclicity of `Fˣ`
(blueprint Lemma no-field-cover): if a field is covered by finitely many
subfields, one of them is the whole field.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5, checklist T1).
-/

namespace AclGeom

open Pointwise

/-- **A field is not a finite union of proper subfields** (blueprint
Lemma no-field-cover): if finitely many subfields cover `F`, one of them
is all of `F`. -/
theorem exists_eq_top_of_subfield_cover {F : Type*} [Field F]
    {n : ℕ} (S : Fin n → Subfield F)
    (hcover : ∀ x : F, ∃ i, x ∈ S i) :
    ∃ i, S i = ⊤ := by
  classical
  -- Neumann: some subfield has finite additive index.
  have hcovers : ⋃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : F) +ᵥ ((S i).toAddSubgroup : Set F) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, hi⟩ := hcover x
    refine Set.mem_biUnion (Finset.mem_univ i) ?_
    simpa using hi
  obtain ⟨i, -, hfin⟩ :=
    AddSubgroup.exists_finiteIndex_of_leftCoset_cover
      (H := fun i ↦ (S i).toAddSubgroup) (g := fun _ ↦ (0 : F))
      (s := Finset.univ) hcovers
  -- Either that subfield is everything, or it is finite.
  by_cases htop : S i = ⊤
  · exact ⟨i, htop⟩
  -- A proper subfield of finite additive index must be finite.
  have hSfin : Finite (S i) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 htop :
      S i < ⊤)
    obtain ⟨hxtop, hxnot⟩ := hx
    -- The map `a ↦ a·x mod Sᵢ` injects `Sᵢ` into the finite quotient.
    haveI := hfin
    have hinj : Function.Injective
        (fun a : S i ↦ (QuotientAddGroup.mk (a.1 * x) :
          F ⧸ (S i).toAddSubgroup)) := by
      intro a b hab
      rw [QuotientAddGroup.eq] at hab
      -- `-(a·x) + b·x = (b - a)·x ∈ Sᵢ` forces `a = b`.
      by_contra hne
      have hba : (b.1 - a.1) * x ∈ S i := by
        have h1 : -(a.1 * x) + b.1 * x = (b.1 - a.1) * x := by ring
        rw [← h1]
        exact hab
      have hba0 : b.1 - a.1 ≠ 0 := by
        intro h0
        refine hne ?_
        have := sub_eq_zero.1 h0
        exact Subtype.ext this.symm
      have hbamem : b.1 - a.1 ∈ S i := sub_mem b.2 a.2
      have hxmem : x ∈ S i := by
        have h2 := mul_mem (inv_mem hbamem) hba
        rwa [inv_mul_cancel_left₀ hba0] at h2
      exact hxnot hxmem
    haveI : Finite (F ⧸ (S i).toAddSubgroup) :=
      AddSubgroup.finite_quotient_of_finiteIndex
    exact (Finite.of_injective _ hinj).not_infinite hinf
  -- A finite subfield of finite index makes the whole field finite.
  haveI : Finite (F ⧸ (S i).toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  haveI hs : Finite ((S i).toAddSubgroup) := hSfin
  haveI hFfin : Finite F :=
    Finite.of_equiv _
      (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
        (s := (S i).toAddSubgroup)).symm
  -- Finite fields have cyclic unit groups; a generator's subfield is
  -- everything.
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨j, hj⟩ := hcover (g : F)
  refine ⟨j, eq_top_iff.2 fun y _ ↦ ?_⟩
  by_cases hy : y = 0
  · rw [hy]
    exact zero_mem _
  · obtain ⟨m, hm⟩ := hg (Units.mk0 y hy)
    have hym : ((g : Fˣ) ^ m : Fˣ) = Units.mk0 y hy := hm
    have hyval : y = ((g : F)) ^ m := by
      have := congrArg (Units.val) hym
      simpa [Units.val_zpow_eq_zpow_val] using this.symm
    rw [hyval]
    exact zpow_mem hj m

/-- Avoidance form of blueprint Lemma no-field-cover: finitely many proper
subfields miss a common element. -/
theorem exists_notMem_of_ne_top {F : Type*} [Field F]
    {n : ℕ} (S : Fin n → Subfield F) (hS : ∀ i, S i ≠ ⊤) :
    ∃ x : F, ∀ i, x ∉ S i := by
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := exists_eq_top_of_subfield_cover S h
  exact hS i hi

end AclGeom
