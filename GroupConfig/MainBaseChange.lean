/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Main
import GroupConfig.Germ.BaseChangeArbitrary

/-!
# Independent base extension of actual main data

The existential main conclusion survives an independent finite base extension.
Its representing tuples and initial HW bijection are replaced by fresh ones;
the actual group points and their action values remain interalgebraic with the input.
Named consumer: `AclGeom.QWitness.Psi.exists_joint_isMainConclusion`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

This project lemma combines independent configuration base change (`lem:gc-invariance`(2))
with arbitrary-small-field HW base change (`lem:hw-basechange`).

**Status:** proved (#12), consumed by the complete joint Ψ realization.
-/

namespace GroupConfig

open AclGeom IntermediateField Set Germ

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed K] [UniversalDomain k K]
  {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₄]
  {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

/-- Independent finite base extension preserves the actual main conclusion, after choosing
fresh representatives for its two loci and its HW datum of bijections. -/
theorem IsMainConclusion.baseChange_racl {F : IntermediateField k K}
    (hF : IsSmall k (F : Set K)) (h : IsMainConclusion k F a b c x y z)
    {S : Set K} (hS : S.Finite)
    (hind : IndepOver (↥F) ∅ S
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z)) :
    IsMainConclusion k (racl k ((F : Set K) ∪ S)) a b c x y z := by
  obtain ⟨iF, uF, ν, ν', _, _, v, v', f₀, ga, gb, gc, y₀, hb, hga, hgb, -, -, hy₀, -, -,
    hcfg, ha, hb₀, hc, hx, hy, hz, hv, hv', -⟩ := h
  let F₁ := racl k ((F : Set K) ∪ S)
  have hF₁ : IsSmall k (F₁ : Set K) := (hF.union (IsSmall.of_finite hS)).racl
  have i₁ : IsAlgClosed ↥F₁ := isAlgClosed_racl _
  have u₁ : UniversalDomain (↥F₁) K := universalDomain_of_isSmall _ hF₁
  have h₀₁ : F ≤ F₁ := fun t ht ↦ subset_racl k _ (Or.inl ht)
  have hrel : IsSmall (↥F) (F₁ : Set K) := isSmall_coe_of_isSmall F hF₁
  have lift : ∀ {A B : Set K}, racl (↥F) A = racl (↥F) B →
      racl (↥F₁) A = racl (↥F₁) B :=
    fun hAB ↦ racl_eq_of_racl_eq F S hAB
  let P := range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z
  let Q := range ga.codeTuple ∪ range gb.codeTuple ∪ range gc.codeTuple ∪
    range (ga.evalGen y₀) ∪ range y₀ ∪ range (gb.evalGen y₀)
  have hPQ : racl (↥F) P = racl (↥F) Q :=
    racl_union_congr (racl_union_congr (racl_union_congr (racl_union_congr
      (racl_union_congr ha hb₀) hc) hx) hy) hz
  have hSQ : IndepOver (↥F) ∅ S Q := (indepOver_congr₀ rfl hPQ).1 hind
  have fresh : ∀ {A : Set K}, IndepOver (↥F) ∅ S A →
      IndepOver (↥F) ∅ A (F₁ : Set K) := by
    intro A hA
    change IndepOver (↥F) ∅ A (racl k ((F : Set K) ∪ S) : Set K)
    rw [← racl_base_coe F S]
    simpa only [empty_union] using indepOver_racl_right_iff.2 hA.symm
  have hPK : IndepOver (↥F) ∅ P (F₁ : Set K) := fresh hind
  have hQK : IndepOver (↥F) ∅ Q (F₁ : Set K) := fresh hSQ
  have hsub := fun i ↦ GroupConfiguration.gcPoints_subset (a := ga.codeTuple) (b := gb.codeTuple)
    (c := gc.codeTuple) (x := ga.evalGen y₀) (y := y₀) (z := gb.evalGen y₀) i
  have hyK : IndepOver (↥F) ∅ (range y₀) (F₁ : Set K) :=
    hQK.mono_left (hsub 4)
  have hgaK : IndepOver (↥F) ∅ (ga.cb : Set K) (F₁ : Set K) :=
    indepOver_of_subset_racl (cb_subset_racl_codeTuple ga) (subset_racl _ _)
      (hQK.mono_left (hsub 0))
  have hgbK : IndepOver (↥F) ∅ (gb.cb : Set K) (F₁ : Set K) :=
    indepOver_of_subset_racl (cb_subset_racl_codeTuple gb) (subset_racl _ _)
      (hQK.mono_left (hsub 1))
  have hxK : IndepOver (↥F) ∅ (range x) (F₁ : Set K) :=
    hPK.mono_left (GroupConfiguration.gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y)
      (z := z) 3)
  -- Replace the locus representatives and the initial bijection, not the input points.
  obtain ⟨v₁, hv₁, hv₁K⟩ := exists_idealOf_eq_indepOver F F₁ hrel v
  obtain ⟨v₁', hv₁', hv₁'K⟩ := exists_idealOf_eq_indepOver F F₁ hrel v'
  obtain ⟨f₁, hf₁, hf₁K⟩ := exists_mem_orbit_indepOver f₀ hrel
  have hdiff : diffSet f₁ = diffSet f₀ := by
    unfold diffSet
    rw [orbit_eq_of_mem hf₁]
  let B : Germ (↥F₁) v₁ v₁' :=
    (f₁.transport hv₁ hv₁').baseChange F F₁ h₀₁ hrel hv₁K hv₁'K
  let Ga : Germ (↥F₁) v₁ v₁ :=
    (ga.transport hv₁ hv₁).baseChange F F₁ h₀₁ hrel hv₁K hv₁K
  let Gb : Germ (↥F₁) v₁ v₁ :=
    (gb.transport hv₁ hv₁).baseChange F F₁ h₀₁ hrel hv₁K hv₁K
  have hB : IsHWBij B :=
    hb.baseChange_transport F F₁ h₀₁ hrel hv₁ hv₁' hv₁K hv₁'K hf₁ hf₁K
  have hGa : Ga ∈ diffSet B :=
    baseChange_transport_mem_diffSet F F₁ h₀₁ hrel hv₁ hv₁' hv₁K hv₁'K hf₁K
      (by rw [hdiff]; exact hga) hgaK
  have hGb : Gb ∈ diffSet B :=
    baseChange_transport_mem_diffSet F F₁ h₀₁ hrel hv₁ hv₁' hv₁K hv₁'K hf₁K
      (by rw [hdiff]; exact hgb) hgbK
  have code (g : Germ (↥F) v v) :
      racl (↥F₁)
        (range ((g.transport hv₁ hv₁).baseChange F F₁ h₀₁ hrel hv₁K hv₁K).codeTuple) =
      racl (↥F₁) (range g.codeTuple) := by
    rw [racl_codeTuple_baseChange F F₁ h₀₁ hrel hv₁K hv₁K]
    refine lift ?_
    rw [racl_codeTuple, cb_transport, ← racl_codeTuple]
  have hcodeA : racl (↥F₁) (range Ga.codeTuple) =
      racl (↥F₁) (range ga.codeTuple) := code ga
  have hcodeB : racl (↥F₁) (range Gb.codeTuple) =
      racl (↥F₁) (range gb.codeTuple) := code gb
  have hcfg₁ : GroupConfiguration (↥F₁) Ga.codeTuple Gb.codeTuple gc.codeTuple
      (ga.evalGen y₀) y₀ (gb.evalGen y₀) :=
    (GroupConfiguration.baseChange_racl F hcfg hS hSQ).ofRaclEq
      hcodeA hcodeB rfl rfl rfl rfl
  have hy₁ : IsGen (↥F₁) v₁ y₀ :=
    (isGen_base_iff F F₁ h₀₁ hrel hv₁K).2
      ⟨(isGen_iff_of_idealOf_eq hv₁ y₀).2 hy₀, hyK⟩
  have hyGa : IndepOver (↥F₁) ∅ (range y₀) (Ga.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl _ _) (cb_subset_racl_codeTuple Ga)
      hcfg₁.indepOver_ay.symm
  have hyGb : IndepOver (↥F₁) ∅ (range y₀) (Gb.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl _ _) (cb_subset_racl_codeTuple Gb)
      hcfg₁.indepOver_by.symm
  have hGay : Ga.evalGen y₀ = ga.evalGen y₀ := by
    exact (evalGen_baseChange F F₁ h₀₁ hrel hv₁K hv₁K
      (ga.transport hv₁ hv₁) hy₁ hyGa).trans (evalGen_transport hv₁ hv₁ ga y₀)
  have hGby : Gb.evalGen y₀ = gb.evalGen y₀ := by
    exact (evalGen_baseChange F F₁ h₀₁ hrel hv₁K hv₁K
      (gb.transport hv₁ hv₁) hy₁ hyGb).trans (evalGen_transport hv₁ hv₁ gb y₀)
  have hcfg₂ : GroupConfiguration (↥F₁) Ga.codeTuple Gb.codeTuple gc.codeTuple
      (Ga.evalGen y₀) y₀ (Gb.evalGen y₀) := by
    rw [hGay, hGby]
    exact hcfg₁
  -- Regenerate the third group point from the same actual configuration.
  have hw := hB.isHW hGb
  have hGaorb : Ga ∈ orbit Gb := by
    rw [← diffSet_eq_orbit hGb]
    exact hGa
  obtain ⟨Ga', hGa'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hGaorb)
  have ht : IndepTriple (↥F₁) (range Ga.codeTuple) (range Gb.codeTuple) (range y₀) :=
    hcfg₂.indep 0 1 4 (by decide) (by decide) (by decide) (by decide)
  have hind₃ : IndepTriple (↥F₁) (Ga.cb : Set K) (Gb.cb : Set K) (range y₀) :=
    indepTriple_of_racl_eq (racl_codeTuple Ga) (racl_codeTuple Gb) rfl ht
  have hv₁pos : 1 ≤ erk (↥F₁) ∅ (range v₁) := by
    rw [erk_empty_range_eq_of_idealOf_eq hy₁.symm]
    exact hcfg₂.one_le_erk_y
  obtain ⟨hconv, hGcx, hGcGa⟩ := hw.groupConfiguration hGaorb (self_mem_orbit Gb)
    hy₁ hind₃ hv₁pos hGa'
  have hGa'mem : Ga' ∈ diffSet B := inv_mem_diffSet hB.isInvertible hGa hGa'
  have hGbGa' : IndepOver (↥F₁) ∅ (Gb.cb : Set K) (Ga'.cb : Set K) := by
    refine indepOver_of_subset_racl (cb_subset_racl_codeTuple Gb) ?_ hcfg₂.indepOver_ab.symm
    rw [racl_codeTuple]
    exact SetLike.coe_subset_coe.2 hGa'.cb_le
  have hGcmem : Gb * Ga' ∈ diffSet B := hB.mul_mem_diffSet hGb hGa'mem hGbGa'
  have hfa : racl (↥F₁) (range a) = racl (↥F₁) (range Ga.codeTuple) :=
    (lift ha).trans hcodeA.symm
  have hfb : racl (↥F₁) (range b) = racl (↥F₁) (range Gb.codeTuple) :=
    (lift hb₀).trans hcodeB.symm
  have hfc : racl (↥F₁) (range c) = racl (↥F₁) (range (Gb * Ga').codeTuple) :=
    (lift hc).trans (hcfg₂.racl_range_c_eq hconv)
  have hfx : racl (↥F₁) (range x) = racl (↥F₁) (range (Ga.evalGen y₀)) := by
    rw [hGay]
    exact lift hx
  have hfz : racl (↥F₁) (range z) = racl (↥F₁) (range (Gb.evalGen y₀)) := by
    rw [hGby]
    exact lift hz
  have rank_base : ∀ {X : Set K}, X.Finite → IndepOver (↥F) ∅ X (F₁ : Set K) →
      erk (↥F₁) ∅ X = erk (↥F) ∅ X := by
    intro X hX hXK
    rw [erk_base_le F F₁ h₀₁, ← empty_union (F₁ : Set K)]
    exact hXK (subset_refl _) hX
  have hrv : erk (↥F₁) ∅ (range v₁) = erk (↥F₁) ∅ (range x) :=
    (rank_base (finite_range _) hv₁K).trans
      ((erk_empty_range_eq_of_idealOf_eq hv₁).trans
        (hv.trans (rank_base (finite_range _) hxK).symm))
  have hrv' : erk (↥F₁) ∅ (range v₁') = erk (↥F₁) ∅ (range x) :=
    (rank_base (finite_range _) hv₁'K).trans
      ((erk_empty_range_eq_of_idealOf_eq hv₁').trans
        (hv'.trans (rank_base (finite_range _) hxK).symm))
  have hrB : erk (↥F₁) ∅ (B.cb : Set K) = erk (↥F₁) ∅ (range a) :=
    (hB.rank Ga hGa).symm.trans ((erk_eq_of_racl_eq (racl_codeTuple Ga).symm).trans
      (erk_eq_of_racl_eq hfa).symm)
  exact ⟨i₁, u₁, ν, ν', inferInstance, inferInstance, v₁, v₁', B, Ga, Gb, Gb * Ga', y₀,
    hB, hGa, hGb, hGcmem, hGcGa.symm, hy₁, hind₃, hGcx, hconv, hfa, hfb, hfc, hfx,
    lift hy, hfz, hrv, hrv', hrB⟩

end

end GroupConfig
