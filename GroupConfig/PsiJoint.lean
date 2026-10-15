/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.PsiFresh
import GroupConfig.MainBaseChange

/-!
# Both actual Ψ configurations over one fresh base

The two finite parameter sets have ranks five and ten,
their union has rank fifteen, and both actual main conclusions hold over its relative closure.
The original algebraic groups, homomorphism, normal subgroup and descent remain obligations.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved (#12), from full Ψ with genuine ACF/universal-domain hypotheses.
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

/-- The rank-two Ψ configuration and its rank-one partial quadrangle admit actual main data
over the same finite independent extension, with all four input ranks preserved. -/
theorem QWitness.Psi.exists_joint_isMainConclusion [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] {w : QWitness k K} (hw : w.Psi) {W : Set K} (hW : W.Finite) :
    ∃ S' T' U' : Point k K, IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'] ∧
      ∃ E₁ E₂ : Set K, E₁.Finite ∧ E₂.Finite ∧ erk k ∅ E₁ = 5 ∧ erk k ∅ E₂ = 10 ∧
        erk k ∅ (E₁ ∪ E₂) = 15 ∧
        IndepOver k ∅ (E₁ ∪ E₂) (range w.repTuple ∪ range ![S'.rep, T'.rep, U'.rep] ∪ W) ∧
        IsMainConclusion k (racl k (E₁ ∪ E₂))
          w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple ∧
        IsMainConclusion k (racl k (E₁ ∪ E₂)) (fun _ : Fin 1 ↦ w.S.rep)
          (fun _ : Fin 1 ↦ w.T.rep) (fun _ : Fin 1 ↦ w.U.rep) (fun _ : Fin 1 ↦ T'.rep)
          (fun _ : Fin 1 ↦ U'.rep) (fun _ : Fin 1 ↦ S'.rep) ∧
        erk (↥(racl k (E₁ ∪ E₂))) ∅ (range w.aTuple) = 2 ∧
        erk (↥(racl k (E₁ ∪ E₂))) ∅ (range w.xTuple) = 1 ∧
        erk (↥(racl k (E₁ ∪ E₂))) ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) = 1 ∧
        erk (↥(racl k (E₁ ∪ E₂))) ∅ (range (fun _ : Fin 1 ↦ T'.rep)) = 1 := by
  obtain ⟨S', T', U', hquad, E₁, hE₁fin, hE₁rank, hE₁ind, hmain₁, -, -⟩ :=
    hw.exists_rankOne_isMainConclusion_fresh hW
  obtain ⟨E₂, hE₂fin, hE₂rank, hE₂ind, hmain₂, -, -⟩ :=
    hw.toCore.exists_isMainConclusion_fresh
      (((finite_range ![S'.rep, T'.rep, U'.rep]).union hW).union hE₁fin)
  let R := range w.repTuple ∪ range ![S'.rep, T'.rep, U'.rep] ∪ W
  let P := range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪
    range w.yTuple ∪ range w.zTuple
  let Q := range (fun _ : Fin 1 ↦ w.S.rep) ∪ range (fun _ : Fin 1 ↦ w.T.rep) ∪
    range (fun _ : Fin 1 ↦ w.U.rep) ∪ range (fun _ : Fin 1 ↦ T'.rep) ∪
    range (fun _ : Fin 1 ↦ U'.rep) ∪ range (fun _ : Fin 1 ↦ S'.rep)
  have hE₂ : IndepOver k ∅ E₂ (R ∪ E₁) := by
    simpa only [R, union_assoc] using hE₂ind
  have hE₂E₁ : IndepOver k ∅ E₂ E₁ := hE₂.mono_right subset_union_right
  have hrel : IndepOver k E₁ R E₂ := by
    have ht : IndepOver k ∅ E₂ (E₁ ∪ R) := by
      rw [union_comm E₁ R]
      exact hE₂
    simpa only [empty_union] using (indepOver_union_right_iff.1 ht).2.symm
  have hJ : IndepOver k ∅ (E₁ ∪ E₂) R := by
    exact (indepOver_union_right_iff.2
      ⟨hE₁ind.symm, by simpa only [empty_union] using hrel⟩).symm
  have hPRep : P ⊆ range w.repTuple := by
    refine union_subset (union_subset (union_subset (union_subset
      (union_subset ?_ ?_) ?_) ?_) ?_) ?_
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [⟨2, rfl⟩, ⟨3, rfl⟩]
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [⟨4, rfl⟩, ⟨5, rfl⟩]
    · rintro _ ⟨_, rfl⟩
      exact ⟨18, rfl⟩
    · rintro _ ⟨_, rfl⟩
      exact ⟨19, rfl⟩
    · rintro _ ⟨_, rfl⟩
      exact ⟨20, rfl⟩
  have hP : P ⊆ R := hPRep.trans (subset_union_left.trans subset_union_left)
  have hQ : Q ⊆ R := by
    refine union_subset (union_subset (union_subset (union_subset
      (union_subset ?_ ?_) ?_) ?_) ?_) ?_
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inl ⟨15, rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inl ⟨16, rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inl ⟨17, rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inr ⟨1, rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inr ⟨2, rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact Or.inl (Or.inr ⟨0, rfl⟩)
  have hind₁ : IndepOver (↥(racl k E₁)) ∅ E₂ Q := by
    apply (indepOver_base_iff (racl k E₁) E₂ Q).2
    apply (indepOver_racl_base_iff E₁ E₂ Q).2
    exact hrel.symm.mono_right hQ
  have hind₂ : IndepOver (↥(racl k E₂)) ∅ E₁ P := by
    apply (indepOver_base_iff (racl k E₂) E₁ P).2
    apply (indepOver_racl_base_iff E₂ E₁ P).2
    have ht : IndepOver k ∅ R (E₂ ∪ E₁) := by
      rw [union_comm E₂ E₁]
      exact hJ.symm
    have ht' : IndepOver k E₂ R E₁ := by
      simpa only [empty_union] using (indepOver_union_right_iff.1 ht).2
    exact ht'.symm.mono_right hP
  have hm₁ := IsMainConclusion.baseChange_racl (IsSmall.of_finite hE₁fin).racl
    hmain₁ hE₂fin hind₁
  have hm₂ := IsMainConclusion.baseChange_racl (IsSmall.of_finite hE₂fin).racl
    hmain₂ hE₁fin hind₂
  rw [racl_union_left] at hm₁ hm₂
  rw [union_comm E₂ E₁] at hm₂
  have keep : ∀ {X : Set K}, X ⊆ R → X.Finite →
      erk (↥(racl k (E₁ ∪ E₂))) ∅ X = erk k ∅ X := by
    intro X hX hXfin
    rw [erk_base_empty, erk_racl_base]
    have ht := hJ.symm hX hXfin
    rwa [empty_union] at ht
  have hsubP := fun i ↦ GroupConfiguration.gcPoints_subset (a := w.aTuple) (b := w.bTuple)
    (c := w.cTuple) (x := w.xTuple) (y := w.yTuple) (z := w.zTuple) i
  have hsubQ := fun i ↦ GroupConfiguration.gcPoints_subset (a := fun _ : Fin 1 ↦ w.S.rep)
    (b := fun _ : Fin 1 ↦ w.T.rep) (c := fun _ : Fin 1 ↦ w.U.rep)
    (x := fun _ : Fin 1 ↦ T'.rep) (y := fun _ : Fin 1 ↦ U'.rep)
    (z := fun _ : Fin 1 ↦ S'.rep) i
  refine ⟨S', T', U', hquad, E₁, E₂, hE₁fin, hE₂fin, hE₁rank, hE₂rank, ?_, hJ,
    hm₂, hm₁, ?_, ?_, ?_, ?_⟩
  · have hr : erk k E₁ E₂ = 10 := by
      have ht := hE₂E₁ (subset_refl _) hE₂fin
      rw [empty_union] at ht
      exact ht.trans hE₂rank
    rw [erk_union_eq, empty_union, hE₁rank, hr]
    norm_num
  · rw [keep (X := range w.aTuple) ((hsubP 0).trans hP) (finite_range _)]
    exact hw.toCore.groupConfiguration_with_ranks.2.1
  · rw [keep (X := range w.xTuple) ((hsubP 3).trans hP) (finite_range _)]
    exact hw.toCore.groupConfiguration_with_ranks.2.2
  · rw [keep (X := range (fun _ : Fin 1 ↦ w.S.rep)) ((hsubQ 0).trans hQ) (finite_range _)]
    simpa using ClosedIF.erk_eq_of_racl_eq (Point.racl_repTuple w.S) w.S.rankEq_one
  · rw [keep (X := range (fun _ : Fin 1 ↦ T'.rep)) ((hsubQ 3).trans hQ) (finite_range _)]
    simpa using ClosedIF.erk_eq_of_racl_eq (Point.racl_repTuple T') T'.rankEq_one

end

end AclGeom
