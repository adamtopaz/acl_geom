/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.PsiRankOne

/-!
# Fresh parameters for the Ψ group configurations

The group configuration theorem chooses its finite parameter set `E` independent from any
prescribed finite set `W` as well as from the configuration
(`GroupConfig.GroupConfiguration.exists_main_fresh_with_parameterRank`). For a Ψ witness `w`
this applies to both of its group configurations, with `E` independent from the representatives
of all twenty-one points of `w` (`QWitness.repTuple`) and from `W`:

* the rank-two configuration of clauses (i)–(iv), with `E` of rank ten
  (`QWitness.PsiCore.exists_isMainConclusion_fresh`);
* the rank-one configuration of the partial quadrangle of clause (vi), with `E` of rank five and
  also independent from the three new points of the quadrangle
  (`QWitness.Psi.exists_rankOne_isMainConclusion_fresh`).

Over `acl(k, E)` the group and space points keep their ranks. Realizing both configurations over
one common base field, the homomorphism `π`, the normal subgroup `N` and descent to the original
fields remain obligations.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#12).
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

namespace QWitness

/-- The representatives of the twenty-one points of a `Q`-configuration witness, in the order of
the fields of `QWitness`. -/
def repTuple (w : QWitness k K) : Fin 21 → K :=
  ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep, w.C₁.rep, w.C₂.rep, w.D.rep, w.E.rep, w.F.rep,
    w.G.rep, w.H.rep, w.I.rep, w.P.rep, w.Q.rep, w.R.rep, w.S.rep, w.T.rep, w.U.rep, w.X.rep,
    w.Y.rep, w.Z.rep]

variable {w : QWitness k K}

/-- `cor:psi` with fresh parameters: for a Ψ witness, the conclusion of the group configuration
theorem holds over `acl(k, E)` for a finite set `E` of rank ten independent from all
representatives of the witness and from a prescribed finite set `W`, with a group of germs of
rank two acting on a curve. -/
theorem PsiCore.exists_isMainConclusion_fresh [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] (hw : w.PsiCore) {W : Set K} (hW : W.Finite) :
    ∃ E : Set K, E.Finite ∧ erk k ∅ E = 10 ∧ IndepOver k ∅ E (range w.repTuple ∪ W) ∧
      IsMainConclusion k (racl k E) w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple ∧
      erk (↥(racl k E)) ∅ (range w.aTuple) = 2 ∧ erk (↥(racl k E)) ∅ (range w.xTuple) = 1 := by
  obtain ⟨hc, ha, hx⟩ := hw.groupConfiguration_with_ranks
  obtain ⟨E, hEfin, hErank, hEind, hmain⟩ :=
    hc.exists_main_fresh_with_parameterRank ((finite_range w.repTuple).union hW)
  /- Ranks of the witness points do not change over `acl(k, E)`. -/
  have hrk : ∀ {X : Set K}, X ⊆ range w.repTuple → erk (↥(racl k E)) ∅ X = erk k ∅ X :=
    fun hX ↦ by
      rw [erk_base_empty, erk_racl_base]
      have := hEind.symm (hX.trans (subset_union_left.trans subset_union_right))
        ((finite_range _).subset hX)
      rwa [empty_union] at this
  have hA : range w.aTuple ⊆ range w.repTuple := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  have hX : range w.xTuple ⊆ range w.repTuple := by
    rintro _ ⟨_, rfl⟩
    exact ⟨18, rfl⟩
  refine ⟨E, hEfin, ?_, hEind.mono_right subset_union_right, hmain, ?_, ?_⟩
  · rw [hErank, ha]
    norm_num
  · rw [hrk hA, ha]
  · rw [hrk hX, hx]

/-- **A rank-one group of germs from the Ψ partial quadrangle, with fresh parameters.** For a Ψ
witness, the partial quadrangle of clause (vi) is realized, over `acl(k, E)` for a finite set
`E` of rank five independent from all representatives of the witness, from the three new points
of the quadrangle and from a prescribed finite set `W`, by Hrushovski–Weil data. Over
`acl(k, E)` its group point `S` and its space point `T'` still have rank one. -/
theorem Psi.exists_rankOne_isMainConclusion_fresh [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] (hw : w.Psi) {W : Set K} (hW : W.Finite) :
    ∃ S' T' U' : Point k K, IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'] ∧
      ∃ E : Set K, E.Finite ∧ erk k ∅ E = 5 ∧
        IndepOver k ∅ E (range w.repTuple ∪ range ![S'.rep, T'.rep, U'.rep] ∪ W) ∧
        IsMainConclusion k (racl k E) (fun _ : Fin 1 ↦ w.S.rep) (fun _ : Fin 1 ↦ w.T.rep)
          (fun _ : Fin 1 ↦ w.U.rep) (fun _ : Fin 1 ↦ T'.rep) (fun _ : Fin 1 ↦ U'.rep)
          (fun _ : Fin 1 ↦ S'.rep) ∧
        erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) = 1 ∧
        erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ T'.rep)) = 1 := by
  obtain ⟨S', T', U', hq⟩ := hw.quad
  obtain ⟨E, hEfin, hErank, hEind, hmain⟩ :=
    hq.groupConfiguration.exists_main_fresh_with_parameterRank
      (((finite_range w.repTuple).union (finite_range ![S'.rep, T'.rep, U'.rep])).union hW)
  have hpt : ∀ P : Point k K, erk k ∅ (range (fun _ : Fin 1 ↦ P.rep)) = 1 := fun P ↦ by
    simpa using ClosedIF.erk_eq_of_racl_eq (Point.racl_repTuple P) P.rankEq_one
  refine ⟨S', T', U', hq, E, hEfin, ?_, hEind.mono_right subset_union_right, hmain, ?_, ?_⟩
  · rw [hErank]
    change 5 * erk k ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) = 5
    rw [hpt]
    norm_num
  · have h1 : erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) =
        erk k ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) := by
      rw [erk_base_empty, erk_racl_base]
      have := hEind.symm (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
        (finite_range _)
      rwa [empty_union] at this
    rw [h1, hpt]
  · have h1 : erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ T'.rep)) =
        erk k ∅ (range (fun _ : Fin 1 ↦ T'.rep)) := by
      rw [erk_base_empty, erk_racl_base]
      have := hEind.symm (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inr h)))) (finite_range _)
      rwa [empty_union] at this
    rw [h1, hpt]

end QWitness

end

end AclGeom
