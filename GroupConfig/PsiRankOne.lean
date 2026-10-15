/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Psi
import GroupConfig.CanonicalBaseCapture
import AclGeom.Geometry.PointTuples

/-!
# The rank-one group configuration of the Ψ partial quadrangle

Clause (vi) of a Ψ witness extends its dependent triple `(S, T, U)` to a partial quadrangle
`(S, T, U, S', T', U')`. In the order `(S, T, U, T', U', S')` its six points form a group
configuration whose group and space points have rank one
(`IsPartialQuadrangle.groupConfiguration`). The group configuration theorem then gives
Hrushovski–Weil data over `acl(k, E)` for a finite set `E` of rank five independent from the
six points (`QWitness.Psi.exists_rankOne_isMainConclusion`).

This is a statement about a group of germs up to interalgebraicity. The algebraic group of the
blueprint's `thm:six-point-group`, the homomorphism `π`, the normal subgroup `N` and descent to
the original fields remain obligations.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#12).
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

/-! ### Points as one-element tuples -/

private theorem erk_point (P : Point k K) : erk k ∅ (range (fun _ : Fin 1 ↦ P.rep)) = 1 := by
  simpa using ClosedIF.erk_eq_of_racl_eq (Point.racl_repTuple P) P.rankEq_one

/-- A point lies below a different point only if they are equal. -/
private theorem not_le_of_ne {P Q : Point k K} (h : P ≠ Q) : ¬ Q.1 ≤ P.1 := fun hle ↦
  h (Subtype.ext ((P.2.le_iff.1 hle).resolve_left Q.2.1).symm)

/-- On a dependent triple of distinct points, any two of them span the line. -/
private theorem line_eq {P Q R : Point k K} (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (h : RankEq 2 (P.1 ⊔ (Q.1 ⊔ R.1))) :
    P.1 ⊔ Q.1 = P.1 ⊔ (Q.1 ⊔ R.1) ∧ P.1 ⊔ R.1 = P.1 ⊔ (Q.1 ⊔ R.1) ∧
      Q.1 ⊔ R.1 = P.1 ⊔ (Q.1 ⊔ R.1) :=
  ⟨RankEq.eq_of_le (sup_le_sup_left le_sup_left _)
      (P.rankEq_one.sup_point_of_not_le (not_le_of_ne hPQ)) h,
    RankEq.eq_of_le (sup_le_sup_left le_sup_right _)
      (P.rankEq_one.sup_point_of_not_le (not_le_of_ne hPR)) h,
    RankEq.eq_of_le le_sup_right (Q.rankEq_one.sup_point_of_not_le (not_le_of_ne hQR)) h⟩

/-! ### Canonical bases on a line -/

/-- On a line `P, Q, R` with `Q ≠ R`, the point `P` is algebraic over the canonical base of
`(Q, R)` over `P`. -/
private theorem subset_racl_canonicalBase_of_line [IsAlgClosed K] [UniversalDomain k K]
    {P Q R : Point k K} (hQR : Q ≠ R) (hR : R.1 ≤ P.1 ⊔ Q.1) :
    range (fun _ : Fin 1 ↦ P.rep) ⊆ racl k (canonicalBase (racl k (range (fun _ : Fin 1 ↦ P.rep)))
      (Sum.elim (fun _ : Fin 1 ↦ Q.rep) (fun _ : Fin 1 ↦ R.rep)) : Set K) := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = racl k (range (fun _ : Fin 1 ↦ P.rep)) := ⟨_, rfl⟩
  rw [← hMdef]
  have _ : IsAlgClosed ↥M := hMdef ▸ isAlgClosed_racl _
  have hM : IsSmall k (M : Set K) := hMdef ▸ (IsSmall.of_finite (finite_range _)).racl
  have hMP : M = P.1.1 := hMdef.trans (Point.racl_repTuple P)
  have hMr : racl k (M : Set K) = P.1.1 := by
    rw [hMdef]
    exact (isRAC_iff_racl_eq.1 (isRAC_racl _)).trans (Point.racl_repTuple P)
  have hb : range (fun _ : Fin 1 ↦ R.rep) ⊆
      racl k ((M : Set K) ∪ range (fun _ : Fin 1 ↦ Q.rep)) := by
    rw [ClosedIF.racl_union_eq_sup hMr (Point.racl_repTuple Q)]
    rintro _ ⟨_, rfl⟩
    exact hR R.mem_rep
  have hcap := GroupConfig.range_subset_racl_canonicalBase M hM (fun _ : Fin 1 ↦ Q.rep)
    (fun _ : Fin 1 ↦ R.rep) hb
  let cb := canonicalBase M (Sum.elim (fun _ : Fin 1 ↦ Q.rep) (fun _ : Fin 1 ↦ R.rep))
  let C : ClosedIF k K := ⟨racl k (cb : Set K), isRAC_racl _⟩
  have hCP : C ≤ P.1 := by
    rw [ClosedIF.le_iff, ← hMP]
    exact racl_le_of_isAlgClosed (canonicalBase_le M _)
  rcases P.2.le_iff.1 hCP with hC | hC
  · -- A canonical base inside the base field would put `R` below `Q`.
    exfalso
    have hcbQ : (cb : Set K) ⊆ racl k (range (fun _ : Fin 1 ↦ Q.rep)) := by
      intro x hx
      have hxC : x ∈ C := subset_racl k _ hx
      have hCQ : C ≤ Q.1 := hC ▸ bot_le
      rw [Point.racl_repTuple Q]
      exact hCQ hxC
    have hle : racl k ((cb : Set K) ∪ range (fun _ : Fin 1 ↦ Q.rep)) ≤
        racl k (range (fun _ : Fin 1 ↦ Q.rep)) :=
      racl_le_of_subset_racl (union_subset hcbQ (subset_racl k _))
    have hRQ : R.rep ∈ Q.1.1 := by
      rw [← Point.racl_repTuple Q]
      exact hle (hcap ⟨0, rfl⟩)
    apply not_le_of_ne hQR
    rw [← R.point_rep]
    exact ClosedIF.point_le_iff.2 hRQ
  · rintro _ ⟨_, rfl⟩
    have hPC : P.rep ∈ C := hC ▸ P.mem_rep
    exact hPC

/-! ### The group configuration -/

/-- The partial-quadrangle index of each group-configuration index, in the order
`(S, T, U, T', U', S')`. -/
private def quadIdx : Fin 6 → Fin 6 := ![0, 1, 2, 4, 5, 3]

private theorem quadIdx_triple : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l → ¬ GCCollinear i j l →
    ({quadIdx i, quadIdx j, quadIdx l} : Finset (Fin 6)).card = 3 ∧
      ({quadIdx i, quadIdx j, quadIdx l} : Finset (Fin 6)) ∉ quadTriples := by
  decide

/-- **The partial quadrangle is a group configuration of rank one.** In the order
`(S, T, U, T', U', S')`, the six points of a partial quadrangle form a group configuration
whose points have rank one. -/
theorem IsPartialQuadrangle.groupConfiguration [IsAlgClosed K] [UniversalDomain k K]
    {f : Fin 6 → Point k K} (h : IsPartialQuadrangle f) :
    GroupConfiguration k (fun _ : Fin 1 ↦ (f 0).rep) (fun _ : Fin 1 ↦ (f 1).rep)
      (fun _ : Fin 1 ↦ (f 2).rep) (fun _ : Fin 1 ↦ (f 4).rep) (fun _ : Fin 1 ↦ (f 5).rep)
      (fun _ : Fin 1 ↦ (f 3).rep) := by
  have hne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j hij ↦ h.injective.ne hij
  have l₁ := line_eq (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    h.rank_STU
  have l₂ := line_eq (hne 0 4 (by decide)) (hne 0 5 (by decide)) (hne 4 5 (by decide))
    h.rank_STU'
  have l₃ := line_eq (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide))
    h.rank_S'TU'
  have l₄ := line_eq (hne 2 3 (by decide)) (hne 2 4 (by decide)) (hne 3 4 (by decide))
    h.rank_S'T'U
  have hsup : ∀ i j : Fin 6, racl k (range (fun _ : Fin 1 ↦ (f i).rep) ∪
      range (fun _ : Fin 1 ↦ (f j).rep)) = ((f i).1 ⊔ (f j).1).1 :=
    fun i j ↦ ClosedIF.racl_union_eq_sup (Point.racl_repTuple _) (Point.racl_repTuple _)
  have hg : ∀ m : Fin 6, gcPoints (fun _ : Fin 1 ↦ (f 0).rep) (fun _ : Fin 1 ↦ (f 1).rep)
      (fun _ : Fin 1 ↦ (f 2).rep) (fun _ : Fin 1 ↦ (f 4).rep) (fun _ : Fin 1 ↦ (f 5).rep)
      (fun _ : Fin 1 ↦ (f 3).rep) m = range (fun _ : Fin 1 ↦ (f (quadIdx m)).rep) := by
    intro m
    fin_cases m <;> rfl
  refine
    { racl_ab_ac := by rw [hsup, hsup, l₁.1, l₁.2.1]
      racl_ab_bc := by rw [hsup, hsup, l₁.2.2, l₁.1]
      racl_ax_ay := by rw [hsup, hsup, l₂.1, l₂.2.1]
      racl_by_bz := by rw [hsup, hsup, l₃.2.1, l₃.1]
      racl_cx_cz := by rw [hsup, hsup, l₄.2.1, l₄.1]
      indep := ?_
      cb_a := subset_racl_canonicalBase_of_line (hne 4 5 (by decide))
        (by rw [l₂.1]; exact le_sup_right.trans le_sup_right)
      cb_b := subset_racl_canonicalBase_of_line (hne 5 3 (by decide))
        (by rw [l₃.2.1]; exact (le_sup_left.trans le_sup_right))
      cb_c := subset_racl_canonicalBase_of_line (hne 4 3 (by decide))
        (by rw [l₄.2.1]; exact (le_sup_left.trans le_sup_right))
      one_le_erk := by rw [erk_point] }
  intro i j l hij hil hjl hcol
  obtain ⟨hcard, hnot⟩ := quadIdx_triple i j l hij hil hjl hcol
  have hr := h.rank_free _ hcard hnot
  rw [hg, hg, hg]
  unfold IndepTriple
  rw [erk_point, erk_point, erk_point]
  have hracl : racl k (range (fun _ : Fin 1 ↦ (f (quadIdx i)).rep) ∪
      range (fun _ : Fin 1 ↦ (f (quadIdx j)).rep) ∪
      range (fun _ : Fin 1 ↦ (f (quadIdx l)).rep)) =
      (({quadIdx i, quadIdx j, quadIdx l} : Finset (Fin 6)).sup fun m ↦ (f m).1).1 := by
    rw [ClosedIF.racl_union_eq_sup
        (ClosedIF.racl_union_eq_sup (Point.racl_repTuple _) (Point.racl_repTuple _))
        (Point.racl_repTuple _),
      Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton, sup_assoc]
  rw [ClosedIF.erk_eq_of_racl_eq hracl hr]
  norm_num

/-! ### The rank-one Hrushovski–Weil group -/

/-- **A rank-one group of germs from the Ψ partial quadrangle.** For a Ψ witness, the partial
quadrangle of clause (vi) is realized, over `acl(k, E)` for a finite set `E` of rank five
independent from its six points, by Hrushovski–Weil data. Over `acl(k, E)` its group point `S`
and its space point `T'` still have rank one. -/
theorem QWitness.Psi.exists_rankOne_isMainConclusion [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] {w : QWitness k K} (hw : w.Psi) :
    ∃ S' T' U' : Point k K, IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U'] ∧
      ∃ E : Set K, E.Finite ∧ erk k ∅ E = 5 ∧
        IndepOver k ∅ E (range (fun _ : Fin 1 ↦ w.S.rep) ∪ range (fun _ : Fin 1 ↦ w.T.rep) ∪
          range (fun _ : Fin 1 ↦ w.U.rep) ∪ range (fun _ : Fin 1 ↦ T'.rep) ∪
          range (fun _ : Fin 1 ↦ U'.rep) ∪ range (fun _ : Fin 1 ↦ S'.rep)) ∧
        IsMainConclusion k (racl k E) (fun _ : Fin 1 ↦ w.S.rep) (fun _ : Fin 1 ↦ w.T.rep)
          (fun _ : Fin 1 ↦ w.U.rep) (fun _ : Fin 1 ↦ T'.rep) (fun _ : Fin 1 ↦ U'.rep)
          (fun _ : Fin 1 ↦ S'.rep) ∧
        erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) = 1 ∧
        erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ T'.rep)) = 1 := by
  obtain ⟨S', T', U', hq⟩ := hw.quad
  obtain ⟨E, hEfin, hErank, hEind, hmain⟩ :=
    hq.groupConfiguration.exists_main_with_parameterRank
  refine ⟨S', T', U', hq, E, hEfin, ?_, hEind, hmain, ?_, ?_⟩
  · rw [hErank]
    change 5 * erk k ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) = 5
    rw [erk_point]
    norm_num
  · have h1 : erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) =
        erk k ∅ (range (fun _ : Fin 1 ↦ w.S.rep)) := by
      rw [erk_base_empty, erk_racl_base]
      have := hEind.symm (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
        (finite_range _)
      rwa [empty_union] at this
    rw [h1, erk_point]
  · have h1 : erk (↥(racl k E)) ∅ (range (fun _ : Fin 1 ↦ T'.rep)) =
        erk k ∅ (range (fun _ : Fin 1 ↦ T'.rep)) := by
      rw [erk_base_empty, erk_racl_base]
      have := hEind.symm (fun _ h ↦ Or.inl (Or.inl (Or.inr h))) (finite_range _)
      rwa [empty_union] at this
    rw [h1, erk_point]

end

end AclGeom
