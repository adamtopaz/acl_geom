/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Psi

/-!
# Lattice consequences of `Psi` under the ratio guard

The meet-elimination part of the corrected blueprint Lemma `affine-grid-extraction` (#27)
starts from incidences that EH95 Corollary 3.4 assumes ("`P, Q, R` points of `A, B, C`") but
the blueprint's `Psi` omits.  They follow from `Psi` by rank counting alone, with no
coordinates. Here the ratio guard is `I ≠ D`. The first four incidence consequences are:

* `QWitness.Psi.P_le_A`: `P ≤ A`, under the guard;
* `QWitness.Psi.P_ne_S`: `P ≠ S`, which needs no guard;
* `QWitness.Psi.Q_le_B`: `Q ≤ B`, which needs no guard either;
* `QWitness.Psi.Q_ne_T`: `Q ≠ T`, under the guard.

Three further necessary consequences use `I ≠ D`:
* `QWitness.Psi.D_not_le_ABC`: `D ≰ A ∨ B ∨ C`;
* `QWitness.Psi.D_ne_S`: `D ≠ S`, supplying the difference-cocycle non-membership;
* `QWitness.Psi.F_ne_U`: `F ≠ U`, for the proposed multiplier-curve argument.

They construct no relocation, curve action or linearity.

The guard is necessary for `Q ≠ T`: the degenerate witness of `Counterexamples.QDegenerate`
satisfies `Psi` with `Q = T`. A hand-checked, unformalized degenerate witness with
`P ≤ S ∨ Y` and `I = D = S` (#27; not accepted) indicates that the guard is also needed
for `P ≤ A`.

The proofs use a small rank calculus in the algebraic-independence matroid: submodularity of
the rank of closed elements, the resulting meet computation `inf_eq_of_rankEq`, the rank of
a join with a new point, and exchange of points across a closed element of finite rank.

**Status:** necessary lattice consequences proved (#27, L0/L0b). Meet elimination, guarded
extraction/completeness and group/action classification remain open; frozen M4a is unused.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section RankCalculus

/-- Bookkeeping in `ℕ∞`: `r + a ≤ b` gives `r ≤ b - a`. -/
private theorem enat_le_sub_of_add_le {r : ℕ∞} {a b : ℕ} (h : r + a ≤ b) :
    r ≤ ((b - a : ℕ) : ℕ∞) := by
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, (r' : ℕ∞) = r := by
    refine ENat.ne_top_iff_exists.1 fun hr ↦ ?_
    rw [hr, top_add, top_le_iff] at h
    exact ENat.natCast_ne_top b h
  norm_cast at h ⊢
  omega

/-- A point is not below the bottom. -/
private theorem Point.not_le_bot (P : Point k K) : ¬ P.1 ≤ ⊥ :=
  fun h ↦ P.2.1 (le_bot_iff.1 h)

/-- Comparable points are equal. -/
private theorem Point.eq_of_le {P Q : Point k K} (h : P.1 ≤ Q.1) : P = Q :=
  Subtype.ext ((Q.2.le_iff_eq P.2.1).1 h)

/-- A point has rank one. -/
private theorem Point.rankEq_one (P : Point k K) : RankEq 1 P.1 := by
  have hind : AlgebraicIndependent k ![P.rep] := by
    rw [algebraicIndependent_unique_type_iff]
    intro halg
    exact P.rep_notMem_bot (ClosedIF.mem_bot_iff.2 halg)
  refine (rankEq_iSup_point hind).congr ?_
  rw [iSup_unique]
  exact P.point_rep

/-- The bottom has rank zero. -/
private theorem rankEq_zero_bot : RankEq 0 (⊥ : ClosedIF k K) :=
  ⟨Fin.elim0, fun i ↦ i.elim0, (iSup_of_empty _).symm⟩

/-- The rank of a join is at most the rank of the union of the two closed elements. -/
private theorem eRk_sup_le_eRk_union (E F : ClosedIF k K) :
    (AlgebraicIndependent.matroid k K).eRk ((E ⊔ F : ClosedIF k K) : Set K) ≤
      (AlgebraicIndependent.matroid k K).eRk ((E : Set K) ∪ (F : Set K)) := by
  have hsub : ((E ⊔ F : ClosedIF k K) : Set K) ⊆
      (AlgebraicIndependent.matroid k K).closure ((E : Set K) ∪ (F : Set K)) := by
    intro x hx
    rw [algebraicMatroid_closure_eq_racl]
    exact ClosedIF.mem_sup_iff.1 hx
  exact ((AlgebraicIndependent.matroid k K).eRk_mono hsub).trans
    ((AlgebraicIndependent.matroid k K).eRk_closure_eq _).le

/-- Rank is subadditive on joins. -/
private theorem eRk_sup_le (E F : ClosedIF k K) :
    (AlgebraicIndependent.matroid k K).eRk ((E ⊔ F : ClosedIF k K) : Set K) ≤
      (AlgebraicIndependent.matroid k K).eRk (E : Set K) +
        (AlgebraicIndependent.matroid k K).eRk (F : Set K) :=
  (eRk_sup_le_eRk_union E F).trans
    ((AlgebraicIndependent.matroid k K).eRk_union_le_eRk_add_eRk _ _)

/-- Submodularity of rank on closed elements. -/
private theorem eRk_inf_add_eRk_sup_le (E F : ClosedIF k K) :
    (AlgebraicIndependent.matroid k K).eRk ((E ⊓ F : ClosedIF k K) : Set K) +
        (AlgebraicIndependent.matroid k K).eRk ((E ⊔ F : ClosedIF k K) : Set K) ≤
      (AlgebraicIndependent.matroid k K).eRk (E : Set K) +
        (AlgebraicIndependent.matroid k K).eRk (F : Set K) := by
  have hinf : ((E ⊓ F : ClosedIF k K) : Set K) = (E : Set K) ∩ (F : Set K) := by
    ext x
    exact ClosedIF.mem_inf_iff
  rw [hinf]
  have hsub := (AlgebraicIndependent.matroid k K).eRk_inter_add_eRk_union_le
    (E : Set K) (F : Set K)
  exact (add_le_add_right (eRk_sup_le_eRk_union E F)
    ((AlgebraicIndependent.matroid k K).eRk ((E : Set K) ∩ (F : Set K)))).trans hsub

/-- **Meets by rank counting**: if `rk E + rk F = rk (E ⊔ F) + i` and `G ≤ E ⊓ F` has rank
`i`, then `E ⊓ F = G`. -/
private theorem inf_eq_of_rankEq {m n j i : ℕ} {E F G : ClosedIF k K} (hE : RankEq m E)
    (hF : RankEq n F) (hEF : RankEq j (E ⊔ F)) (hmn : m + n = j + i) (hG : RankEq i G)
    (hGle : G ≤ E ⊓ F) : E ⊓ F = G := by
  have h := eRk_inf_add_eRk_sup_le E F
  rw [rankEq_iff_eRk.1 hE, rankEq_iff_eRk.1 hF, rankEq_iff_eRk.1 hEF, ← Nat.cast_add,
    hmn] at h
  have hle : (AlgebraicIndependent.matroid k K).eRk ((E ⊓ F : ClosedIF k K) : Set K) ≤ i := by
    have h' := enat_le_sub_of_add_le h
    rwa [Nat.add_sub_cancel_left] at h'
  have hge : (i : ℕ∞) ≤
      (AlgebraicIndependent.matroid k K).eRk ((E ⊓ F : ClosedIF k K) : Set K) := by
    rw [← rankEq_iff_eRk.1 hG]
    exact (AlgebraicIndependent.matroid k K).eRk_mono
      (hGle : (G : Set K) ⊆ ((E ⊓ F : ClosedIF k K) : Set K))
  exact (RankEq.eq_of_le hGle hG (rankEq_iff_eRk.2 (le_antisymm hle hge))).symm

/-- Adding a point outside a closed element of rank `m` gives rank `m + 1`. -/
private theorem rankEq_sup_point_of_not_le {m : ℕ} {E : ClosedIF k K} (hE : RankEq m E)
    {P : Point k K} (hP : ¬ P.1 ≤ E) : RankEq (m + 1) (E ⊔ P.1) := by
  have hEr := rankEq_iff_eRk.1 hE
  have hPr := rankEq_iff_eRk.1 (Point.rankEq_one P)
  have hrep : P.rep ∉ (AlgebraicIndependent.matroid k K).closure (E : Set K) := by
    rw [algebraicMatroid_closure_eq_racl]
    intro hmem
    apply hP
    rw [← P.point_rep]
    exact ClosedIF.point_le_iff.2 ((isRAC_iff_racl_eq.1 E.2).le hmem)
  have hsub : insert P.rep (E : Set K) ⊆ ((E ⊔ P.1 : ClosedIF k K) : Set K) := by
    intro x hx
    rcases hx with rfl | hx
    · exact (le_sup_right : P.1 ≤ E ⊔ P.1) P.mem_rep
    · exact (le_sup_left : E ≤ E ⊔ P.1) hx
  have hlow : (AlgebraicIndependent.matroid k K).eRk (insert P.rep (E : Set K)) =
      (m : ℕ∞) + 1 := by
    rw [Matroid.eRk_insert_eq_add_one (M := AlgebraicIndependent.matroid k K)
      (X := (E : Set K)) (e := P.rep) ((Set.mem_sdiff P.rep).2 ⟨by simp, hrep⟩), hEr]
  have hup : (AlgebraicIndependent.matroid k K).eRk ((E ⊔ P.1 : ClosedIF k K) : Set K) ≤
      (m : ℕ∞) + 1 := by
    have h := eRk_sup_le E P.1
    rwa [hEr, hPr, Nat.cast_one] at h
  have hge : (m : ℕ∞) + 1 ≤
      (AlgebraicIndependent.matroid k K).eRk ((E ⊔ P.1 : ClosedIF k K) : Set K) := by
    rw [← hlow]
    exact (AlgebraicIndependent.matroid k K).eRk_mono hsub
  apply rankEq_iff_eRk.2
  rw [Nat.cast_add, Nat.cast_one]
  exact le_antisymm hup hge

/-- **Exchange of points** across a closed element of finite rank: if `P ≤ E ∨ Q` and
`P ≰ E`, then `Q ≤ E ∨ P`. -/
private theorem le_sup_point_of_le_sup_point {m : ℕ} {E : ClosedIF k K} (hE : RankEq m E)
    {P Q : Point k K} (h : P.1 ≤ E ⊔ Q.1) (hP : ¬ P.1 ≤ E) : Q.1 ≤ E ⊔ P.1 := by
  have hQ : ¬ Q.1 ≤ E := fun hQ ↦ hP (h.trans (sup_le le_rfl hQ))
  have heq : E ⊔ P.1 = E ⊔ Q.1 :=
    RankEq.eq_of_le (sup_le le_sup_left h) (rankEq_sup_point_of_not_le hE hP)
      (rankEq_sup_point_of_not_le hE hQ)
  rw [heq]
  exact le_sup_right

/-- The join of two points has rank at most two. -/
private theorem eRk_le_two (P Q : Point k K) :
    (AlgebraicIndependent.matroid k K).eRk ((P.1 ⊔ Q.1 : ClosedIF k K) : Set K) ≤ 2 := by
  have h := eRk_sup_le P.1 Q.1
  rw [rankEq_iff_eRk.1 (Point.rankEq_one P), rankEq_iff_eRk.1 (Point.rankEq_one Q)] at h
  exact h.trans (by norm_num)

/-- Two closed elements of rank at most two whose join has rank four both have rank two. -/
private theorem rankEq_two_of_rankEq_four {E F : ClosedIF k K}
    (hE : (AlgebraicIndependent.matroid k K).eRk (E : Set K) ≤ 2)
    (hF : (AlgebraicIndependent.matroid k K).eRk (F : Set K) ≤ 2)
    (hEF : RankEq 4 (E ⊔ F)) : RankEq 2 E := by
  have h := eRk_sup_le E F
  rw [rankEq_iff_eRk.1 hEF] at h
  apply rankEq_iff_eRk.2
  lift (AlgebraicIndependent.matroid k K).eRk (E : Set K) to ℕ using
    ne_top_of_le_ne_top (by simp) hE with x
  lift (AlgebraicIndependent.matroid k K).eRk (F : Set K) to ℕ using
    ne_top_of_le_ne_top (by simp) hF with y
  norm_cast at hE hF h ⊢
  omega

end RankCalculus

namespace QWitness

variable {w : QWitness k K}

/-! ### Ranks and meets of the parameter joins -/

/-- `A` has rank two. -/
private theorem Psi.rankEq_A (hw : w.Psi) : RankEq 2 w.A :=
  rankEq_two_of_rankEq_four (eRk_le_two w.A₁ w.A₂) (eRk_le_two w.B₁ w.B₂) hw.rank_AB

/-- `B` has rank two. -/
private theorem Psi.rankEq_B (hw : w.Psi) : RankEq 2 w.B :=
  rankEq_two_of_rankEq_four (eRk_le_two w.B₁ w.B₂) (eRk_le_two w.A₁ w.A₂)
    (RankEq.congr (sup_comm w.A w.B) hw.rank_AB)

/-- `C` has rank two. -/
private theorem Psi.rankEq_C (hw : w.Psi) : RankEq 2 w.C :=
  rankEq_two_of_rankEq_four (eRk_le_two w.C₁ w.C₂) (eRk_le_two w.A₁ w.A₂)
    (RankEq.congr (sup_comm w.A w.C) hw.rank_AC)

/-- `A ∧ B = ⊥`: ranks `2 + 2 = 4`. -/
private theorem Psi.A_inf_B (hw : w.Psi) : w.A ⊓ w.B = ⊥ :=
  inf_eq_of_rankEq (Psi.rankEq_A hw) (Psi.rankEq_B hw) hw.rank_AB (by norm_num)
    rankEq_zero_bot bot_le

/-- `A ∧ C = ⊥`: ranks `2 + 2 = 4`. -/
private theorem Psi.A_inf_C (hw : w.Psi) : w.A ⊓ w.C = ⊥ :=
  inf_eq_of_rankEq (Psi.rankEq_A hw) (Psi.rankEq_C hw) hw.rank_AC (by norm_num)
    rankEq_zero_bot bot_le

/-- `B ∧ C = ⊥`: ranks `2 + 2 = 4`. -/
private theorem Psi.B_inf_C (hw : w.Psi) : w.B ⊓ w.C = ⊥ :=
  inf_eq_of_rankEq (Psi.rankEq_B hw) (Psi.rankEq_C hw) hw.rank_BC (by norm_num)
    rankEq_zero_bot bot_le

/-- `A ∨ C` is already the whole span `A ∨ B ∨ C`. -/
private theorem Psi.AC_eq (hw : w.Psi) : w.A ⊔ w.C = w.A ⊔ w.B ⊔ w.C :=
  RankEq.eq_of_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hw.rank_AC
    hw.rank_ABC

/-- `B ≤ A ∨ C`. -/
private theorem Psi.B_le_AC (hw : w.Psi) : w.B ≤ w.A ⊔ w.C := by
  rw [Psi.AC_eq hw]
  exact le_sup_right.trans le_sup_left

/-- `X ≰ A`. -/
private theorem Psi.X_not_le_A (hw : w.Psi) : ¬ w.X.1 ≤ w.A :=
  fun h ↦ hw.X_notLe (h.trans (le_sup_left.trans le_sup_left))

/-- `Y ≰ B`. -/
private theorem Psi.Y_not_le_B (hw : w.Psi) : ¬ w.Y.1 ≤ w.B :=
  fun h ↦ hw.Y_notLe (h.trans (le_sup_right.trans le_sup_left))

/-- `(A ∨ X) ∧ (A ∨ C) = A`: ranks `3 + 4 = 5 + 2`. -/
private theorem Psi.AX_inf_AC (hw : w.Psi) : (w.A ⊔ w.X.1) ⊓ (w.A ⊔ w.C) = w.A := by
  have hXAC : ¬ w.X.1 ≤ w.A ⊔ w.C := by
    rw [Psi.AC_eq hw]
    exact hw.X_notLe
  have h3 := rankEq_sup_point_of_not_le (Psi.rankEq_A hw) (Psi.X_not_le_A hw)
  have h5 := rankEq_sup_point_of_not_le hw.rank_AC hXAC
  have hj : (w.A ⊔ w.X.1) ⊔ (w.A ⊔ w.C) = (w.A ⊔ w.C) ⊔ w.X.1 := by
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
  exact inf_eq_of_rankEq h3 hw.rank_AC (RankEq.congr hj.symm h5) (by norm_num)
    (Psi.rankEq_A hw) (le_inf le_sup_left le_sup_left)

/-- `(B ∨ Y) ∧ (A ∨ C) = B`: ranks `3 + 4 = 5 + 2`. -/
private theorem Psi.BY_inf_AC (hw : w.Psi) : (w.B ⊔ w.Y.1) ⊓ (w.A ⊔ w.C) = w.B := by
  have hYAC : ¬ w.Y.1 ≤ w.A ⊔ w.C := by
    rw [Psi.AC_eq hw]
    exact hw.Y_notLe
  have hB := Psi.B_le_AC hw
  have h3 := rankEq_sup_point_of_not_le (Psi.rankEq_B hw) (Psi.Y_not_le_B hw)
  have h5 := rankEq_sup_point_of_not_le hw.rank_AC hYAC
  have hj : (w.B ⊔ w.Y.1) ⊔ (w.A ⊔ w.C) = (w.A ⊔ w.C) ⊔ w.Y.1 := by
    apply le_antisymm
    · exact sup_le (sup_le (hB.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  exact inf_eq_of_rankEq h3 hw.rank_AC (RankEq.congr hj.symm h5) (by norm_num)
    (Psi.rankEq_B hw) (le_inf le_sup_left hB)

/-! ### The dependent triple `S, T, U` -/

/-- `S ≠ T`, since `A ∧ B = ⊥`. -/
private theorem Psi.S_ne_T (hw : w.Psi) : w.S ≠ w.T := by
  intro h
  apply Point.not_le_bot w.S
  refine (le_inf hw.S_le ?_).trans (Psi.A_inf_B hw).le
  rw [h]
  exact hw.T_le

/-- `T ≠ U`, since `B ∧ C = ⊥`. -/
private theorem Psi.T_ne_U (hw : w.Psi) : w.T ≠ w.U := by
  intro h
  apply Point.not_le_bot w.T
  refine (le_inf hw.T_le ?_).trans (Psi.B_inf_C hw).le
  rw [h]
  exact hw.U_le

/-- `U ≤ S ∨ T`, from the dependent triple. -/
private theorem Psi.U_le_ST (hw : w.Psi) : w.U.1 ≤ w.S.1 ⊔ w.T.1 := by
  have hTS : ¬ w.T.1 ≤ w.S.1 := fun h ↦ Psi.S_ne_T hw (Point.eq_of_le h).symm
  have heq : w.S.1 ⊔ w.T.1 = w.S.1 ⊔ (w.T.1 ⊔ w.U.1) :=
    RankEq.eq_of_le (sup_le_sup_left le_sup_left _)
      (rankEq_sup_point_of_not_le (Point.rankEq_one w.S) hTS) hw.rank_STU
  rw [heq]
  exact le_sup_right.trans le_sup_right

/-- `S ≤ T ∨ U`, from the dependent triple. -/
private theorem Psi.S_le_TU (hw : w.Psi) : w.S.1 ≤ w.T.1 ⊔ w.U.1 := by
  have hUT : ¬ w.U.1 ≤ w.T.1 := fun h ↦ Psi.T_ne_U hw (Point.eq_of_le h).symm
  have heq : w.T.1 ⊔ w.U.1 = w.S.1 ⊔ (w.T.1 ⊔ w.U.1) :=
    RankEq.eq_of_le le_sup_right
      (rankEq_sup_point_of_not_le (Point.rankEq_one w.T) hUT) hw.rank_STU
  rw [heq]
  exact le_sup_left

/-! ### The points `G`, `H` and the guard -/

/-- `H ≠ U`, since `H ≤ A` and `U ≤ C`. -/
private theorem Psi.H_not_le_U (hw : w.Psi) : ¬ w.H.1 ≤ w.U.1 := by
  intro h
  have hHU : w.H = w.U := Point.eq_of_le h
  apply Point.not_le_bot w.U
  refine (le_inf ?_ hw.U_le).trans (Psi.A_inf_C hw).le
  rw [← hHU, ← hw.meet_H]
  exact inf_le_right

/-- `G ≠ U`: otherwise `H = (U ∨ U) ∧ A ≤ U`. -/
private theorem Psi.G_ne_U (hw : w.Psi) : w.G ≠ w.U := by
  intro hGU
  apply Psi.H_not_le_U hw
  rw [← hw.meet_H, hGU, sup_idem]
  exact inf_le_left

/-- `G ≤ A ∨ C`, by exchange in the line `U ∨ G` through `H`. -/
private theorem Psi.G_le_AC (hw : w.Psi) : w.G.1 ≤ w.A ⊔ w.C := by
  have hH : w.H.1 ≤ w.U.1 ⊔ w.G.1 := by
    rw [← hw.meet_H]
    exact inf_le_left
  have hHA : w.H.1 ≤ w.A := by
    rw [← hw.meet_H]
    exact inf_le_right
  have hG : w.G.1 ≤ w.U.1 ⊔ w.H.1 :=
    le_sup_point_of_le_sup_point (Point.rankEq_one w.U) hH (Psi.H_not_le_U hw)
  exact hG.trans (sup_le (hw.U_le.trans le_sup_right) (hHA.trans le_sup_left))

/-- `G = T` forces `H = S` and then `I = D`. -/
private theorem Psi.I_eq_D_of_G_eq_T (hw : w.Psi) (hGT : w.G = w.T) : w.I = w.D := by
  have hSH : w.S.1 ≤ w.H.1 := by
    rw [← hw.meet_H, hGT]
    exact le_inf ((Psi.S_le_TU hw).trans (sup_comm _ _).le) hw.S_le
  have hHS : w.H = w.S := (Point.eq_of_le hSH).symm
  apply Subtype.ext
  rw [← hw.meet_I, ← hw.meet_D, hHS]
  exact inf_comm _ _

/-! ### The four consequences -/

/-- **`Q ≠ T` under the ratio guard.**  `Q = T` forces `G = T`, hence `H = S` and `I = D`.
The degenerate witness of `Counterexamples.QDegenerate` shows that the guard is needed. -/
theorem Psi.Q_ne_T (hw : w.Psi) (hID : w.I ≠ w.D) : w.Q ≠ w.T := by
  intro hQT
  have hTG : w.T.1 ≤ w.G.1 := by
    rw [← hw.meet_G, hQT]
    exact le_inf le_sup_right le_sup_left
  exact hID (Psi.I_eq_D_of_G_eq_T hw (Point.eq_of_le hTG).symm)

/-- **`P ≤ A` under the ratio guard** (the incidence assumed in EH95 Corollary 3.4).
Meet `D` puts `P` on `D ∨ Y ≤ A ∨ X`; meets `G`, `H` put it on `T ∨ G ≤ A ∨ C`; and
`(A ∨ X) ∧ (A ∨ C) = A` by rank counting. -/
theorem Psi.P_le_A (hw : w.Psi) (hID : w.I ≠ w.D) : w.P.1 ≤ w.A := by
  -- `P ≤ A ∨ X`, from meet `D`.
  have hYAX : w.Y.1 ≤ w.A ⊔ w.X.1 :=
    le_sup_point_of_le_sup_point (Psi.rankEq_A hw) hw.X_le (Psi.X_not_le_A hw)
  have hYS : ¬ w.Y.1 ≤ w.S.1 :=
    fun h ↦ hw.Y_notLe (h.trans (hw.S_le.trans (le_sup_left.trans le_sup_left)))
  have hYSX : ¬ w.Y.1 ≤ w.S.1 ⊔ w.X.1 := fun h ↦
    hw.X_free w.S hw.S_le (le_sup_point_of_le_sup_point (Point.rankEq_one w.S) h hYS)
  have hDSX : w.D.1 ≤ w.S.1 ⊔ w.X.1 := by
    rw [← hw.meet_D]
    exact inf_le_right
  have hDPY : w.D.1 ≤ w.P.1 ⊔ w.Y.1 := by
    rw [← hw.meet_D]
    exact inf_le_left
  have hDY : ¬ w.D.1 ≤ w.Y.1 := fun h ↦ hYSX (by
    rw [← (Point.eq_of_le h : w.D = w.Y)]
    exact hDSX)
  have hPYD : w.P.1 ≤ w.Y.1 ⊔ w.D.1 :=
    le_sup_point_of_le_sup_point (Point.rankEq_one w.Y) (hDPY.trans (sup_comm _ _).le) hDY
  have hPAX : w.P.1 ≤ w.A ⊔ w.X.1 :=
    hPYD.trans (sup_le hYAX (hDSX.trans (sup_le_sup_right hw.S_le _)))
  -- `P ≤ A ∨ C`, from meets `G` and `H`.
  have hGT : ¬ w.G.1 ≤ w.T.1 :=
    fun h ↦ hID (Psi.I_eq_D_of_G_eq_T hw (Point.eq_of_le h))
  have hGPT : w.G.1 ≤ w.P.1 ⊔ w.T.1 := by
    rw [← hw.meet_G]
    exact inf_le_left
  have hPTG : w.P.1 ≤ w.T.1 ⊔ w.G.1 :=
    le_sup_point_of_le_sup_point (Point.rankEq_one w.T) (hGPT.trans (sup_comm _ _).le) hGT
  have hPAC : w.P.1 ≤ w.A ⊔ w.C :=
    hPTG.trans (sup_le (hw.T_le.trans (Psi.B_le_AC hw)) (Psi.G_le_AC hw))
  rw [← Psi.AX_inf_AC hw]
  exact le_inf hPAX hPAC

/-- **`P ≠ S`**, for every `Psi`-witness.  `P = S` forces `D = S`, `F = U`, `R = U` and
`G = U`, which is impossible. -/
theorem Psi.P_ne_S (hw : w.Psi) : w.P ≠ w.S := by
  intro hPS
  apply Psi.G_ne_U hw
  have hSD : w.S.1 ≤ w.D.1 := by
    rw [← hw.meet_D, hPS]
    exact le_inf le_sup_left le_sup_left
  have hDS : w.D = w.S := (Point.eq_of_le hSD).symm
  have hUF : w.U.1 ≤ w.F.1 := by
    rw [← hw.meet_F, hDS]
    exact le_inf le_sup_left ((Psi.U_le_ST hw).trans (sup_comm _ _).le)
  have hFU : w.F = w.U := (Point.eq_of_le hUF).symm
  have hUR : w.U.1 ≤ w.R.1 := by
    rw [← hw.meet_R, hFU]
    exact le_inf le_sup_left hw.U_le
  have hRU : w.R = w.U := (Point.eq_of_le hUR).symm
  have hUG : w.U.1 ≤ w.G.1 := by
    rw [← hw.meet_G, hPS, hRU]
    exact le_inf (Psi.U_le_ST hw) le_sup_right
  exact (Point.eq_of_le hUG).symm

/-- **`Q ≤ B`**, for every `Psi`-witness (the incidence assumed in EH95 Corollary 3.4).
Meet `E` puts `Q` on `Z ∨ E ≤ B ∨ Y`.  Meet `H` shows `G ≰ C`, so meet `G` puts `Q` on
`R ∨ G ≤ A ∨ C`.  Finally `(B ∨ Y) ∧ (A ∨ C) = B` by rank counting. -/
theorem Psi.Q_le_B (hw : w.Psi) : w.Q.1 ≤ w.B := by
  -- `Q ≤ B ∨ Y`, from meet `E`.
  have hZTY : ¬ w.Z.1 ≤ w.T.1 ⊔ w.Y.1 := hw.Z_freeB w.T hw.T_le
  have hET : w.E.1 ≤ w.T.1 ⊔ w.Y.1 := by
    rw [← hw.meet_E]
    exact inf_le_left
  have hEQZ : w.E.1 ≤ w.Q.1 ⊔ w.Z.1 := by
    rw [← hw.meet_E]
    exact inf_le_right
  have hEZ : ¬ w.E.1 ≤ w.Z.1 := fun h ↦ hZTY (by
    rw [← (Point.eq_of_le h : w.E = w.Z)]
    exact hET)
  have hQZE : w.Q.1 ≤ w.Z.1 ⊔ w.E.1 :=
    le_sup_point_of_le_sup_point (Point.rankEq_one w.Z) (hEQZ.trans (sup_comm _ _).le) hEZ
  have hQBY : w.Q.1 ≤ w.B ⊔ w.Y.1 :=
    hQZE.trans (sup_le (hw.Z_le.trans inf_le_left) (hET.trans (sup_le_sup_right hw.T_le _)))
  -- `Q ≤ A ∨ C`, from meet `G`.
  have hRC : w.R.1 ≤ w.C := by
    rw [← hw.meet_R]
    exact inf_le_right
  have hGC : ¬ w.G.1 ≤ w.C := by
    intro h
    apply Point.not_le_bot w.H
    have hH : w.H.1 ≤ w.C ⊓ w.A := by
      rw [← hw.meet_H]
      exact inf_le_inf_right _ (sup_le hw.U_le h)
    exact hH.trans ((inf_comm _ _).le.trans (Psi.A_inf_C hw).le)
  have hGR : ¬ w.G.1 ≤ w.R.1 := fun h ↦ hGC (h.trans hRC)
  have hGQR : w.G.1 ≤ w.Q.1 ⊔ w.R.1 := by
    rw [← hw.meet_G]
    exact inf_le_right
  have hQRG : w.Q.1 ≤ w.R.1 ⊔ w.G.1 :=
    le_sup_point_of_le_sup_point (Point.rankEq_one w.R) (hGQR.trans (sup_comm _ _).le) hGR
  have hQAC : w.Q.1 ≤ w.A ⊔ w.C :=
    hQRG.trans (sup_le (hRC.trans le_sup_right) (Psi.G_le_AC hw))
  rw [← Psi.BY_inf_AC hw]
  exact le_inf hQBY hQAC


/-- **`D` is generic over the parameter join under the ratio guard.** If `D` lay in
`A ∨ B ∨ C`, meet `D` and exchange would give `D = S`. Since `P ≤ A` and `P ≠ S`,
the same meet would put `Y` below `A`, a contradiction. This supplies the non-membership
needed at the first-meet elimination seam. -/
theorem Psi.D_not_le_ABC (hw : w.Psi) (hID : w.I ≠ w.D) :
    ¬ w.D.1 ≤ w.A ⊔ w.B ⊔ w.C := by
  intro hD
  have hDSX : w.D.1 ≤ w.S.1 ⊔ w.X.1 := by
    rw [← hw.meet_D]
    exact inf_le_right
  have hDS : w.D.1 ≤ w.S.1 := by
    by_contra h
    have hX := le_sup_point_of_le_sup_point (Point.rankEq_one w.S) hDSX h
    exact hw.X_notLe (hX.trans
      (sup_le (hw.S_le.trans (le_sup_left.trans le_sup_left)) hD))
  have hDS' : w.D = w.S := Point.eq_of_le hDS
  have hDP : ¬ w.D.1 ≤ w.P.1 := fun h ↦
    hw.P_ne_S ((Point.eq_of_le h).symm.trans hDS')
  have hDPY : w.D.1 ≤ w.P.1 ⊔ w.Y.1 := by
    rw [← hw.meet_D]
    exact inf_le_left
  have hY := le_sup_point_of_le_sup_point (Point.rankEq_one w.P) hDPY hDP
  exact hw.Y_notLe ((hY.trans (sup_le (hw.P_le_A hID)
    (hDS.trans hw.S_le))).trans (le_sup_left.trans le_sup_left))

/-- **`D ≠ S` under the ratio guard.** This is the missing shared-point non-membership
for the difference-cocycle data lemma when affine coordinates are supplied. -/
theorem Psi.D_ne_S (hw : w.Psi) (hID : w.I ≠ w.D) : w.D ≠ w.S := by
  intro hDS
  apply hw.D_not_le_ABC hID
  rw [hDS]
  exact hw.S_le.trans (le_sup_left.trans le_sup_left)

/-- **`F ≠ U` under the ratio guard.** Meet `F` would otherwise put `D` on the line
`T ∨ U` inside `A ∨ B ∨ C`. In the proposed first-meet linearity argument this ensures
the `F`-curve has a generic multiplier projection, rather than a vertical degeneration.
It proves no curve action or linearity. -/
theorem Psi.F_ne_U (hw : w.Psi) (hID : w.I ≠ w.D) : w.F ≠ w.U := by
  intro hFU
  have hUTD : w.U.1 ≤ w.T.1 ⊔ w.D.1 := by
    rw [← hFU, ← hw.meet_F]
    exact inf_le_right
  have hUT : ¬ w.U.1 ≤ w.T.1 := fun h ↦
    Psi.T_ne_U hw (Point.eq_of_le h).symm
  have hDTU := le_sup_point_of_le_sup_point (Point.rankEq_one w.T) hUTD hUT
  exact hw.D_not_le_ABC hID (hDTU.trans
    (sup_le (hw.T_le.trans (le_sup_right.trans le_sup_left))
      (hw.U_le.trans le_sup_right)))

end QWitness

end

end AclGeom
