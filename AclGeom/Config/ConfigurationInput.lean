/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.CanonicalBaseInput

/-!
# Six-point configuration input from the actual Ψ witness

The actual twenty-one-point Ψ witness supplies the supplemental six-point
predicate on the displayed parameter pairs A₁,A₂; B₁,B₂; C₁,C₂ and representatives
of X,Y,Z. Equal finite ranks give GC1 and GC2. The nine plane-pair/space-point
triples have rank five; closure independence and the three line equalities
supply the six mixed triples and the X,Y,Z triple. The committed canonical-base
identifications give GC4, and the parameter planes have rank two. The space
points have rank one. Thus every GC1–GC5 premise is derived from clauses
(i)–(iv) of actual Ψ, packaged as `PsiCore`; clauses (v)–(vii) are unused.

Named consumer: group extraction and the two-dimensional group/curve-action
branch of the guarded initial-chart target. No configuration, group, chart,
action or completeness conclusion is supplied by the caller.

**Status:** the precise clause-(i)–(iv) source input and its ranks are proved in
an algebraically closed universal ambient field, over an arbitrary original base.
The existing full-Ψ public statements are preserved as wrappers.
The canonical universal-ambient package is proved in Config.UniversalConfigurationInput.
Literal comparison with image tuples and finite-ambient chart/action descent,
group extraction/algebraization, action classification and unconditional
reconstruction remain separate obligations. Both output guards remain at the
chart target; they are unnecessary for this input alone.
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

/-- The displayed two representatives of A, for the actual six-point input. -/
def aTuple (w : QWitness k K) : Fin 2 → K := ![w.A₁.rep, w.A₂.rep]

/-- The displayed two representatives of B, for the actual six-point input. -/
def bTuple (w : QWitness k K) : Fin 2 → K := ![w.B₁.rep, w.B₂.rep]

/-- The displayed two representatives of C, for the actual six-point input. -/
def cTuple (w : QWitness k K) : Fin 2 → K := ![w.C₁.rep, w.C₂.rep]

/-- The displayed representative of X, for the actual six-point input. -/
def xTuple (w : QWitness k K) : Fin 1 → K := fun _ ↦ w.X.rep

/-- The displayed representative of Y, for the actual six-point input. -/
def yTuple (w : QWitness k K) : Fin 1 → K := fun _ ↦ w.Y.rep

/-- The displayed representative of Z, for the actual six-point input. -/
def zTuple (w : QWitness k K) : Fin 1 → K := fun _ ↦ w.Z.rep

-- Sole consumer: the actual GroupConfiguration assembly below.
private theorem racl_pair (P Q : Point k K) :
    racl k (range (![P.rep, Q.rep] : Fin 2 → K)) = (P.1 ⊔ Q.1).1 := by
  rw [Matrix.range_cons_cons_empty, ← coe_sup_point₂, P.point_rep, Q.point_rep]

private theorem racl_single (P : Point k K) :
    racl k (range (fun _ : Fin 1 ↦ P.rep)) = P.1.1 := by
  rw [range_const]
  exact congrArg Subtype.val P.point_rep

private theorem racl_union_sup {S T : Set K} {E F : ClosedIF k K}
    (hS : racl k S = E.1) (hT : racl k T = F.1) :
    racl k (S ∪ T) = (E ⊔ F).1 := by
  rw [ClosedIF.coe_sup]
  change racl k (S ∪ T) = racl k ((E.1 : Set K) ∪ (F.1 : Set K))
  rw [← hS, ← hT, racl_union_left, racl_union_right]

private theorem erk_of_racl_rank {S : Set K} {E : ClosedIF k K} {n : ℕ}
    (hS : racl k S = E.1) (hE : RankEq n E) : erk k ∅ S = n := by
  calc erk k ∅ S = erk k ∅ (E : Set K) :=
      erk_eq_of_racl_eq (hS.trans (isRAC_iff_racl_eq.1 E.2).symm)
    _ = n := by rw [erk_empty_eq, rankEq_iff_eRk.1 hE]

private theorem triple_of_rank {A B C : Set K} {E F G : ClosedIF k K} {m n r : ℕ}
    (hA : racl k A = E.1) (hB : racl k B = F.1) (hC : racl k C = G.1)
    (hE : RankEq m E) (hF : RankEq n F) (hG : RankEq r G)
    (hEFG : RankEq (m + n + r) (E ⊔ F ⊔ G)) : IndepTriple k A B C := by
  unfold IndepTriple
  rw [erk_of_racl_rank (racl_union_sup (racl_union_sup hA hB) hC) hEFG,
    erk_of_racl_rank hA hE, erk_of_racl_rank hB hF, erk_of_racl_rank hC hG,
    Nat.cast_add, Nat.cast_add]

private theorem triple_plane_pair_point {A B C : Set K} {E F : ClosedIF k K}
    {P : Point k K} (hA : racl k A = E.1) (hB : racl k B = F.1)
    (hC : racl k C = P.1.1) (hE : RankEq 2 E) (hF : RankEq 2 F)
    (hEF : RankEq 4 (E ⊔ F)) (hP : ¬ P.1 ≤ E ⊔ F) : IndepTriple k A B C :=
  triple_of_rank hA hB hC hE hF P.rankEq_one (hEF.sup_point_of_not_le hP)

private theorem triple_of_indep_union {A B C : Set K} {m : ℕ}
    (hBCfin : (B ∪ C).Finite) (h : IndepOver k ∅ A (B ∪ C))
    (hA : erk k ∅ A = m) (hB : erk k ∅ B = 1) (hC : erk k ∅ C = 1)
    (hBC : erk k ∅ (B ∪ C) = 2) : IndepTriple k A B C := by
  unfold IndepTriple
  rw [union_assoc, erk_union_of_indepOver hBCfin h, hA, hBC, hB, hC]
  norm_num [add_assoc]

private theorem triple_replace_second {A B B' C : Set K}
    (hB : erk k ∅ B = erk k ∅ B') (hAB : racl k (A ∪ B) = racl k (A ∪ B'))
    (h : IndepTriple k A B C) : IndepTriple k A B' C := by
  unfold IndepTriple at h ⊢
  rw [← erk_eq_of_racl_eq (racl_union_congr hAB rfl), ← hB]
  exact h

private theorem subset_line {A Q P : Set K} {E : ClosedIF k K} {Y X : Point k K}
    (hA : racl k A = E.1) (hQ : racl k Q = Y.1.1) (hP : racl k P = X.1.1)
    (hXY : X.1 ≤ E ⊔ Y.1) : Q ∪ P ⊆ racl k (A ∪ Q) := by
  rw [racl_union_sup hA hQ]
  rintro x (hx | hx)
  · exact (le_sup_right : Y.1 ≤ E ⊔ Y.1) (hQ ▸ subset_racl k Q hx)
  · exact hXY (hP ▸ subset_racl k P hx)

variable {w : QWitness k K}

/-- Clauses (i)–(iv) of the actual Ψ witness supply the source six-point input.
All incidences, all sixteen noncollinear triples and all canonical-base clauses
are derived, with group rank two and space rank one. Clauses (v)–(vii) are unused.
The universal-domain
hypothesis is explicit; no group/chart/completeness conclusion is assumed. -/
theorem PsiCore.groupConfiguration [IsAlgClosed K] [UniversalDomain k K] (hw : w.PsiCore) :
    GroupConfig.GroupConfiguration k w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple := by
  have hA : racl k (range w.aTuple) = w.A.1 := racl_pair w.A₁ w.A₂
  have hB : racl k (range w.bTuple) = w.B.1 := racl_pair w.B₁ w.B₂
  have hC : racl k (range w.cTuple) = w.C.1 := racl_pair w.C₁ w.C₂
  have hX : racl k (range w.xTuple) = w.X.1.1 := racl_single w.X
  have hY : racl k (range w.yTuple) = w.Y.1.1 := racl_single w.Y
  have hZ : racl k (range w.zTuple) = w.Z.1.1 := racl_single w.Z
  have rA := erk_of_racl_rank hA hw.rankEq_A
  have rB := erk_of_racl_rank hB hw.rankEq_B
  have rC := erk_of_racl_rank hC hw.rankEq_C
  have rX := erk_of_racl_rank hX w.X.rankEq_one
  have rY := erk_of_racl_rank hY w.Y.rankEq_one
  have rZ := erk_of_racl_rank hZ w.Z.rankEq_one
  have ab : w.A ⊔ w.B = w.A ⊔ w.B ⊔ w.C :=
    RankEq.eq_of_le le_sup_left hw.rank_AB hw.rank_ABC
  have ac : w.A ⊔ w.C = w.A ⊔ w.B ⊔ w.C :=
    RankEq.eq_of_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      hw.rank_AC hw.rank_ABC
  have bc : w.B ⊔ w.C = w.A ⊔ w.B ⊔ w.C :=
    RankEq.eq_of_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      hw.rank_BC hw.rank_ABC
  have nXA : ¬ w.X.1 ≤ w.A := fun h ↦ hw.X_notLe (h.trans (le_sup_left.trans le_sup_left))
  have nYA : ¬ w.Y.1 ≤ w.A := fun h ↦ hw.Y_notLe (h.trans (le_sup_left.trans le_sup_left))
  have nYB : ¬ w.Y.1 ≤ w.B := fun h ↦ hw.Y_notLe (h.trans (le_sup_right.trans le_sup_left))
  have nZB : ¬ w.Z.1 ≤ w.B := fun h ↦ hw.Z_notLe (h.trans (le_sup_right.trans le_sup_left))
  have nXC : ¬ w.X.1 ≤ w.C := fun h ↦ hw.X_notLe (h.trans le_sup_right)
  have nZC : ¬ w.Z.1 ≤ w.C := fun h ↦ hw.Z_notLe (h.trans le_sup_right)
  have axay : w.A ⊔ w.X.1 = w.A ⊔ w.Y.1 :=
    RankEq.eq_of_le (sup_le le_sup_left hw.X_le)
      (hw.rankEq_A.sup_point_of_not_le nXA) (hw.rankEq_A.sup_point_of_not_le nYA)
  have bzby : w.B ⊔ w.Z.1 = w.B ⊔ w.Y.1 :=
    RankEq.eq_of_le (sup_le le_sup_left (hw.Z_le.trans inf_le_left))
      (hw.rankEq_B.sup_point_of_not_le nZB) (hw.rankEq_B.sup_point_of_not_le nYB)
  have czcx : w.C ⊔ w.Z.1 = w.C ⊔ w.X.1 :=
    RankEq.eq_of_le (sup_le le_sup_left (hw.Z_le.trans inf_le_right))
      (hw.rankEq_C.sup_point_of_not_le nZC) (hw.rankEq_C.sup_point_of_not_le nXC)
  have eqAXAY : racl k (range w.aTuple ∪ range w.xTuple) =
      racl k (range w.aTuple ∪ range w.yTuple) := by
    rw [racl_union_sup hA hX, racl_union_sup hA hY, axay]
  have eqBYBZ : racl k (range w.bTuple ∪ range w.yTuple) =
      racl k (range w.bTuple ∪ range w.zTuple) := by
    rw [racl_union_sup hB hY, racl_union_sup hB hZ, bzby]
  have eqCXCZ : racl k (range w.cTuple ∪ range w.xTuple) =
      racl k (range w.cTuple ∪ range w.zTuple) := by
    rw [racl_union_sup hC hX, racl_union_sup hC hZ, czcx]
  have nXY : ¬ w.X.1 ≤ w.Y.1 := fun h ↦ hw.X_free w.A₁ le_sup_left (h.trans le_sup_right)
  have nZY : ¬ w.Z.1 ≤ w.Y.1 := fun h ↦ hw.Z_freeB w.B₁ le_sup_left (h.trans le_sup_right)
  have nZX : ¬ w.Z.1 ≤ w.X.1 := fun h ↦ hw.Z_freeC w.C₁ le_sup_left (h.trans le_sup_right)
  have rXY : erk k ∅ (range w.xTuple ∪ range w.yTuple) = 2 :=
    erk_of_racl_rank (racl_union_sup hX hY)
      ((w.Y.rankEq_one.sup_point_of_not_le nXY).congr (sup_comm _ _))
  have rYZ : erk k ∅ (range w.yTuple ∪ range w.zTuple) = 2 :=
    erk_of_racl_rank (racl_union_sup hY hZ) (w.Y.rankEq_one.sup_point_of_not_le nZY)
  have rXZ : erk k ∅ (range w.xTuple ∪ range w.zTuple) = 2 :=
    erk_of_racl_rank (racl_union_sup hX hZ) (w.X.rankEq_one.sup_point_of_not_le nZX)
  have abX := triple_plane_pair_point hA hB hX hw.rankEq_A hw.rankEq_B hw.rank_AB
    (by rw [ab]; exact hw.X_notLe)
  have abY := triple_plane_pair_point hA hB hY hw.rankEq_A hw.rankEq_B hw.rank_AB
    (by rw [ab]; exact hw.Y_notLe)
  have abZ := triple_plane_pair_point hA hB hZ hw.rankEq_A hw.rankEq_B hw.rank_AB
    (by rw [ab]; exact hw.Z_notLe)
  have acX := triple_plane_pair_point hA hC hX hw.rankEq_A hw.rankEq_C hw.rank_AC
    (by rw [ac]; exact hw.X_notLe)
  have acY := triple_plane_pair_point hA hC hY hw.rankEq_A hw.rankEq_C hw.rank_AC
    (by rw [ac]; exact hw.Y_notLe)
  have acZ := triple_plane_pair_point hA hC hZ hw.rankEq_A hw.rankEq_C hw.rank_AC
    (by rw [ac]; exact hw.Z_notLe)
  have bcX := triple_plane_pair_point hB hC hX hw.rankEq_B hw.rankEq_C hw.rank_BC
    (by rw [bc]; exact hw.X_notLe)
  have bcY := triple_plane_pair_point hB hC hY hw.rankEq_B hw.rankEq_C hw.rank_BC
    (by rw [bc]; exact hw.Y_notLe)
  have bcZ := triple_plane_pair_point hB hC hZ hw.rankEq_B hw.rankEq_C hw.rank_BC
    (by rw [bc]; exact hw.Z_notLe)
  have finA := finite_range w.aTuple
  have finB := finite_range w.bTuple
  have finC := finite_range w.cTuple
  have finX := finite_range w.xTuple
  have finY := finite_range w.yTuple
  have finZ := finite_range w.zTuple
  have subYZ : range w.yTuple ∪ range w.zTuple ⊆
      racl k (range w.bTuple ∪ range w.yTuple) :=
    subset_line hB hY hZ (hw.Z_le.trans inf_le_left)
  have subXZ : range w.xTuple ∪ range w.zTuple ⊆
      racl k (range w.cTuple ∪ range w.xTuple) :=
    subset_line hC hX hZ (hw.Z_le.trans inf_le_right)
  have subYX : range w.yTuple ∪ range w.xTuple ⊆
      racl k (range w.aTuple ∪ range w.yTuple) := subset_line hA hY hX hw.X_le
  have ayz : IndepTriple k (range w.aTuple) (range w.yTuple) (range w.zTuple) := by
    have hind := abY.indepOver_union finA finB finY
    have hcl : IndepOver k ∅ (range w.aTuple)
        (racl k (range w.bTuple ∪ range w.yTuple)) := by
      simpa only [empty_union] using indepOver_racl_right_iff.2 hind
    exact triple_of_indep_union (finY.union finZ) (hcl.mono_right subYZ) rA rY rZ rYZ
  have bxz : IndepTriple k (range w.bTuple) (range w.xTuple) (range w.zTuple) := by
    have hind := bcX.indepOver_union finB finC finX
    have hcl : IndepOver k ∅ (range w.bTuple)
        (racl k (range w.cTuple ∪ range w.xTuple)) := by
      simpa only [empty_union] using indepOver_racl_right_iff.2 hind
    exact triple_of_indep_union (finX.union finZ) (hcl.mono_right subXZ) rB rX rZ rXZ
  have cxy : IndepTriple k (range w.cTuple) (range w.xTuple) (range w.yTuple) := by
    have hind := acY.perm_left.indepOver_union finC finA finY
    have hcl : IndepOver k ∅ (range w.cTuple)
        (racl k (range w.aTuple ∪ range w.yTuple)) := by
      simpa only [empty_union] using indepOver_racl_right_iff.2 hind
    have hyx : erk k ∅ (range w.yTuple ∪ range w.xTuple) = 2 := by
      rw [union_comm]; exact rXY
    exact (triple_of_indep_union (finY.union finX) (hcl.mono_right subYX)
      rC rY rX hyx).perm_right
  have axz := triple_replace_second (rY.trans rX.symm) eqAXAY.symm ayz
  have bxy := (triple_replace_second (rZ.trans rY.symm) eqBYBZ.symm bxz.perm_right).perm_right
  have cyz := (triple_replace_second (rX.trans rZ.symm) eqCXCZ cxy).perm_right
  have xyz : IndepTriple k (range w.xTuple) (range w.yTuple) (range w.zTuple) := by
    have hind := ayz.rotate.rotate.indepOver_union finZ finA finY
    have hcl : IndepOver k ∅ (range w.zTuple)
        (racl k (range w.aTuple ∪ range w.yTuple)) := by
      simpa only [empty_union] using indepOver_racl_right_iff.2 hind
    have subXY : range w.xTuple ∪ range w.yTuple ⊆
        racl k (range w.aTuple ∪ range w.yTuple) := by
      rw [union_comm]; exact subYX
    exact (triple_of_indep_union (finX.union finY) (hcl.mono_right subXY)
      rZ rX rY rXY).rotate
  refine {
    racl_ab_ac := by rw [racl_union_sup hA hB, racl_union_sup hA hC, ab, ac]
    racl_ab_bc := by rw [racl_union_sup hA hB, racl_union_sup hB hC, ab, bc]
    racl_ax_ay := eqAXAY
    racl_by_bz := eqBYBZ
    racl_cx_cz := eqCXCZ
    indep := indep_of_sixteen abX abY abZ acX acY acZ axz ayz bcX bcY bcZ bxy bxz cxy cyz xyz
    cb_a := ?_
    cb_b := ?_
    cb_c := ?_
    one_le_erk := by rw [rA]; norm_num }
  · change range w.aTuple ⊆ racl k (canonicalBase (racl k (range w.aTuple))
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Y.rep)) : Set K)
    rw [hA]
    change range w.aTuple ⊆ racl k (canonicalBase w.A.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Y.rep)) : Set K)
    rw [hw.racl_canonicalBase_XY_eq_A]
    intro t ht
    change t ∈ w.A.1
    rw [← hA]
    exact subset_racl k _ ht
  · change range w.bTuple ⊆ racl k (canonicalBase (racl k (range w.bTuple))
      (Sum.elim (fun _ : Fin 1 ↦ w.Y.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K)
    rw [hB]
    change range w.bTuple ⊆ racl k (canonicalBase w.B.1
      (Sum.elim (fun _ : Fin 1 ↦ w.Y.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K)
    rw [hw.racl_canonicalBase_YZ_eq_B]
    intro t ht
    change t ∈ w.B.1
    rw [← hB]
    exact subset_racl k _ ht
  · change range w.cTuple ⊆ racl k (canonicalBase (racl k (range w.cTuple))
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K)
    rw [hC]
    change range w.cTuple ⊆ racl k (canonicalBase w.C.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K)
    rw [hw.racl_canonicalBase_XZ_eq_C]
    intro t ht
    change t ∈ w.C.1
    rw [← hC]
    exact subset_racl k _ ht

/-- The clause-(i)–(iv) input has group rank two and space rank one. Named consumer:
the two-dimensional group/curve-action branch of initial-chart extraction. -/
theorem PsiCore.groupConfiguration_with_ranks [IsAlgClosed K] [UniversalDomain k K]
    (hw : w.PsiCore) :
    GroupConfig.GroupConfiguration k w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple ∧
      erk k ∅ (range w.aTuple) = 2 ∧ erk k ∅ (range w.xTuple) = 1 :=
  ⟨hw.groupConfiguration, erk_of_racl_rank (racl_pair w.A₁ w.A₂) hw.rankEq_A,
    erk_of_racl_rank (racl_single w.X) w.X.rankEq_one⟩

/-- The full Ψ witness supplies the source configuration through its first four clauses. -/
theorem Psi.groupConfiguration [IsAlgClosed K] [UniversalDomain k K] (hw : w.Psi) :
    GroupConfig.GroupConfiguration k w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple :=
  hw.toCore.groupConfiguration

/-- The full Ψ input retains the group rank two and space rank one package. -/
theorem Psi.groupConfiguration_with_ranks [IsAlgClosed K] [UniversalDomain k K] (hw : w.Psi) :
    GroupConfig.GroupConfiguration k w.aTuple w.bTuple w.cTuple w.xTuple w.yTuple w.zTuple ∧
      erk k ∅ (range w.aTuple) = 2 ∧ erk k ∅ (range w.xTuple) = 1 :=
  hw.toCore.groupConfiguration_with_ranks

end QWitness

end

end AclGeom
