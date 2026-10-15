/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Configuration
import GroupConfig.CanonicalBaseCapture
import AclGeom.Config.PsiLattice

/-!
# Canonical-base clauses of the actual Ψ configuration

In an algebraically closed universal domain, the actual Ψ witness identifies
A with the relative algebraic closure of the canonical base of (X,Y) over A,
and likewise B with (Y,Z), and C with (X,Z). These are the three GC4 clauses
needed by the supplemental six-point configuration input, with genuine Ψ
atom-freeness rather than a caller-supplied canonical-base premise.

Cb1 and the finite-rank tower law capture a target point over the canonical
base and its source point. If that canonical base were contained in an atom
of the rank-two parameter plane, this would contradict Ψ's freeness clause.
The existing rank-two lattice theorem then identifies its closure with the plane.

**Status:** the three actual Ψ canonical-base identifications are proved with
ambient ACF and universal-domain hypotheses. The original base may be arbitrary.
The complete sixteen-triple input is assembled in `Config.ConfigurationInput`;
the canonical universal-ambient package is in `Config.UniversalConfigurationInput`.
The three identifications require only `PsiCore`, clauses (i)–(iv); the full-Ψ
public theorems retain their statements and delegate to these proofs.
Literal image-tuple comparison is proved in `Config.UniversalImageConfigurationInput`;
finite-ambient chart/action descent remains open.
Both output guards remain at the downstream chart target; no chart, algebraic
group, action or reconstruction is extracted here.
-/

namespace AclGeom

open GroupConfig

noncomputable section

open AclGeom Set

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private def pointTuple (P : Point k K) : Fin 1 → K := fun _ ↦ P.rep

private theorem range_pointTuple (P : Point k K) : range (pointTuple P) = {P.rep} := by
  simp [pointTuple]

private theorem coe_sup_pointTuple (E : ClosedIF k K) (P : Point k K) :
    (E ⊔ P.1).1 = racl k ((E : Set K) ∪ range (pointTuple P)) := by
  rw [range_pointTuple, ClosedIF.coe_sup, ← P.point_rep]
  exact racl_union_right (E : Set K) {P.rep}

-- Sole consumers: the three actual Psi canonical-base clauses below.
private theorem canonicalBase_incidence_eq [IsAlgClosed K] [UniversalDomain k K]
    (E : ClosedIF k K) [IsAlgClosed ↥E.1] (hEsmall : IsSmall k (E : Set K))
    (hE : RankEq 2 E) (Q P : Point k K) (hPQ : P.1 ≤ E ⊔ Q.1)
    (hfree : ∀ R : Point k K, R.1 ≤ E → ¬ P.1 ≤ R.1 ⊔ Q.1) :
    racl k (canonicalBase E.1 (Sum.elim (pointTuple Q) (pointTuple P)) : Set K) = E.1 := by
  let B := canonicalBase E.1 (Sum.elim (pointTuple Q) (pointTuple P))
  let C : ClosedIF k K := ⟨racl k (B : Set K), isRAC_racl _⟩
  have hCE : C ≤ E :=
    ClosedIF.le_iff.2 (racl_le_of_isAlgClosed (canonicalBase_le E.1 _))
  have hP : range (pointTuple P) ⊆ racl k ((E : Set K) ∪ range (pointTuple Q)) := by
    rw [← coe_sup_pointTuple]
    rintro x ⟨i, rfl⟩
    exact hPQ P.mem_rep
  have hcapture := range_subset_racl_canonicalBase E.1 hEsmall
    (pointTuple Q) (pointTuple P) hP
  have hEq : C = E := RankEq.eq_of_le_of_not_le_point hCE hE fun R hRE hCR ↦ by
    apply hfree R hRE
    rw [← P.point_rep]
    refine ClosedIF.point_le_iff.2 ?_
    change P.rep ∈ (R.1 ⊔ Q.1).1
    rw [coe_sup_pointTuple]
    refine (racl_mono (union_subset_union_left _ ?_)) (hcapture (mem_range_self 0))
    exact (subset_racl k _).trans hCR
  exact congrArg Subtype.val hEq

private theorem closed_isAlgClosed [IsAlgClosed K] (E : ClosedIF k K) :
    IsAlgClosed ↥E.1 := by
  apply (IsAlgClosed.algebraicClosure_eq_bot_iff ↥E.1 K).mp
  apply bot_unique
  intro x hx
  exact IntermediateField.mem_bot.mpr
    ⟨⟨x, E.2 x (mem_algebraicClosure_iff.mp hx)⟩, rfl⟩

private theorem isSmall_of_rankEq {n : ℕ} {E : ClosedIF k K} (hE : RankEq n E) :
    IsSmall k (E : Set K) := by
  unfold IsSmall
  rw [erk_empty_eq, rankEq_iff_eRk.1 hE]
  exact ENat.natCast_ne_top n

namespace QWitness

variable {w : QWitness k K} [IsAlgClosed K] [UniversalDomain k K]

/-- The clause-(i)–(iv) atom-freeness input identifies the canonical base of X,Y
with the full parameter plane A. Named consumer: GC4 of the actual Ψ input. -/
theorem PsiCore.racl_canonicalBase_XY_eq_A (hw : w.PsiCore) :
    racl k (canonicalBase w.A.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Y.rep)) : Set K) =
      w.A.1 := by
  have _ := closed_isAlgClosed w.A
  rw [canonicalBase_sum_elim_swap]
  exact canonicalBase_incidence_eq w.A (isSmall_of_rankEq hw.rankEq_A) hw.rankEq_A
    w.Y w.X hw.X_le hw.X_free

/-- The clause-(i)–(iv) canonical-base identification on B,Y,Z, for GC4. -/
theorem PsiCore.racl_canonicalBase_YZ_eq_B (hw : w.PsiCore) :
    racl k (canonicalBase w.B.1
      (Sum.elim (fun _ : Fin 1 ↦ w.Y.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.B.1 := by
  have _ := closed_isAlgClosed w.B
  exact canonicalBase_incidence_eq w.B (isSmall_of_rankEq hw.rankEq_B) hw.rankEq_B
    w.Y w.Z (hw.Z_le.trans inf_le_left) hw.Z_freeB

/-- The clause-(i)–(iv) canonical-base identification on C,X,Z, for GC4. -/
theorem PsiCore.racl_canonicalBase_XZ_eq_C (hw : w.PsiCore) :
    racl k (canonicalBase w.C.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.C.1 := by
  have _ := closed_isAlgClosed w.C
  exact canonicalBase_incidence_eq w.C (isSmall_of_rankEq hw.rankEq_C) hw.rankEq_C
    w.X w.Z (hw.Z_le.trans inf_le_right) hw.Z_freeC

/-- The full Ψ witness has the same canonical-base identification on `A`. -/
theorem Psi.racl_canonicalBase_XY_eq_A (hw : w.Psi) :
    racl k (canonicalBase w.A.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Y.rep)) : Set K) =
      w.A.1 := hw.toCore.racl_canonicalBase_XY_eq_A

/-- The full Ψ witness has the same canonical-base identification on `B`. -/
theorem Psi.racl_canonicalBase_YZ_eq_B (hw : w.Psi) :
    racl k (canonicalBase w.B.1
      (Sum.elim (fun _ : Fin 1 ↦ w.Y.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.B.1 := hw.toCore.racl_canonicalBase_YZ_eq_B

/-- The full Ψ witness has the same canonical-base identification on `C`. -/
theorem Psi.racl_canonicalBase_XZ_eq_C (hw : w.Psi) :
    racl k (canonicalBase w.C.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.C.1 := hw.toCore.racl_canonicalBase_XZ_eq_C

end QWitness

end

end AclGeom
