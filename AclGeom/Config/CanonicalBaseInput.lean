/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Configuration
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
The full sixteen-triple configuration input and finite-ambient lift remain open.
Both output guards remain at the downstream chart target; no chart, algebraic
group, action or reconstruction is extracted here.
-/

namespace AclGeom

open GroupConfig

noncomputable section

open AclGeom Set

variable {k K ι κ : Type*} [Field k] [Field K] [Algebra k K]

/-- Algebraicity of a finite target tuple over M and a source tuple can be
captured using the canonical base of their joint locus instead of M.
Named consumer: the canonical-base clauses of the actual Psi configuration input. -/
private theorem range_subset_racl_canonicalBase [IsAlgClosed K] [UniversalDomain k K]
    [Finite ι] [Finite κ] (M : IntermediateField k K) [IsAlgClosed (↥M)]
    (hM : IsSmall k (M : Set K)) (a : ι → K) (b : κ → K)
    (hb : range b ⊆ racl k ((M : Set K) ∪ range a)) :
    range b ⊆ racl k ((canonicalBase M (Sum.elim a b) : Set K) ∪ range a) := by
  let C := canonicalBase M (Sum.elim a b)
  have hrange := Sum.elim_range a b
  have htotal : erk k (C : Set K) (range a ∪ range b) =
      erk k (M : Set K) (range a) := by
    rw [← hrange, erk_canonicalBase_eq M hM, hrange]
    exact erk_union_eq_of_subset_racl k hb
  have hlow : erk k (M : Set K) (range a) ≤ erk k (C : Set K) (range a) :=
    erk_base_mono k (SetLike.coe_subset_coe.2 (canonicalBase_le M (Sum.elim a b))) _
  have hsum : erk k (C : Set K) (range a) +
      erk k ((C : Set K) ∪ range a) (range b) ≤ erk k (C : Set K) (range a) + 0 := by
    rw [← erk_union_eq, add_zero]
    exact htotal.le.trans hlow
  have hz := (ENat.add_le_add_iff_left (erk_ne_top k (finite_range a) (C : Set K))).1 hsum
  exact (erk_eq_zero_iff k).1 (bot_unique hz)



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

/-- The actual Ψ atom-freeness clause identifies the canonical base of X,Y
with the full parameter plane A. Named consumer: GC4 of the actual Ψ input. -/
theorem Psi.racl_canonicalBase_XY_eq_A (hw : w.Psi) :
    racl k (canonicalBase w.A.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Y.rep)) : Set K) =
      w.A.1 := by
  have _ := closed_isAlgClosed w.A
  rw [canonicalBase_sum_elim_swap]
  exact canonicalBase_incidence_eq w.A (isSmall_of_rankEq hw.rankEq_A) hw.rankEq_A
    w.Y w.X hw.X_le hw.X_free

/-- The actual Ψ canonical-base clause on B,Y,Z, for GC4 of its six-point input. -/
theorem Psi.racl_canonicalBase_YZ_eq_B (hw : w.Psi) :
    racl k (canonicalBase w.B.1
      (Sum.elim (fun _ : Fin 1 ↦ w.Y.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.B.1 := by
  have _ := closed_isAlgClosed w.B
  exact canonicalBase_incidence_eq w.B (isSmall_of_rankEq hw.rankEq_B) hw.rankEq_B
    w.Y w.Z (hw.Z_le.trans inf_le_left) hw.Z_freeB

/-- The actual Ψ canonical-base clause on C,X,Z, for GC4 of its six-point input. -/
theorem Psi.racl_canonicalBase_XZ_eq_C (hw : w.Psi) :
    racl k (canonicalBase w.C.1
      (Sum.elim (fun _ : Fin 1 ↦ w.X.rep) (fun _ : Fin 1 ↦ w.Z.rep)) : Set K) =
      w.C.1 := by
  have _ := closed_isAlgClosed w.C
  exact canonicalBase_incidence_eq w.C (isSmall_of_rankEq hw.rankEq_C) hw.rankEq_C
    w.X w.Z (hw.Z_le.trans inf_le_right) hw.Z_freeC

end QWitness

end

end AclGeom
