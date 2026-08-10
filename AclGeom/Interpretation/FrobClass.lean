/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Correctness

/-!
# The Frobenius-class relation on J

`SumPoint`, `MulPoint`, `DirectFrobLink`, the bridge relation `FrobEq` with its
semantic characterization `FrobEq (j x a) (j x' a') ↔ ∃ n, a' = a^(p^n)`
(blueprint Lemma frobeq-correct), the setoid, the fixed class `J₁`, and the
coordinate bijection `μ` (Lemma mu-bij).

**Status:** in progress (M6, checklist I1): the geometric link language is
defined; its exact semantic characterization remains dependent on
configuration completeness.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The derived geometric sum relation: `W` is the sum point of `U,V`
when it is the third free coordinate of a geometric `Q`-configuration. -/
def SumPoint (U V W : Point k K) : Prop :=
  ∃ R : Point k K, QGeom U V W R

/-- The derived geometric product relation: `W` is the product point of
`U,V` when it is the fourth coordinate of a geometric `Q′`-configuration. -/
def MulPoint (U V W : Point k K) : Prop :=
  ∃ S : Point k K, Q'Geom U V S W

/-- A five-tuple belongs to the geometric `J`-locus, using coordinate order
`(X,P,Q,R,A)`. -/
def IsJTuple (u : Fin 5 → Point k K) : Prop :=
  JGeom (u 0) (u 1) (u 2) (u 3) (u 4)

/-- The three points have rank three, the geometric formulation of their
independence. -/
def PointTripleIndependent (X Y A : Point k K) : Prop :=
  RankEq 3 (X.1 ⊔ (Y.1 ⊔ A.1))

/-- A directed Frobenius link between two geometric j-tuples (blueprint
§10): the parameter point is shared and a single multiplier point sends
the target's `X,Q,R` coordinates to the source's corresponding coordinates.
The rank-three clause is the genericity condition on `u_X,v_X,u_A`. -/
structure DirectFrobLink (u v : Fin 5 → Point k K) : Prop where
  /-- The source is a geometric j-tuple. -/
  source_mem : IsJTuple u
  /-- The target is a geometric j-tuple. -/
  target_mem : IsJTuple v
  /-- The source and target share their parameter point. -/
  parameter_eq : u 4 = v 4
  /-- The two X-coordinates and the common parameter are independent. -/
  independent : PointTripleIndependent (u 0) (v 0) (u 4)
  /-- A common geometric multiplier relates the three rigid coordinates. -/
  multiplier : ∃ C : Point k K,
    MulPoint C (v 0) (u 0) ∧
    MulPoint C (v 2) (u 2) ∧
    MulPoint C (v 3) (u 3)

/-- An undirected direct-link edge.  The bridge definition below may use a
direct link in either orientation, exactly as in the blueprint. -/
def DirectFrobEdge (u v : Fin 5 → Point k K) : Prop :=
  DirectFrobLink u v ∨ DirectFrobLink v u

namespace DirectFrobEdge

/-- Direct Frobenius edges are symmetric by construction. -/
theorem symm {u v : Fin 5 → Point k K}
    (h : DirectFrobEdge u v) : DirectFrobEdge v u :=
  h.elim Or.inr Or.inl

/-- The left endpoint of a direct edge is a geometric j-tuple. -/
theorem source_mem {u v : Fin 5 → Point k K}
    (h : DirectFrobEdge u v) : IsJTuple u := by
  rcases h with h | h
  · exact h.source_mem
  · exact h.target_mem

/-- The right endpoint of a direct edge is a geometric j-tuple. -/
theorem target_mem {u v : Fin 5 → Point k K}
    (h : DirectFrobEdge u v) : IsJTuple v :=
  h.symm.source_mem

end DirectFrobEdge

/-- Two j-tuples are Frobenius-equivalent when they admit a common bridge
j-tuple joined to each by an undirected direct edge. -/
def FrobEq (u v : Fin 5 → Point k K) : Prop :=
  ∃ w : Fin 5 → Point k K,
    IsJTuple w ∧ DirectFrobEdge u w ∧ DirectFrobEdge w v

namespace FrobEq

/-- The bridge relation is symmetric. -/
theorem symm {u v : Fin 5 → Point k K} (h : FrobEq u v) :
    FrobEq v u := by
  obtain ⟨w, hw, huw, hwv⟩ := h
  exact ⟨w, hw, hwv.symm, huw.symm⟩

/-- The left endpoint of a Frobenius bridge lies on the geometric j-locus. -/
theorem source_mem {u v : Fin 5 → Point k K} (h : FrobEq u v) :
    IsJTuple u := by
  obtain ⟨w, -, huw, -⟩ := h
  exact huw.source_mem

/-- The right endpoint of a Frobenius bridge lies on the geometric j-locus. -/
theorem target_mem {u v : Fin 5 → Point k K} (h : FrobEq u v) :
    IsJTuple v :=
  h.symm.source_mem

end FrobEq

/-- Semantic sums give geometric sum points under the rank-five
hypothesis. -/
theorem sumPoint_of_qSem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {U V W R : Point k K} (h : QSem U V W R) :
    SumPoint U V W :=
  ⟨R, qGeom_of_qSem_of_five_le_trdeg htr h⟩

/-- Semantic products give geometric product points under the rank-five
hypothesis. -/
theorem mulPoint_of_q'Sem_of_five_le_trdeg [Infinite k]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {U V S W : Point k K} (h : Q'Sem U V S W) :
    MulPoint U V W :=
  ⟨S, q'Geom_of_q'Sem_of_five_le_trdeg htr h⟩

end

end AclGeom
