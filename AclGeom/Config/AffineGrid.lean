/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Config.Soundness

/-!
# The affine-grid extraction boundary

Blueprint Lemma `affine-grid-extraction` says that every witness satisfying
`Psi` can, after interalgebraic changes of representatives, be written in
the explicit table with independent coordinates `a, b, c, d, x`.

At the level of closed points, an interalgebraic change does not change the
point.  Thus `QWitness.HasAffineGridCoordinates` expresses the conclusion
exactly by equality with the already verified table witness `qWitness`.
This module proves the complete algebraic output side:

* the canonical table has affine-grid coordinates;
* affine-grid coordinates force the four free outputs to satisfy `QSem`;
* the single remaining geometric theorem is isolated as the proposition
  `AffineGridExtraction`;
* under that proposition, `QGeom` and `QSem` are equivalent (with the same
  fresh-element hypothesis used by the proved soundness direction).

No extraction theorem is assumed or axiomatized here.  Proving
`AffineGridExtraction` from the clauses of `Psi` is the remaining content of
blueprint Lemma 8.5.

**Status:** complete output/assembly boundary for M4; geometric extraction
remains in progress.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

/-- A witness has the affine-grid coordinates of blueprint (8.5) when it
is the explicit table witness for some independent `a, b, c, d, x`.

Equality of closed points is precisely the permitted replacement by
interalgebraic representatives. -/
def HasAffineGridCoordinates (w : QWitness k K) : Prop :=
  ∃ (a b c d x : K) (hind : AlgebraicIndependent k ![a, b, c, d, x]),
    w = qWitness hind

/-- The explicit table witness has its defining affine-grid coordinates. -/
theorem hasAffineGridCoordinates_qWitness {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    (qWitness hind).HasAffineGridCoordinates :=
  ⟨a, b, c, d, x, hind, rfl⟩

/-- The two free-output representatives `b` and `ax` in the affine table
are algebraically independent. -/
theorem affineGrid_output_independent {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    AlgebraicIndependent k ![b, a * x] := by
  have hb_ax : b ∉ racl k ({a * x} : Set K) := by
    intro hb
    apply qtable_b_notMem_ax hind
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_) hb
    have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hx
  have hax_b : a * x ∉ racl k ({b} : Set K) := by
    intro hax
    apply qtable_x_notMem_ab hind
    have ha : a ∈ racl k ({a, b} : Set K) := subset_racl k _ (by simp)
    have hax' : a * x ∈ racl k ({a, b} : Set K) :=
      racl_le_of_subset_racl (Set.singleton_subset_iff.2
        (subset_racl k ({a, b} : Set K) (by simp))) hax
    have h := MulMemClass.mul_mem (inv_mem ha) hax'
    rw [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h
    exact h
  exact algebraicIndependent_pair hb_ax hax_b

/-- Once a witness has affine-grid coordinates, its four free outputs are
exactly a semantic `Q`-quadruple.  This is the algebraic final step of the
completeness direction. -/
theorem qSem_of_hasAffineGridCoordinates {w : QWitness k K}
    (hgrid : w.HasAffineGridCoordinates) :
    QSem w.P w.D w.Y w.I := by
  obtain ⟨a, b, c, d, x, hind, rfl⟩ := hgrid
  refine ⟨b, a * x, affineGrid_output_independent hind, rfl, rfl, ?_, ?_⟩
  · change ClosedIF.point k (a * x + b) = ClosedIF.point k (b + a * x)
    rw [add_comm]
  · change ClosedIF.point k (a * x / b) = ClosedIF.point k (b / (a * x))
    exact ClosedIF.point_div_symm (a * x) b

end QWitness

/-- The precise unproved geometric core of blueprint Lemma 8.5: every
`Psi` witness admits the normalized affine-grid coordinates. -/
def AffineGridExtraction (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ w : QWitness k K, w.Psi → w.HasAffineGridCoordinates

/-- Affine-grid extraction implies the completeness direction
`QGeom → QSem`. -/
theorem qSem_of_qGeom (hextract : AffineGridExtraction k K)
    {P D Y I : Point k K} (h : QGeom P D Y I) : QSem P D Y I := by
  obtain ⟨w, hpsi, rfl, rfl, rfl, rfl⟩ := h
  exact QWitness.qSem_of_hasAffineGridCoordinates (hextract w hpsi)

/-- Conditional correctness at the exact remaining boundary: affine-grid
extraction plus the proved fresh-element soundness gives
`QGeom ↔ QSem`. -/
theorem qGeom_iff_qSem [Infinite k]
    (hextract : AffineGridExtraction k K)
    (hfresh : ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K))
    {P D Y I : Point k K} :
    QGeom P D Y I ↔ QSem P D Y I :=
  ⟨qSem_of_qGeom hextract, qGeom_of_qSem hfresh⟩

end

end AclGeom
