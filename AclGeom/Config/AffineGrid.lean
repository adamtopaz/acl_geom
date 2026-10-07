/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Config.Soundness

/-!
# The affine-grid extraction boundary

Blueprint Lemma `affine-grid-extraction` (8.5) says that, over algebraically
closed `k ⊆ Ω`, every witness satisfying `Psi` has, after interalgebraic
changes of representatives, the affine-grid coordinates of the explicit table
with independent `a, b, c, d, x`.

`Psi` sees the six generator points `A₁, A₂, B₁, B₂, C₁, C₂` only through the
rank-two joins `A = A₁ ∨ A₂`, `B`, `C` (`QWitness.Psi.of_eq`).  The generator
rows of the blueprint's table (8.5) therefore cannot be forced: exchanging
`A₁` and `A₂` preserves `Psi`.  This module

* records that the literal reading of table (8.5), equality with the table
  witness in all twenty-one fields, is refutable as soon as one table witness
  exists (`not_forall_psi_hasLiteralTableCoordinates`);
* defines the corrected coordinate interface
  `QWitness.HasAffineGridCoordinates`, which constrains the three joins and
  the fifteen remaining points, proves the easy implication (affine-grid
  coordinates give a `Psi`-witness), and checks that the swapped table witness
  has corrected coordinates;
* states the open geometric content over algebraically closed fields as
  `AffineGridExtraction`, together with the weaker witness-level completeness
  `QCompletenessACF`, which is all that the completeness direction of `Q`
  uses;
* proves that affine-grid coordinates force the four free outputs to satisfy
  `QSem`, and assembles the conditional equivalence `QGeom ↔ QSem`.

Nothing here proves completeness: `AffineGridExtraction` and
`QCompletenessACF` are open propositions, neither assumed nor axiomatized.
The swapped-witness check only shows that the corrected interface is not
refuted by the counterexample to the literal one. The configuration
completeness targets here are restricted to algebraically closed fields;
the blueprint's arbitrary-field Q/Q′ consequences have independent
mathematical counterexamples (issue #25), whose Lean formalization is open.

**Status:** coordinate interface stated; the extraction theorem (blueprint
Lemma 8.5 over algebraically closed fields) is open (issue #22).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

/-- `Psi` depends on the generator points only through the joins `A`, `B`,
`C`: a witness with the same joins and the same fifteen remaining points as a
`Psi`-witness is again a `Psi`-witness. -/
theorem Psi.of_eq {w w' : QWitness k K} (h : w.Psi)
    (hA : w'.A = w.A) (hB : w'.B = w.B) (hC : w'.C = w.C)
    (hD : w'.D = w.D) (hE : w'.E = w.E) (hF : w'.F = w.F) (hG : w'.G = w.G)
    (hH : w'.H = w.H) (hI : w'.I = w.I) (hP : w'.P = w.P) (hQ : w'.Q = w.Q)
    (hR : w'.R = w.R) (hS : w'.S = w.S) (hT : w'.T = w.T) (hU : w'.U = w.U)
    (hX : w'.X = w.X) (hY : w'.Y = w.Y) (hZ : w'.Z = w.Z) : w'.Psi := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ := h
  constructor <;>
    simp only [hA, hB, hC, hD, hE, hF, hG, hH, hI, hP, hQ, hR, hS, hT, hU, hX,
      hY, hZ] <;>
    assumption

/-- Exchange the two generator points of the rank-two element `A`. -/
def swapA (w : QWitness k K) : QWitness k K :=
  { w with A₁ := w.A₂, A₂ := w.A₁ }

/-- Exchanging the generators does not change the join `A`. -/
theorem swapA_A (w : QWitness k K) : w.swapA.A = w.A :=
  sup_comm _ _

/-- Exchanging the generators of `A` preserves `Psi`. -/
theorem Psi.swapA {w : QWitness k K} (h : w.Psi) : w.swapA.Psi :=
  h.of_eq w.swapA_A rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl

/-- The literal reading of blueprint table (8.5): the witness *is* the table
witness, including its six generator points.  This reading is refutable
(`not_forall_psi_hasLiteralTableCoordinates`); it is kept only to record that
defect of the original formulation. -/
def HasLiteralTableCoordinates (w : QWitness k K) : Prop :=
  ∃ (a b c d x : K) (hind : AlgebraicIndependent k ![a, b, c, d, x]),
    w = qWitness hind

/-- The table witness with its `A`-generators exchanged is not a table
witness: the first generator of a table witness is its point `S`, while here
it is the point `P`. -/
theorem not_hasLiteralTableCoordinates_swapA {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    ¬ (qWitness hind).swapA.HasLiteralTableCoordinates := by
  rintro ⟨a', b', c', d', x', hind', h⟩
  have h1 : (qWitness hind).swapA.A₁ = (qWitness hind').A₁ := by rw [h]
  have h2 : (qWitness hind).swapA.S = (qWitness hind').S := by rw [h]
  have hba : ClosedIF.point k b = ClosedIF.point k a :=
    congrArg Subtype.val (h1.trans h2.symm)
  exact qtable_a_notMem_b hind (ClosedIF.point_eq_point_iff.1 hba).2

end QWitness

/-- **The literal reading of table (8.5) is false** as soon as one table
witness exists: no extraction theorem can pin the six generator points. -/
theorem not_forall_psi_hasLiteralTableCoordinates
    {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    ¬ ∀ w : QWitness k K, w.Psi → w.HasLiteralTableCoordinates := fun h ↦
  QWitness.not_hasLiteralTableCoordinates_swapA hind
    (h _ (qWitness_psi hind).swapA)

namespace QWitness

/-- A witness has the affine-grid coordinates of blueprint (8.5) when its three
rank-two joins `A, B, C` and its fifteen remaining points are those of the
explicit table witness for some independent `a, b, c, d, x`.

Equality of closed points is precisely the permitted replacement by
interalgebraic representatives.  The individual generators of `A, B, C` are
not constrained, since `Psi` does not see them. -/
def HasAffineGridCoordinates (w : QWitness k K) : Prop :=
  ∃ (a b c d x : K) (hind : AlgebraicIndependent k ![a, b, c, d, x]),
    w.A = (qWitness hind).A ∧ w.B = (qWitness hind).B ∧
    w.C = (qWitness hind).C ∧ w.D = (qWitness hind).D ∧
    w.E = (qWitness hind).E ∧ w.F = (qWitness hind).F ∧
    w.G = (qWitness hind).G ∧ w.H = (qWitness hind).H ∧
    w.I = (qWitness hind).I ∧ w.P = (qWitness hind).P ∧
    w.Q = (qWitness hind).Q ∧ w.R = (qWitness hind).R ∧
    w.S = (qWitness hind).S ∧ w.T = (qWitness hind).T ∧
    w.U = (qWitness hind).U ∧ w.X = (qWitness hind).X ∧
    w.Y = (qWitness hind).Y ∧ w.Z = (qWitness hind).Z

/-- The literal reading implies the corrected one. -/
theorem HasLiteralTableCoordinates.hasAffineGridCoordinates
    {w : QWitness k K} (h : w.HasLiteralTableCoordinates) :
    w.HasAffineGridCoordinates := by
  obtain ⟨a, b, c, d, x, hind, rfl⟩ := h
  exact ⟨a, b, c, d, x, hind, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The explicit table witness has its defining affine-grid coordinates. -/
theorem hasAffineGridCoordinates_qWitness {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    (qWitness hind).HasAffineGridCoordinates :=
  HasLiteralTableCoordinates.hasAffineGridCoordinates ⟨a, b, c, d, x, hind, rfl⟩

/-- Affine-grid coordinates are insensitive to exchanging the generators of
`A`. -/
theorem HasAffineGridCoordinates.swapA {w : QWitness k K}
    (h : w.HasAffineGridCoordinates) : w.swapA.HasAffineGridCoordinates := by
  obtain ⟨a, b, c, d, x, hind, hA, hB, hC, hD, hE, hF, hG, hH, hI, hP, hQ, hR,
    hS, hT, hU, hX, hY, hZ⟩ := h
  exact ⟨a, b, c, d, x, hind, w.swapA_A.trans hA, hB, hC, hD, hE, hF, hG, hH,
    hI, hP, hQ, hR, hS, hT, hU, hX, hY, hZ⟩

/-- The corrected conclusion covers the counterexample to the literal one: the
table witness with exchanged `A`-generators has affine-grid coordinates. -/
theorem hasAffineGridCoordinates_swapA {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    (qWitness hind).swapA.HasAffineGridCoordinates :=
  (hasAffineGridCoordinates_qWitness hind).swapA

/-- The easy implication: every witness with affine-grid coordinates
satisfies `Psi` over any base field, by soundness of the explicit table
witness. The converse is the open extraction theorem. -/
theorem HasAffineGridCoordinates.psi {w : QWitness k K}
    (h : w.HasAffineGridCoordinates) : w.Psi := by
  obtain ⟨a, b, c, d, x, hind, hA, hB, hC, hD, hE, hF, hG, hH, hI, hP, hQ, hR,
    hS, hT, hU, hX, hY, hZ⟩ := h
  exact (qWitness_psi hind).of_eq hA hB hC hD hE hF hG hH hI hP hQ hR hS hT hU
    hX hY hZ

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

/-- The four free outputs of the table witness are a semantic
`Q`-quadruple. -/
theorem qSem_qWitness {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    QSem (qWitness hind).P (qWitness hind).D (qWitness hind).Y
      (qWitness hind).I := by
  refine ⟨b, a * x, affineGrid_output_independent hind, rfl, rfl, ?_, ?_⟩
  · change ClosedIF.point k (a * x + b) = ClosedIF.point k (b + a * x)
    rw [add_comm]
  · change ClosedIF.point k (a * x / b) = ClosedIF.point k (b / (a * x))
    exact ClosedIF.point_div_symm (a * x) b

/-- Once a witness has affine-grid coordinates, its four free outputs are
exactly a semantic `Q`-quadruple.  This is the algebraic final step of the
completeness direction. -/
theorem qSem_of_hasAffineGridCoordinates {w : QWitness k K}
    (hgrid : w.HasAffineGridCoordinates) :
    QSem w.P w.D w.Y w.I := by
  obtain ⟨a, b, c, d, x, hind, -, -, -, hD, -, -, -, -, hI, hP, -, -, -, -, -,
    -, hY, -⟩ := hgrid
  rw [hP, hD, hY, hI]
  exact qSem_qWitness hind

end QWitness

/-- The open geometric core of blueprint Lemma 8.5, in corrected form, over
algebraically closed `k ⊆ K`: every `Psi`-witness has affine-grid
coordinates.  This is an open proposition, not a theorem. -/
def AffineGridExtraction (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] : Prop :=
  ∀ w : QWitness k K, w.Psi → w.HasAffineGridCoordinates

/-- Given the easy implication `HasAffineGridCoordinates.psi`, the open
extraction target is equivalent to the statement that `Psi`-witnesses are
exactly the witnesses with affine-grid coordinates.  Both sides are open. -/
theorem affineGridExtraction_iff [IsAlgClosed k] [IsAlgClosed K] :
    AffineGridExtraction k K ↔
      ∀ w : QWitness k K, w.Psi ↔ w.HasAffineGridCoordinates :=
  ⟨fun h w ↦ ⟨h w, QWitness.HasAffineGridCoordinates.psi⟩,
    fun h w ↦ (h w).1⟩

/-- Witness-level completeness of `Q` over algebraically closed `k ⊆ K`: the
four free outputs of every `Psi`-witness form a semantic `Q`-quadruple.  This
open proposition is all that the completeness direction `QGeom → QSem` uses;
it is the acceptance boundary for the corrected blueprint Lemma 8.5. -/
def QCompletenessACF (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] : Prop :=
  ∀ w : QWitness k K, w.Psi → QSem w.P w.D w.Y w.I

/-- Affine-grid extraction gives witness-level completeness. -/
theorem AffineGridExtraction.qCompletenessACF [IsAlgClosed k] [IsAlgClosed K]
    (h : AffineGridExtraction k K) : QCompletenessACF k K :=
  fun w hw ↦ QWitness.qSem_of_hasAffineGridCoordinates (h w hw)

/-- Witness-level completeness gives the completeness direction
`QGeom → QSem`. -/
theorem qSem_of_qGeom [IsAlgClosed k] [IsAlgClosed K]
    (hcompl : QCompletenessACF k K)
    {P D Y I : Point k K} (h : QGeom P D Y I) : QSem P D Y I := by
  obtain ⟨w, hpsi, rfl, rfl, rfl, rfl⟩ := h
  exact hcompl w hpsi

/-- Conditional correctness of `Q` over algebraically closed fields:
witness-level completeness plus the proved fresh-element soundness gives
`QGeom ↔ QSem`. -/
theorem qGeom_iff_qSem [IsAlgClosed k] [IsAlgClosed K]
    (hcompl : QCompletenessACF k K)
    (hfresh : ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K))
    {P D Y I : Point k K} :
    QGeom P D Y I ↔ QSem P D Y I :=
  ⟨qSem_of_qGeom hcompl, qGeom_of_qSem hfresh⟩

end

end AclGeom
