/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.AffineGrid
import AclGeom.Config.Multiplication

/-!
# A degenerate `Psi`-witness: geometric `Q` is not complete

Clause (vii) of `Psi` only asks the seven meets to be points.  Nothing prevents the auxiliary
point `Q` from coinciding with `T`.  Start from the table-7.1 witness `qWitness` for independent
`a, b, c, d, x` and change five fields:

  `Q := T = [c]`, `E := [c]`, `G := [c]`, `H := S = [a]`, `I := D = [ax]`.

The clauses (i)–(vi) and the meets `D`, `F`, `R` are untouched.  The four changed meets are again
literal independent-variable intersections (blueprint eq. 8.9a):

* `E`: `([c] ∨ [ax+b]) ∧ ([c] ∨ [c(ax+b)+d]) = [c]`;
* `G`: `([b] ∨ [c]) ∧ ([c] ∨ [bc+d]) = [c]`;
* `H`: `([ac] ∨ [c]) ∧ ([a] ∨ [b]) = [a]`;
* `I`: `([a] ∨ [x]) ∧ ([b] ∨ [ax+b]) = [ax]`, which is meet `D` with its two sides exchanged.

So `qWitnessDegenerate` satisfies `Psi` over any base field (`qWitnessDegenerate_psi`).  Its
outputs `(P, D, Y, I) = ([b], [ax], [ax+b], [ax])` have `I = D`, while no semantic `Q`-quadruple
`([u], [v], [u+v], [u/v])` has that shape (`QSem.ratio_ne`): `[u/v] = [v]` would make `u`
algebraic over `v`.  Consequently:

* `not_forall_qGeom_imp_qSem_of_five_indep`: whenever `K/k` has five independent elements,
  some geometric `Q`-quadruple is not semantic;
* `not_qCompletenessACF` and `not_affineGridExtraction`: the witness-level completeness
  `QCompletenessACF` and the legacy unguarded target `AffineGridExtraction` are false over
  every algebraically closed pair with five independent elements;
* `not_forall_qGeom_imp_exists_jGeom_of_five_indep`: the unguarded geometric projection to
  `J` is false for the same witness, because `J` forces its ratio and second points to differ.

The original unguarded completeness half of blueprint Thm `q-correct` and the generator-corrected
legacy Lemma 8.5 are false. Their guarded replacements remain open (#27).
This witness does not refute geometric `J`: the multiplication
diagram's distinctness clause separates the ratio point of every `Q`-instance inside `Q'Geom`
and `JGeom` from its second point.  Completeness under that guard is not addressed here.

**Status:** refutations proved (#27). Guarded completeness remains open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section Degenerate

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/-- Side condition for the degenerate meet `E`: `c(ax+b)+d` is not algebraic over `{ax+b, c}`,
since otherwise `d` would be algebraic over `{a, b, c, x}`. -/
private theorem qtable_Z_notMem_Y_c :
    c * (a * x + b) + d ∉ racl k ({a * x + b, c} : Set K) := by
  intro hmem
  have hY : a * x + b ∈ racl k ({a * x + b, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a * x + b, c} : Set K) := subset_racl k _ (by simp)
  have hd := sub_mem hmem (MulMemClass.mul_mem hc hY)
  rw [add_sub_cancel_left] at hd
  have hsub : racl k ({a * x + b, c} : Set K) ≤ racl k ({a, b, c, x} : Set K) := by
    refine racl_le_of_subset_racl ?_
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    have ha : a ∈ racl k ({a, b, c, x} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({a, b, c, x} : Set K) := subset_racl k _ (by simp)
    have hc' : c ∈ racl k ({a, b, c, x} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, b, c, x} : Set K) := subset_racl k _ (by simp)
    exact ⟨add_mem (MulMemClass.mul_mem ha hx) hb, hc'⟩
  exact qtable_d_notMem_abcx hind (hsub hd)

/-- Side condition for the degenerate meet `G`: `bc+d` is not algebraic over `{b, c}`. -/
private theorem qtable_R_notMem_b_c : b * c + d ∉ racl k ({b, c} : Set K) := by
  intro hmem
  have hb : b ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have hd := sub_mem hmem (MulMemClass.mul_mem hb hc)
  rw [add_sub_cancel_left] at hd
  exact qtable_d_notMem_bc hind hd

/-- The join `[ac] ∨ [c]` in the degenerate meet `H` is `[a] ∨ [c]`. -/
private theorem qtable_racl_ac_c :
    racl k ({a * c, c} : Set K) = racl k ({a, c} : Set K) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact ⟨MulMemClass.mul_mem ha hc, hc⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    have hac : a * c ∈ racl k ({a * c, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a * c, c} : Set K) := subset_racl k _ (by simp)
    have ha := MulMemClass.mul_mem hac (inv_mem hc)
    rw [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at ha
    exact ⟨ha, hc⟩

/-- **The degenerate table witness**: the table-7.1 witness `qWitness` with `Q := T`, `E := T`,
`G := T`, `H := S` and `I := D`. -/
def qWitnessDegenerate : QWitness k K :=
  { qWitness hind with
    Q := (qWitness hind).T
    E := (qWitness hind).T
    G := (qWitness hind).T
    H := (qWitness hind).S
    I := (qWitness hind).D }

-- The opaque witness parameter keeps the kernel from comparing two full,
-- different concrete records before projecting their unchanged fields.
-- The sole consumer below proves the three meet hypotheses from independence.
omit hind in
private theorem psi_degenerate_of_meets (w : QWitness k K) (hw : w.Psi)
    (hE : (w.T.1 ⊔ w.Y.1) ⊓ (w.T.1 ⊔ w.Z.1) = w.T.1)
    (hG : (w.P.1 ⊔ w.T.1) ⊓ (w.T.1 ⊔ w.R.1) = w.T.1)
    (hH : (w.U.1 ⊔ w.T.1) ⊓ w.A = w.S.1) :
    ({ w with Q := w.T, E := w.T, G := w.T, H := w.S, I := w.D } : QWitness k K).Psi
    where
  rank_ABC := hw.rank_ABC
  rank_AB := hw.rank_AB
  rank_BC := hw.rank_BC
  rank_AC := hw.rank_AC
  X_le := hw.X_le
  Z_le := hw.Z_le
  X_notLe := hw.X_notLe
  Y_notLe := hw.Y_notLe
  Z_notLe := hw.Z_notLe
  X_free := hw.X_free
  Z_freeB := hw.Z_freeB
  Z_freeC := hw.Z_freeC
  S_le := hw.S_le
  T_le := hw.T_le
  U_le := hw.U_le
  rank_STU := hw.rank_STU
  quad := hw.quad
  meet_D := hw.meet_D
  meet_E := hE
  meet_F := hw.meet_F
  meet_G := hG
  meet_I := by
    rw [inf_comm]
    exact hw.meet_D
  meet_H := hH
  meet_R := hw.meet_R

/-- **The degenerate witness satisfies `Psi`**, over any base field.  Clauses (i)–(vi) and the
meets `D`, `F`, `R` are those of `qWitness_psi`; the meets `E`, `G`, `H`, `I` are
independent-variable intersections. -/
theorem qWitnessDegenerate_psi : (qWitnessDegenerate hind).Psi := by
  apply psi_degenerate_of_meets (qWitness hind) (qWitness_psi hind)
  · change (ClosedIF.point k c ⊔ ClosedIF.point k (a * x + b)) ⊓
      (ClosedIF.point k c ⊔ ClosedIF.point k (c * (a * x + b) + d)) = ClosedIF.point k c
    exact sup_point_inf_sup_point_eq rfl rfl (qtable_Z_notMem_Y_c hind)
  · change (ClosedIF.point k b ⊔ ClosedIF.point k c) ⊓
      (ClosedIF.point k c ⊔ ClosedIF.point k (b * c + d)) = ClosedIF.point k c
    exact sup_point_inf_sup_point_eq (congrArg (racl k) (Set.pair_comm b c)) rfl
      (qtable_R_notMem_b_c hind)
  · change (ClosedIF.point k (a * c) ⊔ ClosedIF.point k c) ⊓
      (ClosedIF.point k a ⊔ ClosedIF.point k b) = ClosedIF.point k a
    refine sup_point_inf_sup_point_eq (qtable_racl_ac_c hind) rfl ?_
    rw [Set.pair_comm]
    exact qtable_b_notMem_ac hind

/-- **The outputs of the degenerate witness are not a semantic `Q`-quadruple**: its ratio point
`I` is its second point `D`, contradicting `QSem.ratio_ne`. -/
theorem not_qSem_qWitnessDegenerate :
    ¬ QSem (qWitnessDegenerate hind).P (qWitnessDegenerate hind).D
      (qWitnessDegenerate hind).Y (qWitnessDegenerate hind).I := fun h ↦
  h.ratio_ne rfl

/-- **Geometric `Q` is not semantic** whenever `K/k` has five independent elements, over any
base field: the outputs of the degenerate witness form a geometric `Q`-quadruple. -/
theorem not_forall_qGeom_imp_qSem_of_five_indep :
    ¬ ∀ P D Y I : Point k K, QGeom P D Y I → QSem P D Y I := fun h ↦
  not_qSem_qWitnessDegenerate hind
    (h _ _ _ _ ⟨_, qWitnessDegenerate_psi hind, rfl, rfl, rfl, rfl⟩)

/-- **The unguarded geometric projection to `J` is false** with five independent elements,
over any base: the degenerate `Q` outputs have equal ratio and second points, while `J`'s
first multiplication diagram forces those points to differ (#27). -/
theorem not_forall_qGeom_imp_exists_jGeom_of_five_indep :
    ¬ ∀ X Q R A : Point k K, QGeom X Q R A → ∃ P : Point k K, JGeom X P Q R A := by
  intro h
  obtain ⟨P, hP⟩ := h _ _ _ _ ⟨_, qWitnessDegenerate_psi hind, rfl, rfl, rfl, rfl⟩
  exact hP.2.1.ne rfl

end Degenerate

/-- **Witness-level completeness of `Q` is false** over every algebraically closed pair
`k ⊆ K` with five independent elements: the degenerate witness satisfies `Psi`, but its outputs
are not semantic. -/
theorem not_qCompletenessACF [IsAlgClosed k] [IsAlgClosed K] {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) : ¬ QCompletenessACF k K := fun h ↦
  not_qSem_qWitnessDegenerate hind (h _ (qWitnessDegenerate_psi hind))

/-- **The legacy unguarded affine-grid extraction target is false** over every algebraically closed
pair `k ⊆ K` with five independent elements, since it implies `QCompletenessACF`. -/
theorem not_affineGridExtraction [IsAlgClosed k] [IsAlgClosed K] {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) : ¬ AffineGridExtraction k K := fun h ↦
  not_qCompletenessACF hind h.qCompletenessACF

end

end AclGeom
