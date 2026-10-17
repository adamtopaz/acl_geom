/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Transfer.JCorrectness
import AclGeom.Transfer.MulDiagramProduct

/-!
# Corrected geometric `Q` and `Q′` over perfect fields

The original source asserted that the geometric relations `Q` and `Q′` are correct over an
arbitrary perfect field `K/k` of rank five.  Both assertions are refuted
(`Counterexamples.QRefutation`): a semantic witness over `k̄ ⊆ K̄` need not have representatives
in `K`.  This module states the corrected geometric forms, with the missing representatives
supplied by a `K`-point of the geometric `J` relation.

* `qSem_iff_exists_jGeom`: semantic `Q` is the projection of geometric `J`,
  `QSem X Y S V ↔ ∃ P, JGeom X P Y S V`.  This combines the semantic projection
  `qSem_iff_exists_jSem` with the correctness of `J` over perfect fields of rank five
  (`jGeom_iff_jSem_of_perfectField`).
* `q'Sem_iff_exists_jGeom_mulDiagram`: semantic `Q′` is a projected `Q` followed by a
  multiplication diagram.  Soundness takes the actual ratio point and a fresh parameter for the
  diagram (`mulDiagram_of_indep`); completeness reads the product point from the actual
  representatives of the projected `Q` (`MulDiagram.product_point`).

The raw geometric predicates are unchanged, and the existential `J` point is part of the
statement: raw `QGeom` does not imply the projected relation outside algebraically closed
fields.  No general descent of configuration witnesses is asserted.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the corrected projected `Q` and `Q′` equivalences are proved over perfect fields
of rank five (#25).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Semantic `Q` is the projection of geometric `J`** over a perfect field of rank five: four
points form a semantic `Q`-quadruple exactly when some point `P` completes them to a geometric
`J`-tuple `(X, P, Y, S, V)`. -/
theorem qSem_iff_exists_jGeom [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X Y S V : Point k K} : QSem X Y S V ↔ ∃ P : Point k K, JGeom X P Y S V :=
  qSem_iff_exists_jSem.trans (exists_congr fun _ ↦ (jGeom_iff_jSem_of_perfectField htr).symm)

/-- **Semantic `Q′` through the projected `Q`** over a perfect field of rank five: four points
form a semantic `Q′`-quadruple exactly when a ratio point `V` makes `(X, Y, S, V)` a projected
`Q`-quadruple and a multiplication diagram carries `(X, Y, V)` to the product point `E`. -/
theorem q'Sem_iff_exists_jGeom_mulDiagram [PerfectField K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X Y S E : Point k K} :
    Q'Sem X Y S E ↔ ∃ V P A B C D : Point k K,
      JGeom X P Y S V ∧ MulDiagram X Y V E A B C D := by
  constructor
  · classical
    rintro ⟨x, y, hxy, hX, hY, hS, hE⟩
    -- A parameter fresh over the two representatives.
    obtain ⟨a, ha⟩ := fresh_three_of_five_le_trdeg htr {x, y}
      (Finset.card_le_two.trans (by decide))
    have ha' : a ∉ racl k ({x, y} : Set K) := by simpa using ha
    have htriple : AlgebraicIndependent k ![x, y, a] := by
      have h := (AlgebraicIndependent.insert_middle hxy ha').comp ![0, 2, 1] (by decide)
      convert h using 1
      funext i
      fin_cases i <;> rfl
    -- The actual ratio point and its projected `Q`-quadruple.
    set V : Point k K := Point.mk' k (x / y) (mtable_div_notMem_bot htriple)
    obtain ⟨P, hP⟩ : ∃ P : Point k K, JGeom X P Y S V :=
      (qSem_iff_exists_jGeom htr).1 ⟨x, y, hxy, hX, hY, hS, rfl⟩
    -- The multiplication diagram of the independent triple.
    have hM := mulDiagram_of_indep htriple
    have e1 : Point.mk' k x (mtable_x_notMem_bot htriple) = X := Subtype.ext (by rw [hX]; rfl)
    have e2 : Point.mk' k y (mtable_y_notMem_bot htriple) = Y := Subtype.ext (by rw [hY]; rfl)
    have e4 : Point.mk' k (x * y) (mtable_mul_notMem_bot htriple) = E :=
      Subtype.ext (by rw [hE]; rfl)
    rw [e1, e2, e4] at hM
    exact ⟨V, P, _, _, _, _, hP, hM⟩
  · rintro ⟨V, P, A, B, C, D, hJ, hmul⟩
    obtain ⟨x, y, hxy, hX, hY, hS, hV⟩ := (qSem_iff_exists_jGeom htr).2 ⟨P, hJ⟩
    exact ⟨x, y, hxy, hX, hY, hS, hmul.product_point hX hY hV⟩

end AclGeom
