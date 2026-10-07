/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobClass

/-!
# Incidence content of the Frobenius link

A geometric product point lies on the line through its factors: the multiplication diagram inside
`Q'Geom` puts `X, Y, E` on one line.  Consequently the multiplier point of a direct Frobenius link
lies on the three lines joining corresponding `X`, `Q` and `R` coordinates of the two `j`-tuples,
which is the incidence configuration of EH95 Lemma 2.8 (Fig. 3).  No correctness or completeness of
`Q`/`Q′` is used.

**Status:** the incidence reduction is proved (#23). `FrobLinkSemantic` proves direct-link
rigidity for supplied semantic endpoint witnesses over arbitrary base fields. Unconditional
geometric bridge completeness remains open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- In a multiplication diagram, the first factor lies on the line through the second factor and
the product. -/
theorem MulDiagram.X_le_sup {X Y V E A₀ B₀ C₀ D₀ : Point k K}
    (h : MulDiagram X Y V E A₀ B₀ C₀ D₀) : X.1 ≤ Y.1 ⊔ E.1 := by
  have hYE : Y ≠ E := fun hYE ↦ by
    have := h.distinct.ne (show (1 : Fin 8) ≠ 3 by decide)
    exact this (by simpa using hYE)
  have hle : Y.1 ⊔ E.1 ≤ X.1 ⊔ (Y.1 ⊔ (E.1 ⊔ V.1)) :=
    sup_le (le_sup_left.trans le_sup_right)
      (le_sup_left.trans (le_sup_right.trans le_sup_right))
  have hnot : ∀ P : Point k K, P.1 ≤ X.1 ⊔ (Y.1 ⊔ (E.1 ⊔ V.1)) → ¬ Y.1 ⊔ E.1 ≤ P.1 := by
    intro P _ hP
    apply hYE
    have h1 : Y.1 = P.1 := (P.2.le_iff.1 (le_sup_left.trans hP)).resolve_left Y.2.1
    have h2 : E.1 = P.1 := (P.2.le_iff.1 (le_sup_right.trans hP)).resolve_left E.2.1
    exact Subtype.ext (h1.trans h2.symm)
  have heq := RankEq.eq_of_le_of_not_le_point hle h.line_XYEV hnot
  rw [heq]
  exact le_sup_left

/-- **The first factor lies on the line through the second factor and the product.** The points
`V, U` are automatically distinct, by the distinctness clause of the multiplication diagram. -/
theorem MulPoint.le_sup {C V U : Point k K} (h : MulPoint C V U) : C.1 ≤ V.1 ⊔ U.1 := by
  obtain ⟨_, _, _, _, _, _, _, hdiag⟩ := h
  exact hdiag.X_le_sup

/-- The second factor of a geometric product point differs from the product. -/
theorem MulPoint.ne {C V U : Point k K} (h : MulPoint C V U) : V ≠ U := by
  obtain ⟨_, _, _, _, _, _, _, hdiag⟩ := h
  intro hVU
  exact hdiag.distinct.ne (show (1 : Fin 8) ≠ 3 by decide) (by simpa using hVU)

/-- **Concurrency of a direct Frobenius link** (EH95 Lemma 2.8, Fig. 3): the multiplier point lies
on the three lines joining the corresponding `X`, `Q` and `R` coordinates. -/
theorem DirectFrobLink.exists_concurrent {u v : Fin 5 → Point k K} (h : DirectFrobLink u v) :
    ∃ C : Point k K, C.1 ≤ (v 0).1 ⊔ (u 0).1 ∧ C.1 ≤ (v 2).1 ⊔ (u 2).1 ∧
      C.1 ≤ (v 3).1 ⊔ (u 3).1 := by
  obtain ⟨C, h0, h2, h3⟩ := h.multiplier
  exact ⟨C, h0.le_sup, h2.le_sup, h3.le_sup⟩

/-- The concurrency in lattice form: the multiplier point lies below the meet of the three
lines. -/
theorem DirectFrobLink.exists_le_inf {u v : Fin 5 → Point k K} (h : DirectFrobLink u v) :
    ∃ C : Point k K, C.1 ≤ ((v 0).1 ⊔ (u 0).1) ⊓ ((v 2).1 ⊔ (u 2).1) ⊓ ((v 3).1 ⊔ (u 3).1) := by
  obtain ⟨C, h0, h2, h3⟩ := h.exists_concurrent
  exact ⟨C, le_inf (le_inf h0 h2) h3⟩

end AclGeom
