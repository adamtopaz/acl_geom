/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.SmoothCurveCompletion
/-!
# Connected Group Completion

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual one-dimensional connected algebraic group embeds into an internally
constructed proper normal curve. Every actual automorphism of the ORIGINAL group scheme
extends uniquely to that curve. Smoothness and local normality are internal, and no model,
open embedding or extension certificate is a premise. This is the completion and individual
translation-extension step of the source `lem:affine-action`; projectivity and jointly regular
families remain separate obligations. -/
theorem connectedGroup_completion_and_extensions (G : ConnectedAlgebraicGroup k)
    (hdim : topologicalKrullDim G.toGroupScheme.X.left = 1) :
    ∃ (Y : Over (Spec (.of k))) (j : G.toGroupScheme.X ⟶ Y),
      IsIntegral Y.left ∧ IsProper Y.hom ∧ IsOpenImmersion j.left ∧
        topologicalKrullDim Y.left = 1 ∧
        (∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y)) ∧
        (∀ a : G.toGroupScheme.X ≅ G.toGroupScheme.X,
          ∃! F : Y ≅ Y, j ≫ F.hom = a.hom ≫ j) := by
  have : GrpObj (Over.mk G.toGroupScheme.X.hom) := by
    change GrpObj G.toGroupScheme.X
    infer_instance
  have : Smooth G.toGroupScheme.X.hom := smooth_of_grpObj _
  obtain ⟨Y, j, hY, hproper, hopen, hdimY, hnormal⟩ :=
    exists_proper_normal_completion G.toGroupScheme.X hdim
  have : IsIntegral Y.left := hY
  have : IsProper Y.hom := hproper
  have : IsOpenImmersion j.left := hopen
  exact ⟨Y, j, hY, hproper, hopen, hdimY, hnormal,
    fun a ↦ ProperCurve.existsUnique_iso_extension Y G.toGroupScheme.X hdimY.le hnormal j a⟩

end
end AclGeom.CurveCompletion
