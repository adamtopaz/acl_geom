/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableMiddle
import AclGeom.Config.ChunkCurveSemilinearGroupedStableTriangle

/-!
# The involutive e/a base chart for the stable grouped middle

The semantic source chart for the `a` presentation swaps the independent
`e` and `a` rank-two blocks and fixes every other displayed coordinate.
Consequently it is an involution on the whole generated source field, not
only on its chosen generators.  This finite-order fact underlies the next
two-orbit stabilization of the grouped middle cover.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)

set_option maxHeartbeats 1000000 in
-- Extensionality crosses the nested semantic-source presentation.
/-- The semantic `e→a` source automorphism is an involution on the whole
nine-coordinate common source field. -/
theorem commonSourceRightAAut_trans_self
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.commonSourceRightAAut hind).trans
        (R.commonSourceRightAAut hind) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.algHom_ext_of_eq_adjoin k
    R.rightESourceField_eq_commonSourceField.symm
  rintro _ ⟨i, rfl⟩
  change R.commonSourceRightAAut hind
      (R.commonSourceRightAAut hind
        (R.rightESemanticSourceCoordinate i)) =
    R.rightESemanticSourceCoordinate i
  rw [R.commonSourceRightAAut_apply hind i]
  fin_cases i
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 0) =
        R.rightESemanticSourceCoordinate 0
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 1) =
        R.rightESemanticSourceCoordinate 1
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 4) =
        R.rightESemanticSourceCoordinate 2
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 5) =
        R.rightESemanticSourceCoordinate 3
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 2) =
        R.rightESemanticSourceCoordinate 4
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 3) =
        R.rightESemanticSourceCoordinate 5
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 6) =
        R.rightESemanticSourceCoordinate 6
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 7) =
        R.rightESemanticSourceCoordinate 7
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl
  · change R.commonSourceRightAAut hind
      (R.rightESemanticSourceCoordinate 8) =
        R.rightESemanticSourceCoordinate 8
    rw [R.commonSourceRightAAut_apply]
    apply Subtype.ext
    rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
