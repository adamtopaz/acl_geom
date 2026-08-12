/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearTriangleE
import AclGeom.Config.ChunkCurveSemilinearTriangleA
import AclGeom.Config.ChunkCurveSemilinearTriangleB
import AclGeom.Config.ChunkCurveSemilinearTriangleC

/-!
# Four semantic triangles with inverse semilinear source charts

This module collects the `e/a/b/c` source presentations oriented back to
one selected graph/right source and one whole intrinsic `B`-germ embedding.
-/

namespace AclGeom

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- Simultaneously, the four inverse semilinear source charts identify the
entire intrinsic `e/a/b/c` germs with one literal embedding in the selected
graph/right source. -/
theorem fourRightSemilinearSourceCharts_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
        R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind ∧
      (R.sAaRightSemilinearSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToRightASourceRingHom L hind) =
        R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind ∧
      (R.sbRightSemilinearSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToRightBSourceRingHom L hind) =
        R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind ∧
      (R.sAcRightSemilinearSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToRightCSourceRingHom L hind) =
        R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind := by
  refine ⟨?_, R.rightASourceChart_comp_bGermCoefficient L hind,
    R.rightBSourceChart_comp_bGermCoefficient L hind,
    R.rightCSourceChart_comp_bGermCoefficient L hind⟩
  rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
