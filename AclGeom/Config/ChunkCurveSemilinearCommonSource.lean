/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonSourceA
import AclGeom.Config.ChunkCurveSemilinearCommonSourceB
import AclGeom.Config.ChunkCurveSemilinearCommonSourceC

/-!
# Four semantic triangles extended to one common finite source

This module collects the finite pullbacks of the inverse-oriented
`e/a/b/c` triangles.  Their restricted source charts all have the same
literal codomain, and all four carry the whole intrinsic germ to one
literal embedding there.
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

/-- The four finite common-source charts simultaneously carry their whole
intrinsic germs to the same embedding in one literal finite field. -/
theorem fourRightSemilinearCommonSourceCharts_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRightSemilinearCommonSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToSeRightSemilinearExtendedSourceRingHom
            L hind) =
        R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind ∧
      (R.sAaRightSemilinearCommonSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom
            L hind) =
        R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind ∧
      (R.sbRightSemilinearCommonSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToSbRightSemilinearExtendedSourceRingHom
            L hind) =
        R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind ∧
      (R.sAcRightSemilinearCommonSourceChart L hind).toRingHom.comp
          (R.bGermCoefficientToSAcRightSemilinearExtendedSourceRingHom
            L hind) =
        R.bGermCoefficientToRightSemilinearCommonSourceRingHom L hind := by
  exact ⟨R.seRightSemilinearCommonSourceChart_comp_bGermCoefficient L hind,
    R.sAaRightSemilinearCommonSourceChart_comp_bGermCoefficient L hind,
    R.sbRightSemilinearCommonSourceChart_comp_bGermCoefficient L hind,
    R.sAcRightSemilinearCommonSourceChart_comp_bGermCoefficient L hind⟩

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
