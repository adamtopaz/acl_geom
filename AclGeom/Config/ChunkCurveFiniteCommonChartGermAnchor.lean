/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChartFiniteness

/-!
# The intrinsic germ anchor for finite semilinear common charts

The selected `B`-germ first enters the established graph/right source.
Each finite comparison chart can then pull this one intrinsic anchor into
its own finite source.
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
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The intrinsic `e` germ embedded in the established graph/right source. -/
noncomputable def bGermCoefficientToSelectedGraphRightSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
  (R.semanticSourceToSelectedGraphRightSourceRingHom L hind).comp
    (R.seBGermCoefficientToSemanticSourceAlgHom L hind).toRingHom

/-- Evaluation formula for the intrinsic germ anchor in the old graph/right
source. -/
@[simp] theorem bGermCoefficientToSelectedGraphRightSourceRingHom_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind x =
      R.semanticSourceToSelectedGraphRightSourceRingHom L hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x) :=
  rfl

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
