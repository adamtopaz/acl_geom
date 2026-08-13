/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedSourceFiniteness

/-!
# Intrinsic restrictions on the grouped finite triangles

The four grouped source triangles retain the complete intrinsic-germ
restriction squares proved before the sources were reoriented.  Each
middle and target anchor is the old selected-branch anchor included in the
corresponding source extension.  The left, right, and strict direct arrows
therefore agree on the whole intrinsic germ for every face.
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

/-! ### The `s·e=u` face -/

/-- The selected `e` middle anchor included in the grouped middle field. -/
noncomputable def seBGermCoefficientToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.seGroupedSourceField L hind)).comp
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)

/-- The matching selected `e` anchor in the grouped target field. -/
noncomputable def seBGermCoefficientToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.seSelectedGraphRightCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.seGroupedSourceField L hind)).comp
    ((R.seSelectedGraphRightCompositionTriangle L hind).right.toRingHom.comp
      (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The grouped pullback source carries a nested intermediate-field tower.
/-- The grouped `e` left arrow restricts to the named middle anchor. -/
theorem seGrouped_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seGroupedCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSeGroupedSource L hind) =
      R.seBGermCoefficientToGroupedMiddleRingHom L hind := by
  let T := R.seSelectedGraphRightCompositionTriangle L hind
  let X := R.seGroupedSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind)
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)
    (R.seSelectedGraphRight_left_comp_bGermCoefficient L hind)

/-- The grouped `e` right arrow restricts to the named target anchor. -/
theorem seGrouped_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.seBGermCoefficientToGroupedMiddleRingHom L hind) =
      R.seBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.seSelectedGraphRightCompositionTriangle L hind
  let X := R.seGroupedSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.seBGermCoefficientToSelectedGraphRightMiddleRingHom L hind)

/-- The grouped strict `u` arrow has the same `e` target restriction. -/
theorem seGrouped_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seGroupedCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSeGroupedSource L hind) =
      R.seBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.seGroupedCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSeGroupedSource L hind)
    (R.seBGermCoefficientToGroupedMiddleRingHom L hind)
    (R.seBGermCoefficientToGroupedTargetRingHom L hind)
    (R.seGrouped_left_comp_bGermCoefficient L hind)
    (R.seGrouped_right_comp_bGermCoefficient L hind)

/-! ### The `sA·a=u` face -/

/-- The selected `a` middle anchor included in the grouped middle field. -/
noncomputable def sAaBGermCoefficientToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaGroupedSourceField L hind)).comp
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The matching selected `a` anchor in the grouped target field. -/
noncomputable def sAaBGermCoefficientToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaGroupedSourceField L hind)).comp
    ((R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The grouped pullback source carries a nested intermediate-field tower.
/-- The grouped `a` left arrow restricts to the named middle anchor. -/
theorem sAaGrouped_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaGroupedCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSAaGroupedSource L hind) =
      R.sAaBGermCoefficientToGroupedMiddleRingHom L hind := by
  let T := R.sAaRightSemilinearCompositionTriangle L hind
  let X := R.sAaGroupedSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightASourceRingHom L hind)
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sAaRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The grouped `a` right arrow restricts to the named target anchor. -/
theorem sAaGrouped_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaBGermCoefficientToGroupedMiddleRingHom L hind) =
      R.sAaBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sAaRightSemilinearCompositionTriangle L hind
  let X := R.sAaGroupedSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The grouped strict `u` arrow has the same `a` target restriction. -/
theorem sAaGrouped_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaGroupedCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSAaGroupedSource L hind) =
      R.sAaBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sAaGroupedCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSAaGroupedSource L hind)
    (R.sAaBGermCoefficientToGroupedMiddleRingHom L hind)
    (R.sAaBGermCoefficientToGroupedTargetRingHom L hind)
    (R.sAaGrouped_left_comp_bGermCoefficient L hind)
    (R.sAaGrouped_right_comp_bGermCoefficient L hind)

/-! ### The `s·b=uB` face -/

/-- The selected `b` middle anchor included in the grouped middle field. -/
noncomputable def sbBGermCoefficientToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sbGroupedSourceField L hind)).comp
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The matching selected `b` anchor in the grouped target field. -/
noncomputable def sbBGermCoefficientToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sbRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sbGroupedSourceField L hind)).comp
    ((R.sbRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The grouped pullback source carries a nested intermediate-field tower.
/-- The grouped `b` left arrow restricts to the named middle anchor. -/
theorem sbGrouped_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbGroupedCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSbGroupedSource L hind) =
      R.sbBGermCoefficientToGroupedMiddleRingHom L hind := by
  let T := R.sbRightSemilinearCompositionTriangle L hind
  let X := R.sbGroupedSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightBSourceRingHom L hind)
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sbRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The grouped `b` right arrow restricts to the named target anchor. -/
theorem sbGrouped_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sbBGermCoefficientToGroupedMiddleRingHom L hind) =
      R.sbBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sbRightSemilinearCompositionTriangle L hind
  let X := R.sbGroupedSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sbBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The grouped strict `uB` arrow has the same `b` target restriction. -/
theorem sbGrouped_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbGroupedCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSbGroupedSource L hind) =
      R.sbBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sbGroupedCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSbGroupedSource L hind)
    (R.sbBGermCoefficientToGroupedMiddleRingHom L hind)
    (R.sbBGermCoefficientToGroupedTargetRingHom L hind)
    (R.sbGrouped_left_comp_bGermCoefficient L hind)
    (R.sbGrouped_right_comp_bGermCoefficient L hind)

/-! ### The `sA·c=uB` face -/

/-- The selected genuine-`c` middle anchor included in the grouped middle
field. -/
noncomputable def sAcBGermCoefficientToGroupedMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAcGroupedSourceField L hind)).comp
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The matching genuine-`c` anchor in the grouped target field. -/
noncomputable def sAcBGermCoefficientToGroupedTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAcRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAcGroupedSourceField L hind)).comp
    ((R.sAcRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

set_option synthInstance.maxHeartbeats 100000 in
-- The grouped pullback source carries a nested intermediate-field tower.
/-- The grouped `c` left arrow restricts to the named middle anchor. -/
theorem sAcGrouped_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcGroupedCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSAcGroupedSource L hind) =
      R.sAcBGermCoefficientToGroupedMiddleRingHom L hind := by
  let T := R.sAcRightSemilinearCompositionTriangle L hind
  let X := R.sAcGroupedSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightCSourceRingHom L hind)
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sAcRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The grouped `c` right arrow restricts to the named target anchor. -/
theorem sAcGrouped_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcGroupedCompositionTriangle L hind).right.toRingHom.comp
        (R.sAcBGermCoefficientToGroupedMiddleRingHom L hind) =
      R.sAcBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sAcRightSemilinearCompositionTriangle L hind
  let X := R.sAcGroupedSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sAcBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The grouped strict `uB` arrow has the same `c` target restriction. -/
theorem sAcGrouped_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcGroupedCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSAcGroupedSource L hind) =
      R.sAcBGermCoefficientToGroupedTargetRingHom L hind := by
  let T := R.sAcGroupedCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSAcGroupedSource L hind)
    (R.sAcBGermCoefficientToGroupedMiddleRingHom L hind)
    (R.sAcBGermCoefficientToGroupedTargetRingHom L hind)
    (R.sAcGrouped_left_comp_bGermCoefficient L hind)
    (R.sAcGrouped_right_comp_bGermCoefficient L hind)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
