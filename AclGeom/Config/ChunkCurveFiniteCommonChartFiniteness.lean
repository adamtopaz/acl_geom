/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonChart

/-!
# Finiteness of the semilinear common charts

The four pullback sources are finite over the established graph/right
source.  They are kept in a separate module so their deeply dependent
finite-tower witnesses serialize with a bounded memory footprint.
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

set_option synthInstance.maxHeartbeats 100000 in
-- Nested selected-cover types require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
/-- The `e` pullback chart is finite over the established selected graph/right
source field. -/
theorem rightEFiniteCommonChartSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightEFiniteCommonChartSourceField L hind)) := by
  let f := R.selectedGraphRightSourceToRightEJointRingHom L hind
  letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := f.toAlgebra
  letI : FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
    R.selectedGraphJointOverSelectedSource_finiteDimensional L hind f
      R.rightEToJointBaseRingHom
      (by
        letI : Algebra (↥R.semanticCommonSourceField)
            (↥R.rightSourceJointField) :=
          R.semanticSourceToRightSourceJoint.toAlgebra
        exact R.rightSourceJointOverSemantic_finiteDimensional)
      (R.selectedGraphRightSourceToRightEJointRingHom_comp_source L hind)
  exact
    (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
      |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
-- Nested selected-cover types require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
/-- The `a` pullback chart is finite over the established source field. -/
theorem rightAFiniteCommonChartSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightAFiniteCommonChartSourceField L hind)) := by
  let f := R.selectedGraphRightSourceToRightAJointRingHom L hind
  letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := f.toAlgebra
  letI : FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
    R.selectedGraphJointOverSelectedSource_finiteDimensional L hind f
      (R.rightAToJointBaseRingHom hind)
      (R.rightSourceJointOverA_finiteDimensional hind)
      (R.selectedGraphRightSourceToRightAJointRingHom_comp_source L hind)
  exact
    (R.selectedGraphRightSourceToRightAJointClosureExtension L hind)
      |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
-- Nested selected-cover types require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
/-- The `b` pullback chart is finite over the established source field. -/
theorem rightBFiniteCommonChartSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightBFiniteCommonChartSourceField L hind)) := by
  let f := R.selectedGraphRightSourceToRightBJointRingHom L hind
  letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := f.toAlgebra
  letI : FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
    R.selectedGraphJointOverSelectedSource_finiteDimensional L hind f
      (R.rightBToJointBaseRingHom hind)
      (R.rightSourceJointOverB_finiteDimensional hind)
      (R.selectedGraphRightSourceToRightBJointRingHom_comp_source L hind)
  exact
    (R.selectedGraphRightSourceToRightBJointClosureExtension L hind)
      |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
-- Nested selected-cover types require an enlarged instance-search budget.
set_option maxHeartbeats 800000 in
/-- The genuine `c` pullback chart is finite over the established source
field. -/
theorem rightCFiniteCommonChartSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.rightCFiniteCommonChartSourceField L hind)) := by
  let f := R.selectedGraphRightSourceToRightCJointRingHom L hind
  letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := f.toAlgebra
  letI : FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
    R.selectedGraphJointOverSelectedSource_finiteDimensional L hind f
      (R.rightCToJointBaseRingHom hind)
      (R.rightSourceJointOverCChart_finiteDimensional hind)
      (R.selectedGraphRightSourceToRightCJointRingHom_comp_source L hind)
  exact
    (R.selectedGraphRightSourceToRightCJointClosureExtension L hind)
      |>.pullbackField_finiteDimensional rfl ⊥

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
