/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedSource

/-!
# Finiteness of the grouped semilinear source charts

The grouped source pullbacks are finite over their corresponding transported
selected graph/right covers.  The `a`, `b`, and `c` proofs first transport
finiteness of the joint target through the relevant source equivalence and
then apply finite pullback descent.
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

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `e` source is finite over the established selected
graph/right source. -/
theorem seGroupedSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.seGroupedSourceField L hind)) := by
  let fE := R.selectedGraphRightSourceToRightEJointRingHom L hind
  letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := fE.toAlgebra
  letI : FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
    R.selectedGraphJointOverSelectedSource_finiteDimensional L hind fE
      R.rightEToJointBaseRingHom
      (by
        letI : Algebra (↥R.semanticCommonSourceField)
            (↥R.rightSourceJointField) :=
          R.semanticSourceToRightSourceJoint.toAlgebra
        exact R.rightSourceJointOverSemantic_finiteDimensional)
      (R.selectedGraphRightSourceToRightEJointRingHom_comp_source L hind)
  exact (R.selectedGraphRightSourceToRightEJointClosureExtension L hind)
    |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `a` source remains finite over its transported old source. -/
theorem sAaGroupedSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.rightASelectedGraphRightSourceCover L hind).field)
      (↥(R.sAaGroupedSourceField L hind)) := by
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let Na := ↥(R.rightASelectedGraphRightSourceCover L hind).field
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let fA := R.selectedGraphRightSourceToRightAJointRingHom L hind
  let eA := R.selectedGraphRightSourceToRightARingEquiv L hind
  let f := fA.comp eA.symm.toRingHom
  let oldAlgebra : Algebra N P := fA.toAlgebra
  let newAlgebra : Algebra Na P := f.toAlgebra
  let oldModule : Module N P := oldAlgebra.toModule
  let oldFinite : @Module.Finite N P _ _ oldModule := by
    letI : Algebra N P := oldAlgebra
    exact R.selectedGraphJointOverSelectedSource_finiteDimensional L hind fA
      (R.rightAToJointBaseRingHom hind)
      (R.rightSourceJointOverA_finiteDimensional hind)
      (R.selectedGraphRightSourceToRightAJointRingHom_comp_source L hind)
  letI : Algebra Na P := newAlgebra
  letI : FiniteDimensional Na P :=
    @Module.Finite.of_equiv_equiv N P Na P _ _ _ _
      oldAlgebra newAlgebra eA (RingEquiv.refl P) (by
        apply RingHom.ext
        intro x
        change fA (eA.symm (eA x)) = fA x
        rw [eA.symm_apply_apply]) oldFinite
  exact (R.sAaGroupedSourceClosureExtension L hind)
    |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped `b` source remains finite over its transported old source. -/
theorem sbGroupedSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.rightBSelectedGraphRightSourceCover L hind).field)
      (↥(R.sbGroupedSourceField L hind)) := by
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let Nb := ↥(R.rightBSelectedGraphRightSourceCover L hind).field
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let fE := R.selectedGraphRightSourceToRightEJointRingHom L hind
  let eB := R.selectedGraphRightSourceToRightBRingEquiv L hind
  let f := fE.comp eB.symm.toRingHom
  let oldAlgebra : Algebra N P := fE.toAlgebra
  let newAlgebra : Algebra Nb P := f.toAlgebra
  let oldModule : Module N P := oldAlgebra.toModule
  let oldFinite : @Module.Finite N P _ _ oldModule := by
    letI : Algebra N P := oldAlgebra
    exact R.selectedGraphJointOverSelectedSource_finiteDimensional L hind fE
      R.rightEToJointBaseRingHom
      (by
        letI : Algebra (↥R.semanticCommonSourceField)
            (↥R.rightSourceJointField) :=
          R.semanticSourceToRightSourceJoint.toAlgebra
        exact R.rightSourceJointOverSemantic_finiteDimensional)
      (R.selectedGraphRightSourceToRightEJointRingHom_comp_source L hind)
  letI : Algebra Nb P := newAlgebra
  letI : FiniteDimensional Nb P :=
    @Module.Finite.of_equiv_equiv N P Nb P _ _ _ _
      oldAlgebra newAlgebra eB (RingEquiv.refl P) (by
        apply RingHom.ext
        intro x
        change fE (eB.symm (eB x)) = fE x
        rw [eB.symm_apply_apply]) oldFinite
  exact (R.sbGroupedSourceClosureExtension L hind)
    |>.pullbackField_finiteDimensional rfl ⊥

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped genuine-`c` source remains finite over its transported old
source. -/
theorem sAcGroupedSourceField_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.rightCSelectedGraphRightSourceCover L hind).field)
      (↥(R.sAcGroupedSourceField L hind)) := by
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let Nc := ↥(R.rightCSelectedGraphRightSourceCover L hind).field
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let fA := R.selectedGraphRightSourceToRightAJointRingHom L hind
  let eC := R.selectedGraphRightSourceToRightCRingEquiv L hind
  let f := fA.comp eC.symm.toRingHom
  let oldAlgebra : Algebra N P := fA.toAlgebra
  let newAlgebra : Algebra Nc P := f.toAlgebra
  let oldModule : Module N P := oldAlgebra.toModule
  let oldFinite : @Module.Finite N P _ _ oldModule := by
    letI : Algebra N P := oldAlgebra
    exact R.selectedGraphJointOverSelectedSource_finiteDimensional L hind fA
      (R.rightAToJointBaseRingHom hind)
      (R.rightSourceJointOverA_finiteDimensional hind)
      (R.selectedGraphRightSourceToRightAJointRingHom_comp_source L hind)
  letI : Algebra Nc P := newAlgebra
  letI : FiniteDimensional Nc P :=
    @Module.Finite.of_equiv_equiv N P Nc P _ _ _ _
      oldAlgebra newAlgebra eC (RingEquiv.refl P) (by
        apply RingHom.ext
        intro x
        change fA (eC.symm (eC x)) = fA x
        rw [eC.symm_apply_apply]) oldFinite
  exact (R.sAcGroupedSourceClosureExtension L hind)
    |>.pullbackField_finiteDimensional rfl ⊥

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end


end AclGeom
