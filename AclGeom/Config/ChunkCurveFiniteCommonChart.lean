/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveIntrinsicSourceRestriction
import AclGeom.Correspondence.FiniteClosurePullback

/-!
# Finite common charts for the four selected semilinear source maps

The four selected embeddings of the graph/right source have already been
extended to equivalences of algebraic closures with one joint codomain.
Pulling that finite joint codomain back along each extension produces four
source fields and four honest field equivalences onto one literal target.
The companion modules prove finiteness and the exact whole-germ
restrictions.

Unlike the earlier source-induced four-arrow diagram, these charts do not
identify the four right maps with the identity: they retain the semilinear
coefficient movement on a finite field chart.
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
-- The four nested selected algebra structures require an enlarged search budget.
/-- If a selected joint embedding has a finite twisted base and the stated
source square, then its joint codomain is finite over the selected graph/right
source. -/
theorem selectedGraphJointOverSelectedSource_finiteDimensional
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (f : (↥(R.selectedGraphRightSourceCover L hind).field) →+*
      (↥(R.fourSelectedGraphJointCover L hind).field))
    (g : (↥R.semanticCommonSourceField) →+*
      (↥R.rightSourceJointField))
    (hfin : @Module.Finite (↥R.semanticCommonSourceField)
      (↥R.rightSourceJointField) _ _ g.toAlgebra.toModule)
    (hcomp : f.comp
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind) =
      (algebraMap (↥R.rightSourceJointField)
        (↥(R.fourSelectedGraphJointCover L hind).field)).comp g) :
    letI : Algebra (↥(R.selectedGraphRightSourceCover L hind).field)
        (↥(R.fourSelectedGraphJointCover L hind).field) := f.toAlgebra
    FiniteDimensional
      (↥(R.selectedGraphRightSourceCover L hind).field)
      (↥(R.fourSelectedGraphJointCover L hind).field) := by
  let S := ↥R.semanticCommonSourceField
  let N := ↥(R.selectedGraphRightSourceCover L hind).field
  let J := ↥R.rightSourceJointField
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let iSN : S →+* N :=
    R.semanticSourceToSelectedGraphRightSourceRingHom L hind
  letI : Algebra S N := iSN.toAlgebra
  letI : Algebra N P := f.toAlgebra
  letI : Algebra S J := g.toAlgebra
  let algSJP : Algebra S P := ((algebraMap J P).comp g).toAlgebra
  letI : Algebra S P := algSJP
  let towerSJP : IsScalarTower S J P :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional S J := hfin
  let finiteJP : FiniteDimensional J P :=
    (R.fourSelectedGraphJointCover L hind).finiteDimensional
  let finiteSP : @Module.Finite S P _ _ algSJP.toModule := by
    exact @Module.Finite.trans S J P inferInstance inferInstance
      g.toAlgebra.toModule inferInstance algSJP.toModule
      (inferInstance : Module J P) towerSJP hfin finiteJP
  let towerSNP : IsScalarTower S N P :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  exact @Module.Finite.right S N P inferInstance inferInstance
    iSN.toAlgebra.toModule inferInstance f.toAlgebra.toModule
    algSJP.toModule towerSNP finiteSP

/-- The finite source obtained by pulling the joint cover back through the
selected `e` algebraic-closure comparison. -/
noncomputable def rightEFiniteCommonChartSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind).pullbackField
    (⊥ : IntermediateField
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field)))

/-- The corresponding finite pullback source for the `a` comparison. -/
noncomputable def rightAFiniteCommonChartSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind).pullbackField
    (⊥ : IntermediateField
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field)))

/-- The corresponding finite pullback source for the `b` comparison. -/
noncomputable def rightBFiniteCommonChartSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightBJointClosureExtension L hind).pullbackField
    (⊥ : IntermediateField
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field)))

/-- The corresponding finite pullback source for the genuine algebraic-output
`c` comparison. -/
noncomputable def rightCFiniteCommonChartSourceField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedGraphRightSourceToRightCJointClosureExtension L hind).pullbackField
    (⊥ : IntermediateField
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (AlgebraicClosure (↥(R.fourSelectedGraphJointCover L hind).field)))

/-- The restricted `e` closure comparison from its finite pullback source
onto the literal joint cover. -/
noncomputable def rightEFiniteCommonChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightEFiniteCommonChartSourceField L hind)) ≃+*
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightEJointClosureExtension L hind).pullbackBaseEquiv

/-- The restricted `a` closure comparison with the same finite target. -/
noncomputable def rightAFiniteCommonChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightAFiniteCommonChartSourceField L hind)) ≃+*
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightAJointClosureExtension L hind).pullbackBaseEquiv

/-- The restricted `b` closure comparison with the same finite target. -/
noncomputable def rightBFiniteCommonChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightBFiniteCommonChartSourceField L hind)) ≃+*
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightBJointClosureExtension L hind).pullbackBaseEquiv

/-- The restricted genuine `c` comparison with the same finite target. -/
noncomputable def rightCFiniteCommonChart
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.rightCFiniteCommonChartSourceField L hind)) ≃+*
      (↥(R.fourSelectedGraphJointCover L hind).field) :=
  (R.selectedGraphRightSourceToRightCJointClosureExtension L hind).pullbackBaseEquiv

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
