/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearCommonMiddleE
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranchA

/-! # The based germ through the inverse-oriented `a` face

The inverse `a` source chart sends its intrinsic source germ back to the
based `e` germ.  Consequently its left square lands in the based coefficient
anchor inside the `a` middle cover, rather than in the independently
preserved selected `a` branch.  This is the exact input needed from the `a`
face before those two middle embeddings are aligned in one common chart.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

/-- A finite triangle's left arrow fixes an arbitrary map into its
coefficient field. -/
theorem finiteCoverTriangle_left_comp_algebraMap_comp
    {E Ω W : Type*} [Field E] [Field Ω] [Algebra E Ω] [Semiring W]
    (P Q : FiniteCorrespondencePair E Ω) (h : P.target = Q.source)
    (N : AlgebraicClosureTransport.FiniteNormalCover (↥P.sourceField))
    (g : W →+* E) :
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
        P Q h N).toRingHom.comp
          ((algebraMap E (↥N.field)).comp g) =
      (algebraMap E
        (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
          P Q h N).field)).comp g := by
  apply RingHom.ext
  intro x
  exact
    FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv_algebraMap
      P Q h N (g x)

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The based intrinsic germ embedded by the common coefficient field into
the middle cover of the unextended `a` triangle. -/
noncomputable def
    sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (algebraMap (↥R.sAaCommonBaseData.coefficientField)
    (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
        (R := R.sAa) R.sAaCommonBaseData hψ)
      (R.selectedGraphRightSourceCover L hind)).field)).comp
    (R.seBGermCoefficientToCommonCoefficientRingHom L)

set_option synthInstance.maxHeartbeats 100000 in
-- The selected source and middle fields are nested finite-cover transports.
/-- The original `a` left arrow carries the based source anchor to the
matching common-coefficient anchor in its middle field. -/
theorem sAaSelectedGraphRight_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaSelectedGraphRightCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  let P :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  let Q :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.bCorrespondencePair
      (R := R.sAa) R.sAaCommonBaseData hψ
  let h :=
    PsiCurveCompositionBaseChangeRealization.CommonBaseData.aPair_target_eq_bPair_source
      (R := R.sAa) R.sAaCommonBaseData hψ
  let N := R.selectedGraphRightSourceCover L hind
  change
    (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
      P Q h N).toRingHom.comp
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind) =
      R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind
  calc
    _ = (FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp
        ((algebraMap (↥R.sAaCommonBaseData.coefficientField)
          (↥N.field)).comp
            (R.seBGermCoefficientToCommonCoefficientRingHom L)) :=
      congrArg
        ((FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.leftEquiv
          P Q h N).toRingHom.comp)
        (R.bGermCoefficientToSelectedGraphRightSourceRingHom_eq_commonCoefficient
          L hind)
    _ = (algebraMap (↥R.sAaCommonBaseData.coefficientField)
          (↥(FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.middleCover
            P Q h N).field)).comp
        (R.seBGermCoefficientToCommonCoefficientRingHom L) :=
      finiteCoverTriangle_left_comp_algebraMap_comp P Q h N
        (R.seBGermCoefficientToCommonCoefficientRingHom L)
    _ = R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding the source conjugation exposes several nested cover aliases.
/-- After inverse source normalization, the `a` left arrow sends the
intrinsic `a` source germ to the based middle anchor. -/
theorem sAaRightSemilinear_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToRightASourceRingHom L hind) =
      R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind := by
  apply RingHom.ext
  intro z
  have hsource := DFunLike.congr_fun
    (R.rightASourceChart_comp_bGermCoefficient L hind) z
  have hleft := DFunLike.congr_fun
    (R.sAaSelectedGraphRight_left_comp_bGermCoefficient L hind) z
  change (R.selectedGraphRightSourceToRightARingEquiv L hind).symm
      (R.bGermCoefficientToRightASourceRingHom L hind z) =
    R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z at hsource
  change (R.sAaSelectedGraphRightCompositionTriangle L hind).left
      (R.bGermCoefficientToSelectedGraphRightSourceRingHom L hind z) =
    R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind z at hleft
  change (R.sAaSelectedGraphRightCompositionTriangle L hind).left
      ((R.selectedGraphRightSourceToRightARingEquiv L hind).symm
        (R.bGermCoefficientToRightASourceRingHom L hind z)) = _
  exact (congrArg
    (R.sAaSelectedGraphRightCompositionTriangle L hind).left hsource).trans hleft

/-- The based middle anchor included in the middle field of the extended
inverse-oriented `a` triangle. -/
noncomputable def sAaBGermCoefficientToSemilinearCommonMiddleRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionMiddleRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)).comp
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

set_option synthInstance.maxHeartbeats 100000 in
-- The pullback source and transported middle form nested algebra towers.
/-- The common-source `a` left arrow carries its intrinsic source germ to
the based middle anchor. -/
theorem sAaSemilinearCommon_left_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCommonCompositionTriangle L hind).left.toRingHom.comp
        (R.bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom L hind) =
      R.sAaBGermCoefficientToSemilinearCommonMiddleRingHom L hind := by
  let T := R.sAaRightSemilinearCompositionTriangle L hind
  let X := R.sAaRightSemilinearCommonSourceField L hind
  exact T.sourceExtension_left_comp_of_left_comp X
    (R.bGermCoefficientToRightASourceRingHom L hind)
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)
    (R.sAaRightSemilinear_left_comp_bGermCoefficient L hind)

/-- The corresponding based target anchor in the extended `a` target
field. -/
noncomputable def sAaBGermCoefficientToSemilinearCommonTargetRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ((R.sAaRightSemilinearCompositionTriangle L hind)
      |>.sourceExtensionTargetRingHom
        (R.sAaRightSemilinearCommonSourceField L hind)).comp
    ((R.sAaRightSemilinearCompositionTriangle L hind).right.toRingHom.comp
      (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind))

/-- The extended `a` right arrow restricts on the based middle anchor to
the named target map. -/
theorem sAaSemilinearCommon_right_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCommonCompositionTriangle L hind).right.toRingHom.comp
        (R.sAaBGermCoefficientToSemilinearCommonMiddleRingHom L hind) =
      R.sAaBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sAaRightSemilinearCompositionTriangle L hind
  let X := R.sAaRightSemilinearCommonSourceField L hind
  exact T.sourceExtensionRightEquiv_comp_middleRingHom_comp X
    (R.sAaBGermCoefficientToSelectedGraphRightMiddleCommonRingHom L hind)

/-- The strict direct `u` arrow on the common-source `a` face carries the
intrinsic source germ to the same based target map. -/
theorem sAaSemilinearCommon_direct_comp_bGermCoefficient
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRightSemilinearCommonCompositionTriangle L hind).direct.toRingHom.comp
        (R.bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom L hind) =
      R.sAaBGermCoefficientToSemilinearCommonTargetRingHom L hind := by
  let T := R.sAaRightSemilinearCommonCompositionTriangle L hind
  exact T.direct_comp_of_left_right
    (R.bGermCoefficientToSAaRightSemilinearExtendedSourceRingHom L hind)
    (R.sAaBGermCoefficientToSemilinearCommonMiddleRingHom L hind)
    (R.sAaBGermCoefficientToSemilinearCommonTargetRingHom L hind)
    (R.sAaSemilinearCommon_left_comp_bGermCoefficient L hind)
    (R.sAaSemilinearCommon_right_comp_bGermCoefficient L hind)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
