/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveSemilinearGroupedStableBaseA
import AclGeom.Correspondence.FiniteNormalOrbit

/-!
# A finite grouped source stable under the e/a chart

The stable grouped source was originally formed in the algebraic closure of
the four-face joint cover.  We transport it to the canonical algebraic
closure of the semantic source, then adjoin its image under the lifted
`e→a` chart.  Involutivity on the base and normality absorb the possible deck
transformation in the square of the chosen lift, so this two-orbit compositum
is stable under the lift itself.
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

private abbrev groupedStableOrbitSemanticSourceType :=
  ↥R.semanticCommonSourceField

private abbrev groupedStableOrbitJointCoverType
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  ↥(R.fourSelectedGraphJointCover L hind).field

set_option synthInstance.maxHeartbeats 100000 in
-- The ambient closure is reached through the finite joint-cover tower.
set_option maxHeartbeats 800000 in
-- This packages that tower as an algebraic closure of the semantic source.
/-- Identify the algebraic closure of the grouped joint cover with the
canonical algebraic closure of the original semantic source, linearly over
that source. -/
noncomputable def groupedStableToCanonicalClosureEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosure (groupedStableOrbitJointCoverType R L hind) ≃ₐ[
      groupedStableOrbitSemanticSourceType R]
      AlgebraicClosure (groupedStableOrbitSemanticSourceType R) := by
  let S := groupedStableOrbitSemanticSourceType R
  let P := groupedStableOrbitJointCoverType R L hind
  let Ω := AlgebraicClosure P
  letI : FiniteDimensional S P :=
    R.fourSelectedGraphJointCover_finite_over_semantic L hind
  letI : Algebra.IsAlgebraic S P := Algebra.IsAlgebraic.of_finite S P
  letI : IsAlgClosure S Ω := IsAlgClosure.ofAlgebraic S P Ω
  exact IsAlgClosure.equiv S Ω (AlgebraicClosure S)

set_option synthInstance.maxHeartbeats 100000 in
-- Both normal-field presentations and the closure comparison are involved.
set_option maxHeartbeats 800000 in
-- Finiteness and normality are transported through one explicit equivalence.
/-- The stable grouped source transported into the canonical algebraic closure
of the semantic source. -/
noncomputable def groupedStableCanonicalSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (groupedStableOrbitSemanticSourceType R) where
  field := (R.groupedStableNormalField L hind).map
    (R.groupedStableToCanonicalClosureEquiv L hind).toAlgHom
  finiteDimensional := by
    letI : FiniteDimensional (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableNormalField L hind)) := by
      change FiniteDimensional (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableSourceField L hind))
      exact R.groupedStableSourceField_finite_over_semantic L hind
    exact LinearEquiv.finiteDimensional
      (IntermediateField.intermediateFieldMap
        (R.groupedStableToCanonicalClosureEquiv L hind)
        (R.groupedStableNormalField L hind)).toLinearEquiv
  normal := by
    letI : Normal (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableNormalField L hind)) := by
      change Normal (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableSourceField L hind))
      exact R.groupedStableSourceField_normal L hind
    exact Normal.of_algEquiv
      (IntermediateField.intermediateFieldMap
        (R.groupedStableToCanonicalClosureEquiv L hind)
        (R.groupedStableNormalField L hind))

/-- The lifted `e→a` transport has an involutive base equivalence. -/
theorem rightACommonSourceClosureTransport_base_trans_self
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.rightACommonSourceClosureTransport hind).baseEquiv.trans
        (R.rightACommonSourceClosureTransport hind).baseEquiv =
      RingEquiv.refl (groupedStableOrbitSemanticSourceType R) := by
  exact congrArg AlgEquiv.toRingEquiv
    (R.commonSourceRightAAut_trans_self hind)

/-- The finite stable grouped source enlarged by the two-element orbit of the
lifted `e→a` chart. -/
noncomputable def groupedStableAOrbitSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicClosureTransport.FiniteNormalCover
      (groupedStableOrbitSemanticSourceType R) :=
  (R.groupedStableCanonicalSourceCover L hind).twoOrbitCover
    (R.rightACommonSourceClosureTransport hind)

/-- Transport the original stable grouped source into its canonical-closure
presentation. -/
noncomputable def groupedStableSourceToCanonicalSourceAlgEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableSourceField L hind) ≃ₐ[
      groupedStableOrbitSemanticSourceType R]
      (R.groupedStableCanonicalSourceCover L hind).field := by
  change (↥(R.groupedStableNormalField L hind)) ≃ₐ[
      groupedStableOrbitSemanticSourceType R]
    ↥((R.groupedStableNormalField L hind).map
      (R.groupedStableToCanonicalClosureEquiv L hind).toAlgHom)
  exact IntermediateField.intermediateFieldMap
    (R.groupedStableToCanonicalClosureEquiv L hind)
    (R.groupedStableNormalField L hind)

/-- Include the original stable grouped source in the first summand of the
`e/a`-stable two-orbit cover. -/
noncomputable def groupedStableSourceToAOrbitSourceAlgHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableSourceField L hind) →ₐ[
      groupedStableOrbitSemanticSourceType R]
      (R.groupedStableAOrbitSourceCover L hind).field :=
  (IntermediateField.inclusion le_sup_left).comp
    (R.groupedStableSourceToCanonicalSourceAlgEquiv L hind).toAlgHom

/-- Include the whole four-face joint cover in the `e/a`-stable source. -/
noncomputable def groupedJointCoverToAOrbitSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.fourSelectedGraphJointCover L hind).field →+*
      (R.groupedStableAOrbitSourceCover L hind).field :=
  (R.groupedStableSourceToAOrbitSourceAlgHom L hind).toRingHom.comp
    (R.groupedJointCoverToStableSourceRingHom L hind)

/-- The selected inclusion of the joint cover into the final orbit cover
retains the original semantic-source algebra map exactly. -/
@[simp] theorem groupedJointCoverToAOrbitSourceRingHom_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : groupedStableOrbitSemanticSourceType R) :
    R.groupedJointCoverToAOrbitSourceRingHom L hind
        (algebraMap (groupedStableOrbitSemanticSourceType R)
          (groupedStableOrbitJointCoverType R L hind) x) =
      algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableAOrbitSourceCover L hind).field) x := by
  change R.groupedStableSourceToAOrbitSourceAlgHom L hind
      (algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableSourceField L hind)) x) = _
  exact (R.groupedStableSourceToAOrbitSourceAlgHom L hind).commutes x

/-- Use the explicit joint-cover inclusion as the algebra structure on the
stable two-orbit source. -/
noncomputable instance groupedAOrbitJointCoverAlgebra
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Algebra (↥(R.fourSelectedGraphJointCover L hind).field)
      (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).toAlgebra

set_option synthInstance.maxHeartbeats 100000 in
-- The right-dimension argument crosses the joint and canonical presentations.
set_option maxHeartbeats 800000 in
-- The explicit tower equation retains the selected joint-cover inclusion.
/-- The `e/a`-stable source is finite over the whole four-face joint cover. -/
theorem groupedStableAOrbitSource_finite_over_jointCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    FiniteDimensional
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (↥(R.groupedStableAOrbitSourceCover L hind).field) := by
  let S := groupedStableOrbitSemanticSourceType R
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let Q := ↥(R.groupedStableAOrbitSourceCover L hind).field
  letI : FiniteDimensional S Q :=
    (R.groupedStableAOrbitSourceCover L hind).finiteDimensional
  letI : IsScalarTower S P
      (↥(R.groupedStableSourceField L hind)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower S P Q :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap S Q x =
        R.groupedStableSourceToAOrbitSourceAlgHom L hind
          (algebraMap P (↥(R.groupedStableSourceField L hind))
            (algebraMap S P x))
      rw [← IsScalarTower.algebraMap_apply S P
        (↥(R.groupedStableSourceField L hind))]
      exact (R.groupedStableSourceToAOrbitSourceAlgHom L hind).commutes x |>.symm
  exact FiniteDimensional.right S P Q

set_option synthInstance.maxHeartbeats 100000 in
-- The module transport changes the base through an arbitrary source chart.
set_option maxHeartbeats 800000 in
-- This isolates the repeated finiteness argument used by the four siblings.
/-- Any field charted to the joint cover sees the orbit source as a finite
extension through the chart followed by the selected inclusion. -/
theorem groupedStableAOrbitSource_finite_over_chartSource
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    {X : Type u} [Field X]
    (chart : X ≃+* (↥(R.fourSelectedGraphJointCover L hind).field)) :
    letI : Algebra X (↥(R.groupedStableAOrbitSourceCover L hind).field) :=
      ((R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
        chart.toRingHom).toAlgebra
    FiniteDimensional X
      (↥(R.groupedStableAOrbitSourceCover L hind).field) := by
  let P := ↥(R.fourSelectedGraphJointCover L hind).field
  let Q := ↥(R.groupedStableAOrbitSourceCover L hind).field
  let fP := R.groupedJointCoverToAOrbitSourceRingHom L hind
  let f := fP.comp chart.toRingHom
  let oldAlgebra : Algebra P Q :=
    R.groupedAOrbitJointCoverAlgebra L hind
  let newAlgebra : Algebra X Q := f.toAlgebra
  let oldModule : Module P Q := oldAlgebra.toModule
  let oldFinite : @Module.Finite P Q _ _ oldModule := by
    letI : Algebra P Q := oldAlgebra
    exact R.groupedStableAOrbitSource_finite_over_jointCover L hind
  letI : Algebra X Q := newAlgebra
  exact @Module.Finite.of_equiv_equiv P Q X Q _ _ _ _
    oldAlgebra newAlgebra chart.symm (RingEquiv.refl Q) (by
      apply RingHom.ext
      intro x
      change fP (chart (chart.symm x)) = fP x
      rw [chart.apply_symm_apply]) oldFinite

/-- The repeated-`s` intrinsic source embedded in the final orbit cover. -/
noncomputable def groupedStableAOrbitSourceS
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.groupedSourceS L hind)

/-- The repeated-`sA` intrinsic source embedded in the final orbit cover. -/
noncomputable def groupedStableAOrbitSourceSA
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.groupedJointCoverToAOrbitSourceRingHom L hind).comp
    (R.groupedSourceSA L hind)

/-- In the final orbit cover, the repeated-`s` intrinsic source is the
canonical semantic-source algebra map applied to its `e` presentation. -/
theorem groupedStableAOrbitSourceS_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.groupedStableAOrbitSourceS L hind x =
      algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableAOrbitSourceCover L hind).field)
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x) := by
  change R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.selectedGraphRightSourceToRightEJointRingHom L hind
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind
          (R.seBGermCoefficientToSemanticSourceAlgHom L hind x))) = _
  have hE := DFunLike.congr_fun
    (R.selectedGraphRightSourceToRightEJointRingHom_comp_source L hind)
    (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)
  change R.selectedGraphRightSourceToRightEJointRingHom L hind
      (R.semanticSourceToSelectedGraphRightSourceRingHom L hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) =
    algebraMap (↥R.rightSourceJointField)
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (R.rightEToJointBaseRingHom
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) at hE
  rw [hE]
  change R.groupedJointCoverToAOrbitSourceRingHom L hind
      (algebraMap (groupedStableOrbitSemanticSourceType R)
        (groupedStableOrbitJointCoverType R L hind)
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) = _
  exact R.groupedJointCoverToAOrbitSourceRingHom_algebraMap L hind _

/-- In the final orbit cover, the repeated-`sA` intrinsic source is the
canonical semantic-source algebra map applied to its `a` presentation. -/
theorem groupedStableAOrbitSourceSA_apply
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : w.bGermCoefficientField hψ) :
    R.groupedStableAOrbitSourceSA L hind x =
      algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableAOrbitSourceCover L hind).field)
        (R.sAaBGermCoefficientToSemanticSourceAlgHom L hind x) := by
  change R.groupedJointCoverToAOrbitSourceRingHom L hind
      (R.selectedGraphRightSourceToRightAJointRingHom L hind
        (R.semanticSourceToSelectedGraphRightSourceRingHom L hind
          (R.seBGermCoefficientToSemanticSourceAlgHom L hind x))) = _
  have hA := DFunLike.congr_fun
    (R.selectedGraphRightSourceToRightAJointRingHom_comp_source L hind)
    (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)
  change R.selectedGraphRightSourceToRightAJointRingHom L hind
      (R.semanticSourceToSelectedGraphRightSourceRingHom L hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) =
    algebraMap (↥R.rightSourceJointField)
      (↥(R.fourSelectedGraphJointCover L hind).field)
      (R.rightAToJointBaseRingHom hind
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) at hA
  rw [hA]
  change R.groupedJointCoverToAOrbitSourceRingHom L hind
      (algebraMap (groupedStableOrbitSemanticSourceType R)
        (groupedStableOrbitJointCoverType R L hind)
        (R.commonSourceRightAAut hind
          (R.seBGermCoefficientToSemanticSourceAlgHom L hind x))) = _
  rw [R.groupedJointCoverToAOrbitSourceRingHom_algebraMap]
  exact congrArg
    (algebraMap (groupedStableOrbitSemanticSourceType R)
      (↥(R.groupedStableAOrbitSourceCover L hind).field))
    (R.commonSourceRightAAut_comp_seBGermCoefficient L hind x)

/-- The inclusion into the two-orbit cover evaluates as the chosen
canonical-closure comparison. -/
@[simp] theorem groupedStableSourceToAOrbitSourceAlgHom_coe
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : R.groupedStableSourceField L hind) :
    ((R.groupedStableSourceToAOrbitSourceAlgHom L hind x :
        (R.groupedStableAOrbitSourceCover L hind).field) :
      AlgebraicClosure (groupedStableOrbitSemanticSourceType R)) =
    R.groupedStableToCanonicalClosureEquiv L hind
      (x : AlgebraicClosure
        (groupedStableOrbitJointCoverType R L hind)) :=
  rfl

/-- The lifted `e→a` chart restricted as a self-equivalence of the stable
two-orbit source. -/
noncomputable def groupedStableASourceChartRingEquiv
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableAOrbitSourceCover L hind).field ≃+*
      (R.groupedStableAOrbitSourceCover L hind).field :=
  (R.groupedStableCanonicalSourceCover L hind).twoOrbitEquiv
    (R.rightACommonSourceClosureTransport hind)
    (R.rightACommonSourceClosureTransport_base_trans_self hind)

/-- The restricted stable source chart remains exactly semilinear over the
whole `e→a` semantic-source automorphism. -/
@[simp] theorem groupedStableASourceChartRingEquiv_algebraMap
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (x : groupedStableOrbitSemanticSourceType R) :
    R.groupedStableASourceChartRingEquiv L hind
        (algebraMap (groupedStableOrbitSemanticSourceType R)
          (↥(R.groupedStableAOrbitSourceCover L hind).field) x) =
      algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableAOrbitSourceCover L hind).field)
        (R.commonSourceRightAAut hind x) := by
  exact (R.groupedStableCanonicalSourceCover L hind).twoOrbitEquiv_algebraMap
    (R.rightACommonSourceClosureTransport hind)
    (R.rightACommonSourceClosureTransport_base_trans_self hind) x

/-- The final semilinear source chart carries the whole intrinsic
repeated-`s` germ embedding to the repeated-`sA` embedding. -/
theorem groupedStableASourceChartRingEquiv_comp_sourceS
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.groupedStableASourceChartRingEquiv L hind).toRingHom.comp
        (R.groupedStableAOrbitSourceS L hind) =
      R.groupedStableAOrbitSourceSA L hind := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply,
    R.groupedStableAOrbitSourceS_apply L hind]
  change R.groupedStableASourceChartRingEquiv L hind
      (algebraMap (groupedStableOrbitSemanticSourceType R)
        (↥(R.groupedStableAOrbitSourceCover L hind).field)
        (R.seBGermCoefficientToSemanticSourceAlgHom L hind x)) = _
  rw [R.groupedStableASourceChartRingEquiv_algebraMap L hind,
    R.groupedStableAOrbitSourceSA_apply L hind]
  exact congrArg
    (algebraMap (groupedStableOrbitSemanticSourceType R)
      (↥(R.groupedStableAOrbitSourceCover L hind).field))
    (R.commonSourceRightAAut_comp_seBGermCoefficient L hind x)

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
