/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveReferenceBridge

/-!
# B-germ coefficients and the complete selected-B branch

Factorization of the `B`-germ coefficient field through the complete selected-`B`
branch. Split from `AclGeom.Config.ChunkCurveReferenceBridge` (#18).
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace QWitness.PsiCurveFourArrowCommonSourceRealizations

/- These chart types use named intermediate-field and normal-cover aliases.
Lean 4.34's default backward transparency does not unfold those aliases in
rewrites or instance comparisons. This setting is scoped to this bridge;
it affects elaboration only, and the resulting terms are kernel-checked. -/
section ReferenceFieldAliases
set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- All four original complete relocated right branches lie in the same
selected semantic/reference normal closure. -/
theorem fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sb.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k ∧
      (R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchField.restrictScalars k ≤
        (R.selectedSemanticReferenceNormalField L hind).restrictScalars k := by
  let hJ := R.selectedSemanticReferenceJoin_le_normalField_restrictScalars L hind
  exact ⟨(R.seRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAaRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sbRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ,
    (R.sAcRelocatedRightBranch_le_selectedSemanticReferenceJoin L hind).trans hJ⟩

/-- Literal inclusion of the original relocated `e` right branch. -/
noncomputable def seRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.se.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.1 hz)

/-- Literal inclusion of the original relocated `a` right branch. -/
noncomputable def sAaRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sAa.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.1 hz)

/-- Literal inclusion of the original relocated `b` right branch. -/
noncomputable def sbRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sb.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.1 hz)

/-- Literal inclusion of the original relocated `c` right branch. -/
noncomputable def sAcRelocatedRightBranchToSelectedNormalRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource →+*
      R.selectedSemanticReferenceNormalField L hind :=
  let Q := (R.sAc.bCorrespondenceFamilyMember hψ).toPair
  Q.branchOverSourceToIntermediateFieldRingHom
    (R.selectedSemanticReferenceNormalField L hind)
    (fun _ hz ↦ R.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField
      L hind |>.2.2.2 hz)

/-- Canonicalize the original relocated `e` branch after literal inclusion. -/
noncomputable def seRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.seRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `a` branch. -/
noncomputable def sAaRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAaRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `b` branch. -/
noncomputable def sbRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sbRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- Canonicalize the original relocated `c` branch. -/
noncomputable def sAcRelocatedRightBranchToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.ambientSelectedSemanticReferenceNormalFieldToSourceCover L hind).toRingHom.comp
    (R.sAcRelocatedRightBranchToSelectedNormalRingHom L hind)

/-- The original relocated `e` branch in the same graph source. -/
noncomputable def seRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `a` branch in the same graph source. -/
noncomputable def sAaRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `b` branch in the same graph source. -/
noncomputable def sbRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- The original relocated `c` branch in the same graph source. -/
noncomputable def sAcRelocatedRightBranchToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind)

/-- Under the preceding parameter equivalence, the selected canonical `B`
curve equation is exactly the canonical equation of the relocated branch. -/
theorem selectedBCurveEquation_map_relocated
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal) :
    MvPolynomial.map
        (selectedBToRelocatedBParameterEquiv
          (w := w) (hψ := hψ) G h).toRingHom
        (w.yzCorrespondencePairOverB hψ).curveEquation =
      G.toPair.curveEquation := by
  let F := w.yzCorrespondenceFamilyMember hψ
  let ι := commonCurveEmbedding (k := k) (K := K)
  let e₁ := F.parameterMapEquiv ι
  let e₂ := (F.map ι).parameterEquivOfIdealEq G h
  change MvPolynomial.map (e₁.trans e₂).toRingHom
      F.toPair.curveEquation = G.toPair.curveEquation
  calc
    MvPolynomial.map (e₁.trans e₂).toRingHom
        F.toPair.curveEquation =
        MvPolynomial.map e₂.toRingHom
          (MvPolynomial.map e₁.toRingHom F.toPair.curveEquation) := by
      rw [MvPolynomial.map_map]
      rfl
    _ = MvPolynomial.map e₂.toRingHom
        (F.map ι).toPair.curveEquation := by
      rw [F.curveEquation_map_parameterMapEquiv ι]
    _ = G.toPair.curveEquation :=
      (F.map ι).curveEquation_map_parameterEquivOfIdealEq G h

/-- The intrinsic coordinate represented by one coefficient of the selected
canonical `B` curve equation. -/
noncomputable def selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) : w.bGermCoefficientField hψ :=
  (w.yzCorrespondencePairOverB hψ).curveCoefficientCoordinates
    k w.bField
    ⟨(((w.yzCorrespondencePairOverB hψ).curveEquation.coeff d :
        w.bField) : K), ⟨d, rfl⟩⟩

/-- Including an intrinsic coefficient coordinate into the selected
parameter field recovers the corresponding literal polynomial coefficient. -/
@[simp] theorem bGermCoefficientToSelectedBParameterAlgHom_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ)
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      (w.yzCorrespondencePairOverB hψ).curveEquation.coeff d :=
  by
    apply Subtype.ext
    rfl

/-- Two coefficient-linear maps out of the intrinsic selected-`B` germ
field are equal as soon as they agree on every canonical curve
coefficient.  This is the extensionality principle used to descend the
four-arrow comparison from relocated equations to the intrinsic chart. -/
theorem bGermCoefficientAlgHom_ext
    {F : Type u} [Field F] [Algebra k F]
    {f g : (↥(w.bGermCoefficientField hψ)) →ₐ[k] F}
    (h : ∀ d : Fin 2 →₀ ℕ,
      f (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        g (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) :
    f = g := by
  unfold QWitness.bGermCoefficientField
    FiniteCorrespondencePair.curveCoefficientField
  apply IntermediateField.adjoin_algHom_ext k
  rintro _ ⟨d, rfl⟩
  exact h d

/-- Canonical normalized parameter transport carries every intrinsic
selected-`B` curve coefficient to the corresponding coefficient of the
relocated canonical curve equation. -/
theorem projectionParameterTransport_selectedBCurveCoefficient
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) p G hG
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) hp
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
      G.toPair.curveEquation.coeff d := by
  have hcurve := selectedBCurveEquation_map_relocated
    (w := w) (hψ := hψ) G h
  have hcoeff := congrArg (fun f => f.coeff d) hcurve
  rw [MvPolynomial.coeff_map] at hcoeff
  rw [selectedBToRelocatedBParameterEquiv_eq_projection
    (w := w) (hψ := hψ) p x hp G h hG] at hcoeff
  change rankTwoParameterCurveEquivToFamily
      (k := k) (K := K) p G hG
      (locusFunctionFieldEquivOfIdealEq
        (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ)
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d))) = _
  rw [bGermCoefficientToSelectedBParameterAlgHom_selectedBCurveCoefficient]
  change rankTwoParameterCurveEquivToFamily
      (k := k) (K := K) p G hG
      (locusFunctionFieldEquivOfIdealEq
        (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hp.symm)
        ((w.yzCorrespondencePairOverB hψ).curveEquation.coeff d)) = _
    at hcoeff
  exact hcoeff

/-- On every canonical generator, the whole-field relocated parameter map
recovers the matching coefficient of the relocated curve equation. -/
@[simp] theorem
    bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      G.toPair.curveEquation.coeff d := by
  exact projectionParameterTransport_selectedBCurveCoefficient
    (w := w) (hψ := hψ) p x hp G h hG d

/-- The ambient form of the intrinsic coefficient transport.  Its image is
exactly the intrinsic coefficient field of the relocated canonical curve. -/
private noncomputable def bGermToRelocatedAmbientAlgHom
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥((w.yzCorrespondencePairOverB hψ).curveCoefficientField
      k w.bField)) →ₐ[k] CommonCurveAmbient K :=
  G.parameterField.val.comp
    (bGermCoefficientToRelocatedBParameterAlgHom
      (w := w) (hψ := hψ) p x hp G hG)

private theorem bGermToRelocatedAmbient_fieldRange
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (bGermToRelocatedAmbientAlgHom
      (w := w) (hψ := hψ) p x hp G hG).fieldRange =
      G.toPair.curveCoefficientField k G.parameterField := by
  have htop := (w.yzCorrespondencePairOverB hψ).adjoin_curveCoefficientCoordinates_eq_top
    k w.bField
  have htop' : (⊤ : IntermediateField k
      ((w.yzCorrespondencePairOverB hψ).curveCoefficientField k w.bField)) =
      IntermediateField.adjoin k
        (Set.range ((w.yzCorrespondencePairOverB hψ).curveCoefficientCoordinates
          k w.bField)) := htop.symm
  rw [AlgHom.fieldRange_eq_map, htop', IntermediateField.adjoin_map]
  unfold FiniteCorrespondencePair.curveCoefficientField
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := c.2
    have hc : c = ⟨_, ⟨d, rfl⟩⟩ := Subtype.ext hd.symm
    subst c
    refine ⟨d, ?_⟩
    exact (congrArg Subtype.val
      (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
        (w := w) (hψ := hψ) p x hp G h hG d)).symm
  · rintro ⟨d, rfl⟩
    refine ⟨selectedBCurveCoefficient (w := w) (hψ := hψ) d, ?_, ?_⟩
    · exact ⟨⟨_, ⟨d, rfl⟩⟩, rfl⟩
    · exact congrArg Subtype.val
        (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
          (w := w) (hψ := hψ) p x hp G h hG d)

private theorem bGermToRelocatedAmbient_mem_curveCoefficientField
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (z : w.bGermCoefficientField hψ) :
    bGermToRelocatedAmbientAlgHom
        (w := w) (hψ := hψ) p x hp G hG z ∈
      G.toPair.curveCoefficientField k G.parameterField := by
  rw [← bGermToRelocatedAmbient_fieldRange
    (w := w) (hψ := hψ) p x hp G h hG]
  exact AlgHom.mem_fieldRange.mpr ⟨z, rfl⟩

/-- The intrinsic selected-`B` coefficient field is canonically equivalent
to the intrinsic coefficient field of any relocated canonical curve on the
same family locus. -/
noncomputable def bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥(G.toPair.curveCoefficientField k G.parameterField)) := by
  let f : (↥(w.bGermCoefficientField hψ)) →ₐ[k]
      (↥(G.toPair.curveCoefficientField k G.parameterField)) :=
    (bGermToRelocatedAmbientAlgHom
      (w := w) (hψ := hψ) p x hp G hG).codRestrict
      (G.toPair.curveCoefficientField k G.parameterField).toSubalgebra
      (bGermToRelocatedAmbient_mem_curveCoefficientField
        (w := w) (hψ := hψ) p x hp G h hG)
  apply AlgEquiv.ofBijective f
  constructor
  · exact f.injective
  · intro y
    have hy : (y : CommonCurveAmbient K) ∈
        (bGermToRelocatedAmbientAlgHom
          (w := w) (hψ := hψ) p x hp G hG).fieldRange := by
      rw [bGermToRelocatedAmbient_fieldRange
        (w := w) (hψ := hψ) p x hp G h hG]
      exact y.2
    obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hy
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz

/-- The intrinsic coefficient equivalence preserves the monomial index of
every canonical curve coefficient. -/
@[simp] theorem bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p)
    (d : Fin 2 →₀ ℕ) :
    bGermCoefficientToRelocatedBCoefficientAlgEquiv
        (w := w) (hψ := hψ) p x hp G h hG
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
      ⟨((G.toPair.curveEquation.coeff d : G.parameterField) :
          CommonCurveAmbient K),
        G.toPair.coeff_mem_curveCoefficientField k G.parameterField d⟩ := by
  apply Subtype.ext
  change ((bGermCoefficientToRelocatedBParameterAlgHom
      (w := w) (hψ := hψ) p x hp G hG
      (selectedBCurveCoefficient (w := w) (hψ := hψ) d) :
        G.parameterField) : CommonCurveAmbient K) = _
  exact congrArg Subtype.val
    (bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
      (w := w) (hψ := hψ) p x hp G h hG d)

/-- The whole relocated parameter transport is the intrinsic coefficient
equivalence followed by the literal inclusion of the relocated coefficient
field into its displayed parameter field. -/
theorem bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG =
      (IntermediateField.inclusion
        (G.toPair.curveCoefficientField_le k G.parameterField)).comp
        (bGermCoefficientToRelocatedBCoefficientAlgEquiv
          (w := w) (hψ := hψ) p x hp G h hG).toAlgHom := by
  apply bGermCoefficientAlgHom_ext (w := w) (hψ := hψ)
  intro d
  rw [bGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (w := w) (hψ := hψ) p x hp G h hG d]
  apply Subtype.ext
  exact (congrArg Subtype.val
    (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
      (w := w) (hψ := hψ) p x hp G h hG d)).symm

/-- Embedding the relocated parameter transport in the complete branch is
the same map as passing through the intrinsic relocated coefficient field.
This turns the coefficient factorization into an exact branch restriction. -/
theorem bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
    (p : Fin 2 → K) (x : K) (hp : w.psiBProjectionRelation p x)
    (G : FiniteCorrespondenceFamilyMember
      (k := k) (Ω := CommonCurveAmbient K) 2)
    (h : (mappedSelectedBFamily (w := w) (hψ := hψ)).ideal = G.ideal)
    (hG : G.parameter =
      commonCurveEmbedding (k := k) (K := K) ∘ p) :
    (algebraMap (↥G.parameterField)
        (↥G.toPair.branchOverSource)).comp
          (bGermCoefficientToRelocatedBParameterAlgHom
            (w := w) (hψ := hψ) p x hp G hG).toRingHom =
      (relocatedBCoefficientToCompleteRightBranchRingHom G).comp
        (bGermCoefficientToRelocatedBCoefficientAlgEquiv
          (w := w) (hψ := hψ) p x hp G h hG).toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  change algebraMap (↥G.parameterField) (↥G.toPair.branchOverSource)
      (bGermCoefficientToRelocatedBParameterAlgHom
        (w := w) (hψ := hψ) p x hp G hG z) =
    relocatedBCoefficientToCompleteRightBranchRingHom G
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv
        (w := w) (hψ := hψ) p x hp G h hG z)
  rw [DFunLike.congr_fun
    (bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients
      (w := w) (hψ := hψ) p x hp G h hG) z]
  apply Subtype.ext
  rfl

/-- Include the original selected `B` parameter field in the complete
branch of its mapped family member.  This is the one common middle-branch
map from which the four relocated complete-branch transports start. -/
noncomputable def selectedBParameterToMappedCompleteBranchRingHom :
    (↥w.bField) →+*
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) :=
  (algebraMap
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).parameterField)
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource)).comp
    ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
      (commonCurveEmbedding (k := k) (K := K))).toRingEquiv.toRingHom

/-- Restrict the common mapped selected-`B` branch to the intrinsic germ
coefficient field.  This is the candidate common middle map for the final
right-restriction package. -/
noncomputable def bGermCoefficientToMappedCompleteBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) :=
  (selectedBParameterToMappedCompleteBranchRingHom
    (w := w) (hψ := hψ)).comp
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ)).toRingHom

/-- Simultaneously, the four full branch equivalences restrict on the
whole selected `B` parameter field to the canonical selected-to-relocated
parameter transports.  Thus the common middle branch is already identified
before passing to normal middle and target covers. -/
theorem fourSelectedBCompleteBranchRingEquiv_parameter :
    R.seSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.se.bCorrespondenceFamilyMember hψ)
              R.seMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sAaSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sAa.bCorrespondenceFamilyMember hψ)
              R.sAaMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sbSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sb.bCorrespondenceFamilyMember hψ)
              R.sbMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom ∧
      R.sAcSelectedBCompleteBranchRingEquiv.toRingHom.comp
          (selectedBParameterToMappedCompleteBranchRingHom
            (w := w) (hψ := hψ)) =
        (algebraMap
          (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
          (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)).comp
            (selectedBToRelocatedBParameterEquiv
              (w := w) (hψ := hψ)
              (R.sAc.bCorrespondenceFamilyMember hψ)
              R.sAcMappedSelectedBFamily_ideal_eq).toRingEquiv.toRingHom := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply RingHom.ext <;> intro z
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))
  · exact (mappedSelectedBFamily (w := w) (hψ := hψ)
      |>.completeBranchRingEquivOfIdealEq_algebraMap
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        ((w.yzCorrespondenceFamilyMember hψ).parameterMapEquiv
          (commonCurveEmbedding (k := k) (K := K)) z))

/-- The rebased `e` cover is a literal subcover of the four-face right
cover. -/
theorem seRelocatedRightRebasedCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.seRelocatedRightRebasedCover L hind).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field :=
  (le_sup_left.trans le_sup_left).trans le_sup_left

/-- The rebased `a` cover is a literal subcover of the four-face right
cover. -/
theorem sAaRelocatedRightRebasedCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAaRelocatedRightRebasedCover L hind).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field :=
  (le_sup_right.trans le_sup_left).trans le_sup_left

/-- The rebased `b` cover is a literal subcover of the four-face right
cover. -/
theorem sbRelocatedRightRebasedCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sbRelocatedRightRebasedCover L hind).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field :=
  le_sup_right.trans le_sup_left

/-- The rebased `c` cover is a literal subcover of the four-face right
cover. -/
theorem sAcRelocatedRightRebasedCover_le_four
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.sAcRelocatedRightRebasedCover L hind).field ≤
      (R.fourRelocatedRightRebasedCover L hind).field :=
  le_sup_right

/-- The common mapped selected-`B` complete branch carried to the `e`
image in the four-face scalar-rebased cover. -/
noncomputable def seSelectedBCompleteBranchToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedCompleteBranchToFourRebasedCoverRingHom L hind
    (R.se.bCorrespondenceFamilyMember hψ)
    (R.seRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.seRelocatedRightRebasedCover_le_four L hind)).comp
      R.seSelectedBCompleteBranchRingEquiv.toRingHom

/-- The corresponding common-branch map to the `a` image. -/
noncomputable def sAaSelectedBCompleteBranchToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedCompleteBranchToFourRebasedCoverRingHom L hind
    (R.sAa.bCorrespondenceFamilyMember hψ)
    (R.sAaRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sAaRelocatedRightRebasedCover_le_four L hind)).comp
      R.sAaSelectedBCompleteBranchRingEquiv.toRingHom

/-- The corresponding common-branch map to the `b` image. -/
noncomputable def sbSelectedBCompleteBranchToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedCompleteBranchToFourRebasedCoverRingHom L hind
    (R.sb.bCorrespondenceFamilyMember hψ)
    (R.sbRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sbRelocatedRightRebasedCover_le_four L hind)).comp
      R.sbSelectedBCompleteBranchRingEquiv.toRingHom

/-- The corresponding common-branch map to the algebraic `c` image. -/
noncomputable def sAcSelectedBCompleteBranchToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(mappedSelectedBFamily (w := w) (hψ := hψ)).toPair.branchOverSource) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedCompleteBranchToFourRebasedCoverRingHom L hind
    (R.sAc.bCorrespondenceFamilyMember hψ)
    (R.sAcRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sAcRelocatedRightRebasedCover_le_four L hind)).comp
      R.sAcSelectedBCompleteBranchRingEquiv.toRingHom

/-- Transport the whole mapped selected-`B` native normal cover through the
based `e` comparison and then through the branch-preserving scalar rebase. -/
noncomputable def seSelectedBNormalToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedRightNormalToFourRebasedCoverRingHom L hind
    (R.se.bCorrespondenceFamilyMember hψ)
    (R.seRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.seRelocatedRightRebasedCover_le_four L hind)).comp
      R.seSelectedBNormalCoverRingEquiv.toRingHom

/-- Transport the mapped selected-`B` native normal cover through the based
`a` comparison and its scalar rebase. -/
noncomputable def sAaSelectedBNormalToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedRightNormalToFourRebasedCoverRingHom L hind
    (R.sAa.bCorrespondenceFamilyMember hψ)
    (R.sAaRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sAaRelocatedRightRebasedCover_le_four L hind)).comp
      R.sAaSelectedBNormalCoverRingEquiv.toRingHom

/-- Transport the mapped selected-`B` native normal cover through the based
`b` comparison and its scalar rebase. -/
noncomputable def sbSelectedBNormalToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedRightNormalToFourRebasedCoverRingHom L hind
    (R.sb.bCorrespondenceFamilyMember hψ)
    (R.sbRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sbRelocatedRightRebasedCover_le_four L hind)).comp
      R.sbSelectedBNormalCoverRingEquiv.toRingHom

/-- Transport the mapped selected-`B` native normal cover through the based
`c` comparison and its scalar rebase. -/
noncomputable def sAcSelectedBNormalToFourRebasedCoverRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(FiniteCover.normalClosureOver
      (mappedSelectedBFamily (w := w) (hψ := hψ)
        |>.parameterSourceField_le_familyField))) →+*
      (↥(R.fourRelocatedRightRebasedCover L hind).field) :=
  (R.relocatedRightNormalToFourRebasedCoverRingHom L hind
    (R.sAc.bCorrespondenceFamilyMember hψ)
    (R.sAcRelocatedParameterSourceField_le_selectedSemanticReferenceJoin
      L hind)
    (R.sAcRelocatedRightRebasedCover_le_four L hind)).comp
      R.sAcSelectedBNormalCoverRingEquiv.toRingHom

/-- The transported four-face field lies literally in its normal closure
over the common semantic source. -/
theorem fourRelocatedRightTransportedField_le_sourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    R.fourRelocatedRightTransportedField L hind ≤
      (R.fourRelocatedRightSourceCover L hind).field :=
  le_normalClosure _

/-! ### One finite normal codomain for the four semilinear source charts -/

/-- The transported common four-face right cover is a literal subcover of
the right-enlarged graph source. -/
theorem fourRelocatedRightSourceCover_le_selectedGraphRightSourceCover
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (R.fourRelocatedRightSourceCover L hind).field ≤
      (R.selectedGraphRightSourceCover L hind).field :=
  le_sup_right

/-- Carry the four-face right cover from its joint-field model into the
right-enlarged graph source over the literal semantic source. -/
noncomputable def fourRelocatedRightToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(R.fourRelocatedRightRebasedCover L hind).field) →+*
      (↥(R.selectedGraphRightSourceCover L hind).field) :=
  (IntermediateField.inclusion
      (R.fourRelocatedRightSourceCover_le_selectedGraphRightSourceCover
        L hind)).toRingHom.comp
    ((IntermediateField.inclusion
      (R.fourRelocatedRightTransportedField_le_sourceCover
        L hind)).toRingHom.comp
        (R.fourRelocatedRightTransportedFieldRingEquiv L hind).toRingHom)

/-- The common selected-`B` complete branch mapped to the `e` image in the
right-enlarged graph source. -/
noncomputable def seSelectedBCompleteBranchToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.seSelectedBCompleteBranchToFourRebasedCoverRingHom L hind)

/-- The corresponding complete-branch map to the `a` image. -/
noncomputable def sAaSelectedBCompleteBranchToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sAaSelectedBCompleteBranchToFourRebasedCoverRingHom L hind)

/-- The corresponding complete-branch map to the `b` image. -/
noncomputable def sbSelectedBCompleteBranchToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sbSelectedBCompleteBranchToFourRebasedCoverRingHom L hind)

/-- The corresponding complete-branch map to the algebraic `c` image. -/
noncomputable def sAcSelectedBCompleteBranchToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sAcSelectedBCompleteBranchToFourRebasedCoverRingHom L hind)

/-- Carry the selected native normal cover through its `e` comparison and
into the right-enlarged graph source. -/
noncomputable def seSelectedBNormalToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.seSelectedBNormalToFourRebasedCoverRingHom L hind)

/-- Carry the selected native normal cover through its `a` comparison. -/
noncomputable def sAaSelectedBNormalToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sAaSelectedBNormalToFourRebasedCoverRingHom L hind)

/-- Carry the selected native normal cover through its `b` comparison. -/
noncomputable def sbSelectedBNormalToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sbSelectedBNormalToFourRebasedCoverRingHom L hind)

/-- Carry the selected native normal cover through its algebraic `c`
comparison. -/
noncomputable def sAcSelectedBNormalToSelectedGraphRightRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :=
  (R.fourRelocatedRightToSelectedGraphRightRingHom L hind).comp
    (R.sAcSelectedBNormalToFourRebasedCoverRingHom L hind)

/-- All four normalized parameter transports carry each intrinsic selected
`B` coefficient to the coefficient with the same monomial index in the
corresponding relocated right-branch equation. -/
theorem fourProjectionParameterTransports_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) e
        (R.se.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.eProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) a
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.aProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) b
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.1
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.bProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      rankTwoParameterCurveEquivToFamily
        (k := k) (K := K) D.c
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.relocatedBFamily_parameters.2.2.2
        (bGermCoefficientToProjectionParameterAlgHom
          (w := w) (hψ := hψ) L.cProjectionRelation
          (selectedBCurveCoefficient (w := w) (hψ := hψ) d)) =
        (R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d := by
  exact ⟨projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
      (R.se.bCorrespondenceFamilyMember hψ)
      R.seMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
      (R.sAa.bCorrespondenceFamilyMember hψ)
      R.sAaMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
      (R.sb.bCorrespondenceFamilyMember hψ)
      R.sbMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.1 d,
    projectionParameterTransport_selectedBCurveCoefficient
      (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
      (R.sAc.bCorrespondenceFamilyMember hψ)
      R.sAcMappedSelectedBFamily_ideal_eq
      R.relocatedBFamily_parameters.2.2.2 d⟩

/-- The intrinsic coefficient equivalence for the relocated right family in
the `s·e=u` face. -/
noncomputable def seBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.se.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.se.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
    (R.se.bCorrespondenceFamilyMember hψ)
    R.seMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `sA·a=u` face. -/
noncomputable def sAaBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sAa.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
    (R.sAa.bCorrespondenceFamilyMember hψ)
    R.sAaMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `s·b=uB` face. -/
noncomputable def sbBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sb.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
    (R.sb.bCorrespondenceFamilyMember hψ)
    R.sbMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.2.1

/-- The intrinsic coefficient equivalence for the relocated right family in
the `sA·c=uB` face. -/
noncomputable def sAcBGermCoefficientToRelocatedBCoefficientAlgEquiv :
    (↥(w.bGermCoefficientField hψ)) ≃ₐ[k]
      (↥((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveCoefficientField k
          (R.sAc.bCorrespondenceFamilyMember hψ).parameterField)) :=
  bGermCoefficientToRelocatedBCoefficientAlgEquiv
    (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
    (R.sAc.bCorrespondenceFamilyMember hψ)
    R.sAcMappedSelectedBFamily_ideal_eq
    R.relocatedBFamily_parameters.2.2.2

/-- The intrinsic selected-`B` coefficient field embedded in the complete
right `e` branch through its relocated coefficient field. -/
noncomputable def seBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.se.bCorrespondenceFamilyMember hψ)).comp
      (R.seBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `a`
branch. -/
noncomputable def sAaBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sAa.bCorrespondenceFamilyMember hψ)).comp
      (R.sAaBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `b`
branch. -/
noncomputable def sbBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sb.bCorrespondenceFamilyMember hψ)).comp
      (R.sbBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The corresponding intrinsic embedding in the complete right `c`
branch. -/
noncomputable def sAcBGermCoefficientToCompleteRightBranchRingHom :
    (↥(w.bGermCoefficientField hψ)) →+*
      (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource) :=
  (relocatedBCoefficientToCompleteRightBranchRingHom
    (R.sAc.bCorrespondenceFamilyMember hψ)).comp
      (R.sAcBGermCoefficientToRelocatedBCoefficientAlgEquiv L).toRingEquiv.toRingHom

/-- The four intrinsic complete-branch embeddings are restrictions of the
four full branch equivalences from one common mapped selected-`B` branch.
This is the branch-level middle chart, before extension to the four normal
middle covers. -/
theorem fourBGermCoefficientCompleteBranch_factor_selectedB :
    R.seSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.seBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sAaSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sbSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sbBGermCoefficientToCompleteRightBranchRingHom L ∧
    R.sAcSelectedBCompleteBranchRingEquiv.toRingHom.comp
        (bGermCoefficientToMappedCompleteBranchRingHom
          (w := w) (hψ := hψ)) =
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L := by
  obtain ⟨he, ha, hb, hc⟩ :=
    R.fourSelectedBCompleteBranchRingEquiv_parameter
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply RingHom.ext <;> intro z
  · have hbranch := DFunLike.congr_fun he
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.seBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.1) z
    change algebraMap
        (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.seBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.seBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.se.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.se.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun ha
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.1) z
    change algebraMap
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sAaBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAa.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun hb
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.1)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.1) z
    change algebraMap
        (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sbBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sbBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sb.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sb.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)
  · have hbranch := DFunLike.congr_fun hc
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    have hparam := DFunLike.congr_fun
      (selectedBToRelocatedBParameterEquiv_eq_projection
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.2)
      (bGermCoefficientToSelectedBParameterAlgHom
        (w := w) (hψ := hψ) z)
    change selectedBToRelocatedBParameterEquiv
        (w := w) (hψ := hψ)
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        (bGermCoefficientToSelectedBParameterAlgHom
          (w := w) (hψ := hψ) z) =
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L z at hparam
    have hcomplete := DFunLike.congr_fun
      (bGermCoefficientToCompleteRightBranchRingHom_eq_parameter
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq
        R.relocatedBFamily_parameters.2.2.2) z
    change algebraMap
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource)
        (R.sAcBGermCoefficientToRelocatedBParameterAlgHom L z) =
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L z at hcomplete
    exact hbranch.trans ((congrArg
      (algebraMap
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).parameterField)
        (↥(R.sAc.bCorrespondenceFamilyMember hψ).toPair.branchOverSource))
      hparam).trans hcomplete)

/-- On every canonical generator, the four complete-branch embeddings are
the literal same-index relocated curve coefficients. -/
theorem fourBGermCoefficientToCompleteRightBranchRingHom_selected
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.se.bCorrespondenceFamilyMember hψ)
          ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.se.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sAaBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sAa.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sAa.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sbBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sb.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sb.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩ ∧
      R.sAcBGermCoefficientToCompleteRightBranchRingHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        relocatedBCoefficientToCompleteRightBranchRingHom
          (R.sAc.bCorrespondenceFamilyMember hψ)
          ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
              (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
              CommonCurveAmbient K),
            (R.sAc.bCorrespondenceFamilyMember hψ).toPair
              |>.coeff_mem_curveCoefficientField k
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩ := by
  simp only [seBGermCoefficientToCompleteRightBranchRingHom,
    sAaBGermCoefficientToCompleteRightBranchRingHom,
    sbBGermCoefficientToCompleteRightBranchRingHom,
    sAcBGermCoefficientToCompleteRightBranchRingHom, RingHom.comp_apply]
  exact ⟨congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.se.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) e L.se_e L.eProjectionRelation
        (R.se.bCorrespondenceFamilyMember hψ)
        R.seMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sAa.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) a L.sA_a_a L.aProjectionRelation
        (R.sAa.bCorrespondenceFamilyMember hψ)
        R.sAaMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sb.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) b L.s_b_b L.bProjectionRelation
        (R.sb.bCorrespondenceFamilyMember hψ)
        R.sbMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.2.1 d),
    congrArg
      (relocatedBCoefficientToCompleteRightBranchRingHom
        (R.sAc.bCorrespondenceFamilyMember hψ))
      (bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected
        (w := w) (hψ := hψ) D.c L.sA_c_c L.cProjectionRelation
        (R.sAc.bCorrespondenceFamilyMember hψ)
        R.sAcMappedSelectedBFamily_ideal_eq R.relocatedBFamily_parameters.2.2.2 d)⟩

/-- The intrinsic selected-`B` coefficient field embedded through the
original relocated `e` branch into the once-canonicalized selected cover. -/
noncomputable def seBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.seRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.seBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `a` branch. -/
noncomputable def sAaBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sAaBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `b` branch. -/
noncomputable def sbBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sbBGermCoefficientToCompleteRightBranchRingHom L)

/-- The corresponding intrinsic coefficient embedding through the
relocated `c` branch. -/
noncomputable def sAcBGermCoefficientToSelectedSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedSemanticReferenceSourceCover L hind).field :=
  (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind).comp
    (R.sAcBGermCoefficientToCompleteRightBranchRingHom L)

/-- On every canonical coefficient, the four selected-cover maps are
exactly the once-canonicalized literal relocated coefficients in their
complete branches. -/
theorem fourBGermCoefficientToSelectedSourceRingHom_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.seRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.se.bCorrespondenceFamilyMember hψ)
            ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.se.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAaBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAa.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAa.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sbBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sbRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sb.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sb.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAcBGermCoefficientToSelectedSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAc.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAc.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩) := by
  unfold seBGermCoefficientToSelectedSourceRingHom
    sAaBGermCoefficientToSelectedSourceRingHom
    sbBGermCoefficientToSelectedSourceRingHom
    sAcBGermCoefficientToSelectedSourceRingHom
  simp only [RingHom.comp_apply]
  obtain ⟨he, ha, hb, hc⟩ :=
    R.fourBGermCoefficientToCompleteRightBranchRingHom_selected L d
  exact ⟨congrArg (R.seRelocatedRightBranchToSelectedSourceRingHom L hind) he,
    congrArg (R.sAaRelocatedRightBranchToSelectedSourceRingHom L hind) ha,
    congrArg (R.sbRelocatedRightBranchToSelectedSourceRingHom L hind) hb,
    congrArg (R.sAcRelocatedRightBranchToSelectedSourceRingHom L hind) hc⟩

/-- The intrinsic selected-`B` coefficient field on the `e` face, now in
the graph source that also contains the coherent semantic cover. -/
noncomputable def seBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.seBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `a` face in the same graph
source. -/
noncomputable def sAaBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAaBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `b` face in the same graph
source. -/
noncomputable def sbBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sbBGermCoefficientToSelectedSourceRingHom L hind)

/-- The intrinsic coefficient embedding on the `c` face in the same graph
source. -/
noncomputable def sAcBGermCoefficientToSelectedGraphSourceRingHom
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    (↥(w.bGermCoefficientField hψ)) →+*
      (R.selectedGraphSourceCover L hind).field :=
  (R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover
      L hind).toRingHom.comp
    (R.sAcBGermCoefficientToSelectedSourceRingHom L hind)

/-- Passing to the enlarged graph source preserves all four exact
same-index coefficient formulas. -/
theorem fourBGermCoefficientToSelectedGraphSourceRingHom_selected
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.seRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.se.bCorrespondenceFamilyMember hψ)
            ⟨(((R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.se.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.se.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.se.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAaBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAaRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAa.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAa.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAa.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAa.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sbBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sbRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sb.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sb.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sb.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sb.bCorrespondenceFamilyMember hψ).parameterField d⟩) ∧
      R.sAcBGermCoefficientToSelectedGraphSourceRingHom L hind
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        R.sAcRelocatedRightBranchToSelectedGraphSourceRingHom L hind
          (relocatedBCoefficientToCompleteRightBranchRingHom
            (R.sAc.bCorrespondenceFamilyMember hψ)
            ⟨(((R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d :
                (R.sAc.bCorrespondenceFamilyMember hψ).parameterField) :
                CommonCurveAmbient K),
              (R.sAc.bCorrespondenceFamilyMember hψ).toPair
                |>.coeff_mem_curveCoefficientField k
                  (R.sAc.bCorrespondenceFamilyMember hψ).parameterField d⟩) := by
  let ι :=
    R.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover L hind
  constructor
  · have he :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).1
    simpa [seBGermCoefficientToSelectedGraphSourceRingHom,
      seRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι he
  constructor
  · have ha :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.1
    simpa [sAaBGermCoefficientToSelectedGraphSourceRingHom,
      sAaRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι ha
  constructor
  · have hb :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.2.1
    simpa [sbBGermCoefficientToSelectedGraphSourceRingHom,
      sbRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι hb
  · have hc :=
      (R.fourBGermCoefficientToSelectedSourceRingHom_selected L hind d).2.2.2
    simpa [sAcBGermCoefficientToSelectedGraphSourceRingHom,
      sAcRelocatedRightBranchToSelectedGraphSourceRingHom, ι] using
        congrArg ι hc

/-- Simultaneously, the four whole-field maps recover the coefficient with
the same monomial index in each relocated right-family equation. -/
theorem
    fourBGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient
    (d : Fin 2 →₀ ℕ) :
    R.seBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.se.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sAaBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sAa.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sbBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sb.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d ∧
      R.sAcBGermCoefficientToRelocatedBParameterAlgHom L
        (selectedBCurveCoefficient (w := w) (hψ := hψ) d) =
        (R.sAc.bCorrespondenceFamilyMember hψ).toPair.curveEquation.coeff d := by
  exact R.fourProjectionParameterTransports_selectedBCurveCoefficient L d

end ReferenceFieldAliases

end QWitness.PsiCurveFourArrowCommonSourceRealizations

end

end AclGeom
