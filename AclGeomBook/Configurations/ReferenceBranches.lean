/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.ChunkCurveCommonSourceRebasing
import AclGeom.Config.ChunkCurveReferenceBridgeBGermComplete
import AclGeom.Config.ChunkCurveReferenceBridgeSelectedBScalar
import AclGeom.Config.ChunkCurveReferenceBridgeSemanticBranches

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Selected branches and reference source maps" =>

%%%
tag := "configuration-record-reference-branches"
%%%

For the three alternative coefficient presentations, the two source changes
cancel explicitly.  The resulting algebra charts transport the selected
whole-total-field branches first into their rebased canonical covers and
then into the one enlarged comparison source cover:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonRawBaseRoundtrip}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonRawBaseRoundtrip}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonRawBaseRoundtrip}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonCanonicalCoverAlgEquivRebased}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonCanonicalCoverAlgEquivRebased}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonCanonicalCoverAlgEquivRebased}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSelectedTotalEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSelectedTotalEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSelectedTotalEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSelectedTotalEmbeddingInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSelectedTotalEmbeddingInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSelectedTotalEmbeddingInComparisonSourceCover}

The whole-total-field maps have coherent restrictions to both literal
branches of each repeated relation.  Carrier equality transports the
branch containments across their scalar presentations, so the two `sA`
branches, the two direct `u` branches, and the two direct `uB` branches are
all anchored by three shared total-field embeddings.  Normality of the
simultaneous cover then supplies deck transformations carrying every actual
selected face branch to its coherent anchor, with exact action equations:

{docstring IntermediateField.le_of_carrier_eq_pair}

{docstring AclGeom.FiniteCoefficientBranchCompositum.firstBranchOverRebasedSource_le_normalField}

{docstring AclGeom.FiniteCoefficientBranchCompositum.secondBranchOverRebasedSource_le_normalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedLeftBranchEmbeddingViaRepeatedSACommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedLeftBranchEmbeddingViaRepeatedSACommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedDirectBranchEmbeddingViaRepeatedUCommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedDirectBranchEmbeddingViaRepeatedUCommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedDirectBranchEmbeddingViaRepeatedUBCommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedDirectBranchEmbeddingViaRepeatedUBCommonTotal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRepeatedSATotalAnchorAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRepeatedSATotalAnchorAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRepeatedUTotalAnchorAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRepeatedUTotalAnchorAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRepeatedUBTotalAnchorAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRepeatedUBTotalAnchorAlignmentAut_smul}

Once a source-cover chart has been chosen, the strict triangle itself
induces its middle and target charts.  Conjugating by these induced charts
makes the left and direct arrows identities; four chosen source charts thus
give the exact reference-diagram interface needed by semantic
cancellation:

{docstring AclGeom.FieldEquiv.CompositionTriangle.inducedMiddleChart}

{docstring AclGeom.FieldEquiv.CompositionTriangle.inducedTargetChart}

{docstring AclGeom.FieldEquiv.CompositionTriangle.inducedMiddleChart_left_apply}

{docstring AclGeom.FieldEquiv.CompositionTriangle.inducedTargetChart_direct_apply}

{docstring AclGeom.FieldEquiv.CompositionTriangle.conjugate_induced_left}

{docstring AclGeom.FieldEquiv.CompositionTriangle.conjugate_induced_direct}

{docstring AclGeom.FieldEquiv.FourTriangleReference.ofSourceCharts}

The non-induced replacement keeps the source charts but prescribes the two
common left arrows and the two common direct arrows independently.  Each
middle or target chart first returns through the corresponding source chart
and only then follows its prescribed common arrow.  Thus the four right
arrows are the genuine quotients `left⁻¹ ≫ direct`, rather than identities;
the generic constructor packages all repeated-arrow coherence equations
and exposes the eight resulting arrows exactly:

{docstring AclGeom.FieldEquiv.CompositionTriangle.conjugate_inducedMiddle_trans_left}

{docstring AclGeom.FieldEquiv.CompositionTriangle.conjugate_inducedTarget_trans_direct}

{docstring AclGeom.FieldEquiv.CompositionTriangle.conjugate_induced_trans_right}

{docstring AclGeom.FieldEquiv.FourTriangleReference.ofCommonLeftDirect}

{docstring AclGeom.FieldEquiv.FourTriangleReference.ofCommonLeftDirect_toFourArrowDiagram}

For the actual enlarged four-face cover, choose the two `u` anchor
corrections on the first pair of faces and the two `uB` corrections on the
second pair as the four source charts.  Every one of these charts is an
algebra automorphism over the literal common coefficient/source field.
Consequently its induced middle chart may select another conjugate of the
`s` or `sA` branch, but it fixes all coefficients of that branch's canonical
equation.  On the direct branches the induced target charts recover the
shared whole-total-field anchors pointwise.  This gives an instantiated
four-triangle reference and literal semantic cancellation on the common
cover:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientSourceChart}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientSourceChart}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientSourceChart}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientSourceChart}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.coefficientSourceCharts_commute}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.coefficientFourTriangleReference}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientMiddleChart_selectedLeft}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientMiddleChart_selectedLeft}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientMiddleChart_selectedLeft}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientMiddleChart_selectedLeft}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientTargetChart_selectedDirect}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientTargetChart_selectedDirect}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientTargetChart_selectedDirect}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientTargetChart_selectedDirect}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.coefficientFourArrowDiagram}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.coefficientFourArrow_right_arrows_eq_refl}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.coefficientFourArrow_right_cancellation}

Coefficient faithfulness can be checked directly on the selected right
branches, rather than inferred only from the abstract cancellation identity.
The source and target coordinates are first named inside the source-based
branch field.  They satisfy the canonical equation there, and every
coefficient-linear realization preserves that equation:

{docstring AclGeom.FiniteCorrespondencePair.sourceInBranchOverSource}

{docstring AclGeom.FiniteCorrespondencePair.targetInBranchOverSource}

{docstring AclGeom.FiniteCorrespondencePair.curveEquationOverSourceField}

{docstring AclGeom.FiniteCorrespondencePair.aeval_curveEquation_inBranchOverSource}

{docstring AclGeom.FiniteCorrespondencePair.aeval_curveEquation_map}

The finite composition cover contains the literal selected right branch in
its transported middle field.  Any chart fixing the original coefficient
field carries that branch to another zero of its original equation:

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.rightSourceFiniteNormalCover_le_middleCover}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.selectedRightBranchInMiddle_curveEquation}

For the four Ψ faces, all four selected right branches are present in their
middle covers.  Both the induced middle and target charts fix the literal
common coefficient field, and the charted endpoints of each right branch
satisfy its original canonical curve equation:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedRightBranchInComparisonMiddleCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedRightBranchInComparisonMiddleCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedRightBranchInComparisonMiddleCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedRightBranchInComparisonMiddleCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientMiddleChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientMiddleChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientMiddleChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientMiddleChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientTargetChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientTargetChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientTargetChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientTargetChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCoefficientMiddleChart_selectedRight_curveEquation}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCoefficientMiddleChart_selectedRight_curveEquation}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCoefficientMiddleChart_selectedRight_curveEquation}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCoefficientMiddleChart_selectedRight_curveEquation}

The normalized scalar reference cover and the semantic curve action can now
be compared inside one literal finite normal source.  The original
eight-input field maps exactly to the common curve coefficient field; the
transported reference cover remains finite, is normalized after adjoining
the formal curve source, and is joined with the semantic branch-comparison
cover.  The resulting embedding agrees with the semantic algebra map on all
eight free inputs.  Postcomposing the four explicit `toReference` field maps
therefore gives four maps with exactly the same codomain as the semantic
four-arrow action:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.mappedReferenceInputField_eq_commonCoefficientField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.mappedReferenceNormalOverInput_finiteDimensional}

To retain the selected graph copies before canonicalization, a second,
concrete compositum adjoins the two algebraic `c` parameters and the four
right-branch endpoint pairs directly to the transported reference
compositum.  These ten elements are algebraic over the literal common
source, so the joint field is finite there and admits one concrete normal
closure.  Both the four common-base semantic branches and the four original
relocated complete branches are literal subfields of that same closure; in
particular, the algebraic `c` presentation is included without pretending
that it lies in the original eight-input field:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceTuple}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticBranchExtension_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceJoin}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceJoinOverSource_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceNormalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceNormalField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceNormalField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.mappedReferenceNormalField_le_selectedSemanticReferenceNormalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSemanticRightBranches_le_selectedSemanticReferenceNormalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRelocatedRightBranches_le_selectedSemanticReferenceNormalField}

The concrete normal field is then canonicalized exactly once.  The resulting
algebra equivalence is linear over the full common coefficient/source field,
and every semantic or relocated complete branch is mapped through the same
literal ambient inclusion followed by this one equivalence.  Thus the branch
maps no longer inherit independent canonical choices:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceNormalEquivSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemanticRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemanticRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemanticRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemanticRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRelocatedRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRelocatedRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRelocatedRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRelocatedRightBranchToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceSemanticSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceNormalCoverToReferenceSemanticSourceCover_algebraMap}

Before adjoining the formal source, every complete nine-coordinate edge is
also base-changed from its own six-coordinate ambient field to the common
sixteen-coordinate four-arrow field.  These four finite scalar extensions
remain literal subfields of the selected twenty-eight-coordinate component
and hence of the final reference normal cover.  Their inclusions in the
combined semantic/reference source preserve all nine selected coordinates;
in particular the four `B/T` scalars are now named elements of one common
formal-source normal cover without a new branch choice:

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.overTotal_finiteDimensional}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.field_le_jointField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.jointField_le_referenceNormalCover}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.fourTotalBaseChangedEdges_selectedBScalar}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.totalBaseChangedEdgeToReferenceSemanticSourceCover_selectedCoordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourTotalBaseChangedEdges_selectedBScalar_inReferenceSemanticSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceEInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceAInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceBInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceCInSemanticSourceRingHom}

The reference-normalized scalar transition now retains its based
normal-cover correction.  Besides the strict cocycle, it therefore preserves
the selected scalar branch exactly.  Pulling that scalar back through the
selected chart gives one intrinsic function-field generator; the four
promoted reference maps send it to the four literal coordinate-`7` elements
of the scalar-extended complete edges in the common semantic source:

{docstring AclGeom.QWitness.rankTwoScalarSelectedNormalElement}

{docstring AclGeom.QWitness.rankTwoScalarLocusBasedNormalCoverAlgEquiv_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBScalarFunctionFieldElement}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBNormalEquivProjection_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionToReferenceInSemanticSourceRingHom_apply_selectedBScalar}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourToReferenceInSemanticSourceRingHom_selectedBScalar}

In fact the comparison holds on the whole selected nonnormal `B/T` branch,
not merely on its distinguished scalar.  Every scalar-extended complete edge
contains its three-coordinate right scalar extension literally.  Its direct
inclusion in the reference normal cover equals the route through the complete
edge.  The based normalized transition agrees on every element with the
canonical total-field equivalence to each relocated branch; after promotion
to the common semantic source, the four restricted reference embeddings are
therefore exactly the four literal complete-edge maps:

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.TotalBaseChangedEdge.rightScalarField_le_field}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.seRightScalarExtensionToReferenceNormalCover_eq}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sA_aRightScalarExtensionToReferenceNormalCover_eq}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.s_bRightScalarExtensionToReferenceNormalCover_eq}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sA_cRightScalarExtensionToReferenceNormalCover_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBScalarExtensionToFunctionFieldRingHom_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBNormalEquivProjection_selectedExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionToReferenceInSemanticSourceRingHom_apply_selectedExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourReferenceEmbeddingsOnSelectedBScalarExtension}

The comparison also extends through normalization.  On the whole selected
normal field, the ambient map is the based selected-to-projection normal
equivalence followed by the literal inclusions into the reference cover and
the common semantic source.  Pulling this description back through the
selected chart's generic-point equivalence gives equality of ring
homomorphisms on its entire function field, simultaneously for all four
reference projections:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBNormalProjectionInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionViaSelectedBNormalInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourToReferenceInSemanticSourceRingHom_eq_viaSelectedBNormal}

The complete semantic curve branches are now exposed with that same final
codomain.  At the reusable level, a right equivalence on any supplied
finite normal source cover fixes the coefficient field, and every right
arrow of a charted four-triangle reference has a pointwise formula in terms
of its original complete right-arrow transport and target chart.  For each
of the four faces, the selected complete right branch is embedded in the
middle cover, charted, acted on by the corresponding semantic arrow, and
included literally in the combined semantic/reference source:

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.rightEquiv_algebraMap}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram_rightE_apply}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram_rightA_apply}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram_rightB_apply}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram_rightC_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.branchComparisonSourceCoverToReferenceSemanticSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemanticRightCurveBranchToReferenceSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemanticRightCurveBranchToReferenceSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemanticRightCurveBranchToReferenceSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemanticRightCurveBranchToReferenceSourceRingHom}

This comparison is now coefficient-faithful on the intrinsic selected
`B`-germ field, not only on the eight displayed free inputs.  Equality of
the selected and relocated `B/T` loci induces the canonical equivalence of
their rank-two parameter fields.  The normal-cover transition restricts to
that equivalence, so each explicit reference map sends an intrinsic curve
coefficient to its canonical relocated parameter-field value.  All four
restrictions are named and packaged in one simultaneous formula:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToProjectionParameterAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBNormalEquivProjection_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionToReferenceOnBGermCoefficientRingHom_apply_parameterTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceEOnBGermCoefficientRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceAOnBGermCoefficientRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceBOnBGermCoefficientRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceCOnBGermCoefficientRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceOnBGermCoefficientRingHom_apply_parameterTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourToReferenceInSemanticSourceRingHom_restrict_bGerm}

The coefficient values in that formula are now identified with the actual
canonical equations on the four semantic right branches.  At the reusable
correspondence level, ambient embeddings and equality of complete family
loci transport endpoint ideals and their lexicographically monic generators
coefficientwise:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.parameterMapEquiv}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.curveEquation_map_parameterMapEquiv}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.parameterEquivOfIdealEq}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.curveEquation_map_parameterEquivOfIdealEq}

For the selected `B` family, the full-family parameter equivalence is the
same map as the normalized `B/T` scalar-locus equivalence.  Hence every
monomial coefficient is transported to the coefficient with the same index
in each relocated `e`, `a`, `b`, and `c` equation:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBToRelocatedBParameterEquiv_eq_projection}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBCurveCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.projectionParameterTransport_selectedBCurveCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourProjectionParameterTransports_selectedBCurveCoefficient}

These generator formulas now assemble into maps on the entire intrinsic
coefficient field.  The four codomains remain the four relocated family
parameter fields—this is essential for the output `c` field, which is
algebraic over rather than literally contained in the common eight-input
field.  Agreement on all canonical coefficients is an extensionality
principle for maps out of the intrinsic germ field.  Finally, each promoted
reference restriction factors through its whole relocated parameter-field
map, so the remaining semantic comparison has been reduced to those
canonical generators without discarding any algebraic coefficient value:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientAlgHom_ext}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToRelocatedBParameterAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToRelocatedBParameterAlgHom_selectedBCurveCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedBParameterToReferenceSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourToReferenceOnBGermCoefficientRingHom_eq_viaRelocatedParameter}

The parameter-field factorization has now been sharpened to the intrinsic
coefficient fields of the four relocated canonical curves.  The image of the
ambient coefficient transport is proved to be exactly the field generated by
the relocated equation's coefficients.  It therefore induces an algebra
equivalence, preserves every monomial-indexed coefficient, and recovers the
previous parameter transport after the literal inclusion of the coefficient
field.  The four faces are exposed simultaneously, so the remaining semantic
comparison no longer carries unrelated parameter coordinates:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToRelocatedBCoefficientAlgEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToRelocatedBCoefficientAlgEquiv_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedBCoefficientToCompleteRightBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedBCoefficientToCompleteRightBranchRingHom_val}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToCompleteRightBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBGermCoefficientToCompleteRightBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBGermCoefficientToCompleteRightBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToCompleteRightBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToCompleteRightBranchRingHom_selected}

Composing those literal complete-branch inclusions with the single selected
normal-cover canonicalization gives four intrinsic coefficient embeddings
with one common codomain.  Their generator theorem still records the actual
same-index relocated curve coefficients, so canonicalization has not erased
the parameter-dependent coefficient presentations:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBGermCoefficientToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBGermCoefficientToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToSelectedSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToSelectedSourceRingHom_selected}
