/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.ChunkCurveFiniteCommonChartGermA
import AclGeom.Config.ChunkCurveFiniteCommonChartGermB
import AclGeom.Config.ChunkCurveFiniteCommonChartGermC
import AclGeom.Config.ChunkCurveFiniteCommonChartGermERestriction
import AclGeom.Config.ChunkCurveReferenceBridgeFinal
import AclGeom.Config.ChunkCurveReferenceBridgeSemanticBranches
import AclGeom.Config.ChunkCurveSemilinearCommonSource
import AclGeom.Config.ChunkCurveSemilinearCommonSourceBranch
import AclGeom.Config.ChunkCurveSemilinearGroupedBranch
import AclGeom.Config.ChunkCurveSemilinearTriangle

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Semilinear common fields and branch restrictions" =>

%%%
tag := "configuration-record-semilinear-common-fields"
%%%

The once-canonicalized selected cover and the established coherent semantic
branch-comparison cover are finally placed in one literal finite normal
source.  The two inclusions are not new canonicalization choices: they are
the two legs of a single supremum.  Consequently the eight selected whole
branches, the four intrinsic coefficient maps, and the four charted semantic
right-branch maps now have the same codomain.  The intrinsic generator
formulas survive this last inclusion verbatim; the remaining chart problem
is therefore an equality between explicitly named maps, rather than a
comparison of unrelated algebraic-closure models:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.branchComparisonSourceCoverToSelectedGraphSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticReferenceSourceCoverToSelectedGraphSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemanticRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRelocatedRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToSelectedGraphSourceRingHom_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seChartedSemanticRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaChartedSemanticRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbChartedSemanticRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcChartedSemanticRightBranchToSelectedGraphSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToRelocatedBParameterAlgHom_factor_coefficients}

The established source charts also extend from the coherent semantic
subcover to this unified selected source.  The generic extension operation
uses normality of the larger cover and has an exact restriction formula on
the whole embedded subfield.  Applied to the four faces, it gives four
automorphisms of the same selected graph source and hence four strict
composition triangles there.  This is the source-chart half of the
graph-faithful comparison: it retains all previous repeated-branch
alignments, while leaving the independently selected middle and target
charts—and therefore the nontrivial right-arrow restrictions—to the next
step:

{docstring AclGeom.NormalBranchEmbedding.extendAlong}

{docstring AclGeom.NormalBranchEmbedding.extendAlong_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.branchComparisonSourceCoverToSelectedGraphSourceCoverOverSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedGraphSourceChartAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedGraphSourceChartAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedGraphSourceChartAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedGraphSourceChartAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedGraphSourceChartAut_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedGraphSourceChartAut_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedGraphSourceChartAut_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedGraphSourceChartAut_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedGraphCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedGraphCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedGraphCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedGraphCompositionTriangle}

The complete normalized reference edges now use that same selected graph
source as well.  Their transport first enters the concrete selected normal
field and then passes through its single chosen canonicalization, so it does
not introduce a parallel algebraic-closure model.  Every selected edge
coordinate is preserved.  More importantly, the promoted reference map and
the literal complete-edge route agree on the entire selected nonnormal
`B/T` branch for all four faces.  Restricting those equalities along the
intrinsic germ-field inclusion gives whole-field coefficient restrictions,
including the algebraic output `c` edge:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceNormalCoverToSelectedNormal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceNormalCoverToSelectedGraphSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.totalBaseChangedEdgeToSelectedGraphSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.totalBaseChangedEdgeToSelectedGraphSource_selectedCoordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourTotalBaseChangedEdges_selectedBScalar_inSelectedGraphSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToSelectedBScalarExtensionAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBScalarExtensionToReferenceEInSelectedGraphRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBScalarExtensionToSeEdgeInSelectedGraphRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourReferenceEdgesOnSelectedBScalarExtensionInSelectedGraph}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToReferenceInSelectedGraphRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToReferenceInSelectedGraphRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourReferenceEdgesOnBGermCoefficientInSelectedGraph}

These reference restrictions are not merely parallel copies of the named
selected intrinsic maps.  The relocated coefficient-field factorization and
the base square of the scalar-extension equivalence identify the two routes
on an arbitrary element of the intrinsic germ field.  Hence all four
`e/a/b/c` maps are equal as whole-field homomorphisms in the selected graph
source; the output comparison retains its algebraic `c` parameter field:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToSelectedGraph_eq_reference_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBGermCoefficientToSelectedGraph_eq_reference_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBGermCoefficientToSelectedGraph_eq_reference_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToSelectedGraph_eq_reference_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientToSelectedGraph_eq_reference}

The four semantic right branches themselves now have a stronger common
anchor than their separate maps into the selected graph.  The finite field
generated by all four selected semantic faces contains the entire `e`, `a`,
`b`, and `c` branch fields, not only their named coefficient generators.
That whole-face field is included in the concrete normal model and then
passes through the single canonicalization already used by the selected
graph.  Transitivity of literal branch inclusions proves that every one of
the four existing semantic graph maps is the restriction of this one
whole-face embedding.  Thus future middle and target charts can be aligned
against a shared anchor without making four unrelated deck-transformation
choices:

{docstring AclGeom.FiniteCorrespondencePair.branchOverSourceToIntermediateFieldRingHom_trans}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedSemanticBranchExtensionToSelectedGraphSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemanticRightBranch_le_selectedSemanticBranchExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemanticRightBranch_le_selectedSemanticBranchExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemanticRightBranch_le_selectedSemanticBranchExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemanticRightBranch_le_selectedSemanticBranchExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSemanticRightBranchesToSelectedGraph_factor_extension}

Equality of the four complete family loci now provides the complementary
middle-branch comparison.  A reusable family-cover theorem identifies the
family-field presentation with the actual branch-over-source type and turns
equality of loci into a ring equivalence of the complete branches.  Its
restriction to the displayed parameter field is exactly the canonical
parameter transport.  Applied simultaneously to the mapped selected `B`
family and the relocated `e`, `a`, `b`, and `c` families, this gives one
common selected complete branch and four equivalences out of it.  The single
intrinsic germ embedding in that branch factors through those equivalences to
the four previously named complete-branch embeddings.  Thus the common
middle map is already coefficient-faithful before extending the four
equivalences to normal middle and target covers:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.completeBranchRingEquivOfIdealEq}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.completeBranchRingEquivOfIdealEq_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedBParameterToMappedCompleteBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.bGermCoefficientToMappedCompleteBranchRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedBCompleteBranchRingEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSelectedBCompleteBranchRingEquiv_parameter}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourBGermCoefficientCompleteBranch_factor_selectedB}

The same comparison now persists after normalizing the four family
extensions.  The family-cover API retains the selected-branch-corrected
normal-field equivalence itself, rather than forgetting immediately to the
deck-action groupoid, and proves its restriction on the entire actual
complete branch.  Consequently one mapped selected-`B` normal cover maps to
each relocated normal cover, and all four maps extend the full branch
equivalences above.  These are still four separately based normal covers;
their scalar extension and joint transport into the semantic triangle
middle/target covers is the remaining chart step:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.completeBranchToNormalCoverRingHom}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.basedNormalEquivOfIdealEq}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.basedNormalEquivOfIdealEq_completeBranch}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedBNormalCoverRingEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSelectedBNormalCoverRingEquiv_completeBranch}

The four separate bases have now been enlarged honestly to the single
selected semantic/reference joint field.  Each native relocated normal
cover is passed through the branch-preserving finite-basis scalar rebase,
and the four resulting canonical covers are joined into one finite normal
right cover.  Thus one mapped selected-`B` complete branch has four named
images in a literal common codomain.  The corresponding native-normal maps
factor through exactly the based equivalences above before entering the
same common cover; in particular the algebraic output face is treated by
the same construction as the three input faces, rather than by an implicit
containment in the original eight-input field:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedRightRebasedCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedRightNormalToRebasedCoverRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRelocatedRightRebasedCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.relocatedRightNormalToFourRebasedCoverRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedBCompleteBranchToFourRebasedCoverRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedBNormalToFourRebasedCoverRingHom}

The base mismatch has also been removed.  Finiteness of the selected joint
field over the literal semantic source makes the algebraic closure of the
joint field an algebraic closure of the smaller source as well.  A chosen
source-linear equivalence transports the common right field into the
algebraic closure of that smaller source; its finite degree is proved by
the joint-field tower, and taking its normal closure gives a genuine finite
normal source cover.  Joining this with the established graph source yields
one cover containing both all repeated-coordinate coherence and all four
right-family normal covers.  The four existing source charts extend across
this join, while the complete-branch and whole-normal-cover maps now land
in the same enlarged graph source:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedJointAlgebraicClosureRingEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRelocatedRightTransportedField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRelocatedRightSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceChartAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedBCompleteBranchToSelectedGraphRightRingHom}

The enlarged cover alone cannot supply the final four charts: its deck
transformations are linear over the semantic source, whereas the four
normalized right embeddings already differ on coefficients in that source.
The missing base changes are now constructed before passing to covers.  The
fourth label first receives an independent `(s,sA,a,c)` presentation.  Four
nine-coordinate rational source tuples are then ordered so that one common
position contains, respectively, `e`, `a`, `b`, and `c`, and the final
coordinate is always the formal curve source.  Their zero locus ideals are
all bottom, so canonical function-field equivalences carry every displayed
coordinate to the coordinate in the same position.  Finally the
`e`-presentation is identified literally with the existing semantic common
source.  Thus the three new charts genuinely move coefficient presentations
and can be lifted to the common normal covers in the next step:

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.s_sA_a_c_independent}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightESourceTuple}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceTuple}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightParameterIndex}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceTuple_rightParameterIndex}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightESourceTuple_independent}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceTuple_independent}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightEToASourceEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightEToCSourceEquiv_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightESourceField_eq_commonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceToRightCSourceEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceToRightCSourceEquiv_apply}

For the two reordered presentations that use only the original independent
inputs, the base change can already be closed back into the literal semantic
source.  The `a`- and `b`-ordered tuples generate exactly the same
intermediate field as the `e` tuple.  Their coordinatewise equivalences
therefore become honest ground-field automorphisms of that source, still
carrying every one of the nine displayed coordinates to its same-position
counterpart.  Lifting these automorphisms to algebraic closures and mapping
the selected graph/right source cover gives two finite normal source covers
with exact coordinate restriction formulas.  This is genuinely semilinear
over the semantic source presentation; the algebraic `c` presentation
remains a separate base-changing cover rather than being collapsed to a
deck transformation:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightASourceField_eq_commonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightBSemanticSourceCoordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceRightAAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceRightBAut_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightACommonSourceClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightASelectedGraphRightSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightARingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightBRingEquiv_algebraMap}

The algebraic-output face is lifted without pretending that its displayed
source is the original semantic field.  The four interalgebraicity faces
first give an explicit equality between the relative algebraic closures of
the original `(s,e,a,b)` inputs and the `(s,sA,a,c)` presentation.  This
equality persists after embedding and adjoining the common formal curve
source.  The exact `e→c` equivalence therefore lifts to algebraic closures
and restricts to an exact equivalence of finite selected graph covers.

For compatibility, the two literal embedded source fields are retained in
their compositum rather than identified.  The closure equality proves that
this joint source is finite over both the original semantic source and the
genuine `c` source.  It is consequently a valid common base for the later
normal middle/target charts while preserving both semilinear source legs:

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.racl_s_e_a_b_eq_s_sA_a_c}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightESource_racl_eq_rightCSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSelectedGraphRightSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightCRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSourceJointField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSourceJointOverSemantic_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSourceJointOverC_finiteDimensional}

A finite normal cover can now be rebased along an actual embedded base
extension without replacing that embedding by an equivalence of base fields.
The construction transports one finite basis into the new algebraic closure,
adjoins it to the larger base, takes the normal closure, and retains the
selected map from the entire old cover.  On the old base this map is exactly
the displayed inclusion:

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.rebaseCover}

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.rebaseRingHom_algebraMap}

For the four-arrow source, chosen equivalences of algebraic closures extend
both literal inclusions into the joint field.  Rebasing the original, `a`,
`b`, and genuine `c` selected graph covers along these two inclusions and
taking their supremum gives one finite normal codomain.  The four selected
maps into this codomain retain all nine same-position coordinate formulas;
in particular, the fourth map lands on the literal `c` coordinate through the
distinct `Sc → S ⊔ Sc` leg rather than an equality cast or deck action:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.semanticSourceToRightSourceJointClosureRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceToRightSourceJointClosureRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSelectedGraphJointCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightEJointRingHom_coordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightAJointRingHom_coordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightBJointRingHom_coordinate}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightCJointRingHom_coordinate}

The coordinate formulas in fact extend to the whole semantic source field.
After twisting the joint-source algebra structure by the `a`, `b`, and
genuine `c` source charts, finiteness is preserved.  The resulting algebraic
towers extend all four selected embeddings to equivalences of algebraic
closures, with their restriction squares retained as data.  These are the
comparison maps from which a finite stable common chart will be extracted;
they are not themselves substituted for the required finite chart:

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv}

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.ofAlgebraic}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightEJointRingHom_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightAJointRingHom_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightBJointRingHom_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightCJointRingHom_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightEJointClosureRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightAJointClosureRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightBJointClosureRingEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightCJointClosureRingEquiv_algebraMap}

Before taking that finite stable closure, the coefficient action already
restricts to the entire intrinsic selected-`B` germ field.  The relocated
`e`, `a`, and `b` parameter fields lie literally in the semantic source, and
the relocated `c` parameter field lies in the genuine independent output
source.  The two common-source automorphisms and the `e→c` source equivalence
carry the whole intrinsic `e` embedding exactly to the corresponding `a`,
`b`, and `c` embeddings.  These identities provide the coefficient-faithful
source boundary for the finite four-arrow descent:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientField_le_semanticCommonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRelocatedParameterField_le_semanticCommonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRelocatedParameterField_le_semanticCommonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRelocatedParameterField_le_semanticCommonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRelocatedParameterField_le_rightCSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToSemanticSourceAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBGermCoefficientToSemanticSourceAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBGermCoefficientToSemanticSourceAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToRightCSourceAlgHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceRightAAut_comp_seBGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceRightBAut_comp_seBGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceToRightCSourceEquiv_comp_seBGermCoefficient}

The closure comparisons now descend to honest finite charts.  For any
chosen target intermediate field, its inverse image under an embedding-
preserving closure equivalence is a field equivalent to that target; a
finite embedded base change makes the pullback finite as well.  Applying
this to the joint cover itself produces four finite source fields and four
field equivalences onto one literal finite target.  Each equivalence agrees
with the selected `e`, `a`, `b`, or genuine `c` embedding on the entire old
graph/right source, and its restriction to the whole intrinsic germ is the
corresponding normalized target map.  This is finite comparison data rather
than the earlier identity-valued source gauge:

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.pullbackField}

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.pullbackEquiv}

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.pullbackField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightEFiniteCommonChartSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightEFiniteCommonChartSourceField_finiteDimensional}

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.pullbackBaseEquiv_pullbackBaseRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightEFiniteCommonChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightAFiniteCommonChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightBFiniteCommonChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCFiniteCommonChart_comp_bGermCoefficient}

Those four finite source fields now carry the actual strict semantic
composition triangles.  A literal triangle of field equivalences extends
across any intermediate source field by lifting its left and right arrows
to algebraic closures and defining the enlarged direct arrow as their
composite.  This avoids an invalid normality descent: no independently
chosen deck correction has to stabilize the enlarged field.  Applying the
construction to the four finite pullbacks gives strict `s·e=u`, `sA·a=u`,
`s·b=uB`, and `sA·c=uB` triangles whose source charts still restrict to the
four selected whole-source embeddings into the joint cover:

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtension}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionLeftEquiv_algebraMap}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionRightEquiv_algebraMap}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionDirectEquiv_algebraMap}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionMiddleRingHom}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionTargetRingHom}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionRightEquiv_comp_middleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seFiniteCommonCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seFiniteCommonSourceChart_on_oldSource}

The selected complete right branches also survive this enlargement as
whole-field maps, rather than only as displayed coefficients.  Each old
middle field embeds literally in its extended middle field, each old target
does the same, and the extended semantic right arrow forms an exact square
with those embeddings.  The four configurations instantiate that square on
their selected complete `e/a/b/c` branches.  These are the concrete branch
anchors that the remaining independent common middle and target charts must
identify:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedRightBranchToFiniteCommonMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seFiniteCommon_right_comp_selectedRightBranch}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaFiniteCommon_right_comp_selectedRightBranch}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbFiniteCommon_right_comp_selectedRightBranch}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcFiniteCommon_right_comp_selectedRightBranch}

The finite comparisons also have to be oriented correctly.  Their forward
direction sends the selected `e` presentation to `a`, `b`, or the genuine
`c` presentation; using those forward maps as final source charts would ask
one injective repeated-left arrow to identify distinct coefficient
embeddings.  Instead the three nontrivial semantic triangles are first
re-presented on their transported source covers and charted back by the
inverse semilinear equivalences.  On the entire intrinsic germ, all four
source charts then give one literal embedding in the selected graph/right
source, including across the different base field of the `c` face:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRightSemilinearCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRightSemilinearCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRightSemilinearCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.selectedGraphRightSourceToRightA_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightASourceChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightCSourceChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRightSemilinearSourceCharts_comp_bGermCoefficient}

The inverse-oriented triangles can now be enlarged without losing that
whole-germ equality.  A prescribed finite common source is pulled back
through each source chart, each strict triangle is extended across the
pullback, and the restricted charts all land in the same literal finite
field.  Thus this is no longer only an equality between four differently
typed source presentations: the four enlarged triangles have compatible
finite source charts, and the intrinsic germ has one shared embedding there.
The remaining comparison is now confined to their middle and target fields.

{docstring AclGeom.FieldEquiv.CompositionTriangle.commonSourcePullbackField}

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionAlongChart}

{docstring AclGeom.FieldEquiv.CompositionTriangle.commonSourcePullbackChart_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSemilinearCommonSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRightSemilinearCommonCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRightSemilinearCommonCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRightSemilinearCommonCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourRightSemilinearCommonSourceCharts_comp_bGermCoefficient}

The complete selected right branches survive these inverse-oriented
extensions as well.  Each old middle and target field embeds in the newly
extended triangle, and the new right arrow forms an exact square on the
whole selected branch.  These four squares are the preservation constraints
for the independent common middle and target charts: the final charts must
identify these named embeddings, not merely agree on displayed generators.

{docstring AclGeom.FieldEquiv.CompositionTriangle.sourceExtensionRightEquiv_comp_middleRingHom_comp}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedRightBranchToSemilinearCommonMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedRightBranchToSemilinearCommonMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedRightBranchToSemilinearCommonMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedRightBranchToSemilinearCommonMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourSemilinearCommon_right_comp_selectedRightBranch}

The based `e` face now supplies the first complete intrinsic-field
restriction package.  Its germ is written in the common coefficient field,
then carried through the finite source, preserved middle branch, and target.
The left, right, and strict direct arrows form exact squares on the whole
intrinsic field; the generic composition lemma obtains the direct square
from the adjacent two without unfolding the nested finite covers.

{docstring AclGeom.FieldEquiv.CompositionTriangle.direct_comp_of_left_right}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToCommonCoefficientRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemilinearCommon_left_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemilinearCommon_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSemilinearCommon_direct_comp_bGermCoefficient}

The other three faces now carry the same whole-field package through their
inverse-oriented source charts.  Their intrinsic germs all return to the
based `e` embedding before entering separately typed middle covers, where
the common coefficient field supplies a canonical anchor.  Extending those
anchors gives exact left, right, and direct squares for all four faces.  The
middle anchors are deliberately not identified with the preserved selected
branches yet: that equality is precisely the remaining common-middle chart
obligation.

{docstring AclGeom.finiteCoverTriangle_left_comp_algebraMap_comp}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemilinearCommon_left_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemilinearCommon_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSemilinearCommon_direct_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemilinearCommon_left_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemilinearCommon_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSemilinearCommon_direct_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemilinearCommon_left_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemilinearCommon_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSemilinearCommon_direct_comp_bGermCoefficient}

The common-coefficient anchors are compatible with the other half of the
construction: every one factors through its already preserved complete
right branch, both before and after source extension.  The elementwise
extended statements express equality on the entire intrinsic germ while
avoiding pathological normalization of the deeply nested cover types.
Thus a future common chart must retain one concrete embedding, rather than
choose between a coefficient anchor and a selected-branch anchor.

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedRightBranchMiddle_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedRightBranchToSemilinearCommonMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedRightBranchToSemilinearCommonTarget_bGermCoefficient_apply}

The finite common source is next enlarged just enough to support all four
nontrivial selected source charts.  Its normal closure over the semantic
source remains finite, contains both the old graph/right source and the
literal common finite source, and is normal over exactly the field fixed by
the four charts.  Consequently each selected graph/right automorphism
extends to this one stable source while retaining its prescribed action on
the entire old cover.  This removes the stability obstruction without
replacing the semantic charts by identity gauges.

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSemilinearStableSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSemilinearCommonSourceField_le_stableSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSemilinearStableSourceField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.rightSemilinearStableSourceField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.semilinearStableSourceCharts_apply}

All four inverse-oriented semantic triangles now live over this stable
source.  The `e` face extends directly, while the `a`, `b`, and genuine `c`
faces are pulled back through their inverse semilinear source charts before
extension.  Their restricted pullback charts are then postcomposed with the
four stable selected-graph automorphisms.  The resulting source charts share
one literal codomain but retain their generally nontrivial graph actions.
On the whole intrinsic germ, each chart has an exact restriction to its
named selected graph/right automorphism.

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRightSemilinearStableCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRightSemilinearStableCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRightSemilinearStableCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRightSemilinearStableCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seRightSemilinearStableSourceChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaRightSemilinearStableSourceChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbRightSemilinearStableSourceChart_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcRightSemilinearStableSourceChart_comp_bGermCoefficient}

The final restriction cannot use a single source embedding for all four
faces: the repeated left arrows require one source for `e/b` and another
for `a/c`.  Algebraic-closure comparisons can now be precomposed by a
source equivalence while retaining their exact embedding restriction.  The
four selected joint-cover maps are reoriented with this operation and
pulled back to finite source fields.  Their charts land in one literal
joint cover, but restrict to exactly two intrinsic embeddings, grouped by
the repeated left labels.  The four strict semantic triangles extend to
these finite sources, and finiteness is transported through each source
equivalence.

{docstring AclGeom.AlgebraicClosureTransport.EmbeddingClosureEquiv.precompRingEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seGroupedSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaGroupedSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbGroupedSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcGroupedSourceField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seGroupedCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaGroupedCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbGroupedCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcGroupedCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.groupedSourceS}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.groupedSourceSA}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.groupedSourceCharts_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seGroupedSourceField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaGroupedSourceField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbGroupedSourceField_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcGroupedSourceField_finiteDimensional}

The grouped extensions also retain the previously selected middle and
target anchors.  On every face, the left arrow carries the intrinsic source
germ to its selected-branch middle embedding, the right arrow carries that
embedding to the selected target, and the strict direct arrow reaches the
same target.  Thus the next common-chart layer must preserve concrete
whole-germ squares; it cannot silently replace them by induced identities.

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBGermCoefficientToGroupedMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBGermCoefficientToGroupedMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBGermCoefficientToGroupedMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBGermCoefficientToGroupedMiddleRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seGrouped_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaGrouped_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbGrouped_right_comp_bGermCoefficient}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcGrouped_right_comp_bGermCoefficient}

The preservation statement holds on each complete selected branch, not only
on its intrinsic germ.  The branch embeddings into grouped middle and
target fields form exact squares with all four right arrows.  Their
pointwise restrictions recover the named intrinsic anchors above, including
the genuine algebraic-output `c` branch.  A common middle/target chart must
therefore retain a fully specified normalized embedding on every face.

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.fourGrouped_right_comp_selectedRightBranch}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedRightBranchToGroupedMiddle_bGermCoefficient_apply}

The exact cross-edge coherence interface is separated from the construction
of the reference charts.  Four independently typed triangles give a
semantic four-arrow diagram precisely when their twelve cover fields are
identified with three reference fields and the repeated `s`, `sA`, `u`,
and `uB` arrows agree after conjugation:

{docstring AclGeom.FieldEquiv.CompositionTriangle}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram}

{docstring AclGeom.QWitness.PsiCurveFourArrowRealizations.ReferenceAlignment}

{docstring AclGeom.QWitness.PsiCurveFourArrowRealizations.ReferenceAlignment.right_cancellation}
