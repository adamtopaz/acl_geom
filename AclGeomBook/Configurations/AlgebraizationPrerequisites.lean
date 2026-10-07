/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.ChunkFourArrowReference
import AclGeom.Config.ChunkGermChart
import AclGeom.Correspondence.AffineAction
import AclGeom.Correspondence.AlgebraicGroup

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Algebraization prerequisites and the remaining group boundary" =>

%%%
tag := "configuration-record-algebraization-prerequisites"
%%%

The scheme-theoretic target of the next step is now fixed precisely.  An
algebraic group is a separated finite-type group object over the base-field
spectrum; a connected algebraic group is geometrically integral, rather
than merely an abstract group whose carrier happens to be a parameter type:

{docstring AclGeom.AlgebraicGroup}

{docstring AclGeom.ConnectedAlgebraicGroup}

For a group scheme over a field, separatedness no longer has to be supplied
as an independent gluing argument.  The difference morphism has the diagonal
as its fiber over the unit; the unit section is closed, so the diagonal is
closed.  Thus a locally finite-type, quasi-compact group scheme packages
directly as an algebraic group:

{docstring AclGeom.GroupScheme.difference}

{docstring AclGeom.GroupScheme.diagonal_isPullback_unit}

{docstring AclGeom.GroupScheme.isSeparated}

{docstring AclGeom.AlgebraicGroup.ofGroupScheme}

Kernels are formed in the category of group schemes.  Forgetting the
kernel square to schemes identifies it with the pullback along the unit
section.  Consequently the kernel is a closed finite-type separated
subgroup scheme and its inclusion is normal in the internal-group sense:

{docstring AclGeom.AlgebraicGroup.Hom.kernelAlgebraicGroup}

{docstring AclGeom.AlgebraicGroup.Hom.kernelInclusion_normal}

The first Weil-gluing layer now works with actual scheme charts and open
transition overlaps.  Compatible chart morphisms descend to the quotient
scheme:

{docstring AclGeom.WeilGluing.desc}

Local finite type descends chartwise, a finite quasi-compact atlas gives a
quasi-compact structure morphism, and integral charts with nonempty
pairwise overlaps glue to an integral scheme:

{docstring AclGeom.WeilGluing.commonOverlapGlueData}

If the common overlap maps compatibly to a base, the chart structure maps
descend.  Local finite type and quasi-compactness follow from the finite
atlas:

{docstring AclGeom.WeilGluing.commonOverlapToBase}

{docstring AclGeom.WeilGluing.toBase_locallyOfFiniteType}

{docstring AclGeom.WeilGluing.toBase_quasiCompact}

{docstring AclGeom.WeilGluing.isIntegral}

Finite normal function fields are converted into concrete affine charts by
adjoining the displayed parameter coordinates together with a basis of the
finite extension.  The resulting coordinate ring is a finitely generated
domain, its spectrum is integral, separated, quasi-compact, and locally of
finite type over the ground field, and its fraction field recovers the
chosen extension:

{docstring AclGeom.FiniteExtensionChart.liftedCoordinates}

{docstring AclGeom.FiniteExtensionChart.adjoin_liftedCoordinates_eq_top}

{docstring AclGeom.FiniteExtensionChart.scheme}

{docstring AclGeom.FiniteExtensionChart.generatedFieldEquiv}

{docstring AclGeom.FiniteExtensionChart.isFractionRing_extension}

Mutually inverse dominant partial maps can now be shrunk to concrete dense
open isomorphisms.  In particular, mutually inverse rational maps between
integral separated charts produce exactly the transition datum required by
scheme gluing.  Any such partial isomorphism is also packaged directly as
an actual two-chart `Scheme.GlueData`:

{docstring AclGeom.BirationalGluing.partialIsoOfMutualInversePartialMaps}

{docstring AclGeom.BirationalGluing.partialIsoOfMutualInverseRationalMaps}

{docstring AclGeom.BirationalGluing.partialIsoGlueData}

A finite family of partial isomorphisms out of one reference chart can be
shrunk simultaneously.  The finite intersection of their dense source opens
is dense, and using that one source as every overlap produces a full atlas
whose transition maps and triple cocycles are strict identities:

{docstring AclGeom.BirationalGluing.dense_iInf_opens}

{docstring AclGeom.BirationalGluing.partialIsoFamilyGlueData}

When the reference-to-chart partial isomorphisms are over a fixed base, the
same construction descends the chart structure maps and retains the local
finite-type and quasi-compact properties:

{docstring AclGeom.BirationalGluing.partialIsoFamilyToBase}

The denominator-clearing layer chooses one nonzero product denominator for a
finite family of fraction-field elements.  Hence an injective map from a
finitely generated coordinate algebra to a fraction field factors through a
single localization, producing a dominant partial map on an explicit dense
principal open:

{docstring AclGeom.PrincipalLocalization.CommonDenominator.common}

{docstring AclGeom.PrincipalLocalization.partialMapOfGenerators}

At the generic point, the resulting map out of the localization is exactly
the canonical localization map into the source function field:

{docstring AclGeom.PrincipalLocalization.genericAwayMap_eq_mapToFractionRing}

For finite-extension charts this construction applies directly to a field
equivalence, contravariantly embedding the target coordinate ring in the
source fraction field:

{docstring AclGeom.FiniteExtensionTransition.transitionAlgHom}

{docstring AclGeom.FiniteExtensionTransition.partialMap}

Conjugating the ambient field equivalence through the two scheme function
fields gives a canonical dominant rational map.  The denominator-cleared
principal-open map represents precisely that rational map, and the map for
the inverse field equivalence supplies an actual dense-open isomorphism:

{docstring AclGeom.FiniteExtensionTransition.rationalMap}

{docstring AclGeom.FiniteExtensionTransition.partialMap_toRationalMap}

{docstring AclGeom.FiniteExtensionTransition.partialIso}

Both the rational transition and the extracted dense-open isomorphism are
proved to commute with the chart structure maps to the ground-field
spectrum:

{docstring AclGeom.FiniteExtensionTransition.rationalMap_comp_structureMap}

{docstring AclGeom.FiniteExtensionTransition.partialIso_isOver}

Successive ambient field equivalences compose strictly after conjugation
through the chart function fields, so their canonical rational transitions
satisfy the same composition law:

{docstring AclGeom.FiniteExtensionTransition.functionFieldAlgEquiv_trans}

{docstring AclGeom.FiniteExtensionTransition.rationalMap_comp}

For Ψ, the abstract normal-cover equivalence is promoted to a ground-field
equivalence and then localized in this way.  In particular, every repeated
rank-two block of a lifted four-arrow diagram has a concrete dominant
principal-open transition between its two scalar-branch charts:

{docstring AclGeom.QWitness.rankTwoScalarNormalCoverAlgEquiv}

{docstring AclGeom.QWitness.rankTwoScalarTransitionPartialMap}

{docstring AclGeom.QWitness.rankTwoScalarTransitionPartialIso}

The same construction now compares genuinely different generic parameter
tuples on one full rank-two/scalar graph locus.  Equality of the graph loci
first identifies the two rank-two base fields; the scalar extensions and
their normal closures then transport semilinearly over that base change.
After normalization through a selected realization, the resulting rational
maps satisfy a strict transitive cocycle:

{docstring AclGeom.QWitness.rankTwoParameter_ideal_eq_of_scalar_ideal_eq}

{docstring AclGeom.QWitness.rankTwoScalarNormalCoverEquivOfIdealEq}

{docstring AclGeom.QWitness.rankTwoScalarLocusReferenceRationalMap_comp}

For the actual Ψ cancellation chart this means every generic realization of
the `B/T` projection graph is represented by the same affine normal-cover
model, with dominant rational comparisons and dense-open isomorphisms over
the ground-field spectrum:

{docstring AclGeom.QWitness.psiBProjectionAlgebraicChart}

{docstring AclGeom.QWitness.psiBProjectionReferenceRationalMap_comp}

{docstring AclGeom.QWitness.psiBProjectionReferencePartialIso_isOver}

Normal-closure lifts chosen independently need not compose literally.
Choosing one reference branch removes this ambiguity: every transition is
defined by going back to the reference and out again.  The resulting field
equivalences and rational chart maps obey strict cocycle laws, and each
pairwise dense overlap is an honest scheme gluing datum:

{docstring AclGeom.QWitness.rankTwoScalarReferenceTransitionAlgEquiv_trans}

{docstring AclGeom.QWitness.rankTwoScalarReferenceTransitionRationalMap_comp}

{docstring AclGeom.QWitness.rankTwoScalarReferenceTransitionGlueData}

{docstring AclGeom.QWitness.rankTwoScalarReferenceTransitionPartialIso_isOver}

For an arbitrary finite family of branches on the same scalar projection
locus, the reference-normalized transitions now assemble all charts at once;
the corresponding glued scheme is an actual `Scheme`:

{docstring AclGeom.QWitness.rankTwoScalarReferenceAtlasGlueData}

{docstring AclGeom.QWitness.rankTwoScalarReferenceAtlas}

{docstring AclGeom.QWitness.rankTwoScalarReferenceAtlasToSpec}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sAlgebraicTransitionPartialMap}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.uBAlgebraicTransitionPartialMap}

All four repeated blocks of the lifted Ψ diagram now expose these normalized
two-chart gluing data explicitly:

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sAlgebraicTransitionGlueData}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.uAlgebraicTransitionGlueData}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sAAlgebraicTransitionGlueData}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.uBAlgebraicTransitionGlueData}

Applying this construction to every normalized rank-two/scalar branch gives
the concrete `A/S`, `B/T`, and `C/U` affine charts.  Their function fields
are exactly the corresponding finite normal covers, while the two base
coordinates remain algebraically independent on each selected Ψ chart:

{docstring AclGeom.QWitness.rankTwoScalarAlgebraicChart}

{docstring AclGeom.QWitness.rankTwoScalarAlgebraicChartFunctionFieldEquiv}

{docstring AclGeom.QWitness.psiAAlgebraicChart}

{docstring AclGeom.QWitness.psiAParameterCoordinates_independent}

The normalized finite-cover action has therefore supplied explicit
principal-open representatives, genuine dense-open transition isomorphisms,
a strict reference-normalized rational cocycle, pairwise `Scheme.GlueData`,
and a full finite reference-normalized atlas with literal triple cocycles.
Its chart maps descend to a structure morphism over `Spec k`; the resulting
scheme is integral, locally of finite type, and quasi-compact.  This is the
finite branch-normalization layer, not yet the translation-indexed Weil group
atlas.  The next boundary is to realize the relational multiplication and
inverse as rational maps on a common positive-dimensional normalized
parameter cover, then glue the charts indexed by its birational translations.
Once those operations form a group scheme, separatedness follows from the
group diagonal theorem above.  After that the categorical rank-one kernel
must be identified with the connected component of the scheme-theoretic
kernel.  None of these conclusions is inferred merely from the presented
quotient or from finiteness of the earlier deck action.

Before the multiplication graph can be normalized, a correspondence germ
needs coordinates unaffected by rescaling its defining equation.  Its prime
planar ideal now has a canonical lexicographically monic generator.  Equal
branch ideals give literally equal generators, so adjoining their
coefficients produces an intrinsic field contained in every field of
definition.  The equation descends to that field, remains nonzero, and still
vanishes at the selected generic endpoint pair:

{docstring AclGeom.FiniteCorrespondencePair.curveEquation}

{docstring AclGeom.FiniteCorrespondencePair.curveEquation_eq_of_ideal_eq}

{docstring AclGeom.FiniteCorrespondencePair.curveCoefficientField}

{docstring AclGeom.FiniteCorrespondencePair.curveCoefficientField_le}

{docstring AclGeom.FiniteCorrespondencePair.aeval_curveEquationOverCoefficientField}

Partial evaluation of the descended equation now makes the selected target
algebraic over the intrinsic coefficient field and source.  The Ψ atom
clauses then force these coefficients to have the full minimal parameter
rank: a closed subfield of a rank-two flat not contained in any point is the
entire flat.  Applied in the inverse orientation for `A` and the forward
orientation for `B` and `C`, the coefficient closures recover all three
rank-two parameter flats exactly:

{docstring AclGeom.FiniteCorrespondencePair.target_mem_racl_curveCoefficientField_source}

{docstring AclGeom.RankEq.eq_of_le_of_not_le_point}

{docstring AclGeom.QWitness.aInverseGermCoefficientClosure_eq_A}

{docstring AclGeom.QWitness.bGermCoefficientClosure_eq_B}

{docstring AclGeom.QWitness.cGermCoefficientClosure_eq_C}

Equality of these closures has a concrete finite-cover consequence.  Each
displayed two-coordinate parameter field is finite over the corresponding
intrinsic germ coefficient field.  For multiplication, the inverse-`A` and
forward-`B` coefficient fields form an intrinsic independent-input
compositum whose closure is exactly `A ⊔ B`; all six displayed `A,B,C`
coordinates are finite over it.  Their common normal closure is therefore a
single finite normal field on which the selected multiplication component
can be made single-valued:

{docstring AclGeom.finiteDimensional_extendScalars_adjoin_of_close_eq}

{docstring AclGeom.QWitness.aParameterOverInverseGerm_finiteDimensional}

{docstring AclGeom.QWitness.bParameterOverGerm_finiteDimensional}

{docstring AclGeom.QWitness.cParameterOverGerm_finiteDimensional}

{docstring AclGeom.QWitness.abGermCoefficientClosure_eq_A_sup_B}

{docstring AclGeom.QWitness.abcOverAbGerm_finiteDimensional}

{docstring AclGeom.QWitness.germMultiplicationNormalCover}

{docstring AclGeom.QWitness.germMultiplicationNormalCover_finiteDimensional}

{docstring AclGeom.QWitness.germMultiplicationNormalCover_normal}

These fields now have finite algebraic models rather than remaining abstract
intermediate fields.  The support of a canonical equation is finite, so its
coefficient set is finite and its tautological lifts generate the intrinsic
field.  A general function-field embedding between finite-extension charts
spreads to a dominant rational projection after clearing finitely many
denominators.  The common normal multiplication field therefore gives an
integral affine graph chart with dominant rational projections to the
selected inverse-`A`, input-`B`, and output-`C` germ charts:

{docstring AclGeom.FiniteCorrespondencePair.curveCoefficientSet_finite}

{docstring AclGeom.FiniteCorrespondencePair.adjoin_curveCoefficientCoordinates_eq_top}

{docstring AclGeom.FiniteExtensionProjection.rationalMap}

{docstring AclGeom.FiniteExtensionProjection.functionFieldAlgHom_commutes}

{docstring AclGeom.QWitness.adjoin_abGermCoordinates_eq_top}

{docstring AclGeom.QWitness.germMultiplicationAlgebraicChart}

{docstring AclGeom.QWitness.germMultiplicationToA}

{docstring AclGeom.QWitness.germMultiplicationToAFunctionFieldRingHom}

{docstring AclGeom.QWitness.germMultiplicationToA_fromFunctionField}

{docstring AclGeom.QWitness.germMultiplicationToB}

{docstring AclGeom.QWitness.germMultiplicationToBFunctionFieldRingHom}

{docstring AclGeom.QWitness.germMultiplicationToB_fromFunctionField}

{docstring AclGeom.QWitness.germMultiplicationToC}

{docstring AclGeom.QWitness.germMultiplicationToCFunctionFieldRingHom}

{docstring AclGeom.QWitness.germMultiplicationToC_fromFunctionField}

The complete four-arrow difference component is now normalized over its
actual eight free coordinates.  Successive multiplication and division
edges make each selected block algebraic over `(s,e,a,b)`, so all sixteen
displayed coordinates form a finite extension.  One normal closure gives an
integral affine graph chart, and the four based input/output blocks have
dominant rational projections from it.  This remains a relational
difference-product component: forgetting the auxiliary `s` block requires
the subsequent reference-chart factorization argument.

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.totalTuple_mem_input_racl}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.totalOverInput_finiteDimensional}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.normalCover}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.normalCover_normal}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.algebraicChart}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.toE}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.toA}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.toB}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.toC}

The selected complete component also spreads over the whole generic input
locus.  Relocation fixes all eight independent input coordinates literally
while preserving the sixteen-coordinate prime ideal; restricting that ideal
back to each of the four edges recovers the original multiplication locus.
The resulting input-field and total-field equivalences commute, lift to the
normal covers, and give dense-open chart comparisons.  Passing through one
reference realization makes the normal-cover and rational-map comparisons a
strict transitive cocycle.

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.exists_relocation}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.extensionEquiv}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.normalCoverAlgEquiv}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.transitionPartialIso}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.referenceNormalCoverAlgEquiv_trans}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.referenceTransitionRationalMap_comp}

The scalar lifts on the four edges are now normalized together with the
ambient component.  The resulting tuple retains all sixteen ambient
coordinates and all twelve independently selected scalar branches.  Its
four nine-coordinate restrictions are literally the original complete
joint projection relations, while every coordinate is algebraic over the
same eight ambient inputs.  One finite normal cover therefore carries the
whole lifted diagram and has dominant rational projections to the four raw
`B/T` scalar branch charts.  Calling these targets raw is important: their
individual normal closures still have to be adjoined before the existing
reference-model transitions can be applied.

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.jointTuple}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.se_relation}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sAa_relation}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sb_relation}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sAc_relation}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.jointTuple_mem_input_racl}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.jointOverInput_finiteDimensional}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.normalCover}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.normalCover_normal}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.algebraicChart}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toRawE}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toRawA}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toRawB}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toRawC}

Each of those raw scalar fields has its own finite normal closure over its
rank-two parameter block.  A finite-basis compositum construction now
adjoins such a smaller normal field to any larger ambient function field
without introducing an infinite extension.  Iterating it for the four
`B/T` branches gives one field, still finite over the original eight inputs,
that literally contains all four normal fields.  A final common normal
closure therefore projects directly to every normalized branch chart.
Composing those projections with the strict reference transitions places
all four based blocks on the one selected `(B,T)` model.

{docstring AclGeom.FiniteExtensionCompositum.restrictScalars_le_of_basisValues_subset}

{docstring AclGeom.FiniteExtensionCompositum.over_finiteDimensional}

The same finite-basis construction now carries its selected cover through
normalization over the larger base.  Its ambient normal field and canonical
normal cover remain finite, the original smaller normal field is still a
literal subfield of the ambient model, and a named map into the canonical
model factors through the canonical selected embedding of the compositum.
This is the branch-preserving scalar-rebase operation needed for the four
separately based middle covers; using uniqueness of normal closures alone
would forget which conjugate contains the selected branch.

{docstring AclGeom.FiniteExtensionCompositum.normalField}

{docstring AclGeom.FiniteExtensionCompositum.normal_le_normalField_restrictScalars}

{docstring AclGeom.FiniteExtensionCompositum.canonicalCover}

{docstring AclGeom.FiniteExtensionCompositum.originalToCanonicalRingHom}

{docstring AclGeom.FiniteExtensionCompositum.extendScalars_trans_finiteDimensional}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.normalizedField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.eNormalField_le_normalizedField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.aNormalField_le_normalizedField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.bNormalField_le_normalizedField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.cNormalField_le_normalizedField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.normalizedOverInput_finiteDimensional}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.referenceNormalCover}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.referenceNormalCover_normal}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedE}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedA}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedB}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedC}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceE}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceA}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceB}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceC}

These common-cover maps now carry exact generic-point data.  An arbitrary
embedding of integral-scheme function fields has a canonical generic-point
morphism, and denominator clearing is proved to recover exactly the
conjugated ambient embedding.  Reference transport is equally explicit.
Thus every direct projection and every transported `toReference` map is
identified with one displayed contravariant field homomorphism; composition
is literal composition of those homomorphisms.  This isolates the next
obligation cleanly: a faithful comparison with the presented-family arrows
is still required before categorical cancellation can imply an equality of
rational maps.

{docstring AlgebraicGeometry.Scheme.functionFieldMorphismOfHom}

{docstring AclGeom.FiniteExtensionProjection.functionFieldAlgHom}

{docstring AclGeom.FiniteExtensionProjection.rationalMap_fromFunctionField}

{docstring AclGeom.QWitness.rankTwoScalarLocusReferenceRationalMap_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.projectionFunctionFieldRingHom}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.projectionToNormalizedScalar_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedE_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedA_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedB_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toNormalizedC_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.normalizedToSelectedFunctionFieldRingHom}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.projectionToReference_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceE_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceA_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceB_fromFunctionField}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.toReferenceC_fromFunctionField}

On any genuine three-object groupoid, a based arrow family is equivalent to
the vertex group, its four-arrow cancellation defines a
`RationalGroupChunk`, and the chart transports multiplication and inverse
exactly.  The normalized six-point output then has the four product
relations prescribed by the partial quadrangle:

{docstring AclGeom.groupoidFourArrowComposite}

{docstring AclGeom.groupoidArrowChunk}

{docstring AclGeom.groupoidDifferenceEquiv_mul}

{docstring AclGeom.groupoidComposite_eq}

{docstring AclGeom.differenceChart_mul}

{docstring AclGeom.sixPointGroupTuple_relations}

The genus-zero endgame is the explicit affine semidirect product.  Its group
law is the blueprint formula `(c,d)(a,b)=(ca,cb+d)`, conjugation scales the
normal translation subgroup, and two distinct fixed points force an affine
transformation to be the identity:

{docstring AclGeom.AffineTransformation.mul_translation_mul_inv}

{docstring AclGeom.AffineTransformation.eq_one_of_smul_eq_of_smul_eq}

The completeness directions — resting on the affine grid extraction of
blueprint Lemma 8.5, the rational group chunk, and the affine-action
classification — are the remaining chunk of this layer; the design
discussion is tracked on the project's issue tracker.
