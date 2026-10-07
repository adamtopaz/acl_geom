/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.ChunkFiniteFieldAction

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Parameter families and chosen field transports" =>

%%%
tag := "configuration-record-parameter-transport"
%%%

Independently chosen algebraic-closure lifts are not asserted to satisfy a
cocycle.  Instead, choose one reference realization and define every
fiber-to-fiber transition through it.  Identity, reversal, and the cocycle
law then follow from the explicit composition operations on based branch
transports:

{docstring AclGeom.IsPartialQuadrangle.RelocatedChainRealization}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchTrivialization}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchTransition}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchTransition_self}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchTransition_symm}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchTransition_trans}

Applied to the four exact family lifts, the `s·e` realization is a fixed
reference fiber and each of the other three normalized fibers has a
canonical reference-based comparison into it.  These comparisons preserve
the selected branch and the based-arrow difference operations; they do not
identify a parameter with a deck transformation.

{docstring AclGeom.IsPartialQuadrangle.ParameterProductFamilyLift.realization}

{docstring AclGeom.IsPartialQuadrangle.ParameterProductFamilyLift.composes}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts.sA_aToReference}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts.s_bToReference}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts.sA_cToReference}

For each such relocated tuple, the selected chain has its own finite
normal-cover branch groupoid.  Every conjugate branch is reachable from
the literal one, and its based arrow family carries the difference-chart
group chunk.  The final theorem packages this finite categorical fiber
together with the varying generic realization:

{docstring AclGeom.finiteCoverSelectedArrow}

{docstring AclGeom.finiteCoverArrowChunk}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchGroupoid}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchObject}

{docstring AclGeom.IsPartialQuadrangle.finite_relocatedChainBranches}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchGroupoid_isConnected}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainArrowChunk}

{docstring AclGeom.IsPartialQuadrangle.exists_relocated_connected_branch_groupoid}

The exact product lift has the same package while retaining all prescribed
coordinates: its germ triple composes literally, and its selected chain lies
in a connected normal-cover branch groupoid:

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_product_connected_branch_groupoid}

The free triple `(S,T,S')` already gives independent representatives for
the three group-configuration coordinates.  Every other displayed
representative is algebraic over that triple, while each of the parameters
`S,T,U` is recoverable from the endpoints of its selected arrow.  Thus the
full six-coordinate field has a finite normal cover over the independent
three-coordinate field:

{docstring AclGeom.IsPartialQuadrangle.groupReps_independent}

{docstring AclGeom.IsPartialQuadrangle.T_rep_mem_racl_endpoints}

{docstring AclGeom.IsPartialQuadrangle.configurationOverGroupCoordinates_finiteDimensional}

{docstring AclGeom.IsPartialQuadrangle.configurationNormalOverGroupCoordinates_normal}

Parameter recovery can also be normalized arrow by arrow.  A recoverable
one-parameter family has full field `k(p,x,y)` finite over its endpoint
field `k(x,y)`; its normal closure retains every conjugate parameter branch.
For the partial quadrangle, all three displayed arrow families satisfy this
condition, and the `T` cover is exposed with both finiteness and normality:

{docstring AclGeom.RecoverableFiniteCorrespondenceFamilyMember}

{docstring AclGeom.RecoverableFiniteCorrespondenceFamilyMember.familyOverEndpoints_finiteDimensional}

{docstring AclGeom.RecoverableFiniteCorrespondenceFamilyMember.normalFamilyOverEndpoints}

{docstring AclGeom.IsPartialQuadrangle.tRecoverableFamilyMember}

{docstring AclGeom.IsPartialQuadrangle.tNormalFamilyOverEndpoints_finite_normal}

The varying family components now have their own genuine categorical
home.  Start with the free groupoid on parameter-labelled arrows
`T(t) : X₀ ⟶ X₁`, `S(s) : X₁ ⟶ X₂`, and
`U(u) : X₀ ⟶ X₂`, then quotient by the selected-component
relations `T(t) ≫ S(s) = U(u)` whenever `(s,t,u)` lies on the ternary
parameter locus.  A quotient of a free groupoid is again a genuine
groupoid, so inverse and associativity come from category operations rather
than extra laws:

{docstring AclGeom.PresentedFamilyGroupoid}

{docstring AclGeom.PresentedFamilyGroupoid.t_comp_s_eq_u}

The exact four-arrow diagram cancels in this presented groupoid.  After
swapping the two chart inputs to account for categorical composition order,
every independent generic triple `(e,a,b)` therefore has a `T`-family
output representing `a ≫ e⁻¹ ≫ b`.  The four full six-coordinate
lifts certify that this equation concerns the positive-dimensional family
arrows, while the finite branch groupoids above resolve the conjugate
ambiguity in each individual normalized fiber:

{docstring AclGeom.PresentedFamilyGroupoid.fourArrow_cancellation}

{docstring AclGeom.IsPartialQuadrangle.parameterFamilyGroupoid}

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_groupoidDifferenceProduct}

Fixing a generic base `T`-arrow transports the vertex-group structure to
the whole based arrow family.  The four-arrow construction says that its
everywhere associative multiplication returns to the actual
positive-dimensional `T` chart at independent generic inputs:

{docstring AclGeom.IsPartialQuadrangle.parameterTArrowChunk}

{docstring AclGeom.IsPartialQuadrangle.exists_parameterTArrowChunk_mul}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts.groupoid_cancellation}

Equation (8.6) has the same categorical presentation at parameter dimension
two.  Here the parameter type is a pair, the relation is the complete
prime locus of `(A,B,C)`, and the arrows are oriented exactly as the actual
`X → Y → Z` chain.  The selected theorem retains both the groupoid identity
and the finite-correspondence germ certificate:

{docstring AclGeom.PresentedFamilyGroupoidOf}

{docstring AclGeom.QWitness.psiParameterFamilyGroupoid}

{docstring AclGeom.QWitness.psi_selected_family_groupoid_composition}

The same six-coordinate prime locus is generically finite in all three
directions.  Each pair among `(A,B)`, `(A,C)`, and `(B,C)` has rank four,
while the omitted rank-two parameter is coordinatewise algebraic over that
pair.  Packaging these facts gives multiplication and both division
relocations above every independent generic parameter pair; the operation
is still a correspondence, so no uniqueness is asserted:

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.exists_output}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.exists_right}

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.exists_left}

{docstring AclGeom.QWitness.psiParameterMultiplication}

{docstring AclGeom.QWitness.exists_psiParameter_output}

Four independent rank-two inputs contribute eight independent scalar
coordinates.  Along the four-arrow construction, each selected relation
replaces one two-coordinate block by an interalgebraic block.  Thus the
relative algebraic closure of the ambient eight-tuple, and hence its exact
rank, is unchanged at every step.  The final division pair is therefore
generic without an extra hypothesis:

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.exists_fourArrowDifferenceDiagram}

With the `A ≫ B = C` orientation of equation (8.6), cancellation takes
place on the `B`-family chart: the output arrow is exactly
`a ≫ e⁻¹ ≫ b`.  Fixing the base `B(e)` transports the vertex-group
structure to all `B`-arrows, and multiplication returns to the actual
rank-two parameter chart at independent generic inputs:

{docstring AclGeom.PresentedFamilyGroupoidOf.fourArrow_right_cancellation}

{docstring AclGeom.QWitness.exists_psiParameter_groupoidDifferenceProduct}

{docstring AclGeom.QWitness.psiBArrowChunk}

{docstring AclGeom.QWitness.exists_psiBArrowChunk_mul}

The incidence clauses `S ≤ A`, `T ≤ B`, and `U ≤ C` compare this
rank-two chunk with the partial-quadrangle scalar chunk.  The honest object
at this stage is the complete joint locus of the nine coordinates
`(A₁,A₂,B₁,B₂,C₁,C₂,S,T,U)`: incidence makes the last three
coordinates algebraic over the first six, so every realization of the
ambient multiplication locus lifts after algebraic closure.  Restricting
the joint locus recovers both multiplication laws on the same realization:

{docstring AclGeom.QWitness.psiChunkProjectionRelation}

{docstring AclGeom.QWitness.exists_psiChunkProjection_of_relation}

{docstring AclGeom.QWitness.PsiChunkProjectionRelation.psiFamilyComposition}

{docstring AclGeom.QWitness.PsiChunkProjectionRelation.parameterMultiplication}

Coordinate restriction also exposes the three individual graph relations.
In particular the cancellation chart `B` projects to the quadrangle chart
`T`.  Its joint graph has exact rank two, while the target is a point, which
is the dimension count behind the future rank-one kernel.  No literal
single-valued rational map is asserted before the finite-cover ambiguity is
resolved:

{docstring AclGeom.QWitness.psiBProjectionRelation}

{docstring AclGeom.QWitness.PsiChunkProjectionRelation.bProjection}

{docstring AclGeom.QWitness.bTProjection_rank}

The joint locus has its own presented groupoid, with parameter labels
`(rank-two parameter, scalar parameter)`.  Forgetting the scalar coordinate
is an ordinary functor to the ambient $`A/B/C` presentation.  The scalar
coordinate exchanges the first two families, because the ambient relation
is `A ≫ B = C` while the quadrangle relation is `T ≫ S = U`; it therefore
gives a functor that swaps the families and inverts their arrows.  This
functorial formulation resolves the orientation exactly and does not choose
conjugate scalar branches independently:

{docstring AclGeom.PresentedFamilyGroupoidOf.map}

{docstring AclGeom.PresentedFamilyGroupoidOf.reverseMap}

{docstring AclGeom.QWitness.psiChunkFamilyRelation}

{docstring AclGeom.QWitness.psiChunkAmbientFunctor}

{docstring AclGeom.QWitness.psiChunkScalarReverseFunctor}

{docstring AclGeom.QWitness.psiChunkScalarReverseFunctor_map_differenceProduct}

On vertex groups the scalar functor is a genuine group homomorphism.  Its
kernel is consequently an actual normal subgroup, and a based joint
difference chart lies in that kernel precisely when its two scalar `T`
arrows agree.  This is arrow equality in the presented groupoid, not an
unproved injectivity statement about labels:

{docstring AclGeom.QWitness.psiChunkVertexHom}

{docstring AclGeom.QWitness.psiChunkKernel}

{docstring AclGeom.QWitness.psiChunkKernel_normal}

{docstring AclGeom.QWitness.groupoidDifferenceChart_mem_psiChunkKernel_iff}

A branch-compatible four-arrow diagram can now be stated without any
implicit gluing convention: every repeated parameter is literally the same
rank-two/scalar pair.  Its first coordinates form the ambient rank-two
diagram, its second coordinates form the partial-quadrangle diagram, and
the two cancellation formulas follow from the same four joint edges.  The
scalar variables appear in the opposite order, exactly as the reverse
functor predicts:

{docstring AclGeom.QWitness.PsiChunkFourArrowDifferenceDiagram}

{docstring AclGeom.QWitness.PsiChunkFourArrowDifferenceDiagram.ambientDiagram}

{docstring AclGeom.QWitness.PsiChunkFourArrowDifferenceDiagram.scalarDiagram}

{docstring AclGeom.QWitness.PsiChunkFourArrowDifferenceDiagram.ambient_cancellation}

{docstring AclGeom.QWitness.PsiChunkFourArrowDifferenceDiagram.scalar_cancellation}

An arbitrary ambient four-arrow diagram need not come with literally equal
choices of the algebraic scalar branch at every repeated rank-two block.
The finite-cover layer now records exactly what is available.  A scalar
graph realization generates a finite extension of its rank-two parameter
field; two choices over the same parameter and graph locus have equivalent
normal covers and equivariantly equivalent based branch groupoids.  Every
ambient diagram lifts edge by edge, and the four repeated blocks have
explicit normal-cover transports.  Thus branch comparison is genuine
field-theoretic data rather than an implicit equality of conjugates:

{docstring AclGeom.QWitness.rankTwoScalarExtension_finiteDimensional}

{docstring AclGeom.QWitness.rankTwoScalarBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts}

{docstring AclGeom.QWitness.exists_psiChunkFourArrowEdgeLifts}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.s_branchEquiv}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.u_branchEquiv}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.sA_branchEquiv}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.uB_branchEquiv}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.scalar_edge_relations}

Normalizing each scalar graph separately does not yet remember that three
branches occur on one multiplication edge.  The full-edge normalization
does: all nine joint coordinates form a finite extension of the six
ambient coordinates.  Equal-locus edges have compatible ambient-field,
joint-field, and concrete normal-cover equivalences.  Trivializing all four
edge fibers through one reference edge makes the transports strictly
cocyclic, so every reference-based cycle has trivial holonomy:

{docstring AclGeom.QWitness.PsiChunkRelationRealization}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.jointExtension_finiteDimensional}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.basedBranchEquiv}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.branchTransition}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.branchTransition_trans}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.seRealization}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.edge_branchTransition_cocycle}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.fourEdge_branchCycle}

The selected-branch correction is now retained at field level, rather than
discarded after constructing the branch-groupoid equivalence.  A based
normal-cover equivalence records its semilinear base square and an exact
whole-selected-branch square.  For joint edges this sends every one of the
nine named coordinates positionwise; in particular the four normalized
`B/T` scalar branches are images of one selected scalar branch under four
explicit corrected normal-cover equivalences.  Reference-based field
transitions satisfy a strict cocycle, and the four-edge field-level cycle is
literally the identity:

{docstring AclGeom.FiniteCoverBasedNormalEquiv}

{docstring AclGeom.FiniteCoverBasedNormalEquiv.map_selected_apply}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.basedNormalCoverEquiv}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.basedNormalCoverEquiv_selected_coordinate}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.normalCoverTransition}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.normalCoverTransition_trans}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.fourEdgeBasedNormalCoverEquivs}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.fourEdgeBasedNormalCoverEquivs_selectedBScalar}

{docstring AclGeom.QWitness.PsiChunkFourArrowEdgeLifts.fourEdge_normalCoverCycle}

The arrows of an action category also carry a direct based chunk.  Since
categorical composition reverses deck labels, taking the inverse of the
based difference label turns that chunk into an injective homomorphism to
automorphisms of the normal-cover field.  This faithful action is available
for every normal branch groupoid, every concrete finite cover, and in
particular every full joint edge:

{docstring AclGeom.actionCategoryArrowChunk}

{docstring AclGeom.actionCategoryTranslationChunk}

{docstring AclGeom.normalBranchGroupoid.translationChunk}

{docstring AclGeom.finiteCoverTranslationChunk}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.translationChunk}

Choosing one complete joint edge as reference now trivializes the entire
finite branch bundle and the entire deck-group bundle over the joint locus.
The selected branch becomes a constant section, deck actions remain
equivariant, and each based arrow family is reindexed into a translation
chunk on the same fixed reference normal-cover field.  The base coordinate
of this product remains the full joint realization, so this is an actual
descent of finite ambiguity rather than a replacement of the parameter
locus by a finite group:

{docstring AclGeom.QWitness.PsiChunkRelationRealization.branchBundleTrivialization}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.branchBundleTrivialization_selected}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.deckBundleTrivialization}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.normalizeBranch_smul}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.normalizedTranslationChunk}

{docstring AclGeom.QWitness.PsiChunkRelationRealization.normalizedTranslationChunk_translation}

The categorical kernel is now normal, the graph dimension count is in
place, and the finite edge covers have descended to a product local system
equipped with faithful actions on one reference field.  These automorphisms
form the finite deck group; they are not the positive-dimensional parameter
group.

The field-transport construction begins with the curve-coordinate fields
of selected correspondence branches.  A finite correspondence
does not usually act on its source rational field, since its target is only
algebraic over that field.  The displayed transcendental
coordinate fields admit a chosen coordinate equivalence and a semilinear
lift to their algebraic closures.  Chosen lifts are not falsely declared
functorial: the discrepancy between strict composition and a separately
chosen composite lift is an explicit deck transformation fixing the target
curve field:

{docstring AclGeom.AlgebraicClosureTransport}

{docstring AclGeom.FiniteCorrespondencePair.coordinateClosureTransport}

{docstring AclGeom.FiniteCorrespondencePair.coordinateClosureTransport_source}

{docstring AclGeom.FiniteCorrespondencePair.chainCoordinateClosureTransport_source}

{docstring AclGeom.FiniteCorrespondencePair.compositionDefect}

{docstring AclGeom.FiniteCorrespondencePair.chainCoordinateClosureTransport_trans_compositionDefect}

For a Ψ witness the `A` branch carries `X` to `Y` and the `B` branch
carries `Y` to `Z`.  Over their joint coefficient field, the strict composite
agrees with a separately selected endpoint lift after correcting by the
defined discrepancy.  This identity holds by construction.  The lift named
`C` here has not been identified with an intrinsic `C`-parametrized family,
and no positive-dimensional group action or equation `(8.6)` follows from
this identity alone:

{docstring AclGeom.QWitness.psiAClosureTransport}

{docstring AclGeom.QWitness.psiBClosureTransport}

{docstring AclGeom.QWitness.psiABClosureTransport_X}

{docstring AclGeom.QWitness.psiClosureCompositionDefect}

{docstring AclGeom.QWitness.psiClosureComposition}

{docstring AclGeom.QWitness.psiClosureParameters_independent}

The remaining normalization step is to prove that these algebraic-closure
transports and their vertical defects stabilize one common finite curve
cover.  This is now done by taking a finite normal compositum.  Semilinear
transport preserves finite dimensionality and normality, while every
vertical automorphism fixing the target curve field preserves a finite
normal intermediate field as a whole:

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover}

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.map}

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.map_ofAlgEquiv_field}

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.mapEquiv_trans_restrictAlgEquiv}

For Ψ, the source compositum contains the selected `A` and `C` branch
normalizations and the pullback of the selected `B` branch normalization.
Its middle and target transports therefore retain all three finite
correspondences.  The strict composite and independent `C` lift land on
the same finite normal target cover. The constructed endpoint-lift
identity restricts there after the vertical deck correction; identifying
this with the intrinsic `C` family in equation `(8.6)` remains open:

{docstring AclGeom.QWitness.psiXFiniteNormalCover}

{docstring AclGeom.QWitness.psiB_sourceCover_le_psiYFiniteNormalCover}

{docstring AclGeom.QWitness.psiCFiniteNormalCover_field}

{docstring AclGeom.QWitness.psiFiniteCoverCompositionDefect}

{docstring AclGeom.QWitness.psiFiniteCoverComposition}

The semantic target of four-arrow cancellation is now separated from the
formal presentation.  Actual field equivalences can be conjugated to fixed
reference fields without losing composition or equality, and four literal
composition squares cancel faithfully there.  For the selected Ψ edge, the
`A` and `B` restrictions compose to the strict `AB` transport; correcting
the separately chosen endpoint restriction by the inverse deck defect
gives a literal composition triangle. It does not establish the intrinsic
family action of equation `(8.6)`:

{docstring AclGeom.FieldEquiv.conjugate}

{docstring AclGeom.FieldEquiv.conjugate_trans}

{docstring AclGeom.FieldEquiv.conjugate_injective}

{docstring AclGeom.FieldEquiv.FourArrowDiagram.right_cancellation}

To descend that cancellation to an intrinsic parameter chart, the four
right arrows must act on one literal coefficient embedding in the common
middle field.  The following interface records that shared embedding and
its four restrictions; its factorization theorem is the non-gauge target
for the graph-faithful Ψ charts:

{docstring AclGeom.FieldEquiv.FourArrowDiagram.RightRestriction}

{docstring AclGeom.FieldEquiv.FourArrowDiagram.RightRestriction.ofSourceRestrictions}

{docstring AclGeom.FieldEquiv.FourArrowDiagram.RightRestriction.mapC_factorization}

{docstring AclGeom.QWitness.psiAFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiBFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiAFiniteCoverEquiv_trans_psiBFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiStrictCFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiFiniteCoverStrictComposition}
