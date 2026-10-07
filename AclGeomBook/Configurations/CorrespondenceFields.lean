/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.CompositionIdentity

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Selected correspondence fields and branch groupoids" =>

%%%
tag := "configuration-record-correspondence-fields"
%%%

Finite correspondence composition keeps track of a selected generic
component.  The matching theorem relocates the source of the second germ
onto the target of the first; the resulting endpoint pair is the chosen
component.  The fiber-product dimension calculation used in equation (8.6)
is exposed separately as an algebraic-independence and closure statement:

{docstring AclGeom.FiniteCorrespondenceGerm.exists_composite}

{docstring AclGeom.fiber_product_rank_count}

The reverse rank bridge makes that abstract count available from the actual
clauses of a `Psi` witness: `rank_AB` yields independence of the four chosen
parameter representatives, `Y_notLe` supplies the fifth generic coordinate,
and the two incidence clauses make `X,Z` algebraic over it:

{docstring AclGeom.algebraicIndependent_of_rankEq_iSup_point}

{docstring AclGeom.QWitness.psi_fiber_product_rank_count}

Exchange then upgrades the two incidences to literal finite-correspondence
pairs over the combined parameter field.  Their chosen representatives
share `Y`, so the germ calculus selects the `(X,Z)` component without a
relocation:

{docstring AclGeom.QWitness.psi_selected_correspondence_composes}

Selected presentations now carry their reverse and diagonal branches, with
strict associativity at literal shared middles.  The actual `Psi` branches
satisfy these groupoid inverse laws rather than only the forward
composition:

{docstring AclGeom.FiniteCorrespondenceGerm.comp_assoc_of_shared_middles}

{docstring AclGeom.QWitness.psi_selected_correspondence_groupoid_laws}

Each selected branch also carries its concrete joint function field.  It
is finite over either endpoint field; for a composable pair the three-point
chain field is finite over the left branch, the right branch, and the
selected composite branch:

{docstring AclGeom.FiniteCorrespondencePair.branchOverSource_finiteDimensional}

{docstring AclGeom.FiniteCorrespondencePair.chainOverComposite_finiteDimensional}

{docstring AclGeom.QWitness.psi_selected_chain_field_finite_covers}

When the coefficient field varies, the relevant transport datum is a
commuting square: one equivalence on the base branch field and one on the
total chain field, compatible with the two inclusions.  These extension
equivalences have identity, inverse, and composition operations:

{docstring AclGeom.FiniteCover.ExtensionEquiv}

{docstring AclGeom.FiniteCover.ExtensionEquiv.symm}

{docstring AclGeom.FiniteCover.ExtensionEquiv.trans}

Normal closure respects equivalences of the original extension and of its
ambient field, and restricting across a surjective scalar map does not
change it.  Consequently every concrete ambient normal cover can be moved
to a canonical model inside the algebraic closure of its base.  A chosen
normal-extension equivalence records both the finite-extension square and
the compatible semilinear equivalence of canonical normal covers; chosen
lifts are closed under identity, inverse, and composition:

{docstring AclGeom.FiniteCover.map_normalClosure_eq_of_equiv}

{docstring AclGeom.FiniteCover.normalClosure_restrictScalars_of_surjective}

{docstring AclGeom.FiniteCover.canonicalNormalClosure}

{docstring AclGeom.FiniteCover.normalClosureOverEquivCanonical}

{docstring AclGeom.FiniteCover.NormalExtensionEquiv}

{docstring AclGeom.FiniteCover.ExtensionEquiv.normalLift}

Inside an algebraically closed ambient field, taking all conjugates turns
the selected finite chain into a finite normal extension of its endpoint
branch field:

{docstring AclGeom.FiniteCorrespondencePair.chainNormalOverComposite_normal}

{docstring AclGeom.QWitness.psi_selected_chain_normal_cover}

All conjugate branches factor uniquely through that normal field.  There
are finitely many of them; the literal branch selects one embedding, and
ambient embeddings of the normal cover are precisely its automorphisms:

{docstring AclGeom.FiniteCover.normalClosure_val_comp_selectedEmbedding}

{docstring AclGeom.QWitness.psi_selected_chain_component_on_normal_cover}

{docstring AclGeom.QWitness.psiSelectedChainEmbeddingEquivAut}

The finite ambiguity is itself categorical.  Deck transformations act by
postcomposition on embeddings of a branch field into its normal cover.
Normality extends every such embedding to a deck transformation, so the
resulting action category is a connected genuine groupoid with the literal
branch as a distinguished object:

{docstring AclGeom.NormalBranchEmbedding}

{docstring AclGeom.NormalBranchEmbedding.extendToAut_smul_canonical}

{docstring AclGeom.normalBranchGroupoid.isConnected}

{docstring AclGeom.finiteCoverBranchGroupoid_isConnected}

For the actual `Psi` chain this gives the selected object and a connected
groupoid of all conjugate components, rather than merely a finite list of
embeddings:

{docstring AclGeom.QWitness.psiSelectedChainBranchObject}

{docstring AclGeom.QWitness.psiSelectedChainBranchGroupoid_isConnected}

The second `Z` incidence simultaneously presents `(X,Z)` as the member
parametrized by `C`.  After adjoining all six displayed parameters, both
the composed endpoint ideal and the `C`-family ideal lie under the same
prime selected by the literal generic pair.  This is the prime-component
form of equation (8.6); it does not incorrectly assert that finite base
change stays irreducible:

{docstring AclGeom.QWitness.xzCorrespondencePairOverC}

{docstring AclGeom.QWitness.psi_composition_selected_component}

The actual family members are also retained over their separate rank-two
coefficient fields.  Clause (iv) becomes an exact minimality theorem: no
atom below `A`, `B`, or `C` already carries the relevant incidence.  Their
selected base changes are the branches used above:

{docstring AclGeom.QWitness.psi_family_parameters_rank_two_minimal}

Keeping the parameter tuple visible gives a genuine generic member of each
positive-dimensional correspondence family.  The parameter together with
the source coordinate is independent, while the target is algebraic over
that prefix.  An extension theorem for algebraic function fields then pins
any other independent parameter/source prefix literally and supplies a
target with the same complete family ideal:

{docstring AclGeom.FiniteCorrespondenceFamilyMember}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.parameterSource_independent}

{docstring AclGeom.exists_snoc_relocation_fixing}

For the three families occurring in `Psi`, these generic members specialize
exactly to the selected pairs over `k(A)`, `k(B)`, and `k(C)`.  Their
relocation theorems say that every independent generic parameter/source
tuple lies under the corresponding total family locus:

{docstring AclGeom.QWitness.xyCorrespondenceFamilyMember_toPair}

{docstring AclGeom.QWitness.yzCorrespondenceFamilyMember_toPair}

{docstring AclGeom.QWitness.xzCorrespondenceFamilyMember_toPair}

{docstring AclGeom.QWitness.xyFamily_exists_relocation}

{docstring AclGeom.QWitness.yzFamily_exists_relocation}

{docstring AclGeom.QWitness.xzFamily_exists_relocation}

{docstring AclGeom.QWitness.aFamily_map_le_abBranch}

{docstring AclGeom.QWitness.bFamily_map_le_abBranch}

The common coefficient cover used to select the output component is not
merely terminology: equality of the rank-four `A ∨ B` and
`A ∨ B ∨ C` flats makes every `C` coordinate algebraic over the
`A,B` field, and finite generation then gives a finite-dimensional field
extension:

{docstring AclGeom.QWitness.abcOverAb_finiteDimensional}

Taking all ambient conjugates preserves finiteness and produces the normal
coefficient cover used by the selected-component comparison:

{docstring AclGeom.QWitness.abcNormalOverAb_finiteDimensional}

{docstring AclGeom.QWitness.abcNormalOverAb_normal}

On the common normal cover, a chosen branch makes the generic
multiplication and inverse single-valued.  Associativity and the two inverse
identities already force an honest group: the apparently
parameter-dependent left and right units coincide.  The left-translation
chart is consequently an injective homomorphism into the automorphism group
of the normalized function field:

{docstring AclGeom.RationalGroupChunk.toGroup}

{docstring AclGeom.TranslationGroupChunk.translationHom}

The difference chart in the three-object correspondence groupoid is now
fed by the actual partial-quadrangle clause.  Each partial quadrangle gives
the three selected arrows `T : S' → U'`, `S : U' → T'`, and
`U : S' → T'` over `k(S,T,U)`, with the literal composition identity
`S ∘ T = U`; every `Psi` witness therefore contains this concrete
three-object groupoid:

{docstring AclGeom.IsPartialQuadrangle.tPair}

{docstring AclGeom.IsPartialQuadrangle.selected_correspondence_composes}

{docstring AclGeom.QWitness.psi_exists_partialQuadrangle_correspondence_groupoid}

The three selected branches share a finite chain field.  Normalizing it
over the `U` endpoint branch adjoins every ambient conjugate; the literal
chain is one selected embedding, and embeddings of the normal cover are
exactly its automorphisms:

{docstring AclGeom.IsPartialQuadrangle.selected_chain_normal_cover}

{docstring AclGeom.IsPartialQuadrangle.selected_chain_component_on_normal_cover}

{docstring AclGeom.IsPartialQuadrangle.selectedChainEmbeddingEquivAut}

The same construction turns the partial-quadrangle normal-cover components
into a connected action groupoid with the literal `S' → U' → T'` chain as
its selected object:

{docstring AclGeom.IsPartialQuadrangle.selectedChainBranchObject}

{docstring AclGeom.IsPartialQuadrangle.selectedChainBranchGroupoid_isConnected}

At parameter level the dependent rank-two triple `(S,T,U)` is itself a
ternary generically finite correspondence, oriented as `S · T = U`.
Every coordinate pair is independent and the third coordinate is algebraic
over it.  Algebraically closed tuple relocation therefore solves the
generic product and both generic division problems on one fixed prime
locus.  This is the positive-dimensional multiplication graph; it is kept
distinct from the finite deck group acting on any one normalized fiber:

{docstring AclGeom.FiniteCorrespondenceMultiplication}

{docstring AclGeom.FiniteCorrespondenceMultiplication.exists_output}

{docstring AclGeom.FiniteCorrespondenceMultiplication.exists_right}

{docstring AclGeom.FiniteCorrespondenceMultiplication.exists_left}

{docstring AclGeom.IsPartialQuadrangle.parameterMultiplication}

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_output}

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_right}

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_left}

Every displayed point of that locus inherits the same pairwise
independence, algebraicity, and equality of the three two-coordinate
closures.  Starting with four independent parameters `(s,e,a,b)`, exchange
then supplies the entire blueprint difference diagram on the same prime
locus:

`u=s·e`, `sA·a=u`, `uB=s·b`, and `sA·c=uB`.

No independence of the intermediate pairs `(a,u)` or `(sA,uB)` is assumed;
both are derived from the four inputs and the preceding finite relations.
This remains a relational diagram until the selected branch transports
certify the groupoid cancellation identity.

{docstring AclGeom.FiniteCorrespondenceMultiplication.IsRealization}

{docstring AclGeom.FiniteCorrespondenceMultiplication.IsRealization.racl_leftRight_eq_leftOutput}

{docstring AclGeom.FiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram}

{docstring AclGeom.FiniteCorrespondenceMultiplication.exists_fourArrowDifferenceDiagram}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowDifferenceDiagram}

{docstring AclGeom.IsPartialQuadrangle.exists_parameter_fourArrowDifferenceDiagram}

Before passing to the common `k(S,T,U)` cover, the three arrows are genuine
members of separate one-parameter families: `T` carries `S' → U'`, `S`
carries `U' → T'`, and `U` carries `S' → T'`.  Each family locus relocates
above every independent parameter/source pair.  Base change to the common
coefficient field selects exactly the three branches used in the groupoid
composition:

{docstring AclGeom.IsPartialQuadrangle.tFamilyMember}

{docstring AclGeom.IsPartialQuadrangle.sFamilyMember}

{docstring AclGeom.IsPartialQuadrangle.uFamilyMember}

{docstring AclGeom.IsPartialQuadrangle.tFamily_exists_relocation}

{docstring AclGeom.IsPartialQuadrangle.sFamily_exists_relocation}

{docstring AclGeom.IsPartialQuadrangle.uFamily_exists_relocation}

{docstring AclGeom.IsPartialQuadrangle.tFamily_map_le_selectedPair}

{docstring AclGeom.IsPartialQuadrangle.sFamily_map_le_selectedPair}

{docstring AclGeom.IsPartialQuadrangle.uFamily_map_le_selectedPair}

Independent relocation can be performed on the whole finite algebraic
configuration, not only one family member at a time.  The generic tuple
extension theorem fixes any designated independent coordinate subsystem,
and equality of the complete ideal automatically restricts to every
coordinate projection.  Applied to the displayed `(S,T,U,S',T',U')`, one
relocated six-tuple therefore realizes all three original family ideals at once,
with their intermediate and endpoint coordinates shared literally:

{docstring AclGeom.exists_tuple_relocation_fixing}

{docstring AclGeom.idealOf_comp_eq_of_idealOf_eq}

{docstring AclGeom.algebraicIndependent_comp_of_idealOf_eq}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.ofOneTupleIdealEq}

Equal complete loci do more than transfer algebraicity: their coordinate
rings and generated function fields are canonically equivalent, coordinate
by coordinate.  These equivalences respect identity, reversal, and
composition, providing the coherence needed for gluing relocated fibers:

{docstring AclGeom.locusCoordinateRingEquiv}

{docstring AclGeom.locusCoordinateRingEquivOfIdealEq}

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq}

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq_apply}

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq_refl}

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq_symm}

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq_trans}

The same transport extends after adjoining one fresh transcendental
coordinate.  Consequently a relocated algebraic parameter tuple can be
fixed first, then enlarged by a generic family source without changing the
complete augmented locus.  The resulting base equivalence extends once
more across any finite algebraic tuple, yielding relocation with an
arbitrary equal-locus coordinate subsystem fixed literally:

{docstring AclGeom.adjoinTranscendentalEquivOfEquiv}

{docstring AclGeom.adjoinTranscendentalEquivOfEquiv_algebraMap}

{docstring AclGeom.adjoinTranscendentalEquivOfEquiv_generator}

{docstring AclGeom.idealOf_snoc_eq_of_idealOf_eq_of_generic}

{docstring AclGeom.exists_tuple_relocation_fixing_locus}

{docstring AclGeom.IsPartialQuadrangle.exists_configuration_relocation}

In particular, a chosen product branch `(s,t,u)` on the parameter
multiplication locus and a source generic over it lift to one compatible
six-coordinate realization fixing `(s,t,u,x)` exactly:

{docstring AclGeom.IsPartialQuadrangle.exists_configuration_relocation_fixing_parameter_realization}

{docstring AclGeom.IsPartialQuadrangle.exists_compatible_family_relocation}

Projecting the exact lift to the three family-coordinate triples proves the
parameter-level composition law directly: every chosen generic product
`M(s,t,u)` and fresh source `x` admits shared `y,z` with `T(t,x,y)`,
`S(s,y,z)`, and `U(u,x,z)` on their original complete family loci:

{docstring AclGeom.IsPartialQuadrangle.exists_family_composition_of_parameter_product}

The four-arrow parameter diagram can be lifted edge by edge without
introducing four unrelated generic sources.  All of its intermediate
parameters are algebraic over `(s,e,a,b)`, so a fifth independent input is
fresh over every one of the four parameter triples.  Fixing that same
source in all four complete six-tuples gives exact family realizations of
`s·e`, `sA·a`, `s·b`, and `sA·c`:

{docstring AclGeom.IsPartialQuadrangle.ParameterProductFamilyLift}

{docstring AclGeom.IsPartialQuadrangle.exists_parameterProductFamilyLift}

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts}

{docstring AclGeom.IsPartialQuadrangle.exists_parameterFourArrowFamilyLifts}

{docstring AclGeom.IsPartialQuadrangle.exists_parameterFourArrowDiagramWithFamilyLifts}

Complete-ideal equality also transports the genericity and two-way
algebraicity needed for actual finite correspondences.  Hence each
relocated tuple supplies three pairs over its common parameter field, and
their shared coordinates give the composition identity literally.  This
holds above every independent replacement of `(S,T,S')`:

{docstring AclGeom.IsPartialQuadrangle.tPairOfIdealEq}

{docstring AclGeom.IsPartialQuadrangle.sPairOfIdealEq}

{docstring AclGeom.IsPartialQuadrangle.uPairOfIdealEq}

{docstring AclGeom.IsPartialQuadrangle.pairsOfIdealEq_composes}

{docstring AclGeom.IsPartialQuadrangle.exists_relocated_correspondence_groupoid}

For the quadrangle locus this transport is packaged directly between any
two relocated six-coordinate fields.  The first five coordinates generate
the selected composite branch, the sixth supplies the middle point of the
chain, and the two canonical transports form a commuting extension square.
It is coherent on triples of realizations.  Equality transports then identify
this coordinate square with the actual selected composite/chain extension:

{docstring AclGeom.IsPartialQuadrangle.tupleCompositeField}

{docstring AclGeom.IsPartialQuadrangle.relocatedCompositeEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedCompositeEquiv_apply}

{docstring AclGeom.IsPartialQuadrangle.tupleConfigurationField}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationEquiv_apply}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationEquiv_refl}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationEquiv_symm}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationEquiv_trans}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationExtensionEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedConfigurationExtensionEquiv_trans}

{docstring AclGeom.IsPartialQuadrangle.relocatedCompositeBranchField_restrictScalars_eq}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainField_restrictScalars_eq}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainExtensionEquiv}

This extension transport now lifts through normalization.  Passing through
the canonical models gives a compatible isomorphism between the concrete
ambient normal-cover fields.  Conjugating an embedding by the base, chain,
and normal-cover equivalences then identifies the finite branch types of
any two relocated realizations:

{docstring AclGeom.NormalBranchEmbedding.equivOfEquiv}

{docstring AclGeom.NormalBranchEmbedding.deckEquivOfEquiv}

{docstring AclGeom.NormalBranchEmbedding.mapOfEquiv_smul}

{docstring AclGeom.finiteCoverBranchEquivOfExtensionEquiv}

{docstring AclGeom.finiteCoverDeckEquivOfExtensionEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainNormalExtensionEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainNormalCoverEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainNormalCoverEquiv_algebraMap}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchEquiv}

The field-theoretic lift need not send the literal selected branch to the
literal target branch.  Transitivity corrects it by one target deck
transformation; conjugating the deck-group map by that same correction
retains equivariance.  Consequently equal-locus relocation preserves the
distinguished object and gives an equivalence of the whole action
groupoids:

{docstring AclGeom.FiniteCoverBasedBranchEquiv}

{docstring AclGeom.finiteCoverBasedBranchEquivOfExtensionEquiv}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.refl}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.symm}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.trans}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.groupoidEquivalence}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.arrowEquiv}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.arrowEquiv_differenceProduct}

{docstring AclGeom.FiniteCoverBasedBranchEquiv.arrowEquiv_differenceInverse}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBasedBranchEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchGroupoidEquivalence}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBranchGroupoidEquivalence_obj_selected}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBasedArrowEquiv}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBasedArrowEquiv_differenceProduct}

{docstring AclGeom.IsPartialQuadrangle.relocatedChainBasedArrowEquiv_differenceInverse}
