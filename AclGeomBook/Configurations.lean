/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Configurations: the geometric Q, Q′, and J" =>

%%%
tag := "configurations"
%%%

The configuration layer (blueprint §§6–7, milestone M4) defines the finite
geometric predicates through which the field structure will be recovered
from the geometry alone, and proves them correct against their semantic
counterparts. This chapter tracks the layer as it grows; the language and
the semantic relations are in place.

# The incidence language
%%%
tag := "incidence-language"
%%%

Following the blueprint, the formalization does not encode a countable
first-order language: the proof uses a fixed finite collection of lattice
relations, which transport easily through geometry isomorphisms.

{docstring AclGeom.MemCl}

{docstring AclGeom.line}

{docstring AclGeom.Col}

Collinearity is a special case of tuple incidence, and tuple incidence is
membership in the pregeometry's point closure — the bridge to the
foundation layers:

{docstring AclGeom.col_iff_memCl}

{docstring AclGeom.memCl_iff_mem_pointCl}

# The partial quadrangle
%%%
tag := "partial-quadrangle"
%%%

The six-point partial quadrangle is the orientation device of the
Evans–Hrushovski group configuration (blueprint Def partialquad). The four
dependent triples are named once, canonically; the "every other triple is
independent" clause quantifies over three-element finsets of `Fin 6`:

{docstring AclGeom.quadTriples}

{docstring AclGeom.IsPartialQuadrangle}

Simplification lemmas name the four dependent triples (for example the
first, `(S, T, U)`), and the permutation lemma transports the predicate
along any reordering preserving the named triples — at concrete
permutations its hypothesis is checked by `decide`:

{docstring AclGeom.IsPartialQuadrangle.rank_STU}

{docstring AclGeom.IsPartialQuadrangle.comp_perm}

# The semantic relations
%%%
tag := "semantic-relations"
%%%

The semantic configurations record which tuples of points arise from the
field operations at independent generic elements — writing $`[x]` for the
principal closure of $`x`:

{docstring AclGeom.QSem}

{docstring AclGeom.Q'Sem}

{docstring AclGeom.JSem}

The normalization identities of the blueprint — scaling and translating by
base-field constants, nonzero powers (in particular Frobenius powers),
inverses, and negation do not move a principal closure — follow directly
from the singleton-closure calculus:

{docstring AclGeom.ClosedIF.point_algebraMap_mul}

{docstring AclGeom.ClosedIF.point_add_algebraMap}

{docstring AclGeom.ClosedIF.point_pow}

# The geometric relations
%%%
tag := "geometric-relations"
%%%

Gismatullin makes the Evans–Hrushovski witness completely explicit: the
geometric `Q` quantifies a twenty-one-point configuration. Per the
blueprint, the witness is a structure with named fields rather than a
21-tuple — the intersection equations stay readable and permutation
errors are impossible:

{docstring AclGeom.QWitness}

The seven clauses of $`\Psi` are the rank-four joins, the incidences of
the generic points, three universal clauses quantifying over atoms (which
make the correspondences *irreducible*), the dependent triple inside
$`A, B, C`, the partial quadrangle, and the seven meet equations of the
affine grid:

{docstring AclGeom.QWitness.Psi}

{docstring AclGeom.QGeom}

The multiplicative structure enters through the projective multiplication
diagram — eight points and seven concurrent rank-two lines — which
converts the ratio output of `Q` into a product point:

{docstring AclGeom.MulDiagram}

{docstring AclGeom.Q'Geom}

The geometric `J` is then a conjunction of one `Q`-instance and two
`Q′`-instances, the second of which reuses the same sum points against
the shifted representative `a+1`:

{docstring AclGeom.JGeom}

# Soundness of the geometric Q
%%%
tag := "q-soundness"
%%%

The soundness direction of blueprint Theorem q-correct is proved by
exhibiting the explicit 21-point witness of table 7.1: given five
independent generators, every entry is a rational monomial expression and
every clause of $`\Psi` verifies elementwise. The verification runs on a
small toolkit. Geometric rank clauses reduce to field theory through the
*rank bridge*:

{docstring AclGeom.rankEq_of_coe_eq_racl}

{docstring AclGeom.pointIndep_point}

Each table entry is transcendental by a uniform *recovery principle* —
dividing or subtracting away side factors recovers a generator that the
independence hypothesis keeps free:

{docstring AclGeom.notMem_bot_of_recover}

The witness itself, and the assembled verification:

{docstring AclGeom.qWitness}

{docstring AclGeom.qWitness_psi}

Two clauses deserve comment. The seven meet equations of clause (vii)
are literal independent-variable intersections (blueprint eq. 8.9a) —
and that identity is exactly the exchange brick
`mem_racl_of_mem_racl_insert` already proved for the hard kernel's
multiplicative endgame, so no linear-disjointness theory is needed:

{docstring AclGeom.sup_point_inf_sup_point_eq}

The universal atom clauses (iv) are proved by a *specialization
argument* replacing the blueprint's derivation calculation: a relation
over the atom's closure collapses to a one-variable polynomial identity,
which specializes at two base points and recovers both line coefficients
inside the atom — contradicting their independence:

{docstring AclGeom.line_relation_specialize}

{docstring AclGeom.notMem_racl_line}

Consequently every clause holds with only an infinite base field — no
algebraic closure enters the soundness direction. The packaged statement
produces the witness generators from any semantic quadruple by a greedy
fresh chain:

{docstring AclGeom.algebraicIndependent_snoc}

{docstring AclGeom.qtable_indep_of_fresh}

{docstring AclGeom.qGeom_of_qSem}

# Soundness of Q′ and J
%%%
tag := "qprime-j-soundness"
%%%

The multiplication diagram's coordinate check (blueprint Lemma
mul-diagram, forward half) verifies the eight monomial points at an
independent triple — every displayed line is one rational identity, and
the twenty-eight distinctness facts are uniform closure recoveries:

{docstring AclGeom.mulDiagram_of_indep}

Q′-soundness then composes the `Q`-soundness at the ratio point with a
diagram at one fresh parameter, and J-soundness is the three-conjunct
identity with the blueprint's normalizations `[x/(xa)] = [a]`,
`[a+1] = [a]`, and `x(a+1) = x + xa`:

{docstring AclGeom.q'Geom_of_q'Sem}

{docstring AclGeom.jGeom_of_jSem}

The semantic projection identity — `Q` is the `P`-projection of `J` —
follows from the same normalization calculus:

{docstring AclGeom.qSem_iff_exists_jSem}

With this, the soundness half of the configuration layer is complete:
`QSem → QGeom`, `Q'Sem → Q'Geom`, and `JSem → JGeom` all hold over any
infinite base field, given a supply of fresh elements over small sets.

# The affine-grid extraction boundary
%%%
tag := "affine-grid-boundary"
%%%

The completeness half has a precise formal boundary.  At the level of
closed points, the interalgebraic replacements in blueprint Lemma 8.5 amount
to equality with the verified table witness.  Once those coordinates have
been extracted, the free outputs are immediately the semantic quadruple
`([b], [ax], [b+ax], [b/(ax)])`; the reciprocal ratio defines the same
closed point:

{docstring AclGeom.QWitness.HasAffineGridCoordinates}

{docstring AclGeom.QWitness.affineGrid_output_independent}

{docstring AclGeom.QWitness.qSem_of_hasAffineGridCoordinates}

The sole remaining geometric implication is named without being assumed or
axiomatized.  Supplying a proof of it closes the `QGeom ↔ QSem` theorem:

{docstring AclGeom.AffineGridExtraction}

{docstring AclGeom.qGeom_iff_qSem}

# Selected correspondence composition and the group-chunk core
%%%
tag := "group-chunk-core"
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

The positive-dimensional action begins with the actual curve-coordinate
fields of the selected correspondence families.  A finite correspondence
does not usually act on its source rational field, since its target is only
algebraic over that field.  It does induce an equivalence between the
source and target rational fields, and a chosen semilinear equivalence of
their algebraic closures.  Chosen lifts are not falsely declared
functorial: the discrepancy between strict composition and a separately
chosen composite lift is an explicit deck transformation fixing the target
curve field:

{docstring AclGeom.AlgebraicClosureTransport}

{docstring AclGeom.FiniteCorrespondencePair.coordinateClosureTransport}

{docstring AclGeom.FiniteCorrespondencePair.coordinateClosureTransport_source}

{docstring AclGeom.FiniteCorrespondencePair.chainCoordinateClosureTransport_source}

{docstring AclGeom.FiniteCorrespondencePair.compositionDefect}

{docstring AclGeom.FiniteCorrespondencePair.chainCoordinateClosureTransport_trans_compositionDefect}

For the Ψ witness this gives the field-action form of blueprint equation
`(8.6)`: the `A` branch carries `X` to `Y`, the `B` branch carries `Y` to
`Z`, and their strict composite agrees with the independently selected `C`
lift after the vertical deck correction.  Its coefficient field contains
the two independent rank-two parameters `A,B`; this is therefore the first
single-valued positive-dimensional field action, not another finite deck
chart:

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
the same finite normal target cover, and equation `(8.6)` holds there as
an exact equality after the restricted vertical deck correction:

{docstring AclGeom.QWitness.psiXFiniteNormalCover}

{docstring AclGeom.QWitness.psiB_sourceCover_le_psiYFiniteNormalCover}

{docstring AclGeom.QWitness.psiCFiniteNormalCover_field}

{docstring AclGeom.QWitness.psiFiniteCoverCompositionDefect}

{docstring AclGeom.QWitness.psiFiniteCoverComposition}

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
