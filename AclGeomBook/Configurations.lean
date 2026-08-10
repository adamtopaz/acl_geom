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

{docstring AclGeom.IsPartialQuadrangle.ParameterFourArrowFamilyLifts.groupoid_cancellation}

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
