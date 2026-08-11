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

The semantic target of four-arrow cancellation is now separated from the
formal presentation.  Actual field equivalences can be conjugated to fixed
reference fields without losing composition or equality, and four literal
composition squares cancel faithfully there.  For the selected Ψ edge, the
`A` and `B` restrictions compose to the strict `AB` transport; correcting
the independently chosen `C` restriction by the inverse deck defect turns
equation `(8.6)` into a literal composition triangle:

{docstring AclGeom.FieldEquiv.conjugate}

{docstring AclGeom.FieldEquiv.conjugate_trans}

{docstring AclGeom.FieldEquiv.conjugate_injective}

{docstring AclGeom.FieldEquiv.FourArrowDiagram.right_cancellation}

{docstring AclGeom.QWitness.psiAFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiBFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiAFiniteCoverEquiv_trans_psiBFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiStrictCFiniteCoverEquiv}

{docstring AclGeom.QWitness.psiFiniteCoverStrictComposition}

The selected composition triangle can now be moved over an arbitrary point
of the rank-two parameter multiplication locus without relocating its three
curve branches independently.  After choosing one source generic over the
six displayed parameters, the complete nine-coordinate
`(a,b,c,x,y,z)` tuple is relocated at once.  Its three restrictions retain
the selected `A`, `B`, and `C` family prime loci, so their source, middle,
and target coordinates match literally:

{docstring AclGeom.QWitness.psiCurveCompositionTuple}

{docstring AclGeom.QWitness.psiSelectedCurveCompositionTuple_mem_parameterSource_racl}

{docstring AclGeom.QWitness.exists_psiCurveCompositionRealization}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.aFamilyLocus}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.bFamilyLocus}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.cFamilyLocus}

Equal family loci can now be promoted back to generic family members in
every parameter dimension, not only in the earlier one-parameter special
case:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.ofTupleIdealEq}

Generic family members and their complete loci also transport along ambient
field embeddings.  Conversely, complete-locus equality already transfers
the independent parameter/source prefix, so callers need not reconstruct
that independence separately:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.map}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.ofTupleIdealEqOnly}

For the relocated Ψ triangle this packages all three restrictions as
rank-two family members and then as finite-correspondence pairs over the
one field generated by all six parameters.  A reusable normalization
construction enlarges the source cover by the left branch, the pulled-back
right branch, and the direct branch.  The vertical deck defect restricts by
normality, yielding a literal finite-cover identity:

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.strictComposition}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.aCorrespondenceFamilyMember}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.bCorrespondenceFamilyMember}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.cCorrespondenceFamilyMember}

{docstring AclGeom.QWitness.PsiCurveCompositionRealization.finiteCoverStrictComposition}

For the four-arrow difference component, the original eight-coordinate
genericity hypothesis supplies an explicit fresh curve source on every
edge: one unused ambient input coordinate.  The three intermediate
eight-tuples remain independent after each finite parameter replacement,
so all four curve triangles can be constructed together:

{docstring AclGeom.RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.s_sA_a_uB_independent}

{docstring AclGeom.QWitness.exists_psiCurveFourArrowRealizations}

{docstring AclGeom.QWitness.PsiCurveFourArrowRealizations.finiteCoverStrictCompositions}

Those edgewise sources cannot be used after enlarging coefficients to the
whole eight-input field, because each is itself one of the eight inputs.  A
single genuinely fresh coordinate is obtained by passing to the algebraic
closure of the rational-function field over the original ambient field.
Its formal variable is transcendental over that entire field and therefore
generic over every embedded parameter edge:

{docstring AclGeom.CommonCurveAmbient}

{docstring AclGeom.commonCurveSource_transcendental}

{docstring AclGeom.commonCurveSource_notMem_racl}

Ambient invariance transports the complete selected Ψ locus along the
canonical embedding.  The same relocation theorem then fixes the mapped
edge parameters together with the one formal source.  Applying it four
times produces four complete curve triangles whose sources agree literally,
which is the first coefficient-compatible cross-edge identification:

{docstring AclGeom.QWitness.exists_psiCurveCompositionBaseChangeRealization}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations}

{docstring AclGeom.QWitness.exists_psiCurveFourArrowCommonSourceRealizations}

The embedded A/B/C restrictions are genuine generic members of the mapped
families.  Although the selected auxiliary blocks `u`, `sA`, `uB`, and `c`
need not belong to the eight-input field, all their coordinates are
algebraic over it.  This is exactly enough to regard every branch as a
finite correspondence over one common coefficient field.  The middle
coordinate remains generic there because it is interalgebraic with the
formal source:

{docstring AclGeom.QWitness.PsiCurveCompositionBaseChangeRealization.aCorrespondenceFamilyMember}

{docstring AclGeom.QWitness.PsiCurveCompositionBaseChangeRealization.CommonBaseData}

{docstring AclGeom.QWitness.PsiCurveCompositionBaseChangeRealization.CommonBaseData.middle_generic}

Each of the four faces therefore has a strict deck-corrected finite-cover
composition triangle over the same eight-input coefficient field, with the
same literal source coordinate:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seFiniteCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaFiniteCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbFiniteCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcFiniteCoverCompositionTriangle}

Strict composition is stable under enlarging the source normalization: any
finite normal source cover can be transported through the left branch and
the two-step chain, and the same deck correction gives a literal triangle.
Taking the compositum of the four facewise source covers therefore produces
one finite normal field that contains every selected branch normalization.
All four actions are now transported from that exact same source field:

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.OnSourceCover.compositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonFiniteSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seFiniteSourceCover_le_common}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaFiniteSourceCover_le_common}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbFiniteSourceCover_le_common}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcFiniteSourceCover_le_common}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCommonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaCommonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCommonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcCommonCoverCompositionTriangle}

The repeated-locus comparison retains more than an abstract endpoint-field
isomorphism.  For a generic family member, the complete `(parameter,
source,target)` field is finite over `(parameter,source)`.  Equality of
complete family loci canonically identifies this extension coordinate by
coordinate, lifts it to the concrete normal closures, and applies one deck
correction so that the literal selected branch is preserved:

{docstring AclGeom.FiniteCorrespondenceFamilyMember.parameterSourceField}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.familyOverParameterSource_finiteDimensional}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.extensionEquivOfIdealEq}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.extensionEquivOfIdealEq_base_apply}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.normalCoverEquivOfIdealEq_algebraMap}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.basedBranchEquivOfIdealEq_selected}

The independently relocated occurrences of `s`, `sA`, `u`, and `uB` have
equal complete family loci.  They consequently carry four such based,
coefficient-aware comparisons before scalar extension to the entire
eight-input field:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seAFamily_ideal_eq_sbAFamily}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaAFamily_ideal_eq_sAcAFamily}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seCFamily_ideal_eq_sAaCFamily}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbCFamily_ideal_eq_sAcCFamily}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSABasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBBasedBranchEquiv}

Complete-locus equality also descends one level further, to the actual
two-variable curve ideal over the field generated by the shared parameter
tuple.  The induced complete function-field equivalence fixes that
coefficient field generator by generator and carries both endpoint
coordinates.  Thus all four repeated labels already define the same curve
relation over their literal rank-two parameter fields; extending these
equalities across the other six independent inputs is now the remaining
scalar-extension step:

{docstring AclGeom.pairIdeal_eq_over_commonParameter_of_familyIdeal_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSPairIdeal_eq_over_parameterField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAPairIdeal_eq_over_parameterField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUPairIdeal_eq_over_parameterField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBPairIdeal_eq_over_parameterField}

Independent scalar extension is handled at the function-field level.  A
base equivalence extends across matching algebraically independent tuples,
fixing each new coordinate.  If the new tuple is independent over both
complete endpoint fields, equality of the endpoint curve ideals therefore
survives over the enlarged coefficient field.  Algebraicity of the family
target does not destroy this independence:

{docstring AclGeom.adjoinIndependentEquivOfEquiv_generator}

{docstring AclGeom.auxiliary_independent_over_parameterPairField}

{docstring AclGeom.pairIdeal_eq_over_independentExtension_of_pairIdeal_eq}

The four alternative independent eight-coordinate presentations provide
the six complementary coordinates for `s`, `sA`, `u`, and `uB`.  Thus all
four repeated curve relations are equal after full independent scalar
extension.  For `s`, this enlarged field is literally the original common
eight-input coefficient field, giving the first repeated-arrow relation on
the exact common base:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSPairIdeal_eq_over_independentInputField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAPairIdeal_eq_over_independentInputField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUPairIdeal_eq_over_independentInputField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBPairIdeal_eq_over_independentInputField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSPairIdeal_eq_over_commonInputField}

Equality of a selected two-variable curve ideal also identifies the finite
extension from its source-coordinate field to its full branch field.  This
comparison lifts to the concrete normal closures and admits a deck
correction preserving the literal selected branch.  Applying it to the
exact common-base `s` ideal gives the first faithful selected-normal-cover
anchor, rather than merely an abstract chart equivalence:

{docstring AclGeom.FiniteCorrespondencePair.extensionEquivOfIdealEq}

{docstring AclGeom.FiniteCorrespondencePair.normalCoverEquivOfIdealEq_algebraMap}

{docstring AclGeom.FiniteCorrespondencePair.basedBranchEquivOfIdealEq_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSCommonCorrespondencePair_ideal_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSCommonBasedBranchEquiv_selected}

The other three coefficient changes are finite, not transcendental.  One
field adjoins the actual `sA`, `u`, and `uB` blocks to the common inputs;
it is finite over the common field, and its normal closure contains all
three named alternative eight-input fields.  Joint independence also
packages each repeated relation as a genuine finite correspondence over
its own alternative field.  Their equal ideals therefore yield three more
selected-branch-preserving normal-cover comparisons before transport into
the common normal coefficient field:

{docstring AclGeom.source_notMem_racl_independentExtension}

{docstring AclGeom.FiniteCorrespondenceFamilyMember.pairOverIndependentExtension}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientOverInput_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientNormalField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAAlternativeInputField_le_normalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUAlternativeInputField_le_normalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBAlternativeInputField_le_normalField}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedAlternativeBasedBranchEquiv_selected}

The finite comparison field is finite over each alternative base as well
as over the original common inputs.  Ambient closure equality survives an
embedding; applied to the three alternative eight-tuples, it shows that
all common and replacement coefficients are algebraic over each named
alternative field.  Finite adjoining and the tower law then make the same
common coefficient normal field a finite extension of all three bases.
This is the precise finiteness input for taking pairwise normal closures
after the formal source and the common source cover are adjoined, without
assuming that a curve ideal stays prime under algebraic base change:

{docstring AclGeom.algHom_racl_image_eq_of_racl_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonInput_racl_eq_repeatedSAInput}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonInput_racl_eq_repeatedUInput}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonInput_racl_eq_repeatedUBInput}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientOverRepeatedSA_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientOverRepeatedU_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientOverRepeatedUB_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientNormalOverRepeatedSA_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientNormalOverRepeatedU_finiteDimensional}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonCoefficientNormalOverRepeatedUB_finiteDimensional}

A reusable finite-compositum construction now adjoins such a coefficient
extension and two correspondence branches with the same source, then takes
their normal closure over that source-coordinate field.  It proves the
result finite and normal and records all three literal containments.  The
three alternative `sA`, `u`, and `uB` comparisons instantiate this
construction, producing pairwise normal ambient fields.  Equality of the
selected pair ideals also gives a source-linear equivalence between the two
literal branch fields.  Normality extends that embedding to a deck
transformation of the joint field, and the extension is proved to carry the
first displayed target to the second.  All three alternative comparisons
now instantiate these coefficient-bearing branch automorphisms:

{docstring AclGeom.FiniteCoefficientBranchCompositum.normalField_finiteDimensional}

{docstring AclGeom.FiniteCoefficientBranchCompositum.normalField_normal}

{docstring AclGeom.FiniteCoefficientBranchCompositum.coefficientExtension_le_normalField}

{docstring AclGeom.FiniteCoefficientBranchCompositum.firstBranch_le_normalField}

{docstring AclGeom.FiniteCoefficientBranchCompositum.secondBranch_le_normalField}

{docstring AclGeom.FiniteCoefficientBranchCompositum.branchEquivOfIdealEq}

{docstring AclGeom.FiniteCoefficientBranchCompositum.branchAutomorphismOfIdealEq}

{docstring AclGeom.FiniteCoefficientBranchCompositum.branchAutomorphismOfIdealEq_target}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACoefficientBranchNormalField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACoefficientBranchNormalField_contains}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCoefficientBranchNormalField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCoefficientBranchNormalField_contains}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCoefficientBranchNormalField_normal}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCoefficientBranchNormalField_contains}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSABranchAutomorphism}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBranchAutomorphism}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBBranchAutomorphism}

The alternative source fields are algebraically related to, but not nested
with, the literal common input field.  The comparison fields are therefore
renormalized once more over the common coefficient field with the same
formal source adjoined.  A finite-basis compositum proves finiteness over
this new base without pretending the two bases are nested; a second normal
closure supplies a canonical finite normal cover in the exact algebraic
closure used by the four strict triangles.  The two literal target branches
embed in that canonical cover.  The three rebased covers are joined to the
existing simultaneous source cover, and all four composition triangles are
then rebuilt, still strictly, on the enlarged source:

{docstring AclGeom.FiniteCoefficientBranchCompositum.normalField_finiteDimensional_over_coefficientSource}

{docstring AclGeom.FiniteCoefficientBranchCompositum.rebasedCanonicalCover}

{docstring AclGeom.FiniteCoefficientBranchCompositum.firstBranchEmbeddingInRebasedCanonical}

{docstring AclGeom.FiniteCoefficientBranchCompositum.secondBranchEmbeddingInRebasedCanonical}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSARebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedURebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.branchComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seBranchComparisonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaBranchComparisonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbBranchComparisonCoverCompositionTriangle}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcBranchComparisonCoverCompositionTriangle}

The canonical models used above now remember which conjugate came from the
literal ambient branch.  The ambient extension is included in its concrete
normal closure and transported to the canonical model; the inverse
comparison recovers the original inclusion.  The common composition source
cover exposes the selected left and direct branch normalizations, and these
distinguished embeddings are inherited by every larger source cover.  In
particular, all eight selected left/direct occurrences in the four-arrow
diagram now live in `branchComparisonSourceCover`:

{docstring AclGeom.FiniteCover.canonicalSelectedEmbedding}

{docstring AclGeom.FiniteCover.normalClosureOverEquivCanonical_symm_comp_selectedEmbedding}

{docstring AclGeom.finiteCoverCanonicalSelectedBranchIn}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.leftSourceFiniteNormalCover_le_sourceCover}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.directSourceFiniteNormalCover_le_sourceCover}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.selectedLeftBranchIn}

{docstring AclGeom.FiniteCorrespondencePair.FiniteCoverTriangle.selectedDirectBranchIn}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedLeftBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedLeftBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedLeftBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedLeftBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.seSelectedDirectBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAaSelectedDirectBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sbSelectedDirectBranchInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.sAcSelectedDirectBranchInComparisonSourceCover}

Branch comparison now has a chosen, coefficient-linear deck adjustment
rather than only an existential transitivity statement.  An equivalence of
branch domains first reparametrizes the second embedding; anchoring the
temporary algebra structure at the first embedding then extends the second
embedding to a distinguished deck transformation.  The exact common-base
`s` ideal supplies such a domain equivalence.  Its induced automorphism of
`branchComparisonSourceCover` fixes the full eight-input coefficient/source
field, carries the selected first `s` branch to the selected second branch,
and sends the displayed first middle coordinate to the displayed second
middle coordinate.  Rebased pairwise branches can likewise be inherited by
any larger canonical cover once the remaining coefficient-compatible domain
identifications are constructed:

{docstring AclGeom.NormalBranchEmbedding.reparametrize}

{docstring AclGeom.NormalBranchEmbedding.alignmentAut}

{docstring AclGeom.NormalBranchEmbedding.alignmentAut_smul_reparametrize}

{docstring AclGeom.FiniteCoefficientBranchCompositum.firstBranchEmbeddingInRebasedCanonicalIn}

{docstring AclGeom.FiniteCoefficientBranchCompositum.secondBranchEmbeddingInRebasedCanonicalIn}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSCommonBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSBranchAlignmentAut}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSBranchAlignmentAut_selectedTarget}

The first algebraic coefficient change is now transported without an
equality cast.  For the repeated `sA` block, an explicit equivalence of the
raw rebased source with the literal common source is extended to their
algebraic closures.  Both raw selected branches are identified with the
literal branch fields of the `sA·a=u` and `sA·c=uB` faces and transported by
that same semilinear equivalence.  After inclusion in
`branchComparisonSourceCover`, two distinguished deck transformations remove
only the remaining normal-closure choices.  Their action equations therefore
compare the actual selected face branches with the coefficient-comparison
branches over the full common coefficient/source field:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSARebasedSourceEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSARebasedClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSARawRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAFirstBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSASecondBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAFirstBranchEmbeddingInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSASecondBranchEmbeddingInComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAFirstClosureAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSASecondClosureAlignmentAut_smul}

The identical construction for the repeated direct output `u` uses the
strict composite pairs of the first two faces.  A carrier-invariance lemma
for adjoining one ambient generator identifies the raw branches with the
literal selected direct branches.  The source and closure equivalences then
transport both branches together, and two further deck transformations give
their exact alignment equations in the common cover:

{docstring IntermediateField.adjoin_singleton_carrier_eq_of_carrier_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedURebasedSourceEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedURebasedClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedURawRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUFirstBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUSecondBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUFirstClosureAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUSecondClosureAlignmentAut_smul}

Finally, the two strict composite pairs ending at `uB` undergo the same
transport.  The resulting equations align the selected direct branches of
the `s·b=uB` and `sA·c=uB` faces with their coefficient-comparison copies.
Hence all four repeated labels are now represented by coefficient-linear
selected-branch equations on one finite normal source cover:

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBRebasedSourceEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBRebasedClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBRawRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBFirstBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBSecondBranchEmbeddingInRebasedCanonicalCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBFirstClosureAlignmentAut_smul}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBSecondClosureAlignmentAut_smul}

The three alternative-base branch automorphisms are deliberately not
misidentified as deck transformations over the literal common source.  Each
is linear over its own alternative source presentation and can therefore
move coefficients that occur only in the original eight-input presentation.
The literal common source is included in the corresponding comparison normal
field, its image under the restricted ground-field automorphism is retained
as a named intermediate field, and the resulting source equivalence records
that semilinear coefficient change.  All three charts fix the formal curve
coordinate pointwise; only its coefficient presentation is allowed to move:

{docstring IntermediateField.algHomIntoOfLeRestrictScalars}

{docstring IntermediateField.imageUnderAutomorphism}

{docstring IntermediateField.equivImageUnderAutomorphism}

{docstring IntermediateField.equivImageUnderAutomorphism_eq_of_eq_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.commonSourceGenerator}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceImageEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSourceImageEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSourceImageEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceImageEquiv_generator}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSourceImageEquiv_generator}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSourceImageEquiv_generator}

These source equivalences extend to the chosen algebraic closures and hence
restrict to semilinear charts on the entire enlarged common source cover.
The restriction square is explicit on every base-field element, so the three
formal-generator equations survive unchanged at finite-cover level:

{docstring AclGeom.AlgebraicClosureTransport.FiniteNormalCover.mapEquiv_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceImageClosureTransport}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAImageBranchComparisonSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAImageSourceChart}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSAImageSourceChart_commonSourceGenerator}

The branch-faithful lift retains more data than the source square alone.
Each image source is mapped back into the original curve ambient, where it
and the original source both lie in the same pairwise normal field.  The
base equivalence and the actual alternative-base automorphism of that whole
field form one equivalence of nested extensions.  Its normal-closure lift
therefore retains the total-field comparison as well as the moved base:

{docstring IntermediateField.ambientImageUnderAutomorphism}

{docstring IntermediateField.extensionEquivUnderAutomorphism}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSourceExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSourceExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceNormalExtensionEquiv}

Finiteness transports across the full extension square.  Passing from the
canonical models back to the concrete normal closures gives a semilinear
normal-cover equivalence over the moved source.  As with the earlier
selected curve branches, a target deck correction is essential: it makes
the comparison preserve the literal embedded copy of the entire pairwise
total field.  The three alternative comparisons now expose these based
normal-cover transports and their exact selected-branch equations:

{docstring IntermediateField.ambientImageUnderAutomorphism_finiteDimensional}

{docstring AclGeom.FiniteCover.normalCoverEquivUnderAutomorphism}

{docstring AclGeom.FiniteCover.basedBranchEquivUnderAutomorphism}

{docstring AclGeom.FiniteCover.basedBranchEquivUnderAutomorphism_selected}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACoefficientBranchNormalField_finiteDimensional_overCommonSource}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonSourceBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonSourceBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonSourceBasedBranchEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedCommonSourceBasedBranchEquiv_selected}

The concrete based comparisons and the canonical comparison covers now
meet through an explicit equality-based bridge.  The literal common source
and the raw rebased source present the same intermediate field, so they give
an equivalence of the corresponding total extensions.  Its normal lift,
followed by the already chosen raw-to-common algebraic-closure transport,
identifies the direct canonical normal closure with the named rebased cover
which is already a subcover of the simultaneous source compositum:

{docstring AclGeom.FiniteCover.finiteDimensional_of_eq}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonToRawRebasedExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonToRawRebasedExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonToRawRebasedExtensionEquiv}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedSACommonCanonicalCoverEquivRebased}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUCommonCanonicalCoverEquivRebased}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.repeatedUBCommonCanonicalCoverEquivRebased}

The bridge also remembers its base algebra map.  Equality-induced extension
equivalences compute to the canonical equality transport; composing that
map with the inverse raw-to-common source transport is literally the
identity.  The mapped normal-lift interface packages this cancellation as an
algebra equivalence and then transports the distinguished embedding of the
entire finite extension:

{docstring AclGeom.FiniteCover.ExtensionEquiv.ofEq_baseEquiv}

{docstring AclGeom.FiniteCover.NormalExtensionEquiv.mappedNormalEquiv}

{docstring AclGeom.FiniteCover.NormalExtensionEquiv.mappedNormalEquiv_algebraMap}

{docstring AclGeom.FiniteCover.NormalExtensionEquiv.mappedNormalAlgEquiv}

{docstring AclGeom.FiniteCover.ExtensionEquiv.mappedNormalEquiv}

{docstring AclGeom.FiniteCover.ExtensionEquiv.mappedNormalAlgEquiv}

{docstring AclGeom.FiniteCover.ExtensionEquiv.mappedCanonicalSelectedEmbedding}

{docstring AclGeom.FiniteCover.ExtensionEquiv.mappedCanonicalSelectedEmbedding_algebraMap}

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

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceSemanticSourceCover}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.referenceNormalCoverToReferenceSemanticSourceCover_algebraMap}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceEInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceAInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceBInSemanticSourceRingHom}

{docstring AclGeom.QWitness.PsiCurveFourArrowCommonSourceRealizations.toReferenceCInSemanticSourceRingHom}

The exact cross-edge coherence interface is separated from the construction
of the reference charts.  Four independently typed triangles give a
semantic four-arrow diagram precisely when their twelve cover fields are
identified with three reference fields and the repeated `s`, `sA`, `u`,
and `uB` arrows agree after conjugation:

{docstring AclGeom.FieldEquiv.CompositionTriangle}

{docstring AclGeom.FieldEquiv.FourTriangleReference.toFourArrowDiagram}

{docstring AclGeom.QWitness.PsiCurveFourArrowRealizations.ReferenceAlignment}

{docstring AclGeom.QWitness.PsiCurveFourArrowRealizations.ReferenceAlignment.right_cancellation}

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
