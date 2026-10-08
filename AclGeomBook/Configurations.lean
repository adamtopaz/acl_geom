/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.Correctness
import AclGeom.Config.JAssembly
import AclGeom.Config.Transport
import AclGeom.Geometry.FormulaInvariance
import AclGeom.Counterexamples.QRefutation
import AclGeom.Counterexamples.QDegenerate
import AclGeom.Closure.RationalFunctions
import AclGeom.Correspondence.WeightedSupport
import AclGeom.Correspondence.MultiplicativeQuotient
import AclGeomBook.Configurations.GroupChunkRecord

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Configurations: the geometric Q, Q′, and J" =>

%%%
tag := "configurations"
%%%

The configuration layer (blueprint §§6–7, milestone M4) defines the finite
geometric predicates through which the field structure will be recovered
from the geometry alone. Soundness, semantic J assembly, generic finite-formula
invariance and concrete geometric invariance are proved. Unguarded Q completeness/extraction and geometric Q
projection are refuted even over ACF pairs; guarded Q completeness and ACF
Q′/J completeness remain open (#27). Conditional
interpretation and the public lattice-form target keep both perfected
J-completeness inputs explicit. The arbitrary-field Q/Q′ versions have
concrete characteristic-zero Lean refutations. This chapter distinguishes
these results from the still-open guarded extraction and group/action engine.

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

The blueprint's generic recursion method is now formalized. Finite lattice terms
and formulas cover equality/order, finite ranks, Boolean operations and point
quantifiers; assignments extend at index zero under each quantifier. This avoids
encoding the full countable algebraic-closure language:

{docstring AclGeom.GeometryTerm}

{docstring AclGeom.GeometryFormula}

{docstring AclGeom.GeometryTerm.eval}

{docstring AclGeom.GeometryFormula.Holds}

Term evaluation commutes with a lattice isomorphism. Structural recursion on
formulas then preserves satisfaction, using the bijection of points in the
existential and universal cases. The proved presentation bridge gives the same
result for a closure-preserving equivalence of point geometries:

{docstring AclGeom.GeometryTerm.eval_map}

{docstring AclGeom.GeometryFormula.holds_map_iff}

{docstring AclGeom.GeometryFormula.holds_pointEquiv_iff}

Tuple incidence and collinearity are actual instances of this recursion theorem:

{docstring AclGeom.memCl_map_iff}

{docstring AclGeom.col_map_iff}

This completes G1c (#6). The separate concrete transport of partial quadrangles,
Psi and Q/Q′/J remains proved by its existing route. Guarded extraction and the
group/action engine remain open; the frozen M4a chain is unchanged.

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

# Configuration naturality
%%%
tag := "configuration-naturality"
%%%

An arbitrary order isomorphism of closed-subfield lattices, across
independent bases and universe levels, preserves the configurations.
This is the first part of naturality in blueprint
`interpreted-reconstruction` and checklist I6b1.

Finite-rank clauses and injectivity transport partial quadrangles:

{docstring AclGeom.IsPartialQuadrangle.map}

Every one of the twenty-one raw witness points is mapped. The three
rank-two joins commute with the lattice isomorphism:

{docstring AclGeom.QWitness.map}

{docstring AclGeom.QWitness.map_A}

{docstring AclGeom.QWitness.map_B}

{docstring AclGeom.QWitness.map_C}

All twenty-four actual clauses of the witness predicate transport,
including its three universal point clauses and partial quadrangle:

{docstring AclGeom.QWitness.Psi.map}

The multiplication diagram and both geometric configuration relations
are preserved and reflected:

{docstring AclGeom.MulDiagram.map}

{docstring AclGeom.qGeom_map_iff}

{docstring AclGeom.q'Geom_map_iff}

Their conjunction gives geometric J invariance:

{docstring AclGeom.jGeom_map_iff}

These arguments use only joins, meets, order, finite rank and bijective
point transport. They need no perfection, semantic completeness,
rank-five bound or fresh element. Corrected interpretation-relation transport,
quotient-carrier and geometric operation-graph naturality are proved in the
interpretation chapter; actual inducing existence and the public lattice-form
target are proved conditionally in the reconstruction chapter. Both exact
perfected ACF J-completeness inputs remain explicit. Unconditional R1/R2,
completeness/reconstruction, guarded geometric projection completeness and broader
point/automorphism/functorial variants remain open. The frozen M4a record
and literal source obligations are preserved.

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
which specializes at two distinct points of the atom's closure and recovers
both line coefficients inside that closure — contradicting their independence.
The closure is an infinite field because it contains a transcendental element:

{docstring AclGeom.infinite_racl_singleton}

{docstring AclGeom.line_relation_specialize}

{docstring AclGeom.notMem_racl_line}

Consequently every clause holds over any base field. The packaged statement
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
base field, given a supply of fresh elements over small sets.

# Semantic assembly of J
%%%
tag := "j-semantic-assembly"
%%%

Over an algebraically closed pair of rank at least five, a semantic
`Q` witness and the two semantic `Q′` witnesses of the `J` projections
assemble to one semantic `j`-tuple. Their additive and multiplicative
correspondences align the representatives through affine Frobenius
rigidity and the shifted-binomial identity:

{docstring AclGeom.shift_binomial_poly}

{docstring AclGeom.exists_racl_add_eq_of_shifted}

{docstring AclGeom.jSem_of_qSem_q'Sem}

This proves the semantic assembly. Geometric `J` completeness still
requires guarded geometric `Q` completeness and geometric `Q′` completeness over the algebraically
closed pair as explicit hypotheses:

{docstring AclGeom.JCompletenessACF}

{docstring AclGeom.jCompletenessACF_of_completeness}

Neither input is discharged. The previous unguarded Q input is refuted even
over ACF pairs (#27). Its replacement names both necessary ratio inequalities,
already supplied by multiplication distinctness in J. JCompletenessACF and
the public conditional reconstruction target have unchanged types.

# The affine-grid extraction boundary
%%%
tag := "affine-grid-boundary"
%%%

The completeness half reduces to blueprint Lemma 8.5.  Its table (8.5) lists
all twenty-one points, but `Psi` sees the generators of the rank-two elements
`A, B, C` only through their joins, so exchanging two generators preserves
`Psi`:

{docstring AclGeom.QWitness.Psi.of_eq}

{docstring AclGeom.QWitness.Psi.swapA}

Consequently the literal reading of the table, equality with the verified
table witness in every field, cannot be the conclusion of an extraction
theorem:

{docstring AclGeom.not_forall_psi_hasLiteralTableCoordinates}

The corrected coordinate interface constrains the three joins and the fifteen
remaining points.  Witnesses with these coordinates satisfy `Psi`, the
swapped table witness has them, and they force the free outputs to be the
semantic quadruple `([b], [ax], [b+ax], [b/(ax)])`; the reciprocal ratio
defines the same closed point:

{docstring AclGeom.QWitness.HasAffineGridCoordinates}

{docstring AclGeom.QWitness.HasAffineGridCoordinates.psi}

{docstring AclGeom.QWitness.hasAffineGridCoordinates_swapA}

{docstring AclGeom.QWitness.affineGrid_output_independent}

{docstring AclGeom.QWitness.qSem_of_hasAffineGridCoordinates}

The generator-swap repair did not resolve all degeneracies. Change only
`Q=E=G=T`, `H=S`, and `I=D` in the independent table. The actual Psi still
holds, with ratio output equal to its denominator. Semantic Q requires
that point to differ from both inputs:

{docstring AclGeom.QSem.ratio_ne}

{docstring AclGeom.QSem.ratio_ne_fst}

{docstring AclGeom.qWitnessDegenerate}

{docstring AclGeom.qWitnessDegenerate_psi}

{docstring AclGeom.not_forall_qGeom_imp_qSem_of_five_indep}

Thus the legacy unguarded ACF targets are refuted (#27), rather than open.
They remain as explicit refuted propositions for the negative lemmas and
original-source provenance:

{docstring AclGeom.AffineGridExtraction}

{docstring AclGeom.QCompletenessACF}

{docstring AclGeom.not_qCompletenessACF}

{docstring AclGeom.not_affineGridExtraction}

The unguarded geometric Q projection to J also fails: J's actual
multiplication diagrams separate the ratio from each input. This example
does not refute JCompletenessACF, whose distinctness already gives both guards:

{docstring AclGeom.Q'Geom.ne}

{docstring AclGeom.Q'Geom.snd_ne_fst}

{docstring AclGeom.not_forall_qGeom_imp_exists_jGeom_of_five_indep}

The corrected candidates require `I≠D` and `I≠P`. Both are necessary;
sufficiency is unproved. These are open propositions, with no project axiom:

{docstring AclGeom.GuardedAffineGridExtraction}

{docstring AclGeom.GuardedQCompletenessACF}

{docstring AclGeom.GuardedAffineGridExtraction.guardedQCompletenessACF}

Guarded correctness and projection follow conditionally from the explicit
open guarded completeness input and proved soundness:

{docstring AclGeom.qGeom_and_ne_iff_qSem_of_five_le_trdeg}

{docstring AclGeom.qGeom_and_ne_iff_exists_jGeom}

Original q-correct and extraction wording from ed61c33 is preserved in the
blueprint as refuted historical provenance. All 44 original proof blocks
remain byte-exact, with explicit qualifications before the affected sketches.
No guarded extraction, multiplication converse or J completeness proof is
claimed. The frozen 117-item M4a record remains frozen.

Both arbitrary-field Q/Q′ consequences are refuted in Lean by the
rational-function-field example in #25. Over k(X₀,…,X₄) for every
characteristic-zero field k, the displayed tuples satisfy the actual
geometric predicates and have no semantic representatives.

The explicit table and quadrangle witnesses descend from an algebraic
closure through the supplied-instance reflection:

{docstring AclGeom.qGeom_rat}

{docstring AclGeom.qPrimeGeom_rat}

The semantic obstruction fixes one curve polynomial before both
scalings. Characteristic zero forces the ratio, and (2,1)-weighted
homogeneity makes s/x² algebraic:

{docstring AclGeom.isAlgebraic_div_sq_of_qLocus}

The Q′ ratio uses the multiplicative-quotient theorem with a fresh
independent element:

{docstring AclGeom.point_div_eq_of_q'Pair}

Algebraic elements of a multivariate rational function field are
constants, and a nonzero constant times a variable cannot be a square:

{docstring AclGeom.mem_range_algebraMap_of_isAlgebraic_fractionRing}

{docstring AclGeom.not_isSquare_algebraMap_C_mul_X}

A `(2,1)`-weighted-homogeneous relation makes `s/u²` algebraic. Dividing
two multiplicative coset equations with common nonzero exponents makes
the coordinate quotients interalgebraic:

{docstring AclGeom.isAlgebraic_div_sq_of_isWeightedHomogeneous}

{docstring AclGeom.interalgebraic_div_of_coset_equations}

{docstring AclGeom.MulCorrSetup.interalgebraic_div}

Their concrete consumer makes X₀/x² transcendental for every
nonzero x, giving both refutations with no completeness hypothesis:

{docstring AclGeom.not_isAlgebraic_X_div_sq}

{docstring AclGeom.not_forall_qGeom_imp_qSem}

{docstring AclGeom.not_forall_q'Geom_imp_q'Sem}

The reflection applies to these supplied table and quadrangle witnesses.
General witness descent and algebraically closed geometric completeness
remain open. The four-way J target retains its explicit ACF inputs.

{include 0 AclGeomBook.Configurations.GroupChunkRecord}
