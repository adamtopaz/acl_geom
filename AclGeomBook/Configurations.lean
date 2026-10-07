/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.Correctness
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

None of this proves completeness.  The open geometric content of Lemma 8.5,
over algebraically closed fields, is stated without being assumed or
axiomatized, together with the weaker witness-level completeness that the
completeness direction of `Q` actually uses:

{docstring AclGeom.AffineGridExtraction}

{docstring AclGeom.affineGridExtraction_iff}

{docstring AclGeom.QCompletenessACF}

{docstring AclGeom.qGeom_iff_qSem}

{include 0 AclGeomBook.Configurations.GroupChunkRecord}
