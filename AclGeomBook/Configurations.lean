/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.Correctness
import AclGeom.Config.JAssembly
import AclGeom.Config.Transport
import AclGeom.Config.PsiLattice
import AclGeom.Config.ShiftedAffineMeets
import AclGeom.Config.RemainingAffineMeets
import AclGeom.Config.AffineGridNormalization
import AclGeom.Geometry.FormulaInvariance
import AclGeom.Counterexamples.QRefutation
import AclGeom.Counterexamples.QDegenerate
import AclGeom.Closure.RationalFunctions
import AclGeom.Correspondence.WeightedSupport
import AclGeom.Correspondence.MultiplicativeQuotient
import AclGeom.Correspondence.DifferenceCocycle
import AclGeom.Correspondence.AffineRelocation
import AclGeom.Correspondence.MultiplierCurve
import AclGeom.Correspondence.FiniteCurveLoci
import AclGeom.Correspondence.MultiplierPrimeCurve
import AclGeom.Correspondence.AffineLocusCommutation
import AclGeom.Correspondence.AffinePointNormalization
import AclGeomBook.Configurations.GroupChunkRecord

/-!
# Configuration relations and their current formalization boundaries

Verso exposition of the proved semantic and conditional configuration results.
Guarded extraction, literal parameter-fixing relocation and completeness stay explicit.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Configurations: the geometric Q, Q′, and J" =>

%%%
tag := "configurations"
%%%

The configuration layer (blueprint §§6–7, milestone M4) defines the finite
geometric predicates through which the field structure will be recovered
from the geometry alone. Soundness, semantic J assembly, generic finite-formula
invariance and concrete geometric invariance are proved. Unguarded Q
completeness/extraction and geometric Q
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

The first necessary incidences for genuine meet elimination are now proved
by finite-rank counting and exchange. Every Psi witness has P≠S and Q≤B;
I≠D also gives P≤A and Q≠T. The actual degeneration has Q=T, so the last
guard cannot be dropped. The separate proposed P-incidence degeneration
is hand-only and is not a formal result:

{docstring AclGeom.QWitness.Psi.P_le_A}

{docstring AclGeom.QWitness.Psi.P_ne_S}

{docstring AclGeom.QWitness.Psi.Q_le_B}

{docstring AclGeom.QWitness.Psi.Q_ne_T}

The ratio guard also puts D outside the full parameter join A∨B∨C, hence
D≠S, and gives F≠U. The first supplies L1a's shared-point non-membership;
the second supplies the multiplier projection prerequisite for the proposed
finite-fibre/linearity argument. They construct no relocation or curve action:

{docstring AclGeom.QWitness.Psi.D_not_le_ABC}

{docstring AclGeom.QWitness.Psi.D_ne_S}

{docstring AclGeom.QWitness.Psi.F_ne_U}

Two further necessary consequences of the same ratio guard are now proved
(L0c, #27): G≠T and H≠S. G=T forces H=S and then I=D; H=S alone makes
the defining meets of I and D equal. Neither theorem needs a coordinate
chart or algebraic closedness:

{docstring AclGeom.QWitness.Psi.G_ne_T}

{docstring AclGeom.QWitness.Psi.H_ne_S}

The actual PRIVATE guarded two-family consumer uses these two guards
along with P≠S, D≠S, F≠U and Q≠T. Given an explicit independent initial
chart for A/B/C/S/T/U/X/Y/Z, it derives all 16 raw memberships, six
non-memberships and three nonconstancies from the actual Ψ equations
and point representatives. Every raw field input of the accepted
two-family remaining-row composition is derived; none is supplied.
Its seven old helper blocks and original TYPE/proof remain byte-exact
after naming the original example. One new consumed private point bridge
handles the six non-memberships. Both original curves precede ALL supplied
fresh INPUT families; base/ambient ACF and those families stay explicit.
Only the two necessary lattice guards are newly public. Initial chart
existence, INPUT existence/enlargement/descent, combined generators,
actions, linearity, extraction and all completeness remain open;
#11 and frozen117 are independent obligations.

A full affine-grid presentation is now derived conditionally from the
actual configuration (P4, #27). Given Ψ, I≠D, base/ambient ACF, an explicit
independent initial chart for A/B/C/S/T/U/X/Y/Z and two supplied fresh
INPUT families, the new producer derives all three joins and fifteen
points. Every raw field membership, non-membership and nonconstancy is
derived from the guarded witness and chart; no normal-form or
OUTPUT-freshness oracle is supplied:

{docstring AclGeom.QWitness.Psi.hasAffineGridCoordinates_of_chart_supplied_inputs}

The original F prime curve/span precedes ALL first INPUT families.
After the first family the producer obtains κ in k and the original
H-inverse prime curve/span, which precedes ALL second INPUT families.
After the second family it obtains η in k and the chart
a, b+(a-1)κ-η, c, d+(c-1)κ+(c-1)η, x-κ. Constant translates give
P/R/X/Y/Z; triangular changes of the second generators give A/B/C.
The other rows and final independence come from the guarded two-family
composition. All fifteen private helpers are consumed; the old guarded
consumer's TYPE/proof is byte-exact after naming it.

An actual PRIVATE consumer applies the existing Q-semantic theorem
only after deriving this full grid, with the same hypotheses and
curve/span-before-ALL-INPUT nesting. A separate canonical-table example
jointly realizes Ψ, I≠D and all nine initial-chart equalities without
ACF. This checks a genuine initial chart, without constructing the
fresh INPUT families or a chart for an arbitrary witness. The six
generator points of A/B/C are not constrained; no common-shift or
uniqueness theorem is claimed. Initial chart existence, INPUT
existence/enlargement/descent, actions, classification and scheme bridges,
guarded and unconditional extraction and all completeness remain open.
Issue #11 and frozen117 remain independent obligations.

The unchanged pure rank bridge now lives in Geometry.FiniteRank, so this
module imports only Config.Psi:

{docstring AclGeom.rankEq_iff_eRk}

These are necessary lattice consequences (L0, #27). Meet elimination,
linearity and action presentation/classification remain open.

The first difference-cocycle data lemma is also proved (L1a, #27). Two affine
presentations of one value sharing p and δ have translation difference
algebraic over their multipliers. Independence, freshness and the shared
closure memberships and non-memberships are explicit hypotheses; this theorem
does not construct the second presentation. The separate fixed-five relocation
below supplies it when a fresh parameter is given; the ensuing linearity and
coordinate-extraction argument remain open:

{docstring AclGeom.sub_mem_racl_of_affine_value_eq}


Literal relocation is now proved for a supplied affine presentation (L1b, #27).
Under independence of a,b,x,c and the explicit p,δ,f closure conditions,
a given a₀ fresh over those four yields a′x′+b′=ax+b with p,ax+b,δ,c,f
literally fixed and their joint vanishing ideal with the moved triple unchanged.
The new multiplier is algebraic over p,ax+b,c,a₀ and fresh over a,b,x,c;
a′ need not equal a₀. The existence of a₀ and the original affine coordinates
remain caller obligations. Together with D≠S this supplies L1a's constructed
consumer; it also preserves the same c/f fibre relation for the proposed
linearity step. No curve action, linearity or guarded completeness is proved:

{docstring AclGeom.exists_affine_relocation}


The multiplier-curve prerequisites are also proved (L2a, #27). Equality of
joint vanishing ideals transfers polynomial images, so a literal fixed-five
relocation keeps the same locus of (f,a′c,x′), including f∈acl(a′c,x′),
f∉acl(a′c) and x′∈acl(a′c,f). For independent A,B,M,X and
f∈acl(M,X) outside acl(M), the source projection M is generic over A,B,f.
This supplies the existing prime-curve equation theorem over k(A,B,f).
The target X may belong to that parameter field (for example f=X);
no target-genericity or component/action/linearity assumption is used.
The finite-component/stabilizer and iterated-freshness arguments remain open:

{docstring AclGeom.idealOf_aeval_comp_eq_of_idealOf_eq}

{docstring AclGeom.affine_multiplier_curve_of_joint_ideal}

{docstring AclGeom.multiplier_projection_genericity}

The shared prime multiplier equation and uniform curve-locus bound are
now proved (L2b, #27). From L1b's original independence of a,b,x,c,
the derived multiplier coordinates a,b,ac,x are independent. L2a and the
existing FamilyCover common-parameter theorem give the same prime pair
ideal over the actual field k(f) for a literal fixed-five relocation:

{docstring AclGeom.exists_prime_multiplier_curve_of_joint_ideal}

For a fixed nonzero planar equation F, all generic dependent pair ideals
lie in a finite set whose cardinality is at most totalDegree F. Each prime
generator is associated to a factor of F, and the number of factors is
bounded by that degree. Injective coefficient extension preserves the
degree, so the bound can be fixed before selecting a larger coefficient
field. Actual private checks compose the published shared-equation producer
with the color bound after extension. Transcendence and algebraic dependence
over that larger field remain explicit inputs; their geometric producers,
ambient enlargement/descent, stabilizers and linearity remain open.
A reducible equation can have distinct curve ideals, so no geometric
primality after scalar extension is asserted:

{docstring AclGeom.exists_curve_ideal_colors}

{docstring AclGeom.finite_curve_ideals_of_relation}


Finite-stage scale genericity is now proved (L2c, #27). For a supplied
sequence of multipliers fresh over the original a,b,x,c and all earlier
multipliers, c stays outside the relatively closed final coefficient field
L=acl(a,f,all selected multipliers). This theorem proves non-membership;
it does not supply the fresh sequence:

{docstring AclGeom.scale_notMem_racl_of_fresh_multipliers}


The literal relocation producer also preserves freshness over arbitrary
supplied extra data T (L2d, #27), when the given input a₀ is fresh over
the original a,b,x,c together with T. The same joint ideal, controlled
algebraicity, p/δ memberships and affine value are returned:

{docstring AclGeom.exists_affine_relocation_fresh_over}

An actual private consumer now starts with one supplied sequentially fresh
INPUT family. It constructs each relocation independently, derives freshness
of the OUTPUT multipliers over all earlier outputs from their controlled
algebraicity, and applies the scale and original-equation color producers.
One original prime F/span is fixed before all sizes and input families.
The same check also derives every original-versus-relocated translation
difference in the common final field L, using L1a with its separate explicit δ outside acl(a) input.
No literal joint ideals or output-freshness oracle are supplied in that
consumer; its ambient input-family existence and descent remain open.
Only the stronger single-relocation producer is a new library theorem.

Actual private checks now derive each multiplier's transcendence and its
target's algebraic dependence over that same L from this non-membership,
sequential freshness and the literal fixed-five joint ideals. They fix one
prime equation F and the ORIGINAL pair-ideal span before every family size
and family choice, then bound the common color set by totalDegree F after
coefficient extension. The original equation is part of the conclusion;
an unrelated prime of arbitrarily large degree cannot supply the bound.
These composition checks are private, rather than additional library
theorems. Fresh relocation existence, ambient enlargement/descent,
stabilizers, linearity and guarded completeness remain open.

Finite equal-ideal fibres are now proved without a genericity or algebraic
closure hypothesis (B1, #27). If x is algebraic over k(m), all z with
the same pair ideal as (m,x) belong to the finite root set of its minimal
polynomial over k(m):

{docstring AclGeom.finite_same_fibre_ideals}

An actual private check derives finite coefficient-field vertical translations,
polynomial conjugation by same-color relocation maps, and a transcendental
ratio over the original base field. The finite power orbit forces every such
translation to vanish in every characteristic. Its full-family consumer
constructs the relocations from supplied fresh ambient INPUTS, derives OUTPUT
freshness and original-a cocycles, and fixes the original F/span before every
family size and choice. All pair algebraicity and scaling-preservation data
are derived over the same common L. The separate δ outside acl(a) input
remains explicit. This checks zero L-coefficient translations at every
equal-color pair; it does not select equal colors or prove commutators,
common centers, linearity, ambient input existence/descent or completeness.
Only the finite-fibre theorem is a new public library result.

The concrete affine-locus commutation balance is now a library theorem
(B2, #27). Two maps with coefficients in the same L preserve the SAME
pair ideal, x is algebraic over L(m), and one multiplier is transcendental
over the ORIGINAL k. Three polynomial-image transfers derive a preserving
vertical translation; finite fibres and the characteristic-free power orbit
force it to vanish. No action or commutator oracle is supplied:

{docstring AclGeom.affine_locus_commutation_balance}

An actual private full-family check fixes the original prime F/span BEFORE
every supplied fresh INPUT family. At size 2 totalDegree F + 1, it constructs
the relocations and derives OUTPUT freshness, original-a cocycles, common-L
colors, and a selected equal-color triple with the least index as common base.
Both preserving maps, coefficient membership, larger-base algebraicity and
the transcendental ratio are derived from this data. The balance gives
the same affine intersection center for the two pairs, so these three
relocated lines are concurrent. The separate δ outside acl(a) input stays
explicit. This is one selected triple for each supplied input family.
Such a family may not exist at small transcendence degree. Selection and
common centers are actual PRIVATE compositions; the new public theorem is
the concrete commutation balance. Ambient input existence/enlargement/descent,
four-point/C4 linearity, extraction and completeness remain open.

Pairwise relocation differences are now proved (B3, #27). The first
presentation has the actual fixed-five joint ideal, both tuples have the
explicit p/δ memberships and shared affine value, and the later multiplier
is fresh over the original a,b,x plus the first multiplier. Joint-ideal
transport derives independence and p/δ non-memberships at the first tuple;
exchange and L1a give the difference algebraic over the two multipliers
alone. A second joint ideal or separate first freshness is not needed:

{docstring AclGeom.sub_mem_racl_of_two_relocations}

The actual private full-family consumer derives all those inputs from the
constructed relocations, then every ordered pairwise cocycle. Its selected
equal-color triple has the common center algebraic over the ORIGINAL k.
The third pair shares the same center by field algebra; three independent
closure intersections remove every multiplier. Both orders of the later
selected indices are handled. No pairwise-cocycle or constant-center oracle
is supplied. The original F/span still precedes every supplied fresh INPUT
family of size 2 totalDegree F + 1, and δ outside acl(a) remains explicit.
Only pairwise cocycles are a new public theorem; constant centers are
PRIVATE compositions. P/Q normalization and compatibility, the remaining
meets, ambient input existence/enlargement/descent, action extraction and
completeness remain open. Transferring an affine shift back to a k-joint
ideal needs the center in k; algebraic closedness of k is still to be used
in that separate P-normalization consumer.

The concurrent-P closure statement is now proved (P1, #27). Given an
original-base algebraic center, p membership at both pairs, p outside the
first multiplier's closure, later freshness over the first multiplier and
p, and actual shifted concurrence, exchange and the independent-variable
intersection give p interalgebraic with the shifted first intercept.
Every hypothesis is explicit; this closure lemma is characteristic-free
and needs no algebraic-closedness or joint ideal:

{docstring AclGeom.racl_singleton_eq_of_concurrent}

The actual private 575-line family consumer derives every public input
from constructed relocation outputs and its selected triple. It retains
the original F/span before every supplied fresh INPUT family. Under
explicit algebraic closedness of both k and the ambient field, the derived
original-base algebraic center comes from a constant in k. An actual
k-polynomial image of the literal fixed-five joint ideal then transfers
both closure directions to the original: p is interalgebraic with
b + (a - 1) times that constant. No original-P or shifted-P normal-form
oracle is supplied. The separate δ outside acl(a) remains explicit, and
both orders of the selected later indices are handled.
Only the conditional concurrent-P closure lemma is a new public theorem;
the original-P transfer and full-family chain remain PRIVATE. Q
normalization and the combined generator presentation, remaining meets,
ambient input existence/enlargement/descent, actions, linearity, extraction
and all completeness remain open.

The shifted D/F/R rows are now proved conditionally (P2, #27). Starting
with five independent original coordinates and a constant κ in k, the
triangular table shift preserves algebraic independence. If P has the
explicit closure of the shifted intercept, raw D/F/R incidences and
non-memberships determine their singleton closures. The existing table
soundness meets and exchange prove the three rows. No algebraic
closedness is needed by these two public theorems:

{docstring AclGeom.algebraicIndependent_table_shift}

{docstring AclGeom.racl_shifted_D_F_R_of_normalized_P}

The genuine PRIVATE 598-line family consumer derives the four-coordinate
projection from original five-variable independence. It retains the
original F/span before EVERY supplied fresh INPUT family, constructs the
relocations, selects a same-color triple, and derives all cocycles,
concurrence, the original-base center and the original-P closure as in P1.
Under explicit k/ambient ACF it then derives the starred independence
and D/F/R rows from the raw original incidences. No P, D/F/R normal-form
or OUTPUT-freshness oracle is supplied. A separate actual zero-origin
example uses arbitrary raw D/F/R representatives, with P equal to the
point of b and the constant zero; it requires no ACF.
Only the two conditional table-shift/meet theorems are public. The full
family chain remains PRIVATE and supplied INPUT existence may fail at
small transcendence degree. E/G/H/I/Q, the combined generator
presentation, ambient existence/enlargement/descent, actions, linearity,
extraction and all completeness remain open.

The reusable supplied-input P producer is now public (P3a, #27).
For four independent coordinates and explicit raw p/δ/f incidences and
non-memberships, it fixes the original prime multiplier equation BEFORE
every supplied fresh INPUT family of size twice its total degree plus one.
Under explicit algebraic closedness of k and the ambient field it
constructs relocations, selects an actual equal-color triple, derives all
cocycles, concurrence and the original-base algebraic center, and then
transports the derived normalization to the original P:

{docstring AclGeom.racl_normalized_P_of_supplied_fresh_inputs}

The actual PRIVATE 96-line reciprocal-Q consumer derives the independent
inverse tuple and all inverse-closure conversions, then applies the SAME
producer to c, d, b, inverse(ac), q, g, inverse(h). It fixes the original
Q-side curve of (inverse(a), b) over k(inverse(h)) before ALL second
fresh INPUT families and derives q interalgebraic with d + (c - 1)η.
No Q or H normal-form hypothesis is supplied.

The actual PRIVATE 215-line two-family composition first derives κ and
P from the first family, then derives the P2 D/F/R rows and starred
independence. It transports the raw q/g/h incidences using these DERIVED
closures before the second producer gives η and Q. Its nested quantifier
order is original P curve, every P INPUT family, κ, original Q curve,
every Q INPUT family, η. Neither an output-freshness nor a P/Q/H normal-form
oracle is supplied. The q/g/h non-memberships remain EXPLICIT raw
consequences of the guard; deriving them from an actual Ψ witness is still
required. Only the reusable conditional P producer is a new public result.
The reciprocal and two-family chains are PRIVATE, with k/ambient ACF and
supplied INPUT families. Input existence may fail at small transcendence
degree. The remaining E/G/H/I rows, combined generator presentation,
initial action chart, ambient enlargement/descent, actions, extraction
and all completeness remain open. No common-shift or uniqueness theorem
is added; #11 and frozen117 remain independent obligations.

The remaining G/H/I/E rows are now proved conditionally (P3b, #27).
For η in k the coordinate change sends b to b - η and d to
d + (c - 1)η, preserving original five-variable independence and the
closures of P/R/Y/Z. Given the normalized P/Q/R closures, raw G/H/I/E
incidences and nonconstancy determine the four singleton closures.
The soundness meets give G first, H from G, I from H, and E from its
separate joins. H uses the raw A-plane. Neither public theorem needs
algebraic closedness:

{docstring AclGeom.algebraicIndependent_table_Q_shift}

{docstring AclGeom.racl_shifted_G_H_I_E_of_normalized_P_Q}

The genuine PRIVATE 274-line two-family consumer derives κ/P, then
P2 D/F/R, then η/Q by the SAME producer at the inverse tuple. Each
original prime curve/span precedes ALL corresponding supplied INPUT
families. It transports original raw I/E incidences by base translations
to the κ-absorbed chart before deriving G/H/I/E and final independence.
All six older helper blocks remain byte-exact; one consumed pair-translate
helper supplies four raw transports. No P/Q/H or remaining-row normal-form
or OUTPUT-freshness oracle is supplied. k/ambient ACF, both supplied INPUT
families, strong Q-producer non-memberships and raw I/E nonconstancy stay
explicit. A separate actual zero-origin example handles arbitrary raw
G/H/I/E representatives without ACF or helpers.
Only the conditional shift/meet statements are public; the two-family
chain remains PRIVATE. Initial chart, actual guarded-Ψ input derivation,
fresh INPUT existence/enlargement/descent, combined generator presentation,
actions, linearity, extraction and all completeness remain open.
No uniqueness or common-shift theorem; #11 and frozen117 are untouched.

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
