/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Config.Correctness
import AclGeom.Config.GuardedAffineGrid
import AclGeom.Config.Completeness
import AclGeom.Config.JAssembly
import AclGeom.Config.Transport
import AclGeom.Config.PsiLattice
import AclGeom.Config.ParameterField
import AclGeom.Config.ShiftedAffineMeets
import AclGeom.Config.RemainingAffineMeets
import AclGeom.Config.AffineGridNormalization
import AclGeom.Geometry.FreshSequences
import AclGeom.Config.AffineGridInfinite
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
import AclGeom.Correspondence.CompositionAssociativity
import AclGeom.Correspondence.TensorComponent
import AclGeom.Correspondence.TensorRealization
import AclGeomBook.Configurations.GroupChunkRecord

/-!
# Configuration relations and their current formalization boundaries

Verso exposition of the proved semantic and conditional configuration results.
Guarded ACF extraction and completeness are proved; original source obligations remain explicit.
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
projection are refuted even over ACF pairs. Guarded Q completeness is proved for every
ACF pair (#27), and the multiplication converse gives rank-five ACF Q′/J completeness.
The internal interpretation APIs retain explicit perfected J-completeness parameters.
The public lattice reconstruction theorem now supplies those proofs internally.
The arbitrary-field Q/Q′ versions have
concrete characteristic-zero Lean refutations. This chapter distinguishes
the proved guarded chart from the remaining original scheme/action obligations.

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
Psi and Q/Q′/J remains proved by its existing route. Guarded extraction is proved below;
original scheme/action obligations remain open. The frozen M4a chain is unchanged.

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
perfected ACF J-completeness inputs remain explicit in these internal APIs. The public
reconstruction theorem supplies them internally; the broader
point/automorphism/functorial variants remain open. Guarded geometric projection
completeness follows from the new guarded Q theorem below. The frozen M4a record
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

# The multiplication-diagram product converse
%%%
tag := "multiplication-product-converse"
%%%

Over an algebraically closed ambient field of transcendence degree at least
five, a semantic ratio together with an actual multiplication diagram forces
the product output. The base field may be arbitrary:

{docstring AclGeom.q'Sem_of_qSem_of_mulDiagram}

Write `a, b, c, d, e` for representatives of the auxiliary corners and output.
Choose `a₀` outside the closure of `a, x, y`. An ambient automorphism fixing the
entire closed field generated by `b, c` carries `a` to `a₀`. It fixes `x/y`
literally, so its images `x₀, y₀` satisfy `x₀ y = x y₀`. Over the closed field
generated by `a, a₀`, the actual incidence clauses form a multiplicative
correspondence. The proved correspondence theorem forces the common ratio
`α = x₀/x = y₀/y` into that closed field.

Over the smaller closed base generated by `a₀`, closure exchange makes `α`
interalgebraic with `a`, and `α, x, y` are independent. The transported corner
incidences put `b` in the closure of `α x` and `c` in that of `α y`. The two
product meets then put `d` in the closure of `α x y` and `e` in the closure of
`x y` over this fresh base. A final exchange step removes `a₀`, so the original
output point is `[xy]` over the original base.

The source proof invokes curve-coset classification before constructing its
ambient group; this gap is recorded on
[#12](https://github.com/adamtopaz/acl_geom/issues/12#issuecomment-6155280744).
The direct proof above supplies the product conclusion independently.
When the original base is algebraically closed, coherent specialization also
supplies the full auxiliary coordinate table:

{docstring AclGeom.mulDiagram_coordinates}

The ambient transcendence-degree bound can also be removed when both fields
are algebraically closed:

{docstring AclGeom.MulDiagram.exists_coordinates}

For this strengthening, embed the original ambient field into the algebraic
closure of the fraction field of a polynomial ring in five variables. The
previous theorem supplies a normalized multiplier there. Exchange puts that
multiplier in the closure of an original coordinate, so it is algebraic over
the original ambient field and belongs to it by algebraic closedness.
Ambient invariance reflects the coordinate table and independence back to the
original field. Thus the source's full table needs no extra rank hypothesis.

Let `F` be the closed field generated by the original `a, x, y`. The fresh
parameter `a₀` is transcendental over `F`, and `b, c` belong to `F`. Choose
nonzero polynomial equations over `k` for the three dependences
`α ∈ acl(a₀, a)`, `b ∈ acl(a₀, αx)` and `c ∈ acl(a₀, αy)`.
Only finitely many values of `a₀` in `k` annihilate any one of these equations
as a polynomial in its two remaining variables.

Chevalley's theorem gives an open set of specializable parameter values for
the finite-type `F`-algebra generated by `a₀`, `α`, `α⁻¹` and the inverse of
the product excluding those bad values. An algebra homomorphism from this
algebra to `F` can send `a₀` to a value in the infinite subfield `k`. It fixes
all original coordinates, preserves the nonzero multiplier, and specializes
the three incidence equations simultaneously:

{docstring AclGeom.exists_finite_specialization_preserving_polynomials}

The first equation puts the specialized multiplier `β` in `acl(a)`. Because
`β ≠ 0`, independence of `x, y` over `acl(a)` keeps `βx, βy` transcendental,
so the other two equations put `b` in `acl(βx)` and `c` in `acl(βy)`:

{docstring AclGeom.exists_multiplier_descent}

If `β` were algebraic over `k`, the point `B` would equal `X`, contradicting
actual diagram distinctness. Exchange therefore gives `A = [β]` and
independence of `β, x, y`. The original-base product meets give `D = [βxy]`
and `E = [xy]`. One homomorphism preserves all relations, so their common
specialization is proved internally. The true bypassed group/chunk statements
remain obligations.

The two inner ratio inequalities follow from multiplication-diagram
distinctness. Hence guarded Q completeness supplies Q′ completeness:

{docstring AclGeom.q'Sem_of_q'Geom_of_guardedQCompleteness}

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

This proves the semantic assembly. The established geometric `J` assembly
accepts guarded geometric `Q` completeness and geometric `Q′` completeness
over the algebraically closed pair as explicit hypotheses:

{docstring AclGeom.JCompletenessACF}

{docstring AclGeom.jCompletenessACF_of_completeness}

The multiplication converse now derives the Q′ input from guarded Q
completeness, giving a single remaining completeness hypothesis:

{docstring AclGeom.jCompletenessACF_of_guardedQCompleteness}

The guarded input is now proved internally, so the same assembly gives completeness
for every algebraically closed pair of rank at least five:

{docstring AclGeom.jCompletenessACF}

{docstring AclGeom.jGeom_iff_jSem_of_isAlgClosed}

The unguarded Q input remains refuted (#27). Both ratio inequalities are supplied by
multiplication distinctness in J. The public reconstruction theorem now supplies its two
ACF completeness proofs internally.

# Incidence germs recover their parameter fields
%%%
tag := "psi-germ-parameter-fields"
%%%

The first parameter claim in the initial-chart proof of blueprint
Lemma 8.5 is derived from the actual Ψ witness, over arbitrary base
and ambient fields:

{docstring AclGeom.QWitness.Psi.exists_incidence_germs_with_full_coefficients}

The theorem constructs the three finite-correspondence germs Y to X,
Y to Z and X to Z over the fields generated by the displayed parameter
pairs. Their source and target coordinates are exactly the original
point representatives. The existing CurveEquation API supplies the
canonical monic prime equations, their exact branch ideals and
coefficient descent. No new equation normalization or field definition
is introduced.

Their canonical coefficient sets have relative closures exactly A,
B and C. A coefficient closure lies in its parameter plane. If an atom
of the plane contained it, the existing descended equation would put
the target point below that atom joined with the source point. The
literal universal free clause forbids this. The existing rank-two-plane
theorem therefore gives the whole plane. This asserts equality of
RELATIVE CLOSURES, not literal equality of the generated coefficient
field with the finitely generated parameter field.

One new public theorem uses two consumed private helpers. Three existing
parameter-rank facts become public with unchanged statements and proofs.
No closedness, ratio guard, chart, action, prime ideal, basis, rank or
coefficient-field conclusion is supplied by the caller.

Two real private examples check the same produced germs. A canonical
five-coordinate Ψ witness yields all three prime equations, exact span
ideals and original parameter closures. An actual endomorphism fixing
the displayed parameter field derives the same equation at the moved
endpoints. It never transports the globally quantified Ψ.

This covers the rank-two field-of-definition step. The common-closed-base
composition step follows below. Relational germ composition is associative
over arbitrary bases, as proved below. Its identification with components
of geometric fiber products over nonclosed function-field bases, group chunks,
the original scheme/action bridges and endpoint variants remain open.
Guarded initial charts and rank-five ACF Q′/J completeness are proved below. Frozen M4a is
unchanged.

# Composition over the common closed parameter field
%%%
tag := "psi-closed-germ-composition"
%%%

The parameter form of source equation (8.6) is derived from the actual Ψ
in an algebraically closed ambient field, over an arbitrary base:

{docstring AclGeom.QWitness.Psi.exists_composing_closed_incidence_germs}

The three germs now share the relatively closed field A join B and keep
their original endpoints Y to X, Y to Z and X to Z. Their canonical
ambient coefficient sets still have relative closures exactly A, B and C.
No chart, group, action, prime ideal, rank or coefficient conclusion is
supplied by the caller.

Relative closedness inside the algebraically closed ambient field makes
each parameter plane algebraically closed. Equal rank four for A join B
and A join B join C puts C in the common field; the literal notLe clauses
keep all three point representatives generic over that field. Existing
BaseChange proves exact extension of the three closed-germ ideals.
Existing monic-generator uniqueness identifies the mapped equations,
so their ambient coefficient sets are unchanged. The previous free-clause
argument recovers the full parameter closures.

The historical source calls the first arrow Y to X, while (8.6) uses it
in the opposite direction. This was reported on #27, comment 6153067856,
before source changes. The corrected selector transposes the A-germ to
X to Y, follows it by the B-germ Y to Z and obtains the C-germ X to Z.
This selector uses the same endpoints after the substantive no-splitting
and coefficient proof.

The closed-field route is essential to the argument. Finite-generator
presentations may split on extension to their closed parameter planes.
The existing FiniteCorrespondenceFamilyMember.pairOverIndependentExtension
constructs pairs over an independent extension of a finite-generator
parameter field. Here ambient closedness makes the closed parameter planes
algebraically closed. Equality of coefficient CLOSURES
does not assert literal equality of the generated fields.

One new public theorem uses three consumed private helpers and the
previous incidence/coefficient APIs. A native-field endpoint helper is
consumed six times; it keeps the dependent field change out of the main
proof and passes the default kernel limits. Two real private examples
derive all three common-field prime equations, exact ideals, original
closures and composition at the canonical witness, and derive the same
equation at endpoints moved by an actual common-field endomorphism.
The universally quantified Ψ is never transported.

No new public rank wrapper, field definition, normalization interface or
checking option is added. The geometric fiber-product/function-field bridge,
group chunks, original scheme/action bridges and endpoint variants remain open. Guarded initial
charts and rank-five ACF Q′/J completeness are proved below. Frozen M4a is
unchanged.

# Relational correspondence composition is associative
%%%
tag := "correspondence-relational-associativity"
%%%

The field-level associativity assertion in the opening of blueprint §8.1
holds for the existing finite-correspondence germs over any base field,
inside an algebraically closed ambient:

{docstring AclGeom.FiniteCorrespondenceGerm.composes_assoc}

A germ records a prime vanishing ideal with a generic interalgebraic pair
presenting it. `Composes A B C` says that presentations of A and B can share
a literal middle coordinate and yield C at their endpoints. The two
parenthesizations may initially use different presentations of their common
intermediate germ.

Equal endpoint-pair ideals give an ambient automorphism by the proved
finite generic-point theorem. Transport the interior coordinate through that
automorphism: the two presentations then fit one chain of four generic
coordinates. Grouping its first or last two arrows gives the required
intermediate germ. Applying this argument in both directions proves equality
of the possible final germs. Two private helpers transport a branch and
preserve its ideal; both are consumed by the public theorem.

An actual squaring correspondence, its transpose and negation exercise this
regrouping. The input uses a transcendental element and constructs all branch
memberships and compositions; the theorem produces the other intermediate
germ. Algebraic closedness of the base and an ambient rank bound are unnecessary.

The relation keeps all possible components. Identifying these represented
germs with dominating components of geometric fiber products remains a
separate C2 obligation, including the nonclosed function-field base case.
This theorem supplies neither a component-selection operation nor a group
chunk, initial chart or configuration-completeness input.

# Selected function-field tensor components
%%%
tag := "correspondence-tensor-components"
%%%

The function-field part of blueprint §8.1 has a concrete component theorem.
Given actual finite branches `(x,y)` and `(y,z)`, put `E = k(y)`,
`F = E(x)` and `G = E(z)`. The multiplication map from `F ⊗[E] G` to the
ambient field selects a minimal prime:

{docstring AclGeom.FiniteCorrespondencePair.tensor_ker_mem_minimalPrimes}

Both extensions of E are finite, so their tensor product is Artinian.
The kernel is prime because the target is a field, and every prime in this
Artinian ring is minimal. Its quotient is the compositum of F and G:

{docstring AclGeom.FiniteCorrespondencePair.tensor_quotient_equiv_compositum}

The image of the multiplication map is the compositum, and Mathlib's first
isomorphism theorem gives the quotient equivalence. Restricting scalars
identifies that compositum with the existing three-coordinate chain field:

{docstring AclGeom.FiniteCorrespondencePair.tensor_compositum_eq_chainField}

These results work over arbitrary base and ambient fields. In particular,
the middle function field need not be algebraically closed, and the tensor
product is not assumed to be a domain. A concrete squaring branch followed
by its transpose checks all three conclusions: its selected quotient is a
field and its compositum is exactly `k(t)` for transcendental t.

This proves the component selected by an actual shared-middle chain.
Every tensor component has a realization by the theorem below. Connecting
these fields to dominating components of geometric fiber products via
coordinate rings and localization remains an obligation. These component
results supply no group chunk or initial affine chart.

# Realizing every function-field tensor component
%%%
tag := "correspondence-tensor-realization"
%%%

For the existing scalar branch representation, every minimal-prime tensor
component yields an actual composite of the original germs in an algebraically
closed ambient field. The base field can be arbitrary. First, the component
is realized by two embeddings fixing the common middle field:

{docstring AclGeom.FiniteCorrespondencePair.exists_tensor_component_embeddings}

The tensor of the finite branch fields is Artinian, so its prime quotient is
a finite field extension. Mathlib's algebraic-extension embedding theorem maps
that quotient into the ambient ACF. Restricting along the two tensor inclusions
gives the embeddings and recovers exactly the original component kernel.

{docstring AclGeom.FiniteCorrespondencePair.exists_composite_of_tensor_component}

Lift each branch's coordinates into its finite field, then transport them
through the embedding. The existing closure and polynomial-ideal lemmas
preserve genericity, interalgebraicity and the original pair ideals. Both
embeddings fix the middle field, so the transported branches share the original
middle coordinate. Their endpoint pair is an actual `Composes` witness.

{docstring AclGeom.FiniteCorrespondencePair.tensor_component_endpoint_ideal_eq}

Equal tensor kernels give identical polynomial relations on the two endpoint
images. Thus a component determines its composite germ independently of the
chosen embeddings. This does not assert injectivity from tensor components
to endpoint germs. The uniqueness statement needs no ACF hypothesis.

A concrete squaring branch followed by its transpose exercises an arbitrary
minimal-prime component. Its embedded sources both square to the original
middle coordinate; the derived composite has diagonal or antidiagonal
endpoints. A second realization of that component has the same endpoint germ.
The tests construct the branches and derive composition without an input oracle.

The coordinate-ring/localization identification with geometric fiber-product
components remains open. No group chunk, coherent cover, initial affine chart
or reconstruction-completeness hypothesis is supplied by these results.

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

The guarded chart normalization consumes these non-memberships. From an independent
initial chart for A/B/C/S/T/U/X/Y/Z, it derives the raw field incidences and then all
three joins and fifteen points. The supplied-input version fixes each original prime
curve before the corresponding family of fresh inputs:

{docstring AclGeom.QWitness.Psi.hasAffineGridCoordinates_of_chart_supplied_inputs}

Fresh sequences exist over a field of countable transcendence degree. Choosing them
after each curve is fixed gives a chart theorem with no supplied input families:

{docstring AclGeom.exists_fresh_sequence_of_aleph0_le_trdeg}

{docstring AclGeom.QWitness.Psi.hasAffineGridCoordinates_of_chart_of_aleph0_le_trdeg}

The final chart normalization works over every ambient extension of an algebraically
closed base, including fields of finite transcendence degree. It transfers only the raw
field conditions to a countable algebraically closed extension, constructs the input
families there, and descends the remaining rows by closure absoluteness. Both translation
constants lie in the original base. This avoids transporting globally quantified Ψ in
that normalization step:

{docstring AclGeom.QWitness.Psi.hasAffineGridCoordinates_of_chart}

{docstring AclGeom.rankEq_iff_eRk}

The normalization uses the following public coordinate lemmas. Literal relocation fixes
p, the affine value, the shared point, and c/f; a supplied fresh multiplier gives a new
presentation with the same joint vanishing ideal. Extra prescribed data can also be kept
fresh. These are implications from the stated coordinate and independence hypotheses:

{docstring AclGeom.sub_mem_racl_of_affine_value_eq}

{docstring AclGeom.exists_affine_relocation}

{docstring AclGeom.idealOf_aeval_comp_eq_of_idealOf_eq}

{docstring AclGeom.affine_multiplier_curve_of_joint_ideal}

{docstring AclGeom.multiplier_projection_genericity}

{docstring AclGeom.exists_prime_multiplier_curve_of_joint_ideal}

{docstring AclGeom.exists_curve_ideal_colors}

{docstring AclGeom.finite_curve_ideals_of_relation}

{docstring AclGeom.scale_notMem_racl_of_fresh_multipliers}

{docstring AclGeom.exists_affine_relocation_fresh_over}

Finite equal-ideal fibres and the characteristic-free power-orbit argument force the
vertical translation in the affine-locus commutator to vanish. An equal-color triple of
relocated lines is concurrent. Pairwise cocycles and independent closure intersections
put its center in the original base's algebraic closure; algebraic closedness makes it
a base-field constant. This determines the shifted P row:

{docstring AclGeom.finite_same_fibre_ideals}

{docstring AclGeom.affine_locus_commutation_balance}

{docstring AclGeom.sub_mem_racl_of_two_relocations}

{docstring AclGeom.racl_singleton_eq_of_concurrent}

{docstring AclGeom.algebraicIndependent_table_shift}

{docstring AclGeom.racl_shifted_D_F_R_of_normalized_P}

{docstring AclGeom.racl_normalized_P_of_supplied_fresh_inputs}

Apply the same P producer to the inverse coordinate tuple to obtain Q. The second curve
is fixed after the first translation is obtained and before its own fresh input family.
The remaining lattice meets give G/H/I/E; the two triangular changes preserve the
five-variable independence and the required joins:

{docstring AclGeom.algebraicIndependent_table_Q_shift}

{docstring AclGeom.racl_shifted_G_H_I_E_of_normalized_P_Q}

The initial chart itself is now constructed from the actual Ψ witness. Its rank-two HW
action admits an affine generator. After moving the finite witness, upper-triangular
curve classification identifies S, T and U with the two multipliers and their product.
This yields the nine initial rows over a coefficient field independent from the moved
witness, in a universal algebraically closed extension.

Descent chooses genuine annihilators for both closure inclusions in every row. One finite
constructible relation records their coefficient parameters, nonzero denominators and
nonzero coefficients. A single specialization preserves all rows; the resulting finite
fibre has a point in the original algebraically closed field. Closure identities compare
the lift's chosen representatives with the literal embedded originals, and absorb the
automorphism into that embedding. Finally the actual Ψ ranks force independence of the
five original-field coordinates. The chart normalization above gives the full grid:

{docstring GroupConfig.exists_polynomial_closure_table_descent_to}

{docstring AclGeom.guardedAffineGridExtraction}

{docstring AclGeom.guardedQCompletenessACF}

Neither theorem asks the caller for a chart, a universal domain, coefficient witnesses or
fresh input families. Both public ratio guards remain visible. No common-shift,
six-generator or uniqueness statement is asserted. Original scheme/action bridges and
true bypassed source statements remain obligations; the frozen 117-item M4a record stays
unchanged.

The corrected propositions retain `I≠D` and `I≠P`; their sufficiency over ACF pairs is
proved by the extraction above. The unguarded counterexamples remain recorded:

{docstring AclGeom.GuardedAffineGridExtraction}

{docstring AclGeom.GuardedQCompletenessACF}

{docstring AclGeom.GuardedAffineGridExtraction.guardedQCompletenessACF}

The general guarded correctness and projection lemmas retain an explicit completeness
input, now supplied by the proved `guardedQCompletenessACF`, together with soundness:

{docstring AclGeom.qGeom_and_ne_iff_qSem_of_five_le_trdeg}

{docstring AclGeom.qGeom_and_ne_iff_exists_jGeom}

The canonical correctness theorems supply the guarded completeness input internally:

{docstring AclGeom.qGeom_and_ne_iff_qSem_of_isAlgClosed}

{docstring AclGeom.q'Geom_iff_q'Sem_of_isAlgClosed}

Original q-correct and extraction wording from ed61c33 is preserved in the
blueprint as refuted historical provenance. All 44 original proof blocks
remain byte-exact, with explicit qualifications before the affected sketches.
Guarded extraction, the multiplication converse and rank-five ACF J completeness are
proved. They do not discharge every original auxiliary or endpoint variant. The frozen
117-item M4a record remains frozen.

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
The finite polynomial witness descent and guarded ACF completeness are proved above.
The four-way J API retains its explicit ACF input; the new rank-five ACF theorem supplies
it. The original arbitrary-field Q/Q′ consequences remain refuted.

{include 0 AclGeomBook.Configurations.GroupChunkRecord}
