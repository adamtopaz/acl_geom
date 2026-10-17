/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Correspondence.JRigidity
import AclGeom.Transfer.JRigidityStatement
import AclGeom.Correspondence.AdditiveThreePair
import AclGeom.Correspondence.AdditiveSubgroupConnected
import AclGeom.Correspondence.CurveCosetAdditive
import AclGeom.Correspondence.CurveCosetCommutative
import AclGeom.Correspondence.AlgebraicGroupProduct
import AclGeom.Correspondence.AffineGroupGeometry
import AclGeom.Correspondence.AffineSchemeAction
import AclGeom.Correspondence.SchemeCurveFunctionField
import AclGeom.Correspondence.SchemePlaceBoundary
import AclGeom.Correspondence.MultiplicativeLiteral
import AclGeom.Correspondence.MultiplicativeSubgroup
import AclGeom.Correspondence.RegularACF
import AclGeom.Correspondence.GeometricPrime
import AclGeom.Correspondence.GenericExtension
import AclGeom.Correspondence.Family
import AclGeom.Correspondence.AmbientAutomorphism
import AclGeom.Counterexamples.EndpointImage
import AclGeom.Correspondence.TensorFractionRing
import AclGeom.Correspondence.ComponentGeometry
import AclGeom.Correspondence.LocusPullback
import AclGeom.Correspondence.LocusEndDominance
import AclGeom.Correspondence.LocusQuotient
import AclGeom.Correspondence.LocusIncidence
import AclGeom.Correspondence.LocusQuotientComponents
import AclGeom.Correspondence.LocusJointComponent
import AclGeom.Correspondence.LocusComponentField
import AclGeom.Correspondence.TupleComposition
import AclGeom.Correspondence.TupleCompositionField
import AclGeom.Correspondence.LocusIncomparability
import AclGeom.Correspondence.GenericPointExtension
import AclGeom.Correspondence.ThreefoldIncidence
import AclGeom.Correspondence.ScalarCompositionGeometry
import AclGeom.Correspondence.LocusDimension
import AclGeom.Correspondence.LocusGenericFiber

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The hard kernel: loci, relocation, and correspondences" =>

%%%
tag := "hard-kernel"
%%%

The technical heart of the reconstruction theorem (blueprint §8, milestone
M3) shows that the additive and multiplicative structure of the field can be
recovered from the dependence geometry: any two-way finite correspondence
that commutes with addition on independent generic points is, after
normalization by additive polynomials, a power of Frobenius. This chapter
presents the stable lower layers of that argument. Tuples of field elements
define loci by their vanishing ideals. The affine-scheme and coordinate-ring
bridges identify literal projections and fiber-product components, while the
field arguments track their generic tuples.

# Additive polynomials
%%%
tag := "additive-polynomials"
%%%

A polynomial is *additive* when it commutes with addition of points:

{docstring AclGeom.IsAdditive}

In characteristic zero additive polynomials are linear, while in
characteristic $`p` their support is concentrated on powers of $`p` — the
two classification facts feeding the endgame of the correspondence theorem:

{docstring AclGeom.IsAdditive.eq_C_mul_X}

{docstring AclGeom.IsAdditive.coeff_eq_zero_of_ne_pow}

The characteristic-$`p` statement rests on a Lucas-theorem argument
identifying the natural numbers all of whose lower binomial coefficients
vanish mod $`p`:

{docstring AclGeom.eq_pow_of_forall_dvd_choose}

The simultaneous-coset endgame also needs a support statement for polynomial
identities of binomial type:

{docstring AclGeom.eq_monomial_of_eq_smul_binomial}

# The loci dictionary
%%%
tag := "loci"
%%%

The locus $`\mathrm{Loc}_k(a)` of a tuple $`a` of elements of an extension
$`\Omega/k` is, in this formalization, its vanishing ideal:

{docstring AclGeom.idealOf}

{docstring AclGeom.idealOf_eq_bot_iff}

Vanishing ideals are equivariant under embeddings of the ambient field, and —
crucially for the genericity bookkeeping — they control the *relative*
dependence geometry of the coordinates. Two tuples with the same vanishing
ideal have coordinates in exactly the same `racl`-relations:

{docstring AclGeom.idealOf_comp_algHom}

{docstring AclGeom.mem_racl_image_of_idealOf_eq}

{docstring AclGeom.transcendental_of_idealOf_eq}

# Dimension of a finite tuple locus
%%%
tag := "finite-locus-dimension"
%%%

For a finite tuple $`a`, the Krull dimension of the literal coordinate ring
$`k[\iota]/I(a/k)` equals the transcendence degree of the generated field
$`k(a)` over $`k`. Both are the same finite natural number:

{docstring AclGeom.exists_locusCoordinateRing_dimension}

The finite number is constructed internally. No algebraic-closedness,
rank-one, rationality or caller-supplied dimension premise is needed; the
base field, ambient field and index type have independent universes.
Noether normalization embeds a polynomial ring integrally into the
finite-type generated ring. Going up and incomparability compare their
Krull dimensions, and the resulting transcendence basis computes the
fraction field's transcendence degree. The existing coordinate-ring
isomorphism transfers this to the actual quotient by the vanishing ideal.

This proves the dimension assertion in the first paragraph of blueprint §8.
It does not discharge the separate tuple-composition or family obligations.

# Generic points of arbitrary affine loci
%%%
tag := "realizing-affine-primes"
%%%

Conversely, let $`P` be any prime ideal in a polynomial ring in finitely many
variables over $`k`. Its literal quotient has an internally chosen finite
Krull dimension $`n`. The following theorem proves that some tuple in an
algebraically closed extension $`\Omega/k` has vanishing ideal exactly $`P`
if and only if $`n\leq\operatorname{trdeg}_k\Omega`:

{docstring AclGeom.exists_idealOf_eq_iff}

The base field is arbitrary. The base, ambient field and coordinate index
type have three independent universes; neither a dimension certificate nor
a generic point is supplied by the caller.

Noether normalization computes $`n` as the transcendence degree of the
fraction field of $`k[\iota]/P`. A finite transcendence basis of that field
embeds into a transcendence basis of $`\Omega/k`; explicit cardinal lifts
retain the independent universes. Evaluation identifies their rational
function fields, and algebraic closedness extends the embedding across
the remaining algebraic extension. The images of the coordinate classes
then have vanishing ideal exactly $`P`. Conversely, any realizing tuple
has generated-field transcendence degree $`n`, which cannot exceed that
of the ambient field.

For an irreducible correspondence curve, take its prime ideal in the joint
variables $`\alpha\oplus\beta`. Split the realizing tuple into $`v` and
$`w`. The existing `idealOf_eq_comap_rename` identifies their two
vanishing ideals with the contractions of $`P` along the literal coordinate
inclusions. Thus the finite-tuple calculus covers arbitrary irreducible
correspondence curves, including non-rational function fields, once the
necessary ambient-size condition holds. This proves the geometric
presentation step. The next section proves the full finite-coordinate
generic-extension lemma from the source membership and rank conditions.

# Generic points over a coefficient extension
%%%
tag := "generic-extension-full"
%%%

Let $`k` be algebraically closed, $`E/k` any field extension, and $`P` a
prime ideal in finitely many variables. The source defines a generic point
by membership in the locus and its relative transcendence degree. The
following theorem constructs the common finite dimension $`n` of both
literal quotients and proves the complete assertion from those hypotheses:

{docstring AclGeom.genericExtension_genericPoint}

For every point $`v` with $`P\subseteq I(v/k)` and
$`\operatorname{trdeg}_E E(v)=n`, its ideal over $`E` is exactly the
extended ideal, its ideal over $`k` is $`P`, and the image of $`E` and
$`k(v)` are linearly disjoint over $`k`. The universal clause needs no
closedness or size assumption on the given ambient. When that ambient is
algebraically closed, a tuple realizing the extended ideal exists if and
only if its transcendence degree over $`E` is at least $`n`. All four
universes are independent.

The proof chooses a reference point in the algebraic closure of a rational
function field in countably many variables over $`E`. The earlier realization
theorem supplies it, and the existing exact-ideal field-freeness and dimension
theorems compute both quotient dimensions from that point. For an arbitrary
point of the source rank, a maximal independent coordinate subfamily has
$`n` elements. The same coordinates of the reference point form a basis.
Algebraic incomparability then forces the two ideals to coincide:

{docstring AclGeom.exists_poly_of_mem_racl}

{docstring AclGeom.idealOf_eq_of_le_of_comap_eq}

These two reusable lemmas have the same statements as the former private
threefold-incidence helpers. Their actual consumers are the threefold
component proof and this generic-extension argument; the target ideal in
the incomparability theorem need not be prime. The countably infinite
reference field is constructed inside the proof, and its rank is not a
hypothesis on the given ambient.

The other source clauses follow from public APIs with the literal source
hypotheses. For (b), apply the universal clause with $`E=k` to two points
of the locus with the source rank. Their ideals are both $`P`.
`locusFunctionFieldEquivOfIdealEq` is the canonical isomorphism carrying
one tuple to the other, and the first conjunct of
`exists_ambientAutomorphism_of_idealOf_eq` extends this exact isomorphism
to the ambient automorphism. Finite tuples in an algebraically closed
ambient require no enlargement. For (c), Mathlib's
`AlgebraicIndependent.aevalEquivField` is injective, evaluates $`p/q` as
the quotient of the polynomial evaluations, and independence makes every
nonzero denominator evaluate nonzero. These are the rational identity and
specialization assertions.

The source audit checks actual consumers for primality, irreducibility of
the literal coordinate spectrum, the canonical fraction-field isomorphism
and its polynomial formula, as well as (b), (c) and denominator nonvanishing.
These source consumers were compiled outside the library; the continuation
guide and the #5 checkpoint report record their manifests and scope.
Together with the earlier finite-correspondence and normalization results,
this covers the original section-eight opening and finite-correspondence
subsection through generic-extension (a)--(c). The two source qualifications
remain: the joint component field can be properly larger than its endpoint
image field, and an infinite absolute-degree equality alone does not imply
independence. Field freeness supplies the latter conclusion. The original
group/chunk, six-point, affine-action and coherent branch/normal-cover
obligations remain separate. The selected parameter-family component identities
are proved in the configuration chapter.

# Localizing tensor components
%%%
tag := "localizing-tensor-components"
%%%

For domains $`A`, $`B`, $`C` with compatible fraction fields $`K`, $`L`, $`M`,
the minimal primes of $`B\otimes_A C` avoiding the nonzero elements of $`A`
are exactly the pullbacks of the minimal primes of $`L\otimes_K M` under the
canonical map:

{docstring AclGeom.minimalPrimes_tensorProduct_fractionRing}

The proof localizes the two factors and uses flatness over $`A` of the
fraction-field base changes. The remaining denominators are nonzerodivisors,
so they meet no minimal prime. It requires no
Noetherian, separability, reducedness or algebraic-closedness hypothesis.
All algebra and fraction-field structures are genuine inputs; the
localization and minimality conclusions are proved internally.

This supplies the domain-level localization step for C2. The actual
canonical-coordinate affine fiber product below consumes it. The literal
relative quotient maps and their spectrum components are identified below.
The incidence quotient and its actual projections are identified below.
The chosen joint point's component status under a source algebraicity clause
is proved below. The tuple germ layer below identifies composite germs with
endpoint images of the actual components and proves relational associativity.
The family's generic-component argument remains a separate obligation.
General curve function fields are retained throughout.

# Components of the actual affine fiber product
%%%
tag := "affine-fiber-product-components"
%%%

For domains with compatible fraction fields, the contracted minimal primes
define exactly the irreducible components of the tensor-product spectrum
whose images are dense in the base spectrum:

{docstring AclGeom.dominatingComponents_tensorProduct_fractionRing}

The proof uses Mathlib's correspondence between minimal primes and irreducible
components. The closure of a component's projection is the zero locus of the
contracted ideal, so density is exactly avoidance of the nonzero base elements.

For arbitrary tuples $`x,y,z` in a field over $`k`, take the generated rings
$`A=k[y]`, $`B=k[x,y]`, $`C=k[y,z]` and their actual generated fraction fields.
The existing `locusCoordinateRingEquiv` identifies these rings with the
polynomial quotients by the tuple ideals. The theorem constructs all inclusion
algebras, scalar towers and fraction-field structures from these tuples. It
then forms the actual affine-scheme fiber product
$`P=\operatorname{Spec} B\times_{\operatorname{Spec} A}\operatorname{Spec} C`
and its actual projection $`\pi` to $`\operatorname{Spec} A`:

{docstring AclGeom.locusPullback_dominatingComponents}

The components of $`P` with dense $`\pi`-image are exactly the images, under
the homeomorphism of Mathlib's canonical pullback isomorphism, of the zero
loci of the contracted fraction-field tensor minimal primes. The proof transports
both the topology and the actual base projection. All component and density
conclusions are derived internally. The ambient and base fields are arbitrary,
and no rationality of the curve function fields or scalar-coordinate restriction
is imposed.

The algebraicity clauses of source (8.1) say that the coordinates of $`x`
are algebraic over the field generated by $`y` and conversely, and likewise for
$`y,z`. Under precisely those four closure conditions, every subset of the
actual fiber product has dense image under the middle projection if and only
if it has dense image under the first endpoint projection, and likewise under
the second endpoint projection:

{docstring AclGeom.locusPullback_endDominance}

The proof derives algebraicity of all four coordinate-ring extensions from
the closure conditions through the fraction field of the smaller coordinate
ring. An injective algebraic extension of domains reflects density of arbitrary
spectrum images: a nonzero ideal upstairs contracts nontrivially downstairs.
Pushing a subset through the actual two pullback projections therefore
compares all three images. No component classification, rank-one premise,
Noetherian hypothesis or density input is needed for this criterion.

{docstring AclGeom.denseImage_iff_of_isAlgebraic}

Thus the components dominating the middle are exactly those dominating both
ends, in the canonical generated-ring model. The next section transports
these conclusions to the literal relative coordinate rings.

# Literal relative coordinate rings
%%%
tag := "literal-relative-coordinate-rings"
%%%

Write $`Q_y=k[Y]/I(y)`, $`Q_{xy}=k[X,Y]/I(x,y)` and
$`Q_{yz}=k[Y,Z]/I(y,z)`. The two relative maps are induced by the actual
inclusions of the variables $`Y`. Contraction along a variable renaming
recovers the ideal of the reindexed tuple, and the coordinate-ring
identifications commute with those maps:

{docstring AclGeom.idealOf_eq_comap_rename}

{docstring AclGeom.locusCoordinateRingEquiv_comp_quotientMapₐ}

Consequently the literal relative tensor is isomorphic, as a $`k`-algebra,
to the tensor of the generated coordinate rings. The theorem specifies the
image of every pure tensor and every base element:

{docstring AclGeom.exists_locusQuotientTensor_algEquiv}

The induced spectrum homeomorphism intertwines the actual middle and endpoint
projections with the induced homeomorphisms of the base spectra. The minimal primes of
the canonical fraction-field tensor therefore identify exactly the literal spectrum's
components with dense middle image. The map to that tensor is constructed internally and
is specified on pure tensors:

{docstring AclGeom.exists_locusQuotient_dominatingComponents}

Under the four algebraicity clauses of (8.1), every subset has dense middle
image if and only if it has dense first-endpoint image, and likewise for the
second endpoint:

{docstring AclGeom.locusQuotient_endDominance}

The two generic domain/algebraicity lemmas already used for the canonical
scheme criterion are reused here. All rings, maps and fraction-field
structures are derived from the tuples. Base, ambient and index universes
remain independent, without algebraic-closedness or rationality assumptions.

The following section identifies this tensor with the full incidence
quotient and transports the actual projection-density criteria to it.

# The incidence quotient and its projections
%%%
tag := "incidence-quotient"
%%%

Let $`R=k[X,Y,Z]`, and let $`J_{\mathrm{inc}}` be the sum of the extensions
of $`I(x,y)` and $`I(y,z)` along the two variable inclusions. The full
incidence quotient is $`R/J_{\mathrm{inc}}`. Its identification with the
relative tensor is a base-field algebra equivalence. On polynomial pure
tensors it is multiplication of the two renamed polynomials; the middle
base map is also specified:

{docstring AclGeom.exists_locusIncidence_algEquiv}

The three projection maps from the quotients of $`k[X]`, $`k[Y]` and $`k[Z]`
are induced by the actual variable renamings into $`R`. Their ideal
containments follow from the pair ideals, with one lemma used by all three:

{docstring AclGeom.idealOf_le_comap_rename_comp}

Transporting the existing component classification along the equivalence
identifies exactly the incidence spectrum's components with dense middle
image. The map to the canonical fraction-field tensor is constructed
internally and specified on products of the renamed pair polynomials:

{docstring AclGeom.exists_locusIncidence_dominatingComponents}

Under the four algebraicity clauses of (8.1), every subset has dense middle
image if and only if it has dense first-endpoint image, and likewise for
its second-endpoint image:

{docstring AclGeom.locusIncidence_endDominance}

A generic ring-isomorphism component transport is shared by the tensor and
incidence criteria, with a further private algebra-equivalence helper for
the incidence proof; the density transport is also reused. The existing
tensor-spectrum theorems retain their statements. All structures and maps
are derived from the tuples, in five independent universes, without a
rank-one, rationality, finiteness or algebraic-closedness premise.

The following result identifies the chosen joint tuple's component under
one of the source algebraicity clauses. The endpoint-image field can be
smaller than the joint component field.

# The component of the chosen joint tuple
%%%
tag := "joint-tuple-component"
%%%

Evaluation at $`(x,y,z)` kills both extended pair ideals and therefore
factors through the actual incidence quotient $`R/J_{\mathrm{inc}}`:

{docstring AclGeom.locusIncidence_le_idealOf}

Suppose each coordinate of $`z` is algebraic over $`k(y)`. This single
clause of (8.1) suffices: the actual joint evaluation kernel is minimal,
and its zero locus has dense image along the actual middle projection:

{docstring AclGeom.locusIncidence_jointPrime_dominating}

The function-field tensor $`k(x,y)\otimes_{k(y)}k(y,z)` is integral over
$`k(x,y)`, since its right factor is algebraic over $`k(y)`. Its
multiplication kernel contracts to zero in the left field, so the integral
extension theorem makes that kernel minimal. The polynomial formulas for
the incidence-to-function-field map show that its composite with
multiplication is the actual joint evaluation. The component classification
above then gives minimality and middle dominance for the joint prime in
the incidence quotient. Algebraicity and all maps are derived from the
tuples; no condition on $`x`, rank, finiteness, rationality or algebraic
closedness is needed. All five universes remain independent.

# Finite rank and higher-dimensional components
%%%
tag := "rank-additive-incidence-component"
%%%

For finite tuples, the chosen joint point also selects an actual component
under the rank-additivity equation
$`\operatorname{rk}(x,y,z)+\operatorname{rk}(y)=\operatorname{rk}(x,y)+\operatorname{rk}(y,z)`.
Here ranks are transcendence degrees of the generated fields over $`k`.
The base and ambient fields are arbitrary, with five independent universes:

{docstring AclGeom.locusIncidence_jointPrime_dominating_of_rank}

The joint evaluation kernel in the literal incidence quotient is minimal,
and its zero locus has dense image under the literal middle projection.
Contracting its ideal to the endpoint variables gives exactly $`I(x,z)`.
The coordinate ring of this selected component, the incidence quotient
further divided by that kernel, has finite Krull dimension equal to
$`\operatorname{trdeg}_k k(x,y,z)`.

The proof chooses a maximal independent subfamily of $`x` over $`k(y)`.
It spans $`k(x,y)` algebraically. Finite rank cancellation shows that it
stays independent over $`k(y,z)`. Generic base change gives linear
disjointness for its purely transcendental field; the remaining algebraic
extension makes the tensor product integral over that smaller tensor.
The joint multiplication kernel contracts to zero there and is therefore
minimal. The two evaluation maps have the same range, so their quotient
isomorphisms identify the selected component ring with the joint locus
coordinate ring for the dimension computation.

This supplies the chosen-point component and dimension step used in
(8.4c) and (8.6), allowing positive relative dimension on both sides.
For the actual six-point partial quadrangle, the configuration chapter now
constructs the selected incidence germs over the closed parameter join, retaining
the three parameter closures. Over the literal compositum $`k(s,t,u)`, each
selected branch, including the composite, is a minimal prime of its original
parameter-field ideal after extension. The literal Ψ producer in the same
chapter gives the selected (8.6) germ over
$`k(a_1,a_2,b_1,b_2,c_1,c_2)`, from Ψ alone over arbitrary fields. Its
original three two-generator families retain coefficient closures A, B and C;
the selected larger-field ideals are minimal over their extended family ideals.
This does not assert those coefficient closures for split larger-field factors.
In an ACF ambient, every branch of each literal six-point family is now
realized as an actual larger-field generic conjugate of the original endpoints
over that family's own parameter field, as proved in the configuration chapter.
The Ψ analogue now realizes every branch of each of its three literal
two-generator families over the six-generator parameter compositum in the
same way, from Ψ and an ACF ambient alone. It reuses the public literal
producer and asks for no branch-genericity conclusion. Both results treat
branches individually. The selected parameter-family locus forms of (8.4c)
and (8.6) are proved in the configuration chapter by the actual components,
dense projections, canonical finite function fields and exact scalar contractions.
Coherent triples and their common normal cover still require separate proofs.
The geometric presentation
step for arbitrary irreducible correspondence curves is proved above by
`exists_idealOf_eq_iff`, with the necessary ambient-size condition.
The full finite-coordinate generic-extension lemma is proved above.
Coherent-branch and common-normal-cover statements and the original group/chunk
statements remain obligations.

The following classification realizes every dominating component when the
outer tuples are finite and the ambient field is algebraically closed.

# Realizing all dominating incidence components
%%%
tag := "all-incidence-components"
%%%

Assume the outer index types are finite, every coordinate of $`x` and of
$`z` is algebraic over $`k(y)`, and the ambient field is algebraically
closed. The actual incidence spectrum's middle-dominating irreducible
components are exactly the joint loci $`(x',y,z')` that preserve both
original pair ideals. Each joint ideal is mapped into the incidence
quotient before taking its zero locus:

{docstring AclGeom.locusIncidence_dominatingComponents_eq_jointLoci}

The equality proves both directions. The middle tuple remains fixed, and
its index type and the base field are arbitrary. Rank-one and rationality
premises are unnecessary. All five universes remain independent.

The two canonical generated fields are finite over $`k(y)` because the
outer tuples are finite and algebraic over that field. Every prime
component of their tensor product is realized by embeddings into the
algebraically closed ambient field, using the same theorem as the existing
scalar branch realization:

{docstring AclGeom.exists_productMap_ker_of_isPrime}

The polynomial comparison identifies the contracted multiplication kernel
with the image of the joint vanishing ideal. The embeddings preserve the
pair ideals and fix the middle tuple. Conversely, equality of the pair
ideals constructs embeddings of the generated fields that fix the middle
field, giving the same contracted kernel. The comparison also supplies the
previous chosen-point theorem, whose statement remains unchanged.

# Coordinate rings and function fields of actual components
%%%
tag := "incidence-component-fields"
%%%

For every actual middle-dominating irreducible component $`Z` of the
incidence spectrum, the following theorem chooses $`x'` and $`z'` preserving
both pair ideals. It identifies the component's actual reduced coordinate
ring, the incidence quotient modulo $`\operatorname{vanishingIdeal}(Z)`,
with the subalgebra generated by $`(x',y,z')`. Its actual fraction ring is
isomorphic to the compositum $`k(x',y) \vee k(y,z')` inside the ambient
field:

{docstring AclGeom.exists_locusIncidence_component_algEquiv}

Both isomorphisms send every polynomial representative to its evaluation
at the chosen joint tuple. These formulas pin the projection coordinates;
the theorem supplies the realization and identifications internally. Only
the outer index types need be finite, the outer tuples must be algebraic
over $`k(y)`, and the ambient field must be algebraically closed. The base
field and middle tuple are arbitrary, in five independent universes. No
rank-one or rationality premise is used.

The component classification supplies the realization. Primality of the
mapped joint ideal identifies its zero locus's vanishing ideal. The third
isomorphism theorem for algebras identifies the actual double quotient,
and the canonical fraction-ring equivalence gives the generated joint
field. The union of the two pair-generator sets gives the compositum.
The endpoint-image field $`k(x',z')` can still be properly smaller; no
component field is identified with that endpoint field.

# Generic fibres and the finite-correspondence criterion
%%%
tag := "finite-correspondence-criterion"
%%%

The generic fibre of the canonical projection from the locus of $`(v,w)`
to the locus of $`v` is the spectrum of
$`k(v) \otimes_{k[v]} k[v,w]`. For finite $`w`, the next theorem identifies
this actual ring with the subalgebra $`k(v)[w]`, sending $`a \otimes b` to
$`ab`. It also proves both finite dimension over $`k(v)` and finiteness of
the actual spectrum projection exactly when the coordinates of $`w` are
algebraic over $`k(v)`. The tuple $`v`, base field and ambient field remain
arbitrary:

{docstring AclGeom.exists_pairGenericFiber_algEquiv}

Flatness of the fraction field over the generated coordinate ring makes
the multiplication map injective. Its range is the indicated subalgebra.
Finite algebraic generators give finite dimension, and the converse makes
every coordinate algebraic. Mathlib's criterion for finite affine scheme
morphisms gives the actual generic-fibre projection's finiteness.

For two finite tuples, the full assertion that (8.1) says precisely
"finite correspondence" is now proved. The literal projections of
$`k[X,Y]/I(v,w)` to the two tuple loci have dense image. The literal
coordinate quotient has Krull dimension one and both generic-fibre
projections are finite if and only if the two algebraicity and two
rank-one clauses hold:

{docstring AclGeom.pairLocus_finiteCorrespondence_iff}

The two literal quotient maps correspond to injective inclusions of the
generated rings, which proves dominance. The prime vanishing ideal
already makes the joint locus irreducible. The finite-tuple dimension
theorem and algebraic-extension invariance of transcendence degree give
the rank clauses in both directions. The reverse projection uses the
canonically reordered generated ring $`k[w,v] = k[v,w]`. These are the
actual generic-fibre tensor rings. Mathlib's `pullbackSpecIso` identifies
their spectra with the scheme-theoretic generic fibres; the theorem is
stated for the tensor rings and their spectrum projections. The existing
coordinate-ring equivalence matches the literal projection maps. No rationality premise or
supplied rank,
algebraicity or dominance certificate is added outside the equivalence.
The base, ambient and two index types lie in four independent universes;
no algebraic-closedness hypothesis is used.

# Tuple correspondence germs and actual components
%%%
tag := "tuple-correspondence-germs"
%%%

A tuple presentation stores a source of rank one and the two coordinatewise
algebraicity clauses of (8.1). Its ideal is the vanishing ideal of the joint
tuple. Presentations compose at a literally shared middle tuple; a germ is
an ideal with the existence of a presentation:

{docstring AclGeom.TupleCorrespondencePair}

{docstring AclGeom.TupleCorrespondenceGerm}

Composition keeps all possible shared-middle presentations. It is a
relation, with no binary composite selected:

{docstring AclGeom.TupleCorrespondenceGerm.Composes}

In an algebraically closed ambient field, the relation is associative for
four finite tuple index types, in independent universes:

{docstring AclGeom.TupleCorrespondenceGerm.composes_assoc}

A composite exists whenever the contracted middle ideals agree. This
existence theorem requires only finiteness of the middle index type:

{docstring AclGeom.TupleCorrespondenceGerm.exists_composes_of_middle_ideal_eq}

For fixed presentations with literally shared middle tuple, and three
finite index types, the following equality of sets of ideals proves both
directions of the geometric link. Every middle-dominating component of the
actual incidence spectrum produces a composite germ whose carrier is its
vanishing ideal contracted to the endpoint variables. Every composite
carrier arises in this way:

{docstring AclGeom.TupleCorrespondenceGerm.composes_ofPair_carriers_eq}

The incidence ideal stays fixed. An ambient automorphism aligns the middle
tuples or the intermediate endpoint tuples. Equality of pair ideals
transfers rank and closure to new presentations. Primality of the mapped
joint ideal and the quotient contraction formula identify the endpoint
ideal; the all-component classification supplies both directions. The
presentations are arbitrary finite tuples, so their function fields need
not be rational; the base field is arbitrary. All three theorems derive
their alignment and component facts internally.

# Threefold components and normalized generic germs
%%%
tag := "threefold-incidence-components"
%%%

For presentations $`(x,y)`, $`(y,z)` and $`(z,w)` with literally shared
middle tuples, both parenthesizations have exactly the endpoint ideals
$`I(x',w')` obtained while keeping both middle tuples fixed and preserving
the two outer pair ideals:

{docstring AclGeom.TupleCorrespondenceGerm.composes_threefold_carriers_eq}

The next theorem identifies this set with all endpoint contractions of the
vanishing ideals of the actual four-block incidence components whose image
under the literal middle-pair projection is dense:

{docstring AclGeom.TupleCorrespondenceGerm.composes_threefold_components_eq}

The ring is the literal quotient of $`k[X,Y,Z,W]` by the sum of the three
extended consecutive pair ideals. The middle projection is induced by the
renaming of $`Y,Z`, and the endpoint contraction uses the renaming of $`X,W`.
Both inclusions construct genuine witnesses. The four index types are finite;
the base is arbitrary and the ambient field is algebraically closed, in six
independent universes. The given correspondence presentations supply the
algebraicity clauses internally; no rank, freshness, component or realization
certificate is added.

For every irreducible component, let $`\mathfrak p` be its vanishing ideal
contracted to the four-block polynomial ring and let $`A=k[X,Y,Z,W]/\mathfrak p`.
The theorem also constructs the componentwise normalization
$`N=\operatorname{integralClosure}_A\operatorname{Frac}(A)`. It proves that $`N`
is integrally closed and gives a fraction-field isomorphism with
$`\operatorname{Frac}(A)`, fixing every original coordinate. The literal kernel
of the endpoint map into $`\operatorname{Frac}(N)` is the same endpoint
contraction. Thus normalizing each component preserves its endpoint generic
germ. This conclusion holds for all components, including those whose middle
image is not dense. It forms normalization componentwise; no normalization of
the whole possibly non-domain ring is asserted. The joint field can still be
properly larger than the endpoint-image field.

The proof clears polynomial denominators to transfer the two outer algebraicity
clauses to each prime above the incidence ideal with the correct middle
contraction. An algebraically closed-field lift realizes the prime with both
middle tuples fixed. Algebraic incomparability gives equality of the outer
pair ideals and minimality of every realized joint prime. The germ-side
alignment uses ambient automorphisms and reuses relational associativity for
the second parenthesization. A single private normalization helper has the
third conclusion as its only consumer. Checking limits are unchanged.

# Scalar germs and actual incidence components
%%%
tag := "scalar-incidence-components"
%%%

The original scalar API stores branch ideals in $`k[X_0,X_1]`.
The next theorem identifies the carrier ideals of its scalar composites
with the endpoint contractions of all actual middle-dominating incidence
components. It constructs a scalar composite for every such component,
and proves that every scalar composite carrier arises this way:

{docstring AclGeom.FiniteCorrespondenceGerm.composes_ofPair_carriers_eq}

The actual incidence ring uses three single-coordinate tuples, indexed by
$`(\operatorname{Fin}1\oplus\operatorname{Fin}1)\oplus\operatorname{Fin}1`.
Its ideal is the sum of the two extended pair ideals, and the middle
projection is the literal quotient map. The explicit map
$`![\operatorname{inl}0,\operatorname{inr}0]` reindexes only the endpoint
carrier to $`k[X_0,X_1]`; no spectrum transport is supplied or needed.
The ambient field is algebraically closed, while the base is arbitrary;
the two field universes remain independent. The given scalar
presentations retain their genuine genericity and algebraicity clauses.

Two private converters relate scalar presentations and tuples indexed by
$`\operatorname{Fin}1`. The dimension theorem turns a transcendental
coordinate into the tuple rank-one clause. Conversely, rank one excludes
algebraicity over the base, so a tuple presentation gives a genuine
scalar presentation. Reindexing the point ideals in both directions
transports the tuple carrier-set equality to the original scalar API.
This supplies the actual incidence-spectrum link beyond the earlier
function-field tensor realization. The component's joint field remains
distinct from its possibly smaller endpoint-image field.

# Field clauses of tuple correspondences
%%%
tag := "tuple-correspondence-fields"
%%%

The target rank-one clause of (8.1) follows from the stored source rank and
mutual algebraicity. This needs no finite-index or algebraic-closedness
hypothesis:

{docstring AclGeom.TupleCorrespondencePair.target_rank}

For two finite tuples, the joint field is finite over each coordinate field
exactly when each coordinate of either tuple is algebraic over the field
generated by the other. This is the function-field criterion in (8.1),
using the actual common generated joint field and its two canonical
inclusions. The base and ambient fields are arbitrary; no rank-one or
algebraic-closedness hypothesis is needed:

{docstring AclGeom.pairField_finiteDimensional_iff}

Finite dimension makes each coordinate algebraic; the converse adjoins a
finite algebraic tuple. Neither direction asks the caller for a field
algebraicity certificate. The actual generic-fibre finiteness criterion and the
full geometric criterion of (8.1) are proved above.

For actual generated tuple fields, the endpoint field lies in the joint
field:

{docstring AclGeom.endpointField_le_jointField}

If the middle tuple is finite and algebraic over the endpoint field, the
joint field is finite over it. The outer tuples, base field and ambient
field are arbitrary:

{docstring AclGeom.jointField_finiteDimensional}

Under the four closure clauses of (8.1) and three finite index types, the
joint field is also finite over each end field. Rank-one and
algebraic-closedness premises are unnecessary for this field conclusion:

{docstring AclGeom.jointField_finiteDimensional_over_ends}

These statements use the actual generated subfields and Mathlib's inclusion
structures. Restriction of scalars identifies each extension with a field
adjoin of a finite algebraic tuple, and Mathlib proves finite dimension.
For target rank, both fields have the same transcendence degree as the
joint field: the relative tower summand is zero, so no infinite-cardinal
cancellation is used. The finite-dimension and target-rank conclusions are
derived internally.

The threefold incidence-component comparison, including componentwise normalization,
is proved above. The finite-coordinate correspondence calculus of §8.1 is
proved; the selected parameter-family component identities are proved in the
configuration chapter. Coherent branches and their common normal cover remain obligations.

# Component fields and endpoint images
%%%
tag := "component-fields-and-endpoint-images"
%%%

A shared-middle chain $`(x,y,z)` has joint field $`k(x,y,z)`. The field of
its endpoint image is $`k(x,z)`, which can be properly smaller. The finite
correspondences $`x=y^2` and $`z=y^2` give a concrete example: the chain field
is $`k(y)` and the endpoint image is the diagonal with field $`k(y^2)`.
Mathlib's degree-two calculation in the rational-function model proves that
this inclusion is proper, even in characteristic two. The actual selected-branch example is:

{docstring AclGeom.exists_compositeBranchField_lt_chainField}

The existing `compositeBranchField_le_chainField` proves the correct inclusion,
and `chainOverComposite_finiteDimensional` proves finiteness. The tensor
component's compositum is the joint field, as proved by
`tensor_compositum_eq_chainField`; it is not identified with the endpoint
field. This corrects the endpoint-field reading of the original §8.1 wording,
reported on issue #5 before the source annotation. The original paragraph is
retained. Relational germ associativity remains proved.

The canonical fiber-product, literal relative tensor and full incidence quotient results above
apply to arbitrary tuples, including generic-tuple presentations of general curve
function fields. The chosen joint prime is a
middle-dominating component under the stated source algebraicity clause. Under the
finite-outer-tuple and algebraically closed ambient hypotheses above, every middle-dominating
component is realized by a joint locus. The tuple theorem above realizes every component's
endpoint contraction with an internally constructed composite germ, and composition is
relationally associative. The generated joint field's inclusion and finite extension of the
endpoint field, and its finiteness over both end fields, are proved above. The actual component
coordinate-ring and function-field/compositum identifications are also proved above, with
polynomial representative formulas. The scalar specialization and the threefold
incidence-component comparison, including normalized generic germs, are proved above.
The geometric generic-point presentation bridge is proved above by
`exists_idealOf_eq_iff`, and the full finite-coordinate generic-extension
lemma is proved above. The selected parameter-family component identities are
proved in the configuration chapter; coherent branches and their common normal cover
remain open. The actual endpoint contraction retains the scalar field distinction.

# Tensor-domain regularity
%%%
tag := "tensor-domain-regularity"
%%%

Over an algebraically closed base k, the tensor product of any two field
extensions is a domain. This is the scalar-extension domain brick in
blueprint Lemma 8.1(a), tracked separately in issue #11:

{docstring AclGeom.isDomain_tensorProduct_of_isAlgClosed}

The proof places finite tensor coefficients in a finitely generated subalgebra.
Jacobson and Zariski lemmas derive a k-valued algebra map avoiding a nonzero
product of coefficients. A basis of the other field shows both tensors stay
nonzero after specialization; flatness injects the finite subalgebra tensor
product into the original one. All three private helpers are consumed.
This uses finite generation as an algebra, rather than as an intermediate field.

An actual PRIVATE consumer derives the tensor-domain instance and applies
Mathlib's common-field construction to obtain linearly disjoint field images.
This discharges the tensor-domain obligation of #11. The full finite-coordinate
generic-extension lemma is proved above. The finite-tuple composition and
component comparisons, guarded chart and public reconstruction theorem are proved
in their respective chapters. The earlier regularity scaffolding is marked superseded
with an issue reference, and its mathematical declarations remain unchanged.
The proof route differs from the blueprint's separating-basis sketch.
Its independent-left tensor relation argument does not establish absence
of zero divisors; that proof-sketch gap is reported on issue #11, and the
original wording is retained.
Frozen M4a sources remain unchanged.

# Prime ideals after scalar extension
%%%
tag := "geometric-prime"
%%%

The coordinate-ring step of blueprint Lemma `generic-extension` (a)
holds for any prime polynomial ideal over an algebraically closed base
and any field extension, with arbitrary variable type:

{docstring AclGeom.isPrime_map_of_isAlgClosed}

The quotient domain embeds in its fraction field. Tensoring that
embedding with the extension field preserves injectivity by flatness;
the tensor-domain theorem above supplies the target domain. Existing
tensor quotient and polynomial equivalences then give the extended
prime ideal. The one private domain helper is consumed by this theorem.

The private checked consumer `GenericScalarPoint` starts from an arbitrary
tuple, derives the extended quotient domain and constructs its canonical
fraction-field point. Its ideals over the original and extension fields
are exact, and independent affine-space coordinates remain independent
over the extension. No domain, prime-ideal, density or point oracle is
supplied by the caller. The coordinate-subfamily form is proved in the
next section, and the full field-freeness implication follows below.
Numerical field dimension and finite-tuple ambient automorphisms are proved
below. The finite-tuple Krull-dimension bridge is proved above.

The original proof's absolute transcendence-degree equality does not
by itself give independence when the coefficient extension has infinite
transcendence degree. Issue #5 records the counterexample to that inference;
the generic-over-extension premise and original proof wording are retained.
Frozen M4a is unchanged. The original group/chunk and scheme/action obligations
remain separate from the proved finite-tuple composition and guarded-chart route.

# Generic points and coordinate subfamilies
%%%
tag := "generic-subfamilies"
%%%

Blueprint Lemma `generic-extension` (a) has a constructive coordinate form
over any field extension of an algebraically closed base:

{docstring AclGeom.exists_genericPoint_baseChange}

The constructed point lives in the fraction field of the extended
coordinate ring. Its vanishing ideal over the extension is exactly the
extended original ideal, and its base-field ideal is exactly the original
one. Primeness is derived from the preceding theorem; faithful flatness
gives contraction. No prime, domain, exact-ideal, density or point oracle
is supplied by the caller. Three private helpers are consumed.

Every coordinate subfamily independent over the base remains independent
over the extension. Flatness preserves the injectivity of polynomial
evaluation; tensor polynomial and quotient equivalences identify this
with evaluation at the new point. This proves relative independence
directly, without cancelling infinite cardinal sums.

The two actual private consumers derive maximal coordinate independence
and test the dependent tuple (x,x): its singleton remains independent,
the repeated-coordinate relation survives, and both whole tuples are
proved dependent. Subfamily ideal comparison works across ambient fields;
the old single-ambient closure lemma is not used across fields.

Full field freeness and a closed ambient are proved in the next section.
Numerical field dimension and finite-tuple ambient automorphisms follow
below. The finite-tuple Krull-dimension and actual incidence-component bridges
are proved above, as is the full finite-coordinate generic-extension lemma.
The original scheme/action statements remain open (#21). The guarded initial chart and rank-five ACF
completeness are proved (`guardedAffineGridExtraction`, `jCompletenessACF`);
frozen M4a is unchanged.

# Every generic point has field freeness
%%%
tag := "generic-field-freeness"
%%%

The universal relation and field-freeness implication of blueprint
Lemma `generic-extension` (a) holds for every point generic over the
extension, expressed by its explicitly named vanishing-ideal equality:

{docstring AclGeom.isGeneric_baseChange}

The original ideal contracts exactly by faithful flatness. Tensor
quotient and polynomial equivalences identify extended quotient evaluation
with an injective map into the point's ambient field. Transporting the
two tensor factors' linear disjointness through that map gives disjointness
of the extension image and the coordinate ring generated by the point.
A basis remains independent over this ring; Mathlib's fraction-ring
independence theorem promotes it to independence over the generated
rational field. The new private subalgebra bridge is consumed, and the
existing contraction helper is reused. No algebraic closedness assumption
is needed for this universal implication.

An actual private consumer derives the genericity premise from the
constructive theorem above, embeds that same point into its ambient
field's algebraic closure, and applies the universal theorem there.
Both exact ideals, full field freeness and every independent coordinate
subfamily are obtained for that one point. A second consumer derives
affine-space genericity from independence over the extension over
arbitrary base fields. No domain, prime, point or freeness oracle is
supplied by the caller in the constructive consumer.

Together these results cover the relation and independence content of
part (a), including existence in a closed ambient and the universal
implication. The numerical field degree equality is proved below, and the
finite-tuple Krull-dimension bridge above. The full finite-coordinate
generic-extension lemma is proved above from membership and rank.
The existing function-field isomorphism, rational identities and finite-tuple
ambient automorphisms are accounted for below.
Finite-tuple composition, actual component comparisons, the guarded chart and
public reconstruction are proved. The family argument and original group/chunk
and scheme/action obligations remain open; frozen M4a is unchanged.

# Existing generic-point clauses
%%%
tag := "existing-generic-clauses"
%%%

The first clause of blueprint Lemma `generic-extension` (b) was already
proved: equal vanishing ideals give an isomorphism of the rational fields
generated by the two tuples in their common ambient field.

{docstring AclGeom.locusFunctionFieldEquivOfIdealEq}

The existing coordinate equation sends each coordinate to its counterpart;
the reflexivity, symmetry and composition equations give coherent choices.
These results allow arbitrary fields and index types, without algebraic
closedness. An actual private consumer derives equal ideals from an
algebra embedding and checks the resulting coordinate equation. The
finite-tuple ambient extension, the second clause of (b), is proved in
the next section, including a checked enlargement consumer.

Mathlib already proves the literal rational-identity clause (c): canonical
fraction evaluation at an independent tuple is an isomorphism onto its
generated rational field.

{docstring AlgebraicIndependent.aevalEquivField}

The project already uses this equivalence in its transcendental relocation
embedding. Two actual private examples check equality of genuine rational
fractions and zero reflection under the canonical fraction lift. Both
evaluated denominators are derived nonzero from independence and polynomial
nonzero; the caller supplies no injectivity or field-isomorphism oracle.

The existing-clause audit in checkpoint `58bdf10` added no mathematical
declarations or mathematical source/dependency changes and reused both APIs.
Its three examples were checked with standard Mathlib lint and the default
kernel. Its 125 earlier fixture inputs and outputs were retained byte for
byte and were not rerun for that documentation checkpoint.

The finite-tuple Krull-dimension and actual incidence-component bridges are
proved above, including the scalar specialization and threefold normalized
generic-germ comparison over an arbitrary base in an ACF ambient. The full
finite-coordinate generic-extension lemma is proved above. The selected parameter-family
component identities are proved in the configuration chapter; coherent branches and their
common normal cover remain open (#5). The guarded initial
chart and rank-five ACF completeness are proved; the original scheme/action
statements remain open (#21).
Finite-tuple ambient automorphisms and numerical field dimension are proved
below; frozen M4a is unchanged.

# Ambient automorphisms of finite generic points
%%%
tag := "generic-ambient-automorphism"
%%%

The second clause of blueprint Lemma `generic-extension` (b) is proved
for finite tuples in an algebraically closed common ambient, over any
base field. The automorphism extends the entire existing isomorphism of
the generated rational fields and sends every coordinate to its counterpart.

{docstring AclGeom.exists_ambientAutomorphism_of_idealOf_eq}

The generated fields have equal finite transcendence degrees. Applying
the tower formula and cancelling this finite summand gives equal degrees
of their ambient complements, even when the ambient degree is infinite.
Relative transcendence bases therefore have equal cardinalities. The
existing semilinear independent-adjoin equivalence extends the generated-
field isomorphism across these matching bases. Both relative generated
fields have the same ambient as an algebraic closure, so Mathlib's existing
closure-equivalence theorem extends that isomorphism to the ambient field.
Its base equation proves linearity over the original base and every
coordinate equation. One new public theorem uses zero new helpers;
no caller rank, complement basis or automorphism premise is supplied.

An actual private consumer uses the existing relocation theorem with
its explicit independence, containment and algebraicity hypotheses.
It derives the second point and ideal equality, then obtains the full
field extension and automorphism at that same point while retaining
algebraicity over the prescribed relocated coordinate field. A second
example starts in an arbitrary nonclosed ambient with an actual algebra
endomorphism. It derives equal ideals after embedding the finite tuple
into the ambient's algebraic closure and obtains an automorphism there.
No exact ideal, rank or automorphism is supplied by the caller; the second
point comes from the relocation theorem or from the given endomorphism.

For a closed ambient no enlargement is needed. The finite hypothesis is
essential for the cancellation argument and for extension inside the
unchanged ambient. The theorem makes no claim for infinite tuples.
The field content of (a), finite (b) and literal (c) now has formal proofs;
the numerical field degree follows below. The finite-tuple coordinate-ring
Krull dimension equals this transcendence degree by the theorem above, and
the tuple germ theorem identifies composites with endpoint images of the
actual incidence components. The full finite-coordinate generic-extension
lemma is proved above, including the source membership and rank criterion.
The selected parameter-family component identities are proved in the configuration chapter.
Coherent branches, their common normal cover (#5) and the original scheme/action
statements (#21) remain open. The guarded initial chart
and rank-five ACF completeness are proved. Frozen M4a is unchanged.

# Generic-point dimensions after scalar extension
%%%
tag := "generic-field-dimension"
%%%

The numerical field dimension in the proof of blueprint Lemma
generic-extension (a) is derived for every point with the exact extended
vanishing ideal, over arbitrary fields and with arbitrary coordinate type:

{docstring AclGeom.trdeg_adjoin_of_isGeneric}

The existing universal theorem derives full field freeness from that
same genericity premise. A transcendence basis of k(b) therefore remains
independent over E: linear disjointness preserves the linear independence of the evaluated
monomials, and Mathlib's existing injectivity criterion for a mapped spanning family
reflects polynomial evaluation. No new independence helper is introduced.

Every coordinate is algebraic over this basis over k. Existing ambient
closure transport moves that fact into the common ambient. The same
annihilating polynomial, with its coefficients regarded in the larger
generated field, proves algebraicity over E. Existing closure transport
back into E(b) makes the family a transcendence basis there. Both relative
degrees equal its cardinality. One new public theorem uses zero new
helpers, with no closedness, finiteness, cardinal cancellation, or caller
rank, basis or freeness premise.

Two real private examples construct the same point using the earlier
existence theorem and derive its genericity and original ideal. In a
shared universe, the existing coordinate-ring equivalences, quotient
equality and fraction-field equivalence give a cross-ambient isomorphism
with the original point's generated field. The relative degree is thus
the original locus degree, and Mathlib's tower formula gives the source's
absolute degree equation at that point. A second example checks four
independent universes and the lifted absolute equation, measuring the
locus degree at the constructed point. It does not claim the original
point's degree comparison across all four universes.

This theorem measures locus dimension by the transcendence degree of its
generated rational field. The separate finite-tuple Krull-dimension bridge is
proved above, as is the full finite-coordinate generic-extension lemma.
The reported independence-inference gap and original proof are retained; field
independence is proved by the separate freeness route.
Finite-tuple composition, actual component comparisons, the guarded chart and
public reconstruction are proved. The family argument and original group/chunk
and scheme/action obligations remain open; frozen M4a is unchanged.

# Relocation of generic points
%%%
tag := "relocation"
%%%

Blueprint Lemma 8.1(b) provides *independent generic points*: inside an
algebraically closed ambient field, a finitely generated subextension embeds
over $`k` with prescribed images for a transcendence basis. The formalization
splits this into a purely transcendental part and an algebraic extension
part:

{docstring AclGeom.adjoinTranscendentalAlgHom}

{docstring AclGeom.exists_extension_of_isAlgebraic}

{docstring AclGeom.exists_relocation}

The joint form relocates one tuple over the field generated by another,
preserving all joint polynomial relations — this replaces the fiber-product
constructions of the classical argument:

{docstring AclGeom.exists_joint_relocation}

Relocations interact with the additive structure through substitution: a
joint-relation-preserving relocation preserves the loci of componentwise sums
and differences.

{docstring AclGeom.idealOf_add_eq_of_joint}

{docstring AclGeom.idealOf_sub_eq_of_joint}

# The additive correspondence theorem: state of the argument
%%%
tag := "additive-correspondence"
%%%

The hypothesis block of blueprint Theorem 8.8 packages two finite
correspondences with independent generic points and interalgebraic sums:

{docstring AclGeom.AddCorrSetup}

The fused curve-coset chain proceeds by relocating the second pair over the
base $`k(x_1, y_1)`:

{docstring AclGeom.AddCorrSetup.exists_pair_relocation}

The relocated pair inherits the entire correspondence structure — it is
still a two-way finite correspondence, its first coordinate is still generic
over the base, and its sum pair is a generic point of the *same*
one-dimensional sum locus:

{docstring AclGeom.AddCorrSetup.JointRel.snd_mem}

{docstring AclGeom.AddCorrSetup.JointRel.sum_snd_mem}

{docstring AclGeom.AddCorrSetup.JointRel.sum_fst_transcendental}

Finally, the δ-side genericity count: with the fresh element chosen
independent of $`\{x_1, x_2\}`, the relocated sum point remains generic over
the field generated by the translation element $`\delta = c_2 - c_2'`. This
is the input to the generic-translation-invariance step of the argument.

{docstring AclGeom.AddCorrSetup.JointRel.sum_fst_notMem_delta}

# The curve ideal and base change
%%%
tag := "curve-ideal"
%%%

The sum locus is a plane curve, and its vanishing ideal is generated by a
single prime polynomial — a height-one prime of $`k[X,Y]`, located between
the zero ideal and a maximal ideal in a ring of Krull dimension two:

{docstring AclGeom.exists_prime_span_idealOf}

The delicate point is that the generator stays prime after extending
scalars to the field $`k(\delta)` generated by the translation element.
This *base-change irreducibility* is proved without any tensor-product
regularity: the minimal polynomial over the extended field descends
coefficientwise, by a Gauss-lemma integrality argument combined with a
specialization brick — over an infinite field algebraically closed in
`K`, an element of `K(u)` algebraic over `k(u)` already lies in `k(u)`:

{docstring AclGeom.mem_adjoin_base_of_isAlgebraic}

{docstring AclGeom.minpoly_coeff_mem}

{docstring AclGeom.idealOf_map_eq_span}

# The exact translation identity
%%%
tag := "translation-identity"
%%%

A translation substitution perturbs a polynomial only strictly below its
top total degree, so a translation that fixes the ideal generated by `F`
fixes `F` itself:

{docstring AclGeom.translate_eq_self_of_span_eq}

Combining base-change irreducibility at both sum points with the transport
of vanishing ideals along translations yields the exact identity for the
sum-locus generator over $`k(\delta)`:

{docstring AclGeom.AddCorrSetup.JointRel.translate_deltaVec_eq}

The identity then descends from the generic point to every point of the
translation locus, whose coordinates are interalgebraic — the locus is a
genuine curve:

{docstring AclGeom.translate_eq_of_idealOf_le}

{docstring AclGeom.not_algebraicIndependent_of_translate_eq}

{docstring AclGeom.AddCorrSetup.JointRel.exists_prime_span_delta}

# The multiplicative correspondence theorem: state of the argument
%%%
tag := "multiplicative-correspondence"
%%%

The multiplicative chain (blueprint Theorem 8.9) runs in parallel with the
additive one — products replace sums, and the ratio element
$`\rho = c_2 / c_2'` replaces the translation element $`\delta`:

{docstring AclGeom.MulCorrSetup}

{docstring AclGeom.MulCorrSetup.exists_pair_relocation}

{docstring AclGeom.MulCorrSetup.exists_prime_span_mul}

The genericity counts go through with division playing the role of
subtraction, and the same base-change machinery applies over $`k(\rho)`.
The structural difference appears at the rigidity step: a scaling
substitution multiplies each monomial coefficient by the monomial value of
the scaling vector, so instead of an exact fixed-point identity the chain
produces *monomial relations* on $`\rho`:

{docstring AclGeom.scale}

{docstring AclGeom.monomial_prod_eq_of_span_scale_eq}

{docstring AclGeom.MulCorrSetup.JointRel.monomial_prod_rhoVec_eq}

These relations are nontrivial — a single monomial cannot vanish at the
nowhere-zero product point — which forces the coordinates of $`\rho` to be
interalgebraic: the ratio locus is a genuine curve.

{docstring AclGeom.exists_support_pair_of_aeval_eq_zero}

{docstring AclGeom.MulCorrSetup.JointRel.rho_snd_mem}

{docstring AclGeom.MulCorrSetup.JointRel.exists_prime_span_rho}

# The multiplicative endgame
%%%
tag := "multiplicative-endgame"
%%%

The classical endgame identifies the one-dimensional stabilizer subgroup
with the kernel of a character of $`\mathbb G_m^2` and reads off the coset
equations. The formalization takes a shorter, purely elementwise route.
The scaling relation at a support difference $`d = m - m'` of the
product-locus generator says exactly that the monomial value
$`\mu = (x_1x_2)^{d_0}(y_1y_2)^{d_1}` is *invariant under relocation* of
the second pair. An element algebraic over two independent extensions of a
common base is algebraic over the base — an exchange argument:

{docstring AclGeom.mem_racl_of_mem_racl_insert}

Applying this twice — against the fresh transcendental direction, then
against the generic direction of the product point itself — drops $`\mu`
into $`k`:

{docstring AclGeom.MulCorrSetup.JointRel.zpow_rho_support_eq_one}

{docstring AclGeom.MulCorrSetup.JointRel.exists_algebraMap_eq_zpow_mul}

Splitting $`\mu` along the independence of the two correspondence pairs
and descending each factor the same way yields both coset equations with
the same exponents, which are nonzero because algebraicity descends along
nonzero integer powers:

{docstring AclGeom.mem_racl_empty_of_zpow}

{docstring AclGeom.MulCorrSetup.exists_coset_equations}

This core keeps one fresh element explicit. The literal source endpoint below supplies
freshness internally and uses the blueprint's orientation of both equations.

# The additive endgame
%%%
tag := "additive-endgame"
%%%

The additive side classifies the δ-curve itself. Its generator is
canonical — independent of the relocation used to construct it — by
joint-type determination along the correspondence curve:

{docstring AclGeom.joint_idealOf_eq}

{docstring AclGeom.AddCorrSetup.delta_idealOf_eq_of_two_relocations}

A second, independent relocation then produces an independent generic
point of the *same* curve, and the exact translation identity at the
correspondence curve pushes their sum back onto it — the group chunk —
while a transfer to the diagonal puts the origin on the curve:

{docstring AclGeom.AddCorrSetup.JointRel.translate_pair_eq}

{docstring AclGeom.AddCorrSetup.JointRel.chunk_add}

{docstring AclGeom.AddCorrSetup.JointRel.constantCoeff_delta_gen}

The chunk upgrades to the Hopf identity in exact form — the generator is
fixed by translation by its own generic point — and then to full
additivity by the division argument: the additivity defect is a multiple
of the generator in each variable block, the block extensions are coprime
primes, and the total degree leaves no room for their product.

{docstring AclGeom.AddCorrSetup.JointRel.translate_delta_self_eq}

{docstring AclGeom.mem_span_rename_inl_of_aevalFst_eq_zero}

{docstring AclGeom.AddCorrSetup.JointRel.addSubst_delta_gen_eq}

The coset constants descend to `k` by the same relocation-invariance and
double-exchange argument as in the multiplicative endgame, and splitting
the generator into its one-variable specializations produces the additive
polynomials of the classification:

{docstring AclGeom.AddCorrSetup.JointRel.exists_coset_constants}

{docstring AclGeom.AddCorrSetup.exists_coset_equations}

This is the two-pair core of the additive correspondence theorem
(blueprint Theorem 8.8), with two fresh elements explicit.

# The original correspondence statements
%%%
tag := "literal-correspondence-statements"
%%%

The original additive theorem concerns three pairs with a common first curve. Each of
the two-pair results yields a prime split generator. Translating each generator by a
root of its additive polynomial preserves primality. Both translated generators belong
to the same principal prime ideal of the first curve, so they are associates. This gives
one pair of nonzero additive polynomials for all three original pairs:

{docstring AclGeom.addcorr}

The two sum-translation constants are part of the conclusion. Evaluation in an arbitrary
commutative algebra preserves the additivity of a polynomial over an infinite field:

{docstring AclGeom.IsAdditive.aeval_add}

The multiplicative endpoint gives the original orientation with both nonzero integer
exponents and both nonzero constants:

{docstring AclGeom.mulcorr}

Both theorems assume the source ACF setting. They impose no ambient rank, freshness or
universal-domain hypothesis: they pass to the algebraically closed extension
`FreshAmbient Ω`, use its four independent variables, and pull the equations back through
the injective embedding. Closure transport reuses `algHom_racl_image_eq_of_racl_eq`.
The additive theorem omits the unused independence premise for the second triple and is
therefore stronger than the source statement. The separate additive- and torus-subgroup
classifications are proved below. The general curve-coset lemma is proved at the end of
this chapter.

# Connected additive subgroups
%%%
tag := "connected-additive-subgroups"
%%%

For a closed additive subgroup `H ⊆ k²`, its canonical coordinate ring is
`k[X₀,X₁] ⧸ I(H)`, where `I(H)` is its vanishing ideal. Closedness means that the zero locus
of `I(H)` is `H`. Connectedness is connectedness of the prime spectrum of this coordinate
ring, and dimension is its Krull dimension. Under the source hypotheses, the theorem
classifies the ideal and the point locus with two nonzero additive polynomials:

{docstring AclGeom.addSubgroup_classification_of_connected}

The proof derives primality of `I(H)` from connectedness. If two irreducible components
meet at `c`, the closure of their sum minus `c` has a prime vanishing ideal lying between
`I(H)` and both component ideals, so minimality makes the components equal. Distinct
components are disjoint and their ideals are comaximal. The Chinese remainder theorem
would then give a nontrivial idempotent in the coordinate ring; connectedness of its
spectrum forces every idempotent to be zero or one. Thus only one component remains.

The one-dimensional prime-ideal step uses the Nullstellensatz, translation invariance
and the additive defect's degree bound:

{docstring AclGeom.addSubgroup_classification}

The characteristic clauses follow from the existing `IsAdditive.eq_C_mul_X` in
characteristic zero and `IsAdditive.coeff_eq_zero_of_ne_pow` in characteristic `p`:
the polynomials are linear in the first case and have only `p`-power exponents in the
second. These give the additive part of blueprint `subgroup-classification` in its
connected source scope. The multiplicative part follows next; the general curve-coset
lemma is proved at the end of this chapter.

# Connected subgroups of the torus
%%%
tag := "connected-torus-subgroups"
%%%

For a subgroup `H ≤ kˣ × kˣ`, use the standard closed embedding
`(u,v) ↦ (u,v,u⁻¹,v⁻¹)` into affine four-space. Its canonical coordinate ring is
`k[X₀,X₁,X₂,X₃] ⧸ I(H)`, where `I(H)` is the vanishing ideal of the image. Connectedness
and dimension are those of this coordinate ring's prime spectrum. With closedness and
both projections nonconstant, the source theorem gives nonzero integer exponents and the
equation of every coset, including its nonzero constant:

{docstring AclGeom.mulSubgroup_classification_of_connected}

The proof derives primality internally. One shared theorem handles both subgroup
classifications using concrete polynomial operations:

{docstring AclGeom.isPrime_vanishingIdeal_of_connected}

The additive consumer supplies translations for `u + v - c`; the torus consumer supplies
coordinate scalings for `u * v * c⁻¹`. Closedness is in the torus, expressed through its
embedding into affine four-space. Closedness in affine two-space would be a stronger
hypothesis, excluding the nonzero diagonal. Connectedness of the plane closure gives the
wrong test: in characteristic different from two, `u² = v²` is disconnected in the torus
while its plane closure is connected.

After clearing denominators, the plane closure has a height-one prime ideal generated by
an irreducible polynomial. Scaling invariance and two support monomials give a character
relation. Primality and algebraic closedness remove its common integer factor; the
nonconstant projections make both exponents nonzero. Bézout's identity parametrizes the
primitive character kernel. If the subgroup missed a point of that kernel, a nonzero
one-variable polynomial would make its preimage finite, contradicting infinitude of the
subgroup. Translation then gives every coset equation. This proves part (b) of blueprint
`subgroup-classification`; the general curve-coset result is proved at the end of this chapter.

# The simultaneous-coset lemma
%%%
tag := "simultaneous-coset"
%%%

Blueprint 8.9-lemma combines the additive and multiplicative coset
equations at each of the two correspondence curves. The polynomial input
is a classification of the primes that can divide a shifted
additive-split polynomial: they are the coset binomials
$`X^m - c\,Y^n`, which are prime exactly when the exponents are coprime —
proved by a parametrization-kernel argument rather than Newton polygons:

{docstring AclGeom.cosetBinomial_prime}

{docstring AclGeom.mvBinomial_prime}

{docstring AclGeom.eq_smul_binomial_of_dvd_shift}

At each curve, both the multiplicative binomial and the shifted additive
generator vanish on the generic point, so the prime generator divides
both; a sign trichotomy on the integer exponents and an elementary
denominator-clearing argument rule out the mixed orientations:

{docstring AclGeom.sign_cases_of_zpow_relation}

{docstring AclGeom.simultaneous_coset_at_curve}

{docstring AclGeom.no_mixed_relation}

The classification leaves a monomial additive polynomial on each side,
and additivity of a monomial pins its exponent to a power of the
exponential characteristic — a statement uniform across characteristics:

{docstring AclGeom.monomial_isAdditive_expChar}

{docstring AclGeom.simultaneous_coset}

# Rigidity of `j`
%%%
tag := "j-rigidity"
%%%

The last theorem of the hard kernel (blueprint Theorem 8.10) upgrades the
simultaneous coset relations to an exact common power of Frobenius, using
the fifth `j`-coordinate $`x(1+a) \sim y(1+b)`. Three steps. First, a
degenerate application of the multiplicative correspondence theorem — at
the pair $`(t, t)` — shows that interalgebraic elements whose products
with a common generic factor remain interalgebraic differ by a constant:

{docstring AclGeom.base_ratio}

This algebraically closed core takes a supplied fresh third element. The
reconstruction chapter now proves the no-fresh relative base-ratio
corollary and actual base membership under an explicit relatively closed
base hypothesis, by adjoining a rational-function variable. The actual reconstructed map
now satisfies base recovery, both scalar-one conclusions, full tuple/outside-point recovery
and all-point propagation, with the source-setting producers supplying the explicit inputs.
The public `reconstruction_target` supplies both completeness proofs internally: under the
blueprint hypotheses its Φ carries the perfected base onto the perfected base and satisfies
φ(M) = Φ(M^perf) ∩ L. The original literal interpretation proofs retain their provenance;
the corrected interpretation and R1--R4 dispositions are recorded on closed #8/#23/#9.

Second, perfection: the base field is algebraically closed, so the coset
constant has roots of every Frobenius order, and injectivity of the
Frobenius turns the coset relation into an exact twist
$`y = \lambda\,x^{q^e}` in one direction or the other:

{docstring AclGeom.pow_expChar_pow_injective}

{docstring AclGeom.frobenius_normalize}

Third, the normalization: applying the Frobenius to the fifth coordinate
(freshman's dream), dropping constant factors, and comparing coefficients
at the transcendental $`a^{q^e}` via the base-ratio lemma forces
$`\lambda = 1`:

{docstring AclGeom.lambda_eq_one}

{docstring AclGeom.j_rigidity}

The elementwise correspondence results, simultaneous-coset classification,
and the power-equality core `j_rigidity` are proved uniformly in the exponential
characteristic. The next section supplies its freshness internally and records the exact
integer-uniqueness correction. The original three-pair additive and multiplicative
correspondence statements are proved above without freshness hypotheses. The connected
additive- and torus-subgroup classifications are also proved. The general curve-coset
statement is proved below. Coherent branch triples and their common normal cover remain open
in #5. The selected parameter-family component identities are proved in the configuration
chapter. The geometric generic-point presentation bridge and full finite-coordinate
generic-extension lemma are proved above, with the necessary ambient-size
bounds for existence.
The tensor-domain obligation #11 is proved above;
the rational group and affine action construction remain open in #12 and #21.


# The normalized exponent of an actual j-tuple
%%%
tag := "j-rigidity-normalized-exponent"
%%%

The source's literal claim of a unique integer exponent is false in characteristic zero.
Its stated convention uses exponential characteristic one and every integral Frobenius
iterate. For the self-pair of an independent j-tuple, zero and one are distinct valid
exponents. More generally every pair of equal actual j-tuples in characteristic zero
has equal entries, while its unnormalized integer exponent is not unique. The correction
requires the exponent to be zero when the exponential characteristic is one.

{docstring AclGeom.existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq}

This theorem takes both actual independent pairs and their actual five-point tuple equality.
It works over an arbitrary base and a perfect ambient field, with no algebraic closedness,
RAC, ambient-rank, supplied freshness or completeness input. Its two field universes are
independent. In positive characteristic the normalization condition is vacuous, so the
integer itself is unique. In characteristic zero the normalized integer is zero and the
pair is equal.

The proof lifts the representatives and all five point equalities to `FreshAmbient K`.
The four added variables supply the two fresh elements required by the existing rigidity
core. Its equalities of natural powers reflect through the injective embedding. Perfection
turns them into one integral Frobenius exponent. Exponent separation is used only in
positive characteristic, on the actual transcendental first coordinate.

{docstring AclGeom.jTupleOf_eq_charZero_and_exponent_not_unique}

The second theorem proves the source's characteristic-zero pair equality and refutes the
literal integer uniqueness for every such actual tuple equality, using the distinct
exponents zero and one. There are exactly two new public declarations, with standard
axioms and no helper, private, internal or generated addition.

[#32](https://github.com/adamtopaz/acl_geom/issues/32) records the counterexample before
source edits and the independent convention review. The original theorem and proof stay
as provenance. Two downstream source proof steps need the same characteristic split:
J descent fixes the pair directly in characteristic zero, and same-parameter injectivity
uses equality of the pair directly there. Their true statements are already proved;
the source annotations qualify the original orbit/polynomial arguments without changing
the proof blocks. The main reconstruction target already restricted exponent uniqueness
to positive characteristic and is unchanged. Original group/chunk, coherent-cover,
scheme/action obligations remain open.


# Additive finite-correspondence curves as cosets
%%%
tag := "additive-finite-correspondence-cosets"
%%%

The additive finite-correspondence case of blueprint `curve-coset` is now proved over
algebraically closed base and ambient fields. Take actual pairs `(x₁,y₁)` and `(x₂,y₂)`
with `[xᵢ]=[yᵢ]`, independent `x₁,x₂`, and `[x₁+x₂]=[y₁+y₂]`. The third curve is the
locus of their sum. Both projections of each curve are nonconstant.

{docstring AclGeom.curveCoset_additive_of_finiteCorrespondence}

The conclusion constructs an actual additive subgroup `H ⊆ k²`, a prime polynomial
`F` and two base-field vectors `g₁,g₂`. Its canonical vanishing ideal is exactly
`span{F}` and its zero locus is `H`. The prime spectrum of `k[X₀,X₁]/I(H)` is connected
and its Krull dimension is one. Separate witnesses show that both projections of `H`
are nonconstant. These supply all the hypotheses of the already proved
`AclGeom.addSubgroup_classification_of_connected`, the next step of the source
additive-correspondence proof.

All three actual curve ideals are the principal ideals of the corresponding translated
polynomial. Their base-field point loci are exactly `g₁+H`, `g₂+H` and `(g₁+g₂)+H`.
The sign of the polynomial translation is negative: a coset `g+H` has equation
`translate (-g) F = 0`. The two field universes are independent. There is no ambient-rank,
supplied freshness or completeness premise.

The proof supplies the additive core's fresh elements internally in `FreshAmbient Ω`,
then reflects its two constant-value equations to the original ambient field. Roots
over the algebraically closed base choose the translations. Prime generators identify
the three curve ideals; the Nullstellensatz gives the subgroup's canonical ideal.
A translated nonzerodivisor in a maximal ideal of height two gives dimension one, and
the prime quotient gives connectedness. The third constant is the sum of the first two.

This additive theorem has standard axioms and no helper, private, internal or generated
additions. Its explicit polynomial ideals, projection witnesses and field-tuple input supply
the source additive-correspondence argument. These retain their own useful scope alongside
the general group theorem below. It allows abstract torus and constant-coordinate cases
once the ambient group is presented as an `AlgebraicGroup`. The concrete additive-plane
and torus objects are constructed below; the tuple-to-scheme generic-product bridge
remains separate.
The full shared goal remains open on [#5](https://github.com/adamtopaz/acl_geom/issues/5).


# Generic curve products in algebraic groups
%%%
tag := "general-curve-cosets"
%%%

Blueprint `lem:curve-coset` is proved for closed irreducible curves in an algebraic group
over an algebraically closed field. The ambient group need not be connected. Independence
of the two generic points is expressed by a jointly generic point of the actual scheme
product of their reduced induced subschemes. Its product need only belong to the third
curve; the source's stronger genericity assumption implies this membership.

{docstring AclGeom.curveCoset_of_genericProduct}

The result constructs a `ConnectedAlgebraicGroup`, a genuine group morphism into the
ambient group, a closed immersion and dimension one. Writing its image as `H`, the three
curves are exactly `g₁ H`, `H g₂` and `g₁ H g₂`. There is no supplied subgroup, product
irreducibility, operator restriction, ambient rank, freshness or completeness premise.
The statement permits abstract torus and constant-coordinate cases once the ambient
group is presented as an `AlgebraicGroup`. The concrete additive-plane and torus objects
appear below. Turning the source tuple loci and independence into the required scheme
curves and jointly generic product point remains separate; the earlier additive theorem
has its own coordinate interface.

For a commutative ambient group, all three are left cosets of the same subgroup:

{docstring AclGeom.curveCoset_of_genericProduct_commutative}

The proof first establishes integrality of the actual product of integral schemes over
an algebraically closed field. It uses the existing domain theorem for tensor products
of fields and scheme-theoretic dominance under flat base change. It does not identify the
scheme product with the ordinary product topology. Closed-point density then turns the
generic-product input into the product condition on all base-field points.

Each translate of the first curve by a point of the second is a closed curve in the third
of the same dimension, hence equal to it. A sandwich between two translated curves gives
the closed subgroup set. The reduced induced scheme carries actual restricted unit,
multiplication and inverse morphisms; a monic inclusion checks all group laws.

{docstring AclGeom.exists_connectedClosedSubgroup_of_points}

Finite type, quasi-compactness, separatedness and geometric integrality are derived.
Thus the conclusion supplies the algebraic subgroup itself, rather than leaving its
scheme structure as an open hypothesis. The source's original statement and proof remain
preserved. Original group/chunk, six-point, affine-action, coherent-cover, algebraization
and scheme/action/descent obligations remain open; this theorem does not supply an
ambient algebraic group for an earlier group-extraction argument.


# Concrete group schemes and the affine action on the line
%%%
tag := "concrete-affine-action"
%%%

The target action in blueprint (8.4a) now exists as an actual scheme action over every
field k. The additive vector group uses the symmetric algebra with primitive generators;
its antipode is negation. Mathlib already supplies the bialgebra and the passage from a
Hopf algebra to a group scheme. The new antipode and the point-coordinate equivalences
complete this construction.

{docstring AclGeom.AdditiveGroupScheme.algebraicGroup}

{docstring AclGeom.AdditiveGroupScheme.pointsMulEquiv}

Its scheme dimension is n. The multiplicative group is the spectrum of the Laurent
polynomial algebra `k[ℤ]`,  with its usual group-like Hopf structure. Its base-field points
are the units of k, and products give the actual torus Gm².

{docstring AclGeom.multiplicativeGroup}

{docstring AclGeom.multiplicativeGroupSq.pointsMulEquiv}

These commutative group schemes make the additive plane and torus available as ambient
objects for the general curve-coset theorem. The source tuple-locus-to-scheme-curves and
jointly generic product bridge is still needed to instantiate that theorem directly
from the correspondence hypotheses.

The affine group has coordinate algebra `k[a,a⁻¹,b]`. Its comultiplication sends a to a⊗a
and b to a⊗b+b⊗1; thus the scheme multiplication is the semidirect-product law, and its
base-field points form the existing group of invertible affine transformations.

{docstring AclGeom.AffineGroupScheme.pointsMulEquiv}

The coordinate ring is a polynomial ring in b over the Laurent polynomial ring. The
latter is a nonfield principal ideal domain, so it has dimension one. The affine group
has dimension two over every field, and over an algebraically closed base the actual
connected algebraic-group package is constructed internally.

{docstring AclGeom.AffineGroupScheme.dimension}

{docstring AclGeom.AffineGroupScheme.connectedAlgebraicGroup}

The action morphism is the spectrum of X↦a⊗X+b⊗1. Its unit and associativity identities
are checked on points over arbitrary commutative k-algebras, using the actual affine
spectrum isomorphism for the products. Mathlib's existing ModObj interface records the
scheme action laws.

{docstring AclGeom.AffineSchemeAction.modObj}

{docstring AclGeom.AffineSchemeAction.lift_groupPoint_linePoint_smul}

Faithfulness holds for points over every commutative coefficient algebra C in the base
universe: fixing 0 and 1 forces b=0 and a=1. The ring-level coordinate formulas allow an
independent coefficient universe. No Hopf structure is required on C.

{docstring AclGeom.AffineSchemeAction.eq_one_of_lift_smul_eq}

This realizes the concrete standard affine model in (8.4a). The classification of an
arbitrary connected two-dimensional algebraic group acting on a curve, the required
normal subgroup, original group/chunk and six-point producers, and scheme/action
algebraization and descent remain open. All eight original requirements of
[#21](https://github.com/adamtopaz/acl_geom/issues/21) remain obligations. The full shared
goal remains active and incomplete.


# From scheme curves to function-field actions
%%%
tag := "scheme-curve-function-field"
%%%

An integral curve scheme, locally of finite type over an arbitrary field k and of scheme
dimension one, now supplies the curve library's one-variable field hypothesis internally.
Its field is the actual stalk at the scheme's generic point. The base algebra comes from
the given morphism to Spec k, rather than from an additional caller choice.

{docstring AclGeom.scheme_functionField_isFunctionFieldOneVar}

The class asks for a transcendental element t and finiteness over k(t); this needs no
perfectness or separability premise. The proof chooses a nonempty affine open of dimension
one, identifies its section domain's fraction field with the actual generic stalk, and
uses the existing Noether-normalization dimension calculation. The affine open comes
from a strict chain of irreducible closed subsets and Mathlib's order isomorphism for an
open embedding; no general open-cover dimension interface is introduced.

{docstring AclGeom.exists_isAffineOpen_dimension_one}

{docstring AclGeom.exists_ringKrullDim_trdeg_eq_of_finiteType}

A regular scheme action also supplies actual automorphisms over Spec k. Mathlib already
makes morphisms into a group object act on morphisms into its space; global points give
these scheme automorphisms. Pulling back functions is contravariant, so the resulting
homomorphism lands in the opposite group of k-algebra automorphisms.

{docstring CategoryTheory.ModObj.pointAut}

{docstring AclGeom.ActionFunctionField.functionFieldAction}

{docstring AclGeom.ActionFunctionField.algEquivOfIso_apply}

The two constructions use the same derived base algebra. The spectrum/global-section
adjunction identifies pullback along the generic-point morphism with the canonical global
section followed by its generic germ. This supplies the scalar tower in the curve-field
proof without another implementation of pullback.

{docstring AclGeom.ActionFunctionField.functionFieldAlgebra_eq_germ}

For an integral scheme separated over k, an automorphism over Spec k is determined by its
function-field action. The proof uses the dominant generic-stalk inclusion and Mathlib's
separated-morphism extensionality theorem. The base compatibility is part of the data of
an automorphism over Spec k.

{docstring AclGeom.ActionFunctionField.autFunctionField_injective}

Consequently the scheme action gives an injective field homomorphism when its point-action
kernel is trivial. The hypothesis states exactly that no nontrivial k-point acts as the
identity of the scheme. In positive characteristic, this is weaker than scheme-theoretic
faithfulness, since nonreduced kernels can be invisible on k-points.

{docstring AclGeom.ActionFunctionField.functionFieldAction_injective}

These are genuine scheme/function-field bridges in the second work item of
[#21](https://github.com/adamtopaz/acl_geom/issues/21). The action input here is regular;
the original source assumes a rational action. The next section constructs the places
action for regular actions. Rational-action regularization, the connected-group fixed-place
step, the arbitrary curve-action classifier, the normal-subgroup producer and the original
algebraization/descent requirements remain separate. All eight original work
items remain open, and the full shared goal remains active and incomplete.


# Places and the boundary of an affine curve
%%%
tag := "scheme-curve-place-boundary"
%%%

A k-automorphism of a field transports a place by taking the preimage of its valuation ring.
This reverses composition, giving a left action of the opposite group of field automorphisms.
The fields and the base may have independent universes.

{docstring AclGeom.Place.comap}

{docstring AclGeom.Place.op_smul_eq_comap}

The boundary of a k-subalgebra consists of places whose valuation rings fail to contain it.
For a finitely generated subalgebra of a one-variable function field over an algebraically
closed base, this set is finite: every boundary place is a pole of a nonzero generator.

{docstring AclGeom.Place.boundary}

{docstring AclGeom.Place.boundary_finite}

{docstring AclGeom.Place.comap_mem_boundary_iff}

The actual function field of an integral curve scheme now supplies discrete valuation rings
for all its places over an algebraically closed base. The one-variable condition is derived
from local finite type and scheme dimension one, using the same derived base algebra as the
scheme action. No caller field-finiteness or one-variable certificate is needed.

{docstring AclGeom.SchemePlaceAction.isDiscreteValuationRing_place}

For a regular scheme action, pulling back fields and then pulling back valuation rings
reverses composition twice. The result is a genuine left action of G(k) on the places of the
actual generic-stalk function field. It is an explicit homomorphism to permutations; there
is no global instance that must recover the scheme from its field.

{docstring AclGeom.SchemePlaceAction.placeAction}

{docstring AclGeom.SchemePlaceAction.placeAction_apply}

The global-section model is the actual range of the generic-germ map in that field.
Naturality of the generic germ shows that every automorphism over Spec k preserves this
subalgebra. Applying that fact to the regular action proves boundary invariance, for any
integral scheme, without requiring the scheme to be affine.

{docstring AclGeom.SchemePlaceAction.globalSections}

{docstring AclGeom.SchemePlaceAction.map_globalSections_algEquivOfIso}

{docstring AclGeom.SchemePlaceAction.placeAction_mem_boundary_iff}

For an affine integral curve locally of finite type and of dimension one, the model is
finitely generated over k. Its boundary is finite when k is algebraically closed. Both
finite generation and the one-variable field hypothesis are derived from the actual curve.

{docstring AclGeom.SchemePlaceAction.globalSections_fg}

{docstring AclGeom.SchemePlaceAction.boundary_finite}

The boundary is also nonempty, over any base field. A transcendental element of the actual
stalk field is a fraction of global sections. Some numerator or denominator has
transcendental generic germ, and its pole place is a missing place of the model.

{docstring AclGeom.SchemePlaceAction.boundary_nonempty}

This supplies a finite, nonempty invariant set of valuation places for an actual affine
curve over an algebraically closed field. It does not prove that a connected group fixes
each place. The abstract finite-index argument is insufficient in positive characteristic;
the remaining proof needs algebraic information about the regular action. The points–places
identification, scheme extension and uniqueness, projective completion, rational-action
regularization and arbitrary-action classification remain owed. No equivalence between
field-action faithfulness and place-action faithfulness is asserted. All eight original work
items of [#21](https://github.com/adamtopaz/acl_geom/issues/21) remain open, and the complete
shared goal remains active and incomplete.
