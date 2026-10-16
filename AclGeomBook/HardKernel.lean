/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Correspondence.JRigidity
import AclGeom.Correspondence.AdditiveThreePair
import AclGeom.Correspondence.AdditiveSubgroupConnected
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
import AclGeom.Correspondence.LocusDimension

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
presents the stable lower layers of that argument. Everything here works
*elementwise with tuples* — a locus is the vanishing ideal of a tuple of
field elements, and no scheme-theoretic machinery is involved.

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
algebraicity certificate. The scheme-level generic-fibre dictionary remains
a separate obligation.

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

The scheme-level finite-generic-fibre dictionary, threefold incidence-component comparison,
scalar specialization
and higher-dimensional family argument remain obligations.
C2 remains open.

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
apply to arbitrary tuples and general curve function fields. The chosen joint prime is a
middle-dominating component under the stated source algebraicity clause. Under the
finite-outer-tuple and algebraically closed ambient hypotheses above, every middle-dominating
component is realized by a joint locus. The tuple theorem above realizes every component's
endpoint contraction with an internally constructed composite germ, and composition is
relationally associative. The generated joint field's inclusion and finite extension of the
endpoint field, and its finiteness over both end fields, are proved above. The actual component
coordinate-ring and function-field/compositum identifications are also proved above, with
polynomial representative formulas. The scheme-level finite-generic-fibre dictionary,
threefold incidence-component comparison, scalar specialization and higher-dimensional
family argument remain open. The actual endpoint contraction retains the scalar field distinction.

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
This discharges the tensor-domain obligation of #11; the full generic-point
statement, correspondence composition and reconstruction completeness are
separate obligations. The earlier regularity scaffolding is marked superseded
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
below; geometric rank and Krull dimension remain separate.

The original proof's absolute transcendence-degree equality does not
by itself give independence when the coefficient extension has infinite
transcendence degree. Issue #5 records the counterexample to that inference;
the generic-over-extension premise and original proof wording are retained.
Frozen M4a and the composition, chart, action and completeness obligations
remain unchanged.

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
below. Geometric rank, Krull dimension and the packaged variety-level lemma
remain separate. The guarded initial chart and rank-five ACF completeness
are proved (`guardedAffineGridExtraction`, `jCompletenessACF`). The
geometric fiber-product identification of composites and the original
scheme/action statements remain open (#5, #21); frozen M4a is unchanged.

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
implication. The numerical field degree equality is proved below; geometric
rank, Krull dimension and the packaged variety-level lemma remain separate.
The existing function-field isomorphism, rational identities and finite-tuple
ambient automorphisms are accounted for below.
Composition, charts, actions and reconstruction completeness remain
open; frozen M4a is unchanged.

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

Geometric rank, Krull dimension and the packaged variety-level lemma remain
open. Over an arbitrary base, function-field tensor components give actual
composite germs (configurations chapter); their identification with
geometric fiber-product components, including over nonclosed bases, remains
open (#5). The guarded initial chart and rank-five ACF completeness are
proved; the original scheme/action statements remain open (#21).
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
actual incidence components. The packaged variety-level lemma, its geometric
formulation and the higher-dimensional family argument remain open (#5), as
do the original scheme/action statements (#21). The guarded initial chart
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

The locus dimension convention is the existing transcendence degree of
its generated rational field. No Krull or geometric dimension bridge,
packaged variety-level lemma or repair of the source's own independence
inference is claimed. That reported gap and the original proof remain
retained; field independence is proved by the separate freeness route.
Composition, charts, actions and reconstruction completeness remain
open; frozen M4a is unchanged.

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
classifications are proved below. The general curve-coset lemma remains an obligation.

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
lemma remains open.

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
`subgroup-classification`; the general curve-coset result remains a separate obligation.

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
base hypothesis, by adjoining a rational-function variable. It also proves
corrected conditional base recovery for the actual interpreted ring
equivalence, under explicit carrier/completeness and RAC inputs; corrected
conditional scalar one and outside-point recovery are proved there without
RAC. The public `reconstruction_target` supplies both completeness inputs
internally: under the blueprint hypotheses its Φ carries the perfected base
onto the perfected base and satisfies φ(M) = Φ(M^perf) ∩ L. The original
general R1/R2 interpretation arguments and literal provenance remain
obligations (#9, #23).

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
and `j_rigidity` are proved uniformly in the exponential characteristic,
meeting M3's rigidity acceptance test. The original three-pair additive and multiplicative
correspondence statements are proved above without freshness hypotheses. The connected
additive- and torus-subgroup classifications are also proved. The general curve-coset
statement, geometric fiber-product bridge and full generic-extension lemma remain open in #5.
The tensor-domain obligation #11 is proved above;
the rational group and affine action construction remain open in #12 and #21.
