# Shared project goal

Last reviewed: 2026-10-17.
Jointly maintained by `aclgeom.codex` and `aclgeom.claude`.

## Objective

Complete the Lean 4/Mathlib formalization of the mathematical content of
[sources/blueprint.tex](sources/blueprint.tex): the Evans–Hrushovski–Gismatullin
reconstruction theorem, its auxiliary results, and its stated variants and
functorial consequences. Produce unconditional public theorems under the
blueprint's genuine hypotheses, a matching Verso exposition, and reproducible
validation. Preserve the provenance and justified corrections of source errors.

The project also formalizes, in the `GroupConfig` library, the group
configuration theorem of
[sources/group_configuration_blueprint.tex](sources/group_configuration_blueprint.tex),
whose parts are in [sources/group_configuration/](sources/group_configuration/).
That supplementary blueprint was written for this project to supply the group
extraction that the source route needs. It adds obligations and removes none
from the original blueprint; see
[Group configuration theorem](#group-configuration-theorem) below.

The shared goal is the mathematical result, rather than a particular proof
route or a collection of interfaces. Alternative proofs are welcome; true
blueprint statements bypassed by a route remain obligations.

## Mathematical endpoint

For relatively algebraically closed extensions $K/k$ and $L/l$, with
$\operatorname{trdeg}(K/k)\geq5$, every order isomorphism
$\phi:\mathcal G(K/k)\simeq\mathcal G(L/l)$ must:

- imply equality of the two transcendence degrees;
- arise from an isomorphism $\Phi:K^{\mathrm{perf}}\simeq L^{\mathrm{perf}}$
  carrying the perfected base onto the perfected base and inducing $\phi$ on
  every relatively closed intermediate field;
- have exactly integral Frobenius twists as its possible reconstructions:
  literal uniqueness in characteristic zero, and a unique twist exponent
  between any two reconstructions in positive characteristic.

Prove the converse and the point-geometry formulation, automorphism exact
sequence, literal functor laws and exact Hom fibres, and the fully faithful
Frobenius-quotient formulation. The literal geometry functor is fully faithful
in characteristic zero; positive characteristic requires the Frobenius quotient.
Cover arbitrary chosen perfections and the blueprint's universe generality.

## When the project is complete

All of the following must hold:

1. The public reconstruction theorem has only the mathematical hypotheses above.
   Open completeness, chart, action or reconstruction conclusions are proved
   internally, rather than supplied by the caller. In particular, the current
   `JCompletenessACF` inputs in [AclGeom/Main.lean](AclGeom/Main.lean) are discharged.
2. Every intended blueprint statement has a recorded disposition and Lean
   evidence: proved with its precise hypotheses, or refuted with original
   provenance and a justified, proved corrected replacement. A source error or
   a bypass does not silently erase an obligation or narrow the final theorem.
   If a correction remains unresolved, the associated obligation remains open.
   The same holds for the group configuration blueprint. Its main theorem
   (`thm:main`), the constructible group (`thm:constructible`), descent
   (`thm:descent`), the Ψ application (`prop:psi-gc`, `cor:psi`) and their
   prerequisites must each be proved in the project or refuted with provenance.
   Proofs may live in `GroupConfig` or in project bridges such as `AclGeom/Config`.
3. The endpoint's variants and consequences above are proved. No conditional
   configuration or reconstruction theorem is presented as unconditional.
4. No `sorry`, `admit` or project axiom occurs on main. Final public theorem
   dependency checks report only the expected standard Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`); checking a selected scope is
   never described as checking the whole library.
5. Full `lake build`, `lake exe book` and CI pass for the final committed head.
   Source coverage, theorem statements, docstrings, book, README, issues and
   continuation guide agree. A final report on the repository's issues links
   the theorem and coverage evidence.

A theorem with named open hypotheses proves only the implication from those
hypotheses (AGENTS rule 4). It is progress; it does not discharge the corresponding
unconditional obligation.
Green builds or the existence of a public wrapper alone do not mean completion.

## Current frontier and critical path

The library already contains substantial foundations, hard-kernel results,
generic-point field clauses, semantic configuration assembly, transfer and
reconstruction. The public lattice-form theorem now has exactly the blueprint's genuine
hypotheses; both perfected ACF completeness proofs are constructed internally. The central
remaining work is source validation and the original auxiliary source obligations:

| Work | Required result and tracker |
|---|---|
| Guarded geometric Q | Proved for every ACF pair: the actual Ψ chart, coherent finite parameter specialization and original-field descent give the full affine grid and guarded Q completeness internally. Both public guards remain visible. The public reconstruction theorem consumes this internally. [#27](https://github.com/adamtopaz/acl_geom/issues/27), [#6 G3](https://github.com/adamtopaz/acl_geom/issues/6). |
| Geometric Q′ | The product-output clause is proved over arbitrary base and ambient fields for actual representatives X=[x], Y=[y], V=[x/y], with no closedness, perfection or rank premise (`MulDiagram.product_point`). Only the product equality reflects from the algebraic closure; no auxiliary-table descent is asserted over arbitrary fields. The full original-base auxiliary table over ACF k/K needs no rank bound. Rank-five ACF Q′ completeness follows from the now-proved guarded Q completeness. [#6 G4](https://github.com/adamtopaz/acl_geom/issues/6). |
| Geometric J and transfer | Rank-five ACF `JCompletenessACF` is proved by the guarded Q theorem and multiplication converse. The public reconstruction API supplies these proofs internally. The four-way J descent/correctness theorem is proved over arbitrary perfect ambient fields at rank five. Corrected projected Q/Q′ equivalences are also proved over arbitrary bases and perfect ambient fields at rank five, with all existential points over K and no RAC premise. The original raw consequences retain their refutations. General raw existential-witness descent is an unresolved exploratory question, not a separately stated source theorem. [#6 G5](https://github.com/adamtopaz/acl_geom/issues/6), [#7](https://github.com/adamtopaz/acl_geom/issues/7). |
| Reconstruction and variants | The chosen-perfection lattice-form target, its exact Frobenius fibre and converse are proved under the genuine RAC/rank-five hypotheses. The point-geometry and automorphism variants, literal functor laws/exact fibres and rank-five fully faithful Frobenius quotient are proved. Perfection-choice equivalence and agreement of the geometry functors are proved. The rational-function-field example works over arbitrary bases and with arbitrary chosen perfections; In positive characteristic, Frobenius injectivity needs only positive transcendence degree. The global Frobenius relation is a proved setoid on geometric J-tuples over perfect ambient fields at rank five, without RAC or an infinite base. The original direct-link common-representative claim (10.1) is also proved for supplied semantic endpoints over arbitrary bases and perfect ambient fields, with no rank bound. It gives all three point equalities for one representative of every chosen multiplier point satisfying the first two clauses; the direct link retains its full existential multiplier hypothesis. The proof uses incidence rigidity and concurrency uniqueness, while the original separate-representative inference remains unjustified provenance. The literal negation and total-nonzero-addition graphs have separate nonfunctionality refutations, including all auxiliary class conditions, over infinite bases at rank five. Their corrected coupled replacements have proved semantics. The true existence half of literal total nonzero addition is proved under the three individual independent-pair hypotheses over arbitrary fields at rank five, without joint independence of the two inputs, perfection or completeness. The named `blueprintRatioEq_no_decoder` refutes the advertised literal decoder on a fixed class, even after equivalence closure. Literal predicate invariance and the raw image-base quotient-carrier correspondence are proved without semantic hypotheses. Literal ratio symmetry is proved over arbitrary fields, fixed-class reflexivity is proved over perfect ambient fields at rank five without caller completeness, and transitivity is refuted over arbitrary fields at rank five. The relation itself cannot form the advertised setoid. The true converse of literal ratio semantics is proved on semantic representatives with a common parameter over arbitrary fields at rank five, without perfection or completeness; the forward implication and advertised decoder remain refuted. Both literal operation recipes are transcribed on raw class-pair representatives, with all replacement witnesses and geometric invariance proved over arbitrary fields in four universes. Both forward advertised operation laws are refuted on explicit semantic representatives over infinite bases and perfect ambient fields at rank five, without assuming a decoder. Raw multiplication totality on the actual class is proved over perfect ambient fields at rank five with internal normalization and completeness. Its corrected representative-level reverse law for nonzero semantic inputs is proved over arbitrary fields at rank five. Raw addition totality on the actual class is also proved over perfect ambient fields at rank five with internal normalization and completeness. Its two corrected reverse branches for nonzero semantic inputs hold over arbitrary fields at rank five; the nonzero-output branch derives sum nonvanishing. The extension of the raw reverse law to arbitrary zero inputs is refuted, because the zero completion uses equality of representatives. Literal addition functionality is refuted after every identification of nonzero representatives with the named zero adjoined when `2 ≠ 0` in the base, over arbitrary fields at rank five with the actual semantic base pair; no perfection, infinite base, completeness or decoder is used. This gives no characteristic-two refutation and no claim that an unrelated field structure is impossible. The universally quantified literal TOT/decoded construction has recorded refutations, its true raw components are proved, and its corrected coupled field/graph replacement is proved. The original I6b/I6c clauses are disposed of with their exact hypotheses, geometric transport and chosen-class decoding diagram; original formulas/proofs retain their provenance. The actual reconstructed map satisfies base recovery, both scalar-one conclusions, all-point recovery and atomistic extension (R1--R4). `interpretedRingEquiv_jTupleOf` exposes the full canonical tuple image and target-pair independence, in four universes, without RAC or a scalar/freshness oracle. The proved producers supply all explicit completeness, target-rank, characteristic and image-base inputs in the source setting. Compatibility and all-point propagation use both genuine RAC bases; the full tuple and outside-point formulas do not. The named actual-H lattice equality gives every closed-field set image, and its conjugated chosen-perfection instance gives the original-field intersection formula for that actual H. The original literal RatioEq/JMul proofs retain their provenance. True bypassed source statements remain separate, and no operation descent is asserted for the literal recipes. Bare field-isomorphism existence is proved for arbitrary bases and perfect ambient fields at source rank five, without caller-supplied completeness. The corrected source-setting class-field map now also retains any chosen semantic base class, its actual semantic image base and the ratio decoding diagram for every mapped pair of semantic representatives, in four independent universes, with target rank, both completeness proofs and characteristic exponents internal. This is a source-facing record of the existing corrected interpretation; compatibility with the whole lattice map remains the stronger RAC-base reconstruction conclusion. The numbered validation suite TEST-1 through TEST-11 has precise Lean evidence, with true literal coordinate soundness and prescribed-witness ratio reverse distinguished from refuted uniqueness/forward laws and the proved corrected replacements. The direct Frobenius point identity needs no RAC; positive-characteristic distinctness needs only positive transcendence degree. The corrected projected Q/Q′ equivalences are proved over perfect ambient fields at rank five, with all existential points over K. The original raw consequences remain refuted. No general raw existential-witness descent theorem is stated by the source or asserted either way; that question remains unresolved and exploratory. The full original/supplementary source-disposition audit remains open. Repeat the reproducible whole-library dependency audit for each final head. [#8](https://github.com/adamtopaz/acl_geom/issues/8), [#9](https://github.com/adamtopaz/acl_geom/issues/9), [#10](https://github.com/adamtopaz/acl_geom/issues/10). |
| Group configuration theorem | The precise and informal main theorems, the canonical-code constructible group/stabilizer/homogeneous-space presentations, arbitrary-small-ACF base change, parameter descent and the full `cor:psi` are proved. Full Ψ also gives rank-one HW data from its partial quadrangle; two new fresh Ψ consumers (`GroupConfig.PsiFresh`) choose parameters of rank ten or five fresh from all twenty-one witness representatives, prescribed finite sets and, in rank one, the extra quadrangle points. Both actual main conclusions now hold jointly over one fresh base with total parameter rank fifteen (`GroupConfig.PsiJoint`). The actual HW action on a rank-one curve, with group rank at least two, has a complete constructible determinant-one matrix lift over an internally chosen small ACF field, with matrix/canonical-base interalgebraicity and the actual rank bound (`GroupConfig.Constructible.SLLift`). For ordinary canonical-base rank exactly two, the complete actual HW consumer now chooses a transcendental generator of the original K-function field in which every group element acts by a*u+b with a nonzero, internally classifying the constructible lift as a conjugate of the upper Borel (`GroupConfig.Germ.AffineGenerator`). Moving the finite witness coherently, classifying actual upper-triangular curve cosets and descending a finite polynomial closure table now construct the guarded Q chart over the original ACF ambient, without a supplied chart or universal-domain hypothesis. The original scheme/action, algebraization and scheme/action descent bridges and auxiliary source obligations remain open; the chart route does not discharge them. [#12](https://github.com/adamtopaz/acl_geom/issues/12), [#27](https://github.com/adamtopaz/acl_geom/issues/27). |
| Remaining source mathematics | For finite tuples over arbitrary base and ambient fields, the literal coordinate quotient has dimension equal to the generated field transcendence degree (`exists_locusCoordinateRing_dimension`), and `pairLocus_finiteCorrespondence_iff` proves that dimension one of this quotient together with finiteness of both actual generic-fibre projections is equivalent to the two algebraicity and two rank-one clauses of (8.1), deriving both literal projection-dominance facts internally. `pairField_finiteDimensional_iff` supplies the function-field criterion. For finite tuples satisfying the four (8.1) closure clauses, in an ACF ambient over an arbitrary base, the actual affine-scheme fibre product, literal incidence quotient, dominating components and their endpoint-density criteria are proved. Every actual middle-dominating component has its coordinate ring and fraction field identified with the realized joint ring and compositum, with polynomial representative formulas (`exists_locusIncidence_component_algEquiv`). Tuple and original scalar germ composites are exactly the endpoint contractions of all these actual components; composition is nonempty for matching middle loci and relationally associative. The joint field is finite over both ends and over the endpoint-image field, which can be properly smaller, as the proved chain `(t²,t,t²)` shows ([source correction](https://github.com/adamtopaz/acl_geom/issues/5#issuecomment-6215313613)). `TupleCorrespondenceGerm.composes_threefold_components_eq` now identifies the final carriers of both parenthesizations with the endpoint contractions of all actual four-block incidence components having dense image under the literal middle-pair projection. Its genuine correspondence presentations supply the closure clauses internally; the finite indices and fields have six independent universes. For every component, its normalization, formed as the integral closure of its coordinate domain in its fraction field, is integrally closed, has that same fraction field and preserves its endpoint generic ideal. For finite tuples satisfying rank additivity, `locusIncidence_jointPrime_dominating_of_rank` constructs the chosen middle-dominating component, its endpoint ideal and its actual coordinate-ring dimension, over arbitrary fields. For any prime ideal in finitely many variables, `exists_idealOf_eq_iff` constructs a generic tuple in an algebraically closed ambient exactly when its transcendence degree is at least the internally computed finite dimension. This supplies the variety-to-joint-generic-point bridge for arbitrary irreducible correspondence curves, including non-rational function fields, with arbitrary base and three independent universes. For an actual six-point partial quadrangle, the selected incidence germs over the closed parameter join retain the three intrinsic parameter closures. Over the literal compositum k(s,t,u), each selected branch, including the composite, is a minimal prime of its original k(t), k(s) or k(u) family ideal after extension. Both source producers derive the needed ranks and incidences internally; the literal-field result works over arbitrary fields. For an actual Ψ witness alone, over arbitrary fields, `QWitness.Psi.exists_literal_composing_incidence_germs` gives the selected (8.6) germ over k(a₁,a₂,b₁,b₂,c₁,c₂). Its original two-generator families retain coefficient closures A, B and C, and the selected larger-field ideals are minimal primes of their corresponding extended family ideals. No such coefficient-closure claim is made for split larger-field factors. In an ACF ambient, `IsPartialQuadrangle.literal_family_branches_are_conjugates` now realizes every minimal-prime branch of each literal six-point family as an actual larger-field generic conjugate over its own original parameter field. It derives the needed ambient capacity and all family data from the existing public partial-quadrangle producer. The automorphisms need not preserve the larger coefficient field. The actual Ψ consumer `QWitness.Psi.literal_family_branches_are_conjugates` also realizes every branch of its three extended literal two-generator family ideals over the six-generator compositum, from Ψ and an ACF ambient alone. It reuses the original family data and larger-field generic source from the public literal producer, with no new helper or caller branch-genericity premise. The selected parameter-family k-locus forms of (8.4c) and (8.6) are proved by the actual component and common-function-field-cover consumers in AclGeom/Config/FamilyLoci.lean and the exact composite-ideal contractions in ParameterField. Each configuration supplies both literal incidence components, their source dimensions, four dense projections of the full tuple locus and canonical finite function fields, from the genuine source hypotheses over arbitrary fields. The scalar contraction uses exactly the parameter-family joint tuple, including its index renaming. Coherent triples of branches and their common normal cover remain owed; no classification of all parameter-family components is asserted. For an ACF base and any coefficient-field extension, `genericExtension_genericPoint` constructs both equal finite quotient dimensions and derives the exact extended ideal, original relations and field freeness from locus membership and the source relative rank. Its universal clause allows an arbitrary ambient; sharp existence needs an ACF ambient, with four independent universes. The canonical function-field isomorphism of two finite generic points extends to the ambient automorphism, and Mathlib's evaluation equivalence proves the rational identity clause. This completes generic extension (a)--(c) in the source finite-coordinate setting. The actual j-tuple rigidity theorem now has a unique normalized exponent over arbitrary bases and perfect ambient fields, without an ambient rank bound or supplied fresh elements (`existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq`). The original literal integer-uniqueness clause is refuted in characteristic zero, with pair equality and distinct valid exponents zero/one proved for actual equal tuples; original provenance and the downstream characteristic-zero proof qualifications are retained (#32). The additive finite-correspondence case of the curve-coset lemma is proved over ACF base and ambient fields (`curveCoset_additive_of_finiteCorrespondence`), with the actual closed subgroup, prime principal ideal, connected coordinate spectrum, dimension one, both nonconstant projections and all three ideal/point cosets, without a caller rank/freshness/completeness input. This supplies the subgroup-classification inputs in the source additive-correspondence proof. The general curve-coset statement is now proved for closed irreducible curves over an ACF base (`curveCoset_of_genericProduct`), including an actual connected one-dimensional closed algebraic subgroup and all three noncommutative cosets. The ambient group need not be connected; the jointly generic scheme-product point need only map into the third curve. Product integrality and every restricted group operation are proved internally. The commutative theorem gives all three left cosets of the same subgroup. Abstract torus and constant-coordinate cases are permitted once the ambient group is presented as an `AlgebraicGroup`. Concrete Gaⁿ, Gm, Gm² and affine group schemes are now constructed, with their point coordinates. The affine group has dimension two and, over ACF, an actual connected algebraic-group package; its standard affine scheme action has the literal ax+b formula and is faithful over every commutative coefficient algebra in the base universe. This constructs the target model of (8.4a), not the classification of an arbitrary source action. The actual scheme/function-field bridge now proves the one-variable class for the genuine generic stalk of every integral locally finite-type curve of dimension one, over arbitrary fields. Actual regular scheme actions give a contravariant homomorphism of base-field points into the opposite group of field automorphisms; for a separated scheme it is injective under the explicit point-action kernel criterion. Both results share one internally constructed base algebra. Actual regular scheme actions now give a left action on the places of the same field and preserve its global-section subalgebra. For an integral affine locally finite-type curve of dimension one, its valuation-place boundary is nonempty over arbitrary fields and finite over an algebraically closed base, with finite generation and the one-variable hypotheses derived internally. Every place of an actual integral locally finite-type dimension-one curve over an algebraically closed base is a DVR. For an actual connected algebraic group acting regularly on such an affine curve, every boundary place is fixed and an actual fixed boundary place is chosen internally. Closedness of order conditions is derived from the regular action using uniform finite tensor sums and algebraic dual separation, in every characteristic. A separate algebraic coefficient-field input is now proved: injective restriction of base-field points from a finite-type domain to a coefficient ring makes its fraction field algebraic over a compatible coefficient field, allowing inseparability. The actual generic translate is now constructed internally on Frac(k(G) tensor_k k(V)) for integral groups acting regularly on integral affine schemes over an ACF base, with its literal global-section/function-field comparison. No generic-point or coordinate-action certificate is supplied. For a given actual affine parameter family of a regular action on an affine locally finite-type scheme over any field, finite global-section algebra generators and one common finite independent section family now have coefficients that evaluate uniformly over every commutative parameter algebra, for both action directions. These finite data and the coordinate action are constructed internally. For a given parameter-field evaluation of that actual family, its effective coefficient field, lifted field generators, essential finite type and both tensor-ring automorphism directions are now constructed from the same coefficients, retaining the raw matrix and every evaluation formula. Over an ACF base and for integral affine V, that same actual family and field evaluation now construct the action on Frac(C0 tensor_k k(V)), its actual coordinate-field comparison and an injective ordinary coefficient-variation map, retaining the same raw matrix, independent sections and field generators. All tensor domains and finite matrix premises are derived internally. A formal Frobenius affine-family example shows that field-point faithfulness does not make ordinary derivations of the original parameter field detect its coefficients; the proved variation uses the effective coefficient field. For an integral locally finite-type group of dimension at least two acting regularly and faithfully on an integral affine locally finite-type dimension-one curve over an ACF base, the actual chart and parameter fraction field are now chosen internally. The same raw matrix gives point-map faithfulness, algebraicity over the effective coefficient field allowing inseparability, its rank bound and two independent regular curve variations. An internally chosen algebraically closed constant extension K gives a one-variable canonical field Frac(K tensor_k k(V)) of genus zero, with the actual generic-stalk k(V), domains and all prerequisites internal. No chart, matrix, rank, variation, regularity, one-variable or genus certificate is a caller premise. Original-base rationality/genus-zero descent, non-affine and rational-action cases remain open. Rational-action regularization, completion/points identification and arbitrary-action classification remain open; all eight original #21 items are retained. The tuple-locus-to-scheme-curves and jointly generic product bridge remains separate. The additive coordinate theorem retains its separate interface. The original group chunk, six-point configurations and affine-action statements remain owed. The original three-pair additive and multiplicative correspondence equations are proved without extra ambient-rank or freshness hypotheses; the connected one-dimensional additive-plane and torus subgroup classifications are proved at their documented source hypotheses. The book and continuation guide record the exact API scope and evidence. [#5](https://github.com/adamtopaz/acl_geom/issues/5), [#12](https://github.com/adamtopaz/acl_geom/issues/12), [#13](https://github.com/adamtopaz/acl_geom/issues/13), [#21](https://github.com/adamtopaz/acl_geom/issues/21). |

The existing Q/Q′-to-J assembly is an established dependency. On the source's
group/chunk route, the two-dimensional Q chart and the one-dimensional Q′
six-point argument share an open bridge: extract an algebraic group from an
actual finite-correspondence configuration, up to interalgebraicity. The source
multiplication converse has not supplied the ambient group required by its
curve-coset invocation. The finite group-chunk variant has not proved the
coherent lift and closure under words required by its proposed finite cover.
These are proof gaps, not verified refutations; the original wording remains.
The joint audit is recorded on
[#12](https://github.com/adamtopaz/acl_geom/issues/12#issuecomment-6155280744) and
[#27](https://github.com/adamtopaz/acl_geom/issues/27#issuecomment-6155281059).

This describes a dependency of the source route, not a necessity for every
proof. The direct Q′ route is now proved in
[AclGeom/Config/MultiplicationConverse.lean](AclGeom/Config/MultiplicationConverse.lean):
a literal semantic ratio, a fixed-field ambient automorphism and the proved
multiplicative correspondence theorem force the product output. Its consumers in
[AclGeom/Config/Correctness.lean](AclGeom/Config/Correctness.lean) derive rank-five ACF Q′ and J
completeness from guarded Q completeness alone, now proved in
[AclGeom/Config/GuardedAffineGrid.lean](AclGeom/Config/GuardedAffineGrid.lean). Coherent specialization now
proves the full original-base auxiliary coordinate table over an ACF base:
one homomorphism preserves the finite incidence equations and the common
nonzero multiplier. An auxiliary extension and descent remove the table
theorem’s ambient rank bound over algebraically closed fields. This bypasses
group extraction for both multiplication conclusions; the true bypassed group/chunk statements remain obligations.
Audit the needed targets and dependencies before investing in group, chunk or
action infrastructure. No route is declared sufficient without proofs.
The frozen 117-item M4a chain is historical, not a list of deliverables. Related
source statements remain owed; revisiting frozen code requires a concrete
mathematical purpose and agreed ownership.

## Group configuration theorem

[sources/group_configuration_blueprint.tex](sources/group_configuration_blueprint.tex)
was committed in c082e7e and is tracked on
[#12](https://github.com/adamtopaz/acl_geom/issues/12). It gives an informal proof
of Hrushovski's group configuration theorem in the language of fields. The fields
are algebraically closed, $k\subseteq K$, and $K$ has infinite transcendence
degree over $k$. The theorem says that, after a finite independent
base extension, a six-point configuration is interalgebraic with the standard
configuration of a group of germs of quasi-rational maps acting on a variety.
Over a further generic extension that group is constructible
(`thm:constructible`), and the descent theorem (`thm:descent`) controls the base
fields. The application (`prop:psi-gc`, `cor:psi`) takes the actual Ψ witness
with $n=2$ and $m=1$. Its output is a rank-two constructible group acting on a rank-one homogeneous
space. Algebraization must turn these quotient presentations into the algebraic
group and curve action required by the original blueprint's Lemma `affine-action`
([#21](https://github.com/adamtopaz/acl_geom/issues/21)).

Part [12](sources/group_configuration/12-lean.tex) of the supplementary blueprint
proposes the Lean architecture: a `lean_lib GroupConfig` in this package.

Its scope section states three non-goals:

- Weil's algebraization of constructible groups;
- the classification of the resulting group;
- elimination of imaginaries beyond the codes it constructs.

These are non-goals of the supplementary blueprint alone. Weil algebraization and
the group classification remain obligations of the original reconstruction
blueprint and the shared endpoint. Those include the original group-chunk,
six-point and action statements (`thm:rational-group-chunk`,
`thm:six-point-group`, `lem:affine-action`) and the chart and reconstruction
steps built on them. The supplementary non-goals cannot erase
these obligations. Completing `GroupConfig` does not by itself make the original
group, chunk, action, chart or reconstruction results complete, and it must not
be described as doing so.

On main are the following established layers. This lists layers; it does not
certify every auxiliary statement in the corresponding source sections.

- the universal-domain, rank, automorphism, locus and dimension foundations;
- fields of definition and canonical bases;
- codes, quasi-rational expressions and germ varieties;
- germ representatives, graph ideals, automorphisms, evaluation and composition;
- independent generic conjugacy, definable values and triple germs;
- the Hrushovski–Weil group and faithful transitive homogeneous space;
- rational representatives for every element of the actual HW two-product group on a
  rank-one locus, in both characteristics;
- its actual one-variable locus function field and a faithful action of the actual HW group
  by K-algebra automorphisms, with the coordinate formula for every rational inverse representative;
- genus zero over K for that actual function field when the ordinary canonical-base rank is
  at least two, derived from genuine HW data and curve rank one;
- a transcendental generator of that same K-function field in which every element of the
  actual HW action is fractional linear, with nonzero determinant and denominator;
- the full actual determinant-one lift of that action as a constructible subgroup of SL₂(K),
  with internally chosen coefficient field and samples, finite sign ambiguity, reversed
  composition, matrix/canonical-base interalgebraicity, the rank bound and an actual generic
  element attaining it;
- the full translation example, including its actual germs, homogeneous space and the
  obstruction to an independent presentation of the zero class;
- the final-base rank, one-orbit and two-product properties of its generic elements;
- constructible group, stabilizer and homogeneous-space presentations on the actual canonical
  code, after internally chosen two-stage generic sampling;
- extraction of those data from a configuration after finite independent base extension,
  with the actual five-copy parameter rank over the original base;
- arbitrary small ACF base change, with the group and homogeneous space preserved;
- descent of independent parameters in constructible relations;
- model completeness of algebraically closed fields, as an actual elementary embedding
  for every prescribed field embedding, with preservation of all finite-arity ring formulas;
- the configuration predicate, its invariance and independent-base descent, with necessity
  of its clauses from the actual main conclusion over a finite independent extension;
- the explicit canonical-base line example and the finite-ambient representative-collapse warning;
- the full nonfaithful product-group example, with the actual Ψ clauses (i)–(iii), failure
  of (iv), and the obstruction to realization by the precise main conclusion;
- base-algebraic-closure invariance of closures, ranks, closed fields and points;
- constructible sets, with Chevalley's theorem and generic quantification;
- the clause-(i)–(iv) form of `prop:psi-gc` and full `cor:psi`, including the actual
  constructible presentations, original-base freshness and final-base rank/orbit conclusions.

For the last item, all configuration clauses with group rank two and space rank
one are derived from `QWitness.PsiCore`, precisely clauses (i)–(iv), in a
universal ACF ambient
([AclGeom/Config/ConfigurationInput.lean](AclGeom/Config/ConfigurationInput.lean)).
A canonical universal ACF lift
([AclGeom/Config/UniversalConfigurationInput.lean](AclGeom/Config/UniversalConfigurationInput.lean))
applies to a Ψ witness over arbitrary original fields. It produces the
configuration in its chosen universal extension, not in the original $K$.
The core clauses also lift, and the configuration is proved on the literal
images of the original six displayed tuples under the canonical embedding
([AclGeom/Config/UniversalImageConfigurationInput.lean](AclGeom/Config/UniversalImageConfigurationInput.lean)).

The precise `thm:main` of part 08 is proved in
[GroupConfig/Main.lean](GroupConfig/Main.lean). Its conclusion constructs actual
Hrushovski–Weil data, three difference germs and their action values, with the
six points interalgebraic with the input over a finite independent extension.
Its stronger `GroupConfiguration.exists_main_with_parameterRank` retains the rank of the
actual chosen parameters: `erk k ∅ E = 5 * erk k ∅ (Set.range a)`, over the original base.
The existing definability, Step I and Step III producers retain the three-plus-two generic
copy ranks, and the old public existence statements are projections with unchanged hypotheses.
This proves `rem:params` and retains the universal-domain hypothesis; the finite-ambient
collapse warning and the remaining application witness-descent obligations still apply.
The homogeneous space has a faithful transitive action. The arbitrary-small-ACF
base-change package transports the actual loci to fresh representing tuples;
it preserves the generic and difference sets, group and homogeneous space.
[GroupConfig/Descent.lean](GroupConfig/Descent.lean) proves the parameter-descent
theorem for constructible relations. The stronger degree-only usage claim is refuted in
[GroupConfig/ClosureCounterexample.lean](GroupConfig/ClosureCounterexample.lean), with original
provenance and the fixed-formula correction on [#31](https://github.com/adamtopaz/acl_geom/issues/31).
Fixed finite polynomial and quasi-rational witness formulas, with their coefficients and
nonvanishing conditions retained, have constructible satisfaction predicates by the existing
polynomial, graph and quantifier theorems. This does not by itself descend the application
witnesses or recover their independence.
[GroupConfig/ModelCompleteness.lean](GroupConfig/ModelCompleteness.lean) proves model
completeness itself: a prescribed embedding of algebraically closed fields is an actual
Mathlib ring-language elementary embedding, with the same underlying map and preservation
of every finite-arity formula. The proof uses constructibility of actual bounded formulas
and a Tarski–Vaught fibre fixing the existing parameters. No universal-domain or rank
hypothesis is used. This supplies the logical input cited in `rem:psi-hyp`(c) and
`rem:finite-trdeg`. The guarded Ψ chart's finite formulas, independence recovery and
coordinate descent to the original ACF ambient are proved in
[AclGeom/Config/GuardedAffineGrid.lean](AclGeom/Config/GuardedAffineGrid.lean).
The original scheme/action descent remains a separate obligation.
[GroupConfig/ConfigurationNecessity.lean](GroupConfig/ConfigurationNecessity.lean) descends
configurations from a small independent base field. Applied to the actual main conclusion
over a finite independent extension, it recovers the original configuration, including GC4
for the first group point as asserted in `rem:main-props`.
[AclGeom/Config/PsiNonfaithful.lean](AclGeom/Config/PsiNonfaithful.lean) constructs the
product-units action through its first factor and the literal witness in `rem:psi-hyp`(b).
All nine assertions of Ψ (i)–(iii) hold, while the source atom `acl(s)` violates (iv).
[AclGeom/Config/PsiNonfaithfulObstruction.lean](AclGeom/Config/PsiNonfaithfulObstruction.lean)
computes the canonical-base obstruction over arbitrary fields. In an algebraically closed
universal ambient it transfers that obstruction to the actual witness tuples and rules out
`IsMainConclusion` over any finite independent base extension. This is the precise germ
theorem's realization condition; the original algebraic-group and curve-action bridges
remain separate obligations.
[GroupConfig/CanonicalBaseCounterexample.lean](GroupConfig/CanonicalBaseCounterexample.lean)
proves the literal `rem:cb-not-acl` line example, its canonical base, rank and noncontainment.
The line ideal and canonical-base proof are shared over any coefficient field containing
the slope and intercept, with `t` transcendental over that field. The five
original public example statements remain unchanged.
[GroupConfig/Germ/FiniteAmbient.lean](GroupConfig/Germ/FiniteAmbient.lean) proves smallness
and absence of generic points over the whole field when the ambient transcendence degree is
finite. In an algebraically closed ambient field, the generated representative equivalence
relation then collapses. The existing germ definition retains its universal-domain hypothesis.
These auxiliary results preserve the separate original-field descent and reconstruction obligations.
[GroupConfig/BaseClosure.lean](GroupConfig/BaseClosure.lean) proves that replacing the base
by its relative algebraic closure inside the same ambient field preserves relative closures
and ranks, and constructs the actual carrier-preserving order isomorphism of closed-field
lattices. The existing point and lattice-rank transports apply to this isomorphism, proving
the base-closure assertion of `rem:psi-hyp`(c) over arbitrary fields. This keeps the ambient
field fixed; witness descent from a larger ambient extension remains an obligation.

[GroupConfig/Germ/Translation.lean](GroupConfig/Germ/Translation.lean) constructs the actual
translation germs, their canonical bases and Hrushovski–Weil structure. The generic orbit
consists of translations by transcendental parameters, and the generated group consists of
all translations. [GroupConfig/Germ/TranslationSpace.lean](GroupConfig/Germ/TranslationSpace.lean)
proves the full example in `rem:connected`: the actual homogeneous space is equivalent to K,
with pairs identified exactly when their parameter-plus-point sums agree. The total action
is addition, and the embedded generic points are exactly the transcendental elements.
The class `[-t,t]` maps to zero and has no presentation using a generic point independent
from the acting group element. The HW structure is proved internally, not supplied as a premise.

[GroupConfig/Germ/FunctionField.lean](GroupConfig/Germ/FunctionField.lean) constructs the
literal fraction field of the prime locus quotient and proves that it is a one-variable
function field over K when the input tuple has rank one. Primeness and the one-variable
property are derived, not supplied as certificates.
[GroupConfig/Germ/FunctionFieldAction.lean](GroupConfig/Germ/FunctionFieldAction.lean)
constructs a faithful homomorphism from the actual HW two-product subgroup into its
K-algebra automorphisms. The actual rationality theorem chooses the representatives
internally; inverse substitution corrects contravariance. The coordinate formula holds
for every equal exponent-zero representative of the inverse. This supplies a genuine
function-field action. [GroupConfig/Germ/CurveGenus.lean](GroupConfig/Germ/CurveGenus.lean)
proves genus zero over K when the ordinary canonical-base rank is at least two. It derives
its formal field comparisons, rational inverse, independent derivations and regularity from
the actual HW and rank-one data; the one-variable instance is also derived internally.
[GroupConfig/Germ/MoebiusAction.lean](GroupConfig/Germ/MoebiusAction.lean) then supplies a
transcendental generator of the same K-function field and the fractional-linear formula for
every element of the actual HW action, with nonzero determinant and denominator. Classification
of the actual rank-two lift and its affine coordinate are now proved in
[GroupConfig/Germ/AffineGenerator.lean](GroupConfig/Germ/AffineGenerator.lean), under ordinary
canonical-base rank exactly two. The original affine-action classification, scheme/action
bridge, algebraization and normal-subgroup producer remain obligations.

[GroupConfig/MainConstructible.lean](GroupConfig/MainConstructible.lean) proves the combined
`thm:main-informal` on those same data: for every generic base point it chooses the canonical
family and fresh samples internally, proves combined-parameter independence over the original
base, and obtains the actual group, stabilizer and homogeneous-space presentations. The
final-base rank, orbit and two-product conclusions use the rank of the original input tuple.
The finite supporting audit on #29 is complete; these results do not certify every auxiliary
statement in the sources.

[GroupConfig/Constructible/CanonicalPresentation.lean](GroupConfig/Constructible/CanonicalPresentation.lean)
proves `thm:constructible` for every Hrushovski–Weil datum of bijections, in particular
the one supplied by the main theorem. It chooses the family on its literal canonical code, derives equal dimension
from invertibility, and chooses both sampling stages internally. The actual group, stabilizer
and homogeneous-space presentations have the source coefficient fields and retain the
generic-point provenance, joint ranks and freshness from any prescribed small field. These
are constructible quotient presentations in the source sense. Original algebraization, the
original affine-action classification and scheme/action descent remain obligations.
The actual rank-two HW affine coordinate and the guarded chart over the original ACF
ambient are proved by the separate consumers above.

[GroupConfig/Psi.lean](GroupConfig/Psi.lean) applies the precise main theorem to
`QWitness.PsiCore` over an ACF universal domain, obtaining the rank-two group of
germs acting on a curve up to interalgebraicity.
[GroupConfig/PsiConstructible.lean](GroupConfig/PsiConstructible.lean) specializes the
general configuration theorem with constructibility on the same actual data. It chooses a
generic base point and both sampling stages internally, proves freshness of the combined
parameters over the original base, and states the rank-two, one-orbit and two-product
conclusions over the literal final algebraically closed base. The group, stabilizer and
homogeneous-space presentations have the source fields. These theorems do not algebraize
the group or descend the chart/action to the original fields.

Open:

- auxiliary source statements outside the completed finite #29 audit;
- the source's definability-in-families assertions for rank and connectedness;
- original algebraization, affine-action classification and scheme/action descent,
  including the remaining witness descent.

The guarded chart's fixed formulas, independence and original-ACF-field coordinate descent
are proved in `GuardedAffineGrid`; they do not discharge the separate scheme/action statements.

The proved Q′ route bypasses group extraction, but the group configuration
statements remain obligations under the rules above.

## Fidelity and collaboration

Preserve the refutations and corrections in [#22](https://github.com/adamtopaz/acl_geom/issues/22),
[#23](https://github.com/adamtopaz/acl_geom/issues/23),
[#25](https://github.com/adamtopaz/acl_geom/issues/25),
[#27](https://github.com/adamtopaz/acl_geom/issues/27) and
[#31](https://github.com/adamtopaz/acl_geom/issues/31) and
[#32](https://github.com/adamtopaz/acl_geom/issues/32). Keep recorded proof gaps
distinct from false statements: the tensor-domain sketch
([#11](https://github.com/adamtopaz/acl_geom/issues/11)), the inference from infinite
absolute degree to independence ([#5](https://github.com/adamtopaz/acl_geom/issues/5)),
and the generic evaluation-map dimension argument
([#21](https://github.com/adamtopaz/acl_geom/issues/21)) do not themselves supply
their advertised conclusions.
Report an error with evidence on an issue before changing the source.

Follow [AGENTS.md](AGENTS.md). Both agents coordinate through chit, agree on
ownership before editing, and use one monitored Lean/Lake family at a time.
Prefer existing Mathlib APIs and prove only source results or reusable lemmas
with named mathematical consumers. Commit and push at natural green
checkpoints, after full library/book validation, and report on the relevant
issues. All communication with Adam is through issues on this repository;
GitHub activity stays within the repository.

## Keeping this goal current

Either agent may update this entire document as the project evolves. Coordinate
the editor through chit, keep changes reviewable, and record the review date
and the issue or evidence behind a genuine change in targets, dependencies,
critical path or completion criteria. Routine progress belongs in issues and
[CONTINUATION.md](CONTINUATION.md); do not grow a checkpoint diary here.

Read this goal and the current issues when resuming work. Adam's instructions
take precedence; `AGENTS.md` governs working rules, this file the shared
objective and completion criteria, and `CONTINUATION.md` the detailed handoff.
Changing a plan must not silently weaken the intended mathematical result.
Any proposed narrowing must be justified on a repository issue in the same
change; editing this file cannot make an unresolved obligation complete.
