/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import AclGeom.Config.JCoordinates
import AclGeom.Interpretation.FrobClass
import AclGeom.Interpretation.FrobTransport
import AclGeom.Interpretation.FrobLinkSoundness
import AclGeom.Interpretation.JArithSem
import AclGeom.Interpretation.JArithTransport
import AclGeom.Interpretation.FrobLinkIncidence
import AclGeom.Interpretation.FrobEqForward
import AclGeom.Interpretation.FrobEqCorrect
import AclGeom.Interpretation.FrobSetoid
import AclGeom.Interpretation.ClassCoordinates
import AclGeom.Interpretation.ClassArithmetic
import AclGeom.Interpretation.Ratio
import AclGeom.Interpretation.Decode
import AclGeom.Interpretation.Interp
import AclGeom.Interpretation.TotalOps
import AclGeom.Interpretation.TotalTransport
import AclGeom.Interpretation.Field
import AclGeom.Interpretation.Naturality
import AclGeom.Interpretation.CompleteNaturality
import AclGeom.Counterexamples.BlueprintTransport
import AclGeom.Counterexamples.GenericArithmetic
import AclGeom.Counterexamples.RatioTransitivity
import AclGeom.Counterexamples.RatioReflexivity
import AclGeom.Counterexamples.RatioGraphValues
import AclGeom.Counterexamples.BlueprintTotalGraphs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Interpreting the field" =>

%%%
tag := "interpretation"
%%%

The interpretation layer (milestone M6) aims to quotient the
geometric `J`-locus by Frobenius ambiguity and construct a field. The global
Frobenius relation is now a setoid over perfect ambient fields at rank five (#8).
The corrected geometric ratio
quotient, full carrier decoding and total operation graphs are proved below
under explicit ACF completeness. A named transported field structure and
the actual decoding ring equivalence are proved below under the same inputs.
Geometric J-locus, Frobenius-link/bridge, coupled meet/join arithmetic
and corrected totalization/ratio transport are proved below with no
completeness input. Conditional class/carrier maps and graph transport are
proved below, given the canonical image-base equality and the actual
carriers' semantic inputs. The same geometric map gives an actual RingEquiv
and its composition with the decodings below. The canonical image base and
conditional field-isomorphism existence are also proved below, keeping both
ACF-completeness hypotheses explicit. Rank-five ACF `J` completeness is proved
(`jCompletenessACF`) and supplies these inputs; inducing reconstruction is completed in the
reconstruction chapter, whose public `reconstruction_target` discharges them internally. The
older statements of this chapter keep the inputs explicit. A new existence theorem below
supplies them internally and needs only perfect ambient fields, source rank five and the
closed-lattice isomorphism; its bases need not be relatively algebraically closed.
The historical addition and multiplication incidences are projections
of the `Q` and `Q′` predicates;
they are relations on closed points, whose interalgebraic representatives
can give different outputs. Corrected generic fixed-class semantics for the
coupled operations follows below under explicit ACF completeness (#23).
The Frobenius rigidity implications below keep their semantic endpoint
and bridge-completeness hypotheses explicit:

{docstring AclGeom.SumPoint}

{docstring AclGeom.MulPoint}

# The Frobenius-link language
%%%
tag := "frobenius-links"
%%%

A direct link shares the parameter coordinate and uses one multiplier point
on the three rigid coordinates `X,Q,R`.  The required genericity is expressed
as a rank-three clause.  Since later bridges may use a link in either
orientation, the undirected edge is symmetric definitionally:

{docstring AclGeom.DirectFrobLink}

{docstring AclGeom.DirectFrobEdge.symm}

The two-step bridge is the geometric Frobenius-class relation. Its semantic
characterization under explicit ACF completeness is displayed below; that input is
supplied at rank five by `jCompletenessACF`. `FrobSetoid` now proves the global equivalence
relation on all geometric J-tuples over perfect ambient fields at rank five, without a RAC
or infinite-base hypothesis. Its proof chooses a single semantic middle tuple and adds the
two Frobenius exponents; it supplies ACF completeness internally:

{docstring AclGeom.frobEq_equivalence}

{docstring AclGeom.frobEqSetoid}

The underlying relation and symmetry are:

{docstring AclGeom.FrobEq}

{docstring AclGeom.FrobEq.symm}

The multiplier point lies on the three lines joining corresponding rigid
coordinates. This is the incidence configuration of EH95 Lemma 2.8,
Figure 3; it follows directly from the multiplication diagram, without
configuration completeness or a choice of common representatives:

{docstring AclGeom.DirectFrobLink.exists_concurrent}

Three-line concurrence now forces an exact Frobenius twist for the
parameters of semantic endpoint witnesses. The algebraic proof compares
scaled curve loci over the closure of the multiplier representative;
common primitive signed exponents and shifted-binomial rigidity give the
exact parameter relation:

{docstring AclGeom.frobenius_of_concurrent_lines}

Lifting only the algebraic facts to an algebraically closed overfield and
its algebraic base removes both closure hypotheses. The natural-power
conclusion returns by injectivity of the field embedding:

{docstring AclGeom.frobenius_of_concurrent_lines_rel}

The link's rank clause supplies independence, and its shared parameter
point supplies interalgebraicity. The semantic endpoint equations then
identify the three lines, without configuration completeness:

{docstring AclGeom.DirectFrobLink.frobenius_of_witnesses}

The two-link bridge uses semantic coordinates for its geometric middle
tuple as the explicit hypothesis `hJ`. Its canonical form obtains them
for perfect K of rank at least five from the explicit ACF
`JCompletenessACF` input (supplied at rank five by `jCompletenessACF`):

{docstring AclGeom.FrobEq.frobenius_of_witnesses}

{docstring AclGeom.FrobEq.frobenius_of_witnesses_of_completeness}

The completeness input is supplied at rank five by `jCompletenessACF`; no separate
unconditional bridge statement is given, and the original common-representative
calculation remains open (#23). These statements
preserve the original geometric relations.

Semantic tuples with the same literal parameter are related by a fresh
bridge `j(t,a)`. Raising both representatives to the same positive
Frobenius power preserves all five closed points. Hence, if one semantic
parameter is a positive Frobenius power of the other, the tuples satisfy
`FrobEq`. The displayed statements require transcendence degree at least
five over any base field, including finite bases. They use configuration
soundness and require no completeness hypothesis:

{docstring AclGeom.jTupleOf_pow_expChar_pow}

{docstring AclGeom.frobEq_jTupleOf_of_common}

{docstring AclGeom.frobEq_of_frobenius_twist}

# Frobenius-link naturality
%%%
tag := "frobenius-link-naturality"
%%%

An arbitrary closed-lattice order isomorphism preserves and reflects the
geometric J-locus and Frobenius-link language. Its product relation
transports as a relation; its historical functionality is still refuted:

{docstring AclGeom.mulPoint_map_iff}

The tuple locus and rank-three independence clause are invariant,
across independent bases and universe levels:

{docstring AclGeom.isJTuple_map_iff}

{docstring AclGeom.pointTripleIndependent_map_iff}

All five directed-link fields transfer. In particular one common
multiplier serves the three rigid coordinates; no separate multipliers
are substituted:

{docstring AclGeom.directFrobLink_map_iff}

The two-edge bridge transfers with its tuple witness and the given
orientations of both edges. Mathlib's dependent-function equivalence
pulls back arbitrary tuple witnesses:

{docstring AclGeom.frobEq_map_iff}

This completes I6b2a, the Frobenius-relation stage of blueprint
`interpreted-reconstruction`. The proofs need only Field/Algebra
structures and the lattice isomorphism, with no perfection, semantic
completeness, rank-five bound, exponential characteristic or freshness
premise. They supply class-membership invariance for later quotient
carrier transport; they do not supply a global Frobenius setoid.

Coupled arithmetic and corrected totalization/ratio transport are proved
below. Conditional carrier/graph transport is proved later, given the
canonical image-base equality and carrier inputs. Conditional image-base
existence and the field-isomorphism endpoint are proved below under ACF
completeness. General interpreted reconstruction in its original scope remains open
(#23/#8). The literal source obligations and frozen M4a record are
preserved.

# Conditional Frobenius classes
%%%
tag := "conditional-frobenius-class"
%%%

Combining the two-link rigidity implication with geometric soundness gives
the exact relation between semantic tuples. Perfection, rank five and
the explicit ACF `JCompletenessACF` input (supplied at rank five by `jCompletenessACF`) remain
explicit; the reverse
twist-to-class direction uses soundness alone:

{docstring AclGeom.frobEq_iff_frobenius_twist}

Natural powers in either orientation are the same relation as an integral
Frobenius power in a perfect field:

{docstring AclGeom.exists_frobeniusZPow_iff}

{docstring AclGeom.frobEq_iff_exists_frobeniusZPow}

The class of `j(x₀,a)` consists exactly of tuples `j(x,a)` with the same
literal parameter. The geometric endpoint is made semantic by the explicit
ACF-completeness input. Applying inverse Frobenius to all its coordinates
fixes their closed points and normalizes its parameter to `a`:

{docstring AclGeom.frobEq_jTupleOf_iff}

No infinite-base or relatively closed base assumption is used. These
conditional statements preserve the original geometric relation. They do
not prove ACF completeness or non-generic totalization. The conditional
coordinate bijection, corrected generic class arithmetic, exact corrected
ratio semantics, bijective nonzero quotient decoding and the full adjoined-zero
carrier equivalence are displayed below.
The common-representative calculation remains a separate open obligation
([issue #23](https://github.com/adamtopaz/acl_geom/issues/23)).

# Coordinates on a fixed class
%%%
tag := "fixed-class-coordinates"
%%%

A tuple with a fixed literal parameter determines its first coordinate.
The arbitrary-field j-rigidity theorem compares Frobenius exponents;
a transcendental parameter separates them. In characteristic zero
Frobenius is the identity. Rank five supplies the two fresh elements:

{docstring AclGeom.eq_of_jTupleOf_eq}

This injectivity uses no perfection, completeness or relatively closed
base hypothesis. The actual coordinate bijection uses the conditional
class description above. It identifies the geometric class with exactly
the elements outside the parameter's relative closure:

{docstring AclGeom.jClassEquiv}

{docstring AclGeom.jClassEquiv_jTupleOf}

{docstring AclGeom.jClassEquiv_ne_zero}

Perfection, rank five and the explicit ACF `JCompletenessACF` input (supplied at rank five by
`jCompletenessACF`)
remain explicit for that class description. No infinite-base or relatively
closed base hypothesis is added. The map's domain is the original geometric
`FrobEq` class, and its inverse encodes the same point tuple. Corrected
generic fixed-class arithmetic is proved below under the same explicit
inputs. Exact corrected ratio semantics is also proved below under these
inputs. The geometric ratio quotient and bijective nonzero decoding are
proved below, followed by the full adjoined-zero carrier equivalence.
Corrected total geometric graphs are proved below under the same inputs.
A named transported field structure and its actual decoding ring equivalence
are proved below. Conditional carrier/graph transport with the image-base
equality explicit is proved below. Its canonical image-base existence and
conditional field-isomorphism endpoint are also proved below, keeping ACF
completeness explicit ([issue #23](https://github.com/adamtopaz/acl_geom/issues/23)).

# Refutations of the literal generic operation graphs
%%%
tag := "generic-arithmetic-audit"
%%%

The original blueprint addition and multiplication graphs allowed each
incidence clause to choose its own representatives. Scaling one input by a
nonzero base constant therefore gives extra outputs:

{docstring AclGeom.BlueprintJAdd}

{docstring AclGeom.BlueprintJMul}

Over an infinite base and with transcendence degree at least five, these
graphs are not functional even among tuples satisfying the same encoded
Frobenius-class membership relation:

{docstring AclGeom.blueprintJAdd_not_functional_on_class}

{docstring AclGeom.blueprintJMul_not_functional_on_class}

The literal ratio relation consequently relates pairs with different decoded
ratios. All its witnesses satisfy that class-membership relation:

{docstring AclGeom.BlueprintRatioEq}

{docstring AclGeom.blueprintRatioEq_counterexample}

The same counterexample rules out the advertised decoding function on a fixed class.
Even passing to the equivalence closure of the literal relation cannot make a function
respecting that relation send every semantic pair to its ratio:

{docstring AclGeom.blueprintRatioEq_no_decoder}

These refutations preserve the original predicates for provenance. The
faithful generic arithmetic below follows the meet/join construction of
EH95 Lemma 2.11, keeping the original tuple coordinates coupled.

# Laws of the literal ratio relation
%%%
tag := "literal-ratio-laws"
%%%

The source separately asserts reflexivity, symmetry and transitivity of its literal
ratio relation. Symmetry holds by exchanging the multiplier witnesses, for arbitrary
base and endpoint tuples over arbitrary fields:

{docstring AclGeom.BlueprintRatioEq.symm}

Over perfect ambient fields at rank five, the relation is reflexive on every pair in
the class of a semantic base tuple. Completeness and the characteristic exponent are
supplied internally; the base field may be arbitrary:

{docstring AclGeom.blueprintRatioEq_refl}

Transitivity fails over arbitrary base and ambient fields at rank five:

{docstring AclGeom.blueprintRatioEq_not_transitive}

For independent `x,y,z,a`, write `j(c)=j(c,a)`. The pairs
`r=(j(x),j(x))`, `m=(j(y),j(z))` and `t=(j(x),j(x²))` satisfy the first two
literal relations but not the third. The positive witnesses use that the right input
of literal multiplication contributes only its first and parameter points, and a square
has the same first point. The negative direction uses the multiplication diagram and
rank-three genericity alone. No perfection or completeness is needed for this refutation.

Thus the literal relation cannot supply the advertised setoid. The corrected coupled
ratio setoid and decoder are proved. The literal equivalence-closure carrier correspondence
below asserts no field structure or decoder. The positive scalar families also now work
over arbitrary bases when their scalar is specified; infinite bases are used to select
scalars in the existential counterexamples.

# Naturality of the literal predicates and quotient carriers
%%%
tag := "literal-arithmetic-naturality"
%%%

The geometric invariance assertion in the original interpreted-reconstruction proof is
separate from the failed operation semantics. An order isomorphism of closed-subfield
lattices preserves and reflects the literal predicates over arbitrary fields in four
independent universes. No perfection, completeness or rank hypothesis is needed:

{docstring AclGeom.sumPoint_map_iff}

{docstring AclGeom.blueprintJAdd_map_iff}

{docstring AclGeom.blueprintJMul_map_iff}

{docstring AclGeom.blueprintRatioEq_map_iff}

{docstring AclGeom.blueprintJNeg_map_iff}

{docstring AclGeom.blueprintJAddTotalNZ_map_iff}

The pointwise map also gives the quotient-carrier correspondence with an adjoined zero,
for any base tuple and its actual image. These are quotients by the equivalence closure
of the literal ratio relation; no field operations or decoding are asserted on them:

{docstring AclGeom.blueprintRatioCarrierMap}

The literal equivalence-relation assertion is refuted above at transitivity; symmetry and
fixed-class reflexivity in the source setting are proved. The following section transcribes
the two raw operation recipes and proves their geometric invariance. The advertised
forward operation laws are refuted on semantic representatives below. Totality, reverse
directions and the remaining provenance retain separate obligations, with no quotient
operation descent asserted.
This progress leaves the full I6b and I6c source-validation obligations open.

# Literal operation recipes on representatives
%%%
tag := "literal-total-graph-formulas"
%%%

The original nonzero recipes use explicit literal ratio-relation witnesses to replace
both inputs and compare the output. Every representative and arithmetic witness ranges
over the chosen class. The zero clauses complete these recipes with the identities named
in the source proof. The carrier here is the option of raw pairs of class members:

{docstring AclGeom.BlueprintRatioAddGraph}

{docstring AclGeom.BlueprintRatioMulGraph}

Addition uses a common denominator, with a negation zero branch or a total nonzero
addition branch. Multiplication uses two literal generic products, with their existing
independence guards. No further independence or non-negation guard is added.

The pointwise map sends a raw base tuple's class bijectively onto its actual image class:

{docstring AclGeom.frobEqClassMap}

Both recipe formulas are preserved and reflected over arbitrary fields in four
independent universes, with all replacement, comparison, arithmetic and class witnesses:

{docstring AclGeom.blueprintRatioAddGraph_map_iff}

{docstring AclGeom.blueprintRatioMulGraph_map_iff}

These are representative-level formulas with explicit relation witnesses. They do not
replace those witnesses with quotient equality. The next section refutes the advertised
forward operation laws on semantic representatives. Totality and reverse directions
remain separately tracked. No quotient operation descent or field structure is asserted
for these literal formulas.

# Wrong values in the literal operation recipes
%%%
tag := "literal-operation-wrong-values"
%%%

The two raw recipes admit outputs with the wrong sums and products of their explicit
semantic generator ratios. Both counterexamples use an infinite base, a perfect ambient
field and transcendence degree at least five. Every numerator and denominator tuple
belongs to the actual Frobenius class of `j(x,a)`. No quotient decoder is assumed.

For independent `x,y,a` and a base scalar `κ` different from zero and one, addition
accepts the common-denominator inputs `(j(x,a),j(y,a))` and `(j(y,a),j(y,a))`, with
output `(j(κx+y,a),j(y,a))`. Its ratio differs from `x/y + y/y`:

{docstring AclGeom.blueprintRatioAddGraph_wrong_sum}

Multiplication accepts the reciprocal inputs `(j(x,a),j(y,a))` and `(j(y,a),j(x,a))`,
with output `(j(κxy,a),j(xy,a))`. Its ratio is `κ`, whereas the input ratios multiply
to one:

{docstring AclGeom.blueprintRatioMulGraph_wrong_product}

The scalar-family arithmetic producers supply these outputs. Literal ratio reflexivity
supplies all input replacements and output comparisons, and the common-parameter bridges
supply every tuple's class membership. The addition proof uses the existing denominator
`y`; no extra independence or rank-six assumption is needed.

These refute both forward advertised operation laws on semantic representatives.
Totality remains a separate obligation. Reverse directions require a precise domain:
the raw addition clause at a zero input requires equality of output representatives,
so equal ratios alone cannot justify replacing that output. No quotient functionality
or descent is claimed. The corrected coupled graphs, decoding and reconstruction remain
proved. The source error was reported on issue #8 before source annotations; the original
statements and proofs are preserved.

# Coupled generic arithmetic
%%%
tag := "coupled-j-arithmetic"
%%%

For independent `x,y,a`, the EH95 subtraction and division constructions
intersect lines spanned by coordinates of `j(x,a)` and `j(y,a)`:

{docstring AclGeom.jSub}

{docstring AclGeom.jDiv}

The coordinate identities compute `j(x-y,a)` and `j(x/y,a)` over any base
field. They need no configuration completeness or rank-five hypothesis:

{docstring AclGeom.jSub_jC}

{docstring AclGeom.jDiv_jC}

Negation and inversion use a generic auxiliary tuple; addition and
multiplication follow from subtraction and division. The Point-valued
relations are defined by these meets and joins, and are functional. On
inputs with a shared literal parameter and independent representatives,
they have the unique outputs `j(x+y,a)` and `j(xy,a)`:

{docstring AclGeom.JAddRel}

{docstring AclGeom.JMulRel}

{docstring AclGeom.jAddRel_jTupleOf_iff}

{docstring AclGeom.jMulRel_jTupleOf_iff}

The output is semantic; geometric `J` membership follows from the
rank-five soundness theorem over any base field. The class-level computation
under explicit completeness is displayed next, followed by the ratio quotient
and corrected total geometric graphs, then a named transported field
structure and its actual decoding ring equivalence. Coupled arithmetic
and corrected totalization/ratio naturality are proved next, followed by
conditional carrier/graph transport with the image-base equality explicit.
Image-base existence is proved below under ACF completeness; general interpreted
reconstruction in its original scope remains open (#23/#8).

# Coupled arithmetic naturality
%%%
tag := "coupled-arithmetic-naturality"
%%%

The EH95 difference and quotient are lattice formulas, so they commute
with every closed-lattice order isomorphism, across arbitrary bases and
universe levels. Their map laws hold on all closed-lattice five-tuples,
without requiring point tuples or generic representatives:

{docstring AclGeom.jSub_map}

{docstring AclGeom.jDiv_map}

Point-tuple coordinates commute definitionally with the induced point
map. The derived negation, inverse, sum and product commute locally;
Mathlib's injectivity of composition reflects the coordinate equality
that defines the coupled relations:

{docstring AclGeom.jAddRel_map_iff}

{docstring AclGeom.jMulRel_map_iff}

This completes I6b2b, the coupled-arithmetic stage of blueprint
`interpreted-reconstruction`. It preserves the original coordinate
coupling and order with no semantics, genericity, completeness,
perfection, rank-five, exponential-characteristic, Infinite or freshness
premise. The named consumers are corrected total negation/nonzero
addition, ratio equivalence and the full-carrier product graph.

Corrected totalization/ratio transport is proved next, followed by
conditional carrier/graph transport with the image-base equality explicit.
Conditional image-base existence is proved below under ACF completeness.
General interpreted reconstruction in its original scope remains open (#23/#8). The
literal source obligations and frozen M4a record are preserved.

# Totalization and ratio naturality
%%%
tag := "totalization-and-ratio-naturality"
%%%

An arbitrary closed-lattice order isomorphism preserves and reflects
the corrected total relations, for an arbitrary base tuple and all raw
point tuples, across independent bases and universe levels.

Negation retains both witness tuples and both generic coupled additions:

{docstring AclGeom.jNegTotalRel_map_iff}

Total nonzero addition retains all four witness tuples, the corrected
negation clause and all three generic coupled additions. Its output
is arbitrary; class membership is not a premise:

{docstring AclGeom.jAddTotalNZRel_map_iff}

Ratio equivalence retains all four witness tuples and all four generic
coupled cross-products, with every independence clause:

{docstring AclGeom.ratioEq_map_iff}

Mathlib's dependent-function equivalence pulls back every target witness;
the earlier Frobenius, coupled arithmetic and rank-three iff laws transfer
the conjuncts. No semantics, genericity, completeness, perfection,
rank-five, exponential-characteristic, Infinite or freshness premise
or global Frobenius setoid is assumed.

This completes I6b2c and the corrected-relation transport stage I6b2
of blueprint `interpreted-reconstruction`. Its named consumers are
class-pair quotient well-definedness and full-carrier graph preservation.
Conditional carrier/graph transport is proved next with the canonical
image-base equality and carrier inputs explicit. Conditional image-base
existence is proved below under ACF completeness. General interpreted
reconstruction in its original scope remains open (#23/#8). The literal source
obligations and frozen M4a record remain.

# Conditional carrier and graph naturality
%%%
tag := "conditional-carrier-and-graph-naturality"
%%%

Fix a closed-lattice order isomorphism across independent bases and
universe levels, and explicitly identify the image of the source
canonical base tuple with the chosen target canonical base tuple.
The pointwise tuple equivalence restricts to the fixed Frobenius classes;
this class map needs no perfection, rank or completeness input:

{docstring AclGeom.ratioClassMap}

Pairs of class members map componentwise. The corrected ratio iff law
makes Mathlib's quotient equivalence well-defined, and its option
congruence extends over the adjoined zero. This is the actual geometric
map; it is not defined through decoding. Its zero and representative
values, and the pointwise value of the class map, are definitional:

{docstring AclGeom.ratioInterpMap}

Addition transports both zero clauses and the common-denominator clause,
including the opposite-numerator and total-nonzero-sum branches:

{docstring AclGeom.ratioAddGraph_map_iff}

Multiplication transports the zero-factor branch and both generic
numerator/denominator products, with all six class witnesses and both
rank-three independence clauses:

{docstring AclGeom.ratioMulGraph_map_iff}

Target witnesses pull back by class-map surjectivity; carrier equalities
reflect by injectivity. The base-image equality is rewritten in
propositions after restating the pointwise map, preserving dependent types.
The actual carriers keep independent perfection, rank-five, exponential-
characteristic and ACF-completeness inputs on both sides.

This accepts I6b3 under the stated image-base equality and carrier inputs.
The following section bundles this same geometric map as an actual RingEquiv
and composes it with both decoding equivalences. The canonical image base
and conditional field-isomorphism endpoint follow in the next section.
General interpreted reconstruction in its original scope remains open (I6b/I6c), along
with the literal source obligations. The global Frobenius setoid is proved above under
perfection and rank five; the frozen M4a record is preserved.

# Conditional induced ring isomorphisms
%%%
tag := "conditional-induced-ring-isomorphisms"
%%%

The geometric carrier map is additive and multiplicative for the actual
named field structures because the full geometric graphs characterize
these operations and the map preserves those graphs:

{docstring AclGeom.ratioInterpMapRingEquiv}

Its underlying Equiv is exactly `ratioInterpMap`. Native zero and
representatives remain definitional; one and inverse follow from Mathlib's
RingEquiv API. No new global field instance or evaluation declaration is
installed. The source/target field instances are proof-local named ones.

Composing with both actual decoding RingEquivs gives the corrected
counterpart of blueprint `interpreted-reconstruction`, given the canonical
image-base equality:

{docstring AclGeom.interpretedRingEquiv}

Its pointwise value is exactly `D_L ∘ Φ ∘ D_K⁻¹`, with the same geometric
map in the middle. Pointwise forward and inverse composite values are
checked definitionally; the decoding diagram commutes by the inverse laws. Both perfections,
separate exponential-characteristic
parameters, rank-five bounds, ACF-completeness inputs and the canonical
image-base equality remain explicit across independent bases and universes.
This accepts the constructive part I6c1. The next section proves the
canonical image-base existence and conditional field-isomorphism endpoint
I6c2. General I6b/I6c remain open under their original scope. The named
consumers are that conditional existence endpoint, accepted conditional R1b
base recovery and corrected conditional scalar one in the reconstruction
chapter. The global Frobenius setoid is proved above under perfection and rank five.
The literal source obligations remain open, and the frozen M4a record is preserved.

The reconstruction chapter proves actual base-range compatibility for
this same `interpretedRingEquiv` under explicit RAC bases and these carrier
inputs. Its inverse is the swapped construction pointwise by reflexivity.
The same chapter proves corrected conditional scalar one and outside-point
recovery without RAC, and assembles actual inducing equality and compatible
inducing existence in perfect fields under RAC bases and explicit completeness.
Conditional original-field inducing existence through chosen perfections is
proved in the reconstruction chapter with both perfected completeness inputs
explicit. Main assembles the public lattice-form target and supplies both inputs by
`jCompletenessACF`, so `reconstruction_target` is unconditional. The base-image and scalar
steps (R1/R2) of the reconstruction chapter keep their completeness inputs explicit.

# Conditional image-base and field-isomorphism existence
%%%
tag := "conditional-image-base-existence"
%%%

The image of a canonical source base tuple is a geometric J-tuple by
naturality and rank-five soundness. The target rank-five bound follows
from the order isomorphism, including across independent universes.
Target ACF J completeness then gives an independent target pair with the
exact canonical tuple equality:

{docstring AclGeom.exists_map_jTupleOf_eq}

This theorem needs only target perfection, its exponential characteristic
and target ACF completeness, the lattice isomorphism and source rank/pair.
It needs no source perfection/completeness or supplied target-rank bound.
Its named consumer derives a source independent pair inline by freshness
at rank five, obtains the image pair and applies the actual decoded
geometric RingEquiv:

{docstring AclGeom.nonempty_ringEquiv_of_closedIF_orderIso}

This accepts I6c2 in its conditional scope. The conclusion is the actual
`Nonempty (K ≃+* L)`, with no supplied pair, target rank or image-base
equality. Both perfections, separate exponential-characteristic parameters
and both ACF J-completeness hypotheses remain explicit (each supplied at rank five by
`jCompletenessACF`), across
independent bases/universes and including finite bases and characteristics
zero/two. No helper, global instance or evaluation declaration is added.

The existence theorem does not assert `Induces` compatibility with the
supplied lattice map or recovery of the base fields; those are proved in the
reconstruction chapter. General I6b/I6c in their original scope and all literal
source/TOT obligations remain open; the rank-five global Frobenius setoid is proved above. The
frozen M4a record is preserved.

# Field-isomorphism existence for perfect ambient fields
%%%
tag := "perfect-field-isomorphism-existence"
%%%

The proved rank-five ACF completeness theorem supplies both completeness inputs of the
conditional existence result. The target rank bound follows from the lattice isomorphism,
and the characteristic exponents are chosen internally:

{docstring AclGeom.nonempty_ringEquiv_of_closedIF_orderIso_of_perfectField}

This result needs only perfect ambient fields, source transcendence degree at least five
and the closed-lattice order isomorphism, over arbitrary bases and four independent
universes. It asserts existence of a field isomorphism. Compatibility with the supplied
lattice map and recovery of the bases are additional conclusions of the public
reconstruction theorem under its relatively algebraically closed base hypotheses.

# Generic arithmetic on the fixed class
%%%
tag := "generic-class-arithmetic"
%%%

Take two members of the original geometric `FrobEq` class. Their `X`
coordinates and common parameter must satisfy the geometric rank-three
genericity clause. The conditional class description presents them with
the same literal parameter; rank three then gives independent generators.
The coupled meet/join operation output remains in the class, and the
coordinate bijection computes the corresponding field operation:

{docstring AclGeom.JAddRel.jClassEquiv_add}

{docstring AclGeom.JMulRel.jClassEquiv_mul}

{docstring AclGeom.JSubRel.jClassEquiv_sub}

{docstring AclGeom.JDivRel.jClassEquiv_div}

Perfection, rank five and the explicit ACF `JCompletenessACF` input (supplied at rank five by
`jCompletenessACF`) remain
explicit. There is no infinite-base or relatively closed base assumption.
The output is a geometric point tuple, and its class membership is proved
rather than assumed. These are the coupled EH95 relations, with the original
genericity clause; the refuted literal projections retain their provenance.

This proves corrected generic fixed-class semantics. The following
sections construct the corrected ratio quotient and its nonzero decoding.
Corrected total graphs are proved later under the explicit input. Rank-five ACF
completeness is `jCompletenessACF`, and chosen-perfection reconstruction is proved in the
reconstruction chapter.


# Corrected ratio semantics
%%%
tag := "corrected-ratio-semantics"
%%%

The historical ratio predicate is refuted above. Its corrected replacement
keeps the four witness products, uses the coupled `JMulRel`, and requires
geometric rank-three genericity for each product. Every auxiliary witness
is a member of the original geometric class; the definition uses no field
coordinates:

{docstring AclGeom.RatioEq}

For arbitrary input class members, every witness gives equality of decoded
ratios. Class coordinates are outside the parameter closure and hence nonzero,
so the four multiplication equations can be cancelled:

{docstring AclGeom.RatioEq.div_eq}

Conversely, equality of ratios writes one of the four field coordinates in
the closure of the other three and the parameter. A single fresh multiplier
outside this explicit four-element set supplies the witnesses. The four
genericity clauses are proved separately; numerator and denominator within
an input pair need not be generic with one another:

{docstring AclGeom.ratioEq_of_div_eq}

{docstring AclGeom.ratioEq_iff}

Perfection, rank five and the explicit ACF `JCompletenessACF` input (supplied at rank five by
`jCompletenessACF`) remain
explicit. No infinite-base or relatively closed base assumption is added.
The corrected relation keeps the geometry and exact rank budget. The literal
predicate and its counterexample remain preserved.

This proves the corrected ratio equivalence with decoded equality. The
next section packages its geometric setoid/quotient and bijective nonzero
decoding, followed by the full adjoined-zero carrier equivalence.
Corrected total field graphs are proved later under the same explicit inputs.

# The ratio quotient and nonzero decoding
%%%
tag := "ratio-quotient-nonzero-decoding"
%%%

On pairs of members of the fixed geometric class, corrected `RatioEq`
is an equivalence relation because its exact semantics is equality of
decoded ratios. The setoid retains this geometric relation:

{docstring AclGeom.ratioEq_equivalence}

{docstring AclGeom.ratioSetoid}

Its quotient maps into the actual nonzero field elements `Kˣ`. Both
coordinates are nonzero, by `jClassEquiv_ne_zero`, and every geometric
witness gives the same ratio; `Quotient.lift` therefore descends:

{docstring AclGeom.ratioDecode}

{docstring AclGeom.ratioDecode_mk}

Injectivity is the converse of corrected ratio semantics. For any
nonzero `z`, choose `t` outside the closure of the explicit three-element
set `{a, z, x₀}`. Both `t` and `z*t` are outside the closure of
`{x₀, a}`. Pair restrictions of independent triples give the two class
members `j(z*t,a)` and `j(t,a)`; their quotient decodes to `z`:

{docstring AclGeom.ratioDecode_bijective}

{docstring AclGeom.ratioDecodeEquiv}

This proves the nonzero part of blueprint `decode-equiv` for the corrected
geometric quotient. Perfection, rank five and explicit ACF
`JCompletenessACF` (supplied at rank five by `jCompletenessACF`) remain explicit, over arbitrary
base fields.
This corrected ratio construction does not use the global Frobenius setoid proved above. The
next section adjoins zero and
decodes the full carrier, followed by corrected total operation graphs.
The transported field structure is proved below. Historical literal definitions and
their refutation stay preserved.


# The adjoined-zero carrier and full decoding
%%%
tag := "adjoined-zero-carrier-decoding"
%%%

Adjoin a new zero to the corrected geometric ratio quotient, using
Mathlib's `WithZero` carrier:

{docstring AclGeom.RatioInterp}

The accepted equivalence of nonzero decoding extends by
`Equiv.optionCongr`, then Mathlib's `WithZero.withZeroUnitsEquiv`
identifies the units with an adjoined zero and the full field.
This constructs the actual carrier equivalence onto every element of `K`:

{docstring AclGeom.ratioInterpDecode}

Both evaluation laws reduce by definition:

{docstring AclGeom.ratioInterpDecode_zero}

{docstring AclGeom.ratioInterpDecode_coe}

This proves the full corrected blueprint `decode-equiv` under explicit
perfection, rank five and explicit ACF `JCompletenessACF` (supplied at rank five by
`jCompletenessACF`).
The carrier is the geometric ratio quotient with its new zero. A named
transported field structure and actual decoding ring equivalence are proved
below after the total geometric graphs, and naturality is proved later. The global
Frobenius setoid is proved above under perfection and rank five. The original literal
construction and its counterexample remain preserved.


# Corrected total negation
%%%
tag := "corrected-total-negation"
%%%

The blueprint avoids the non-point zero by passing through two generic
additions. The corrected relation keeps both auxiliary class members
and both geometric genericity clauses, using the coupled `JAddRel`:

{docstring AclGeom.JNegTotalRel}

Every witness has the same coordinate equations `r = u+z` and
`z = v+r`, so the second input is the negative of the first:

{docstring AclGeom.JNegTotalRel.neg_eq}

Conversely, present the two inputs with their common literal parameter.
For `y = -x`, choose `z` outside the closure of the explicit two-element
set `{a,x}` and put `r = x+z`. The triples `(x,z,a)` and
`(-x,x+z,a)` are independent, by insertion and mutual closure membership.
Both witnesses lie in the original geometric class:

{docstring AclGeom.jNegTotalRel_of_neg_eq}

{docstring AclGeom.jNegTotalRel_iff}

The genericity proof is shared with direct Frobenius links and corrected
ratios. Its type and proof use no perfection, exponential characteristic,
rank-five or completeness input:

{docstring AclGeom.pointTripleIndependent_jTupleOf}

Perfection, rank five and explicit ACF `JCompletenessACF` (supplied at rank five by
`jCompletenessACF`) remain
explicit for the semantic negation equivalence. There is no genericity
assumption between the two original inputs. This proves the corrected
counterpart of the blueprint's two-addition negation detour.
The original literal negation/total-nonzero-addition claims are separately refuted in
`Counterexamples.GenericNegation`; their formulas and proof retain their provenance.
The validation chapter displays the class-level refutations.
The corrected nonzero-addition detour is displayed next, followed by total
ratio-carrier graphs. The named transported field structure is proved below. The global
Frobenius setoid is proved above under perfection and rank five. Conditional carrier/graph
transport is proved above with the
canonical image-base equality and carrier inputs explicit; conditional image-base existence
and the field-isomorphism endpoint are also proved above. General interpreted
reconstruction in its original scope remains open.


# Corrected total nonzero addition
%%%
tag := "corrected-total-nonzero-addition"
%%%

The corrected counterpart of the blueprint's nonzero-addition detour
retains four auxiliary class members, corrected negation, and three
coupled additions with their geometric genericity clauses:

{docstring AclGeom.JAddTotalNZRel}

The output is an arbitrary tuple. Every witness derives output class
membership and the sum of the input coordinates:

{docstring AclGeom.JAddTotalNZRel.exists_mem_add}

Conversely, present all three tuples with their common literal parameter
and write `c = x+y`. An element `z` fresh over the explicit
three-element set `{a,x,y}` gives generic triples `(x,z,a)`,
`(y,-z,a)` and `(c,x+z,a)`. Mutual closure membership then gives
`(x+z,y-z,a)`. The witnesses are `j(z,a)`, `j(-z,a)`,
`j(x+z,a)` and `j(y-z,a)`:

{docstring AclGeom.jAddTotalNZRel_of_add_eq}

{docstring AclGeom.jAddTotalNZRel_iff}

No genericity between the original two inputs is assumed, and output
membership is derived in the forward direction and kept inside the
existential on the right of the equivalence. For canonical inputs, if
`x+y` lies outside `racl k {a}`, the relation holds exactly when the
raw output equals `j(x+y,a)`. This is the blueprint's actual output
condition; being merely nonzero in `K` is insufficient.

Perfection, uniform rank five and explicit ACF `JCompletenessACF` (supplied at rank five by
`jCompletenessACF`)
remain explicit. This establishes the corrected class-level detour,
and the following section gives the full ratio-carrier graphs.
The literal negation/total-nonzero-addition claims are refuted with their original provenance
preserved; the later literal full-carrier TOT claim remains open. The named transported field
structure is proved below. The global
Frobenius setoid is proved above under perfection and rank five. Conditional carrier/graph
transport is proved above with the
canonical image-base equality and carrier inputs explicit; conditional image-base existence
and the field-isomorphism endpoint are also proved above. General interpreted
reconstruction in its original scope remains open.


# Corrected total geometric field graphs
%%%
tag := "corrected-total-field-graphs"
%%%

On the full corrected geometric ratio carrier, addition uses the named
zero clauses and existential representatives with a common denominator.
Opposite numerators give the named zero; otherwise the corrected total
nonzero numerator sum gives the output ratio:

{docstring AclGeom.RatioAddGraph}

Multiplication chooses representatives whose numerator and denominator
pairs have generic coupled products, then takes their output ratio:

{docstring AclGeom.RatioMulGraph}

The definitions use geometric class members and quotient equalities for
the corrected geometric ratio setoid. They contain no decoded coordinates,
choices or `Quotient.out`. Their semantic laws cover every witness:

{docstring AclGeom.ratioAddGraph_iff}

{docstring AclGeom.ratioMulGraph_iff}

For addition, a denominator fresh over `{a,c,d}` moves the nonzero
decoded values, including a nonzero sum, outside `racl k {a}`.
The existing inner addition detour may use a fifth independent element.
For multiplication, successive fresh elements over `{a,c,d}` and
`{a,c,d,b}` give the two independent product triples. Both constructions
keep the explicit uniform rank-five bound and require no sixth element.

The existing fresh-multiple and independent-pair helpers are now public;
their unchanged types and proofs serve both the old class/ratio
constructions and these graph witnesses:

{docstring AclGeom.mul_fresh_notMem}

{docstring AclGeom.pair_of_notMem}

Decoding is bijective, so each pair of interpreted inputs has exactly
one graph output:

{docstring AclGeom.ratioAddGraph_existsUnique}

{docstring AclGeom.ratioMulGraph_existsUnique}

This proves the corrected totality/functionality and decoded-operation
part of blueprint `total-field-graphs`, with explicit perfection,
rank five and explicit ACF `JCompletenessACF` (supplied at rank five by `jCompletenessACF`) over
arbitrary base fields.
Graph representative invariance comes from the geometric ratio quotient.
The common denominator is chosen existentially: an arbitrary choice
can put the numerator sum inside `racl k {a}`.

The following section installs a named transported field structure with
these exact geometric graphs. Conditional carrier/graph transport is proved
above with the canonical image-base equality and carrier inputs explicit.
Conditional image-base existence and the field-isomorphism endpoint are
proved above under ACF completeness. The global Frobenius setoid is proved under perfection
and rank five. Original simultaneous-representative obligations remain open. The literal TOT
argument retains its historical/open status
and exact provenance.


# Named interpreted field structure
%%%
tag := "named-interpreted-field"
%%%

The corrected full-carrier total graphs characterize the operations of a
named transported Field structure. It uses Mathlib's injective-field
constructor with the carrier's existing adjoined zero and the decoding
transfer data for every other operation:

{docstring AclGeom.ratioInterpField}

This structure is reducible and installed explicitly when needed, with
no global Field instance. Its zero agrees definitionally with the native
geometric zero. The actual decoding is a ring equivalence onto the whole
field:

{docstring AclGeom.ratioInterpRingEquiv}

The geometric graphs agree exactly with the installed sum and product:

{docstring AclGeom.ratioAddGraph_iff_eq_add}

{docstring AclGeom.ratioMulGraph_iff_eq_mul}

This completes the corrected conditional field-transport part of
blueprint `decode-equiv` and I5c, under explicit perfection, rank five
and explicit ACF J completeness (supplied at rank five by `jCompletenessACF`) over
arbitrary base fields. It supplies
the field structures for later interpreted reconstruction. Conditional
carrier/graph transport is proved above with the canonical image-base
equality and carrier inputs explicit. Conditional image-base existence and
the field-isomorphism endpoint are also proved above. The explicit completeness input is
supplied at rank five by `jCompletenessACF`, and the public reconstruction theorem is
unconditional. The global Frobenius setoid is proved under perfection and rank five;
original simultaneous-representative obligations remain open.
The literal source construction and TOT argument retain their historical/open status.
