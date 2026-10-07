/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import AclGeom.Config.JCoordinates
import AclGeom.Interpretation.FrobClass
import AclGeom.Interpretation.FrobLinkSoundness
import AclGeom.Interpretation.JArithSem
import AclGeom.Interpretation.FrobLinkIncidence
import AclGeom.Interpretation.FrobEqForward
import AclGeom.Interpretation.FrobEqCorrect
import AclGeom.Interpretation.ClassCoordinates
import AclGeom.Interpretation.ClassArithmetic
import AclGeom.Interpretation.Ratio
import AclGeom.Interpretation.Decode
import AclGeom.Interpretation.Interp
import AclGeom.Interpretation.TotalOps
import AclGeom.Interpretation.Field
import AclGeom.Counterexamples.GenericArithmetic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Interpreting the field" =>

%%%
tag := "interpretation"
%%%

The interpretation layer (milestone M6) aims to quotient the
geometric `J`-locus by Frobenius ambiguity and construct a field. The quotient
by a global Frobenius setoid remains open (#8). The corrected geometric ratio
quotient, full carrier decoding and total operation graphs are proved below
under explicit ACF completeness. Transported field structure and naturality
remain open. The historical addition and multiplication incidences are projections
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
characterization under explicit ACF completeness is displayed below;
unconditional completeness and the resulting setoid laws remain open:

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
for perfect K of rank at least five from the still-open ACF
`JCompletenessACF` input:

{docstring AclGeom.FrobEq.frobenius_of_witnesses}

{docstring AclGeom.FrobEq.frobenius_of_witnesses_of_completeness}

Unconditional geometric bridge completeness and the original
common-representative calculation remain open (#23). These statements
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

# Conditional Frobenius classes
%%%
tag := "conditional-frobenius-class"
%%%

Combining the two-link rigidity implication with geometric soundness gives
the exact relation between semantic tuples. Perfection, rank five and
the still-open ACF `JCompletenessACF` input remain explicit; the reverse
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

Perfection, rank five and the still-open ACF `JCompletenessACF` input
remain explicit for that class description. No infinite-base or relatively
closed base hypothesis is added. The map's domain is the original geometric
`FrobEq` class, and its inverse encodes the same point tuple. Corrected
generic fixed-class arithmetic is proved below under the same explicit
inputs. Exact corrected ratio semantics is also proved below under these
inputs. The geometric ratio quotient and bijective nonzero decoding are
proved below, followed by the full adjoined-zero carrier equivalence.
Corrected total geometric graphs are proved below under the same inputs.
Transported field structure and naturality remain open
([issue #23](https://github.com/adamtopaz/acl_geom/issues/23)).

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

These refutations preserve the original predicates for provenance. The
faithful generic arithmetic below follows the meet/join construction of
EH95 Lemma 2.11, keeping the original tuple coordinates coupled.

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
and corrected total geometric graphs. Transported field structure and
naturality remain open (#23/#8).

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

Perfection, rank five and the still-open ACF `JCompletenessACF` input remain
explicit. There is no infinite-base or relatively closed base assumption.
The output is a geometric point tuple, and its class membership is proved
rather than assumed. These are the coupled EH95 relations, with the original
genericity clause; the refuted literal projections retain their provenance.

This proves corrected generic fixed-class semantics. The following
sections construct the corrected ratio quotient and its nonzero decoding.
Corrected total graphs are proved later under the explicit input.
Unconditional ACF completeness, R1/R2 and reconstruction existence remain open.


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

Perfection, rank five and the still-open ACF `JCompletenessACF` input remain
explicit. No infinite-base or relatively closed base assumption is added.
The corrected relation keeps the geometry and exact rank budget. The literal
predicate and its counterexample remain preserved.

This proves the corrected ratio equivalence with decoded equality. The
next section packages its geometric setoid/quotient and bijective nonzero
decoding, followed by the full adjoined-zero carrier equivalence.
Corrected total field graphs are proved later under the same explicit inputs.
R1/R2, unconditional completeness and final reconstruction remain open.

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
geometric quotient. Perfection, rank five and still-open ACF
`JCompletenessACF` remain explicit, over arbitrary base fields.
No global Frobenius setoid is claimed. The next section adjoins zero and
decodes the full carrier, followed by corrected total operation graphs.
Transported field structure, unconditional completeness, R1/R2 and
reconstruction remain open. Historical literal definitions and their refutation stay preserved.


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
perfection, rank five and still-open ACF `JCompletenessACF`.
The carrier is the geometric ratio quotient with its new zero. No quotient
field structure is installed. Corrected total operation graphs are proved below;
transported field structure, naturality, global Frobenius setoid, unconditional
completeness, R1/R2 and reconstruction remain open. The original literal
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

Perfection, rank five and still-open ACF `JCompletenessACF` remain
explicit for the semantic negation equivalence. There is no genericity
assumption between the two original inputs. This proves the corrected
counterpart of the blueprint's two-addition negation detour.
The original literal negation/totalization derivation retains its
historical/open status; no separate negation counterexample is claimed.
The corrected nonzero-addition detour is displayed next, followed by total
ratio-carrier graphs. Transported field structure, global Frobenius setoid,
unconditional completeness, naturality, R1/R2 and reconstruction remain open.


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

Perfection, uniform rank five and still-open ACF `JCompletenessACF`
remain explicit. This establishes the corrected class-level detour,
and the following section gives the full ratio-carrier graphs.
The historical literal negation/TOT derivation retains its open status and
exact provenance. Transported field structure, global Frobenius setoid,
unconditional completeness, naturality, R1/R2 and reconstruction remain open.


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
rank five and still-open ACF `JCompletenessACF` over arbitrary base fields.
Graph representative invariance comes from the geometric ratio quotient.
The common denominator is chosen existentially: an arbitrary choice
can put the numerator sum inside `racl k {a}`.

Transported field structure, graph naturality, global Frobenius setoid,
unconditional completeness, simultaneous representatives, R1/R2 and
reconstruction remain open. The literal TOT argument retains its
historical/open status and exact provenance.
