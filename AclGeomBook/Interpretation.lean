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
import AclGeom.Counterexamples.GenericArithmetic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Interpreting the field" =>

%%%
tag := "interpretation"
%%%

The interpretation layer (milestone M6) aims to quotient the
geometric `J`-locus by Frobenius ambiguity and construct a field.  The quotient
and its field operations are still open (#8).  The current addition and
multiplication incidences are projections of the `Q` and `Q′` predicates;
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
not prove ACF completeness, setoid laws, ratio semantics or non-generic
totalization. The conditional coordinate bijection and corrected generic
class arithmetic are displayed below.
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

Perfection, rank five and the still-open ACF `JCompletenessACF` input
remain explicit for that class description. No infinite-base or relatively
closed base hypothesis is added. The map's domain is the original geometric
`FrobEq` class, and its inverse encodes the same point tuple. Corrected
generic fixed-class arithmetic is proved below under the same explicit
inputs. Setoid laws, ratio semantics and non-generic totalization remain
open ([issue #23](https://github.com/adamtopaz/acl_geom/issues/23)).

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
under explicit completeness is displayed next; non-generic totalization and
ratio-field construction remain open (#23/#8).

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

This proves corrected generic fixed-class semantics. It does not handle
non-generic inputs or prove a ratio quotient, totalization, setoid laws,
unconditional ACF completeness, R1/R2 or reconstruction existence.
