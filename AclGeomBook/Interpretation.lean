/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import AclGeom.Interpretation.FrobClass
import AclGeom.Interpretation.FrobLinkIncidence
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
can give different outputs.  The required representative alignment and the
Frobenius-link correctness argument remain open (#23):

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

The two-step bridge is the geometric Frobenius-class relation.  Its exact
semantic characterization and the resulting setoid laws are the next part
of the interpretation milestone:

{docstring AclGeom.FrobEq}

{docstring AclGeom.FrobEq.symm}

The multiplier point lies on the three lines joining corresponding rigid
coordinates. This is the incidence configuration of EH95 Lemma 2.8,
Figure 3; it follows directly from the multiplication diagram, without
configuration completeness or a choice of common representatives:

{docstring AclGeom.DirectFrobLink.exists_concurrent}

The converse still needs an algebraic argument from this concurrence to an
exact Frobenius twist. The two-link bridge also needs an explicit semantic
completeness statement for its geometric middle tuple (#23).

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

These refutations preserve the original predicates for provenance. EH95
Lemma 2.11 uses meets of joins of the given tuple coordinates to keep the
coupling lost by those predicates. Generic meet identities and derived
operations have checked private drafts; their integration, class correctness,
totalization and ratio-field construction remain open (#23).
