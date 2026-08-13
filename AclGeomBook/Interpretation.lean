/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import AclGeom.Interpretation.FrobClass

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Interpreting the field" =>

%%%
tag := "interpretation"
%%%

The interpretation layer (blueprint §10, milestone M6) starts from the
geometric `J`-locus and quotients its tuples by the Frobenius ambiguity that
the dependence geometry cannot see.  Its basic addition and multiplication
incidences are projections of the already-defined `Q` and `Q′` predicates:

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
