/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import GroupConfig.Constructible.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Group configuration: constructibility" =>

%%%
tag := "group-configuration-constructibility"
%%%

The separate `GroupConfig` library follows the supplemental
`sources/group_configuration_blueprint.tex`. That document gives an informal
group-configuration proof and records the remaining algebraization and
application boundaries. Its full Lean formalization remains open (#12).

The first proved part is Section 9's constructibility foundation. A set of
points is constructible over a field $`k` when it is a finite union of cells,
each cut out by finitely many polynomial equations and one polynomial
inequation with coefficients in $`k`. The implementation uses the pullback of
a constructible subset of the polynomial prime spectrum; the following
equivalence proves that this is exactly the stated polynomial definition.

{docstring GroupConfig.IsConstructibleOver}

{docstring GroupConfig.isConstructibleOver_iff_exists_polynomial_data}

# Chevalley on points
%%%
tag := "group-configuration-chevalley-points"
%%%

A finite coordinate projection preserves constructibility over $`k` when
the ambient field $`K` is algebraically closed. The base $`k` may be arbitrary,
and this theorem needs no transcendence-degree bound.

{docstring GroupConfig.IsConstructibleOver.image_projection}

Mathlib's Chevalley theorem first gives a constructible image in the prime
spectrum. To obtain an actual $`K`-valued point over a specified base point,
the proof localizes a prime quotient at the polynomial required to stay
nonzero. Its tensor product with $`K` is a nonzero algebra of finite type.
A maximal quotient embeds into $`K`, preserving the base point, all equations,
and the required nonvanishing. This proves equality with the image on points.

The generic-quantifier lemma, extraction and constructibility of the group,
parameter and witness descent, algebraization, and the guarded initial affine
chart remain separate obligations. The public reconstruction theorem still
has its open completeness inputs.
