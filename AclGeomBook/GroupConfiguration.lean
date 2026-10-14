/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import GroupConfig

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Group configuration: foundations" =>

%%%
tag := "group-configuration-constructibility"
%%%

The separate `GroupConfig` library follows the supplemental
`sources/group_configuration_blueprint.tex`. That document gives an informal
group-configuration proof and records the remaining algebraization and
application boundaries. Its full Lean formalization remains open (#12).

The library proves the following rank, universal-domain and constructibility
foundations. These results do not extract a group from a configuration.

# Rank, independence and fresh tuples
%%%
tag := "group-configuration-rank"
%%%

Over a base set $`C`, rank is the extended natural-number rank in the
algebraic-independence matroid over $`k(C)`. Independence of sets means that
every finite subset preserves its rank on adjoining the other set to the base.
The tower law, finite character, closure invariance, symmetry, transitivity,
independent closure intersection and independent base change are proved for
arbitrary fields. Cancellation in extended natural numbers uses finite ranks.

{docstring GroupConfig.erk}

{docstring GroupConfig.IndepOver}

{docstring GroupConfig.erk_union_eq}

{docstring GroupConfig.IndepOver.racl_inter_eq}

{docstring AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg}

A small set has finite rank. The universal-domain hypothesis explicitly
requires infinite transcendence degree over the base. It gives fresh tuples
of every finite rank over any small set, using finite generators for its
algebraic closure. Algebraic closedness is unnecessary for these lemmas.

{docstring GroupConfig.UniversalDomain}

{docstring GroupConfig.IsSmall.exists_finite_racl_eq}

{docstring GroupConfig.exists_erk_range_eq}

Automorphisms preserve the relative matroids, ranks and independence.

{docstring GroupConfig.erk_image}

{docstring GroupConfig.IndepOver.image}

# Constructible sets
%%%
tag := "group-configuration-constructible-sets"
%%%

Section 9 starts with a polynomial definition. A set of
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
