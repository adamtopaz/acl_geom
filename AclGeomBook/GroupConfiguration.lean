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

The library proves the following rank, universal-domain, dimension, locus and constructibility
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

# Dimension and generic loci
%%%
tag := "group-configuration-locus"
%%%

A surjection of domains over a field with a nonzero kernel strictly decreases
finite transcendence degree. Lifting a transcendence basis from the target and
using algebraicity forces the kernel to meet the polynomial ring on that basis,
contradicting its injectivity there. For finite tuples this proves that proper
containment of vanishing ideals strictly lowers rank. Equal ranks therefore turn
a containment of their vanishing ideals into equality.

{docstring Algebra.trdeg_lt_of_surjective_of_ker_ne_bot}

{docstring GroupConfig.erk_lt_of_idealOf_lt}

The locus ideal extends a tuple's vanishing ideal to ambient-field coefficients.
It contracts back to the original ideal, and is prime when its coefficient field
is algebraically closed. Genericity over an intermediate field means that the
vanishing ideal is exactly the extension of the original base ideal.

{docstring GroupConfig.locusIdeal}

{docstring GroupConfig.IsGenericOver}

This exact-ideal premise implies equality of the base ideals, preservation of
rank, and independence from the larger coefficient field for finite tuples.
Genericity descends to smaller intermediate fields. In an algebraically closed
ambient field, any two finite generic tuples are conjugate over their common
coefficient field.

{docstring GroupConfig.IsGenericOver.erk_coe_eq}

{docstring GroupConfig.IsGenericOver.indepOver}

{docstring GroupConfig.IsGenericOver.exists_algEquiv}

For finite tuples, the locus of an existing tuple over an algebraically closed
base has a generic point over every finite-rank intermediate field in an
algebraically closed universal domain. The proof embeds the abstract generic
point into the ambient field: relocate a finite transcendence basis to fresh
elements and extend the resulting embedding algebraically. Combining this witness
with dimension drop proves that independence is equivalent to an unchanged locus.

{docstring GroupConfig.exists_isGenericOver}

{docstring GroupConfig.isGenericOver_self_iff}

Every finite tuple also has a conjugate over a small algebraically closed subfield
that is independent from any specified small set.

{docstring GroupConfig.exists_algEquiv_indepOver}

The arbitrary-prime formulation of the supplemental generic-point existence lemma
remains an obligation; the theorem above constructs points of represented base
loci. All universal-domain and smallness hypotheses are explicit. These results
do not yet extract a group from a configuration.

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

# Boolean operations, substitution and quantifiers
%%%
tag := "group-configuration-closure-operations"
%%%

Constructible sets are closed under finite unions, intersections and complements.
Polynomial zero sets and nonzero loci are constructible. Polynomial substitution
preserves the coefficient field, and enlarging that field preserves constructibility.
These statements hold over arbitrary fields, without a transcendence-degree bound.

{docstring GroupConfig.IsConstructibleOver.preimage_polynomial}

{docstring GroupConfig.IsConstructibleOver.extend_base}

Chevalley and complementation give existential and universal quantifiers over all
ambient-field tuples. Both coordinate blocks are finite and the ambient field is
algebraically closed. These operations are inputs to the later generic-quantifier
lemma, whose quantifiers range over generic points of an irreducible variety.

{docstring GroupConfig.IsConstructibleOver.exists}

{docstring GroupConfig.IsConstructibleOver.forall}

The generic-quantifier lemma, extraction and constructibility of the group,
parameter and witness descent, algebraization, and the guarded initial affine
chart remain separate obligations. The public reconstruction theorem still
has its open completeness inputs.
