/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Foundations: closure, lattice, and points" =>

%%%
tag := "foundations"
%%%

Fix a field extension $`K/k`. The mathematical object underlying the whole
reconstruction theorem is the operator sending a subset $`S \subseteq K` to
the set of elements of $`K` algebraic over the subfield $`k(S)`. This chapter
describes its formalization: the operator itself, the complete lattice of its
closed sets, and the point geometry given by the atoms of that lattice —
blueprint sections *Foundation I* and *Foundation II*, checklist items F1–F5.

# The relative algebraic closure operator
%%%
tag := "racl"
%%%

The closure operator is built from Mathlib's `IntermediateField.adjoin` and
relative `algebraicClosure`, with scalars restricted back to `k`:

{docstring AclGeom.racl}

Following the blueprint's proof-engineering rule, no downstream proof unfolds
this definition; everything goes through the carrier-level membership
criterion:

{docstring AclGeom.mem_racl_iff}

The operator is a *pregeometry* (blueprint Proposition 4.1): it is extensive
({name}`AclGeom.subset_racl`), monotone ({name}`AclGeom.racl_mono`),
idempotent ({name}`AclGeom.racl_racl`), and of finite character
({name}`AclGeom.exists_finset_racl`). Two small lemmas carry most of the
weight, converting between algebraicity over an intermediate field and
annihilating polynomials in $`K[X]` with coefficients in it:

{docstring AclGeom.isAlgebraic_of_coeff_mem}

{docstring AclGeom.exists_poly_of_isAlgebraic}

The *exchange* property is the geometric heart of the matter. Rather than the
blueprint's transcendence-degree computation, the formalization uses Mathlib's
algebraic-independence API — the pair $`(y, x)` is algebraically independent
iff each member is transcendental over the other's adjoin — bridged between
the ring $`F[x]` and the field $`F(x)` by the fraction-field instance:

{docstring AclGeom.isAlgebraic_adjoin_exchange}

{docstring AclGeom.racl_exchange}

Equivariance holds for any isomorphism of extensions of `k`
({name}`AclGeom.racl_map`), and the closure is invariant under replacing all
generators by a fixed positive power ({name}`AclGeom.racl_image_pow`) — over a
perfect field this makes every positive Frobenius iterate act trivially, with
negative iterates deferred to the perfection layer.

# The lattice of closed subextensions
%%%
tag := "closed-lattice"
%%%

An intermediate field is *relatively algebraically closed* when it captures
every element algebraic over it:

{docstring AclGeom.IsRAC}

The relatively algebraically closed intermediate fields form the lattice
$`\mathcal{G}(K/k)` of the blueprint:

{docstring AclGeom.ClosedIF}

The structural fact organizing this file is that `racl` is a *Galois
insertion* onto the closed fields ({name}`AclGeom.ClosedIF.gi`), and the
complete lattice structure is lifted along it. The insertion is set up so
that, definitionally, infima are intersections
({name}`AclGeom.ClosedIF.coe_sInf`) and suprema are relative closures of
composita ({name}`AclGeom.ClosedIF.coe_sSup`) — exactly the description in
blueprint Proposition 4.3.

# Points: atoms and atomisticity
%%%
tag := "points"
%%%

The *points* of the combinatorial geometry are the atoms of
$`\mathcal{G}(K/k)`. Every element $`x` outside the lattice bottom generates
one:

{docstring AclGeom.ClosedIF.point}

{docstring AclGeom.ClosedIF.point_le_iff}

Exchange gives the two facts that make the geometry work (blueprint Lemma
4.4): principal closures are atoms, and every atom is principal.

{docstring AclGeom.ClosedIF.isAtom_point}

{docstring AclGeom.ClosedIF.IsAtom.exists_eq_point}

Atomisticity (blueprint Lemma 4.5) is provided as an instance of Mathlib's
`IsAtomistic`, so the general theory of atomistic complete lattices applies
to $`\mathcal{G}(K/k)` directly.

Note a small generalization over the blueprint: nothing in this chapter
assumes that $`k` is relatively algebraically closed in $`K`. All statements
are relative to the lattice bottom $`\bot` (the closure of the image of
$`k`); the blueprint's hypothesis merely identifies that bottom with $`k`
and will be imposed only where it is genuinely needed.

# Equivalence of the two presentations
%%%
tag := "equivalence"
%%%

The geometry can be presented either as the closed lattice or as the set of
points with the closure operation

{docstring AclGeom.pointCl}

The bridge between the presentations is the computation of joins of points as
relative closures of sets of chosen generators:

{docstring AclGeom.sSup_point_image}

from which point-closure membership reduces to `racl` membership
({name}`AclGeom.mem_pointCl_iff_rep_mem`), exchange transports to the point
geometry ({name}`AclGeom.pointCl_exchange`), and the two presentations are
exhibited as order isomorphic:

{docstring AclGeom.ClosedIF.pointSetIso}

This is blueprint checklist item F5; the finite-rank predicates (F6) and the
transport of order isomorphisms to geometry equivalences complete the
foundations layer.
