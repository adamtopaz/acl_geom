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

#doc (Manual) "Transfer to arbitrary fields" =>

%%%
tag := "transfer"
%%%

Gismatullin's transfer principle (blueprint §9, milestone M5) moves the
correctness of the geometric relations from algebraically closed fields to
arbitrary perfect fields with a relatively algebraically closed base. The
statements the proof transfers are Boolean combinations of
closure-membership assertions, so no first-order syntax is formalized: the
entire principle reduces to three pieces of field theory about the
closures `racl k A` inside a fixed algebraically closed overfield.

# A field is not a finite union of proper subfields
%%%
tag := "no-field-cover"
%%%

The pigeonhole underlying the transfer (blueprint Lemma no-field-cover) is
proved from mathlib's B. H. Neumann coset-cover theorem applied to the
additive subgroups: some covering subfield has finite additive index; a
proper *infinite* subfield of finite index is impossible, because
multiplication by an outside element injects it into the quotient; and a
finite subfield of finite index forces the whole field to be finite, where
cyclicity of the unit group hands the covering to a single subfield.

{docstring AclGeom.exists_eq_top_of_subfield_cover}

{docstring AclGeom.exists_notMem_of_ne_top}

# Finite generators for intersections
%%%
tag := "intersection-generators"
%%%

The transfer needs intersections `racl k A ⊓ racl k B` to again be
finitely generated closures, with generators inside any prescribed field
`K₁` containing `A` and `B` (blueprint Lemma
finite-intersection-generator). The formalization diverges from the
blueprint proof twice, in both cases replacing infrastructure by a
computation:

* the transcendence-degree bookkeeping runs through mathlib's
  *algebraic-independence matroid*, whose closure operator is exactly
  `racl` — a matroid basis of the intersection's carrier is finite because
  it is an independent set inside the closure of the finite set `A`;

{docstring AclGeom.mem_matroidClosure_iff}

* the blueprint extends `K₁`-embeddings to automorphisms of `Ω` to see
  that the conjugates of a basis element stay in the intersection; the
  formal proof instead uses divisibility of minimal polynomials — an
  annihilator over `k(A)` with coefficients in `K₁` is divisible by the
  `K₁`-minimal polynomial, so all conjugates satisfy it:

{docstring AclGeom.conjugate_mem_racl}

The generators are then the coefficients of the minimal polynomials of the
basis elements: they lie in `K₁` by construction, and in the intersection
because a monic split polynomial's coefficients live wherever its roots
do.

{docstring AclGeom.coeff_mem_of_roots_mem}

{docstring AclGeom.exists_finite_inter_generator}

Only one of the two sets needs to be finite, a slight strengthening of the
blueprint statement that costs nothing.

# Strict-inclusion transfer
%%%
tag := "strict-transfer"
%%%

Properness of an inclusion of traced closures transfers between any two
fields `K₁ ≤ K₂` over which the data is defined (blueprint Lemma
strict-transfer): downward, a witness in `K₂` would have its `k(B)`-minimal
polynomial's coefficients trapped in the trace equality on `K₁`, making it
algebraic over the smaller closure.

{docstring AclGeom.inf_lt_inf_iff_of_le}

# The one-quantifier transfer
%%%
tag := "one-quantifier"
%%%

The three bricks assemble into the transfer principle (blueprint Theorem
one-quantifier-transfer). A disjunct of the normal form is a conjunction
of memberships `z ∈ racl k (Aᵢ)` and non-memberships `z ∉ racl k (Bⱼ)`;
iterating the intersection generator fuses the memberships into a single
closure `racl k C`, on which each excluded closure traces as another
finitely generated closure:

{docstring AclGeom.exists_finite_iInter_generator}

A witness in `K` exists exactly when the subfield `racl k C ⊓ K` is not
covered by the traced subfields — the relative no-field-cover:

{docstring AclGeom.exists_intermediateField_eq_of_subset_iUnion}

Each covering equality is the negation of a strict inclusion, which
transfers between `K₁` and `K₂`. As long as at least one membership
conjunct is present, no transcendence-degree hypothesis is needed —
blueprint hypothesis (9.4) enters only the degenerate no-`Aᵢ` case, which
is deferred to the descent milestone alongside its trdeg interface:

{docstring AclGeom.one_quantifier_transfer}

The remaining piece of this layer is the application to the geometric
`J`-predicate (blueprint §9's descent theorem), tracked on the M5
milestone issue.
