/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import VersoManual
import AclGeom.Functorial.Literal
import AclGeom.Functorial.FrobeniusQuotient

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The functorial formulation" =>

%%%
tag := "functorial"
%%%

This chapter formalizes blueprint §20. The source groupoid `Ext^i` has relatively
algebraically closed extensions with a chosen perfection as objects. Its arrows are
isomorphisms of the chosen perfections that carry the perfected base onto the perfected base.
The literal geometry functor sends an arrow to its transported lattice isomorphism. It is full
on extensions of transcendence degree at least five, and its fibres are exactly the integral
Frobenius orbits. Quotienting by those orbits gives a functor that is bijective on Hom-sets
there (blueprint Thm `functorial-reconstruction`). In characteristic zero the literal functor is
already fully faithful; in positive characteristic it is not faithful.

The geometry side uses the closed-lattice presentation permitted after blueprint (20.3): the
groupoid `Core PartOrd` of partial orders and order isomorphisms, with `𝒢(K/k)` as the image of
`K/k`. Blueprint §20.1 also shows that the source groupoids for two choices of perfections are
canonically equivalent. That equivalence is not formalized here; `Perfection.induces_liftEquiv`
proves that the comparison isomorphisms induce the identity of `𝒢(K/k)`.

# Objects and arrows
%%%
tag := "functorial-objects"
%%%

An object bundles the extension with its chosen perfection; the perfected base of (20.1) is the
perfection's `basePerf`. The arrows are the blueprint's `PairPerfIso`, and they form a
groupoid with the composition, identities and inverses of field isomorphisms:

{docstring AclGeom.PerfExt}

{docstring AclGeom.PerfExt.Hom}

# The literal geometry functor
%%%
tag := "literal-geometry-functor"
%%%

An arrow `Φ` goes to the transported lattice isomorphism `T_Φ(M) = Φ(M^i) ∩ L` of (20.6). The
functor laws (20.9) and (20.11) are the identity and composition laws of the transported map
(`Perfection.inducedIso_refl`, `Perfection.inducedIso_trans`):

{docstring AclGeom.geomLit}

{docstring AclGeom.Perfection.inducedIso_refl}

{docstring AclGeom.Perfection.inducedIso_trans}

Isomorphisms in `PartOrd` are converted back to order isomorphisms of the closed lattices:

{docstring AclGeom.orderIsoOfPartOrdIso}

# Frobenius naturality
%%%
tag := "functorial-frobenius"
%%%

Integral Frobenius powers are automorphisms of every object. They act trivially on the
geometry (20.12) and commute with every arrow (20.14). The two characteristic exponents of an
arrow's source and target are not assumed equal; they agree because the arrow is a field
isomorphism:

{docstring AclGeom.PerfExt.frobHom}

{docstring AclGeom.PerfExt.geomLit_map_frobHom}

{docstring AclGeom.PerfExt.frobHom_naturality}

{docstring AclGeom.PerfExt.frobHom_eq_id}

# Fullness and the Hom-set fibres
%%%
tag := "hom-set-fibres"
%%%

On extensions of transcendence degree at least five the literal functor is full (20.15), by
the reconstruction theorem. Two arrows have the same image exactly when they differ by an
integral Frobenius power of the target (20.16), by the Frobenius kernel theorem. This is
blueprint Prop `hom-fibres`; in positive characteristic the exponent is unique:

{docstring AclGeom.geomLit_map_surjective}

{docstring AclGeom.geomLit_map_eq_iff}

{docstring AclGeom.PerfExt.frobHom_comp_injective}

# The Frobenius-orbit groupoid
%%%
tag := "frobenius-orbit-groupoid"
%%%

The Frobenius relation (20.17) is a congruence, so Mathlib's quotient category is the groupoid
`Ext^i/Frob` of (20.18)–(20.21). The literal functor is constant on classes and descends
(20.22):

{docstring AclGeom.PerfExt.frobRel}

{docstring AclGeom.PerfExt.congruence_frobRel}

{docstring AclGeom.geomQuot}

# Full faithfulness
%%%
tag := "functorial-reconstruction"
%%%

For extensions of transcendence degree at least five the descended functor is bijective on
Hom-sets (blueprint (20.23), Thm `functorial-reconstruction`). Its restriction to the full
subgroupoid `PerfExt.rankFive` is therefore full and faithful:

{docstring AclGeom.geomQuot_map_bijective}

{docstring AclGeom.PerfExt.rankFive}

In characteristic zero every integral Frobenius power is the identity. The literal functor is
then already bijective on Hom-sets, and its restriction to `PerfExt.rankFiveCharZero` is full and
faithful:

{docstring AclGeom.geomLit_map_bijective_of_p_eq_one}

{docstring AclGeom.PerfExt.rankFiveCharZero}

In positive characteristic and positive transcendence degree, Frobenius is a nontrivial
automorphism with trivial image, so the literal functor is not faithful. Only positive
transcendence degree is used here; fullness is claimed only at rank five:

{docstring AclGeom.PerfExt.frobHom_one_ne_id}

{docstring AclGeom.geomLit_map_not_injective}
