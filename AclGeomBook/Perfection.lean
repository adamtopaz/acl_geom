/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom.Perfection.Lattice
import AclGeom.Perfection.Existence
import AclGeom.Perfection.Naturality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Invariance under perfection" =>

%%%
tag := "perfection"
%%%

The reconstruction theorem produces field isomorphisms only after passing to
perfections: in positive characteristic, the combinatorial geometry cannot
distinguish an element from its $`p`-th power, so the reconstructed maps are
naturally defined on perfect closures. This chapter presents the perfection
layer (blueprint §Foundation III, checklist items P1–P3): the bundled
perfection, the perfected subfields, and the invariance of the whole closed
lattice — and hence of the geometry — under perfection.

# The perfection bundle
%%%
tag := "perfection-bundle"
%%%

The bundle is uniform in the characteristic exponent (`p = 1` in
characteristic zero). Theorems can use any chosen perfection:

{docstring AclGeom.Perfection}

Every field admits a chosen perfection. One construction uses the relative
perfect closure inside an algebraic closure:

{docstring AclGeom.Perfection.ofExpChar}

{docstring AclGeom.Perfection.instNonempty}

In characteristic zero, the identity inclusion gives a smaller choice:

{docstring AclGeom.Perfection.ofCharZero}

The perfected subfield of `M ≤ K` collects the elements with some `p`-power
in the image of `M`:

{docstring AclGeom.Perfection.perfSubfield}

{docstring AclGeom.Perfection.mem_perfSubfield_iff}

# The perfection order isomorphism
%%%
tag := "perfection-iso"
%%%

The compatible perfected base $`k^i` of blueprint equation (20.1) lives
inside the perfection of $`K`, avoiding any incompatible pair of choices:

{docstring AclGeom.Perfection.basePerf}

For a closed subextension $`M \in \mathcal{G}(K/k)`, the perfected subfield
is a closed subextension of the perfection: this is the raise-to-$`p^s`
argument of blueprint Proposition 5.1, executed with polynomial transport
along the Frobenius ring homomorphism and descent along the inclusion.

{docstring AclGeom.Perfection.isRAC_perfIF}

Together with the two pullback equations (5.1) and (5.2) —

{docstring AclGeom.Perfection.incl_mem_perfIF_iff}

{docstring AclGeom.Perfection.perfClosed_comapClosed}

— the perfection assembles into the order isomorphism of blueprint
Proposition 5.1:

{docstring AclGeom.Perfection.latticeIso}

Through `Point.map` and `pointCl_map_iff` from the foundations chapter, this
isomorphism transports the entire point geometry: the geometry of $`K/k` and
of $`K^{\mathrm{perf}}/k^{\mathrm{perf}}` are the same. The reconstruction
argument may therefore assume its ambient fields perfect, transporting the
final results back through this isomorphism.

# The integral Frobenius action
%%%
tag := "frobenius-action"
%%%

On the perfection, Frobenius is an automorphism, and its integral powers form
a `ℤ`-indexed family with the expected composition laws for free:

{docstring AclGeom.Perfection.frobZPow}

The key triviality theorem — the reason reconstruction can only ever be
unique *up to Frobenius* in positive characteristic — is that every integral
Frobenius power fixes every closed subextension of the perfection, and hence
every point of its geometry:

{docstring AclGeom.Perfection.frobZPow_mem_iff}

{docstring AclGeom.Perfection.frobZPow_image_closed}

# Naturality and change of chosen perfection
%%%
tag := "perfection-naturality"
%%%

A field isomorphism extends uniquely to any two chosen perfections. The
extension satisfies identity, composition and inverse laws:

{docstring AclGeom.Perfection.liftEquiv}

{docstring AclGeom.Perfection.liftEquiv_unique}

{docstring AclGeom.Perfection.liftEquiv_refl}

{docstring AclGeom.Perfection.liftEquiv_trans}

{docstring AclGeom.Perfection.liftEquiv_symm}

Perfected subfields commute with this transport. A compatible base-field
map also carries the perfected base onto the other perfected base:

{docstring AclGeom.Perfection.perfSubfield_map}

{docstring AclGeom.Perfection.basePerf_map}

The two perfection order isomorphisms intertwine the original transport:

{docstring AclGeom.Perfection.latticeIso_natural}

Taking the original field map to be the identity compares two choices of
perfection and induces the identity on the original closed-field lattice.
These establish the foundational naturality carryover in issues #24 and #10.
Explicit Induces packaging and the literal and quotient functors remain open.
