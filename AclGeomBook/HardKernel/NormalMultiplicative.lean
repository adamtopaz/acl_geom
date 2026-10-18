/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.NormalMultiplicativeSubgroup

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The torus alternative: normal multiplicative subgroups are central" =>
%%%
tag := "normal-multiplicative-central"
%%%

The torus alternative in the original proof of Lemma 8.4 now has an actual scheme theorem.
A normal multiplicative-subgroup morphism into a connected algebraic group over an ACF base
is central: the joint conjugation morphism from G times Gm equals the second projection
followed by the inclusion. The exponent, regular conjugation lift, separating point and
constancy are proved internally. Every characteristic, including two, is covered.

{docstring AclGeom.MultiplicativeRigidity.normal_multiplicativeGroup_conj}

First classify actual group-scheme automorphisms of Gm over any field. Hopf-Spec full
faithfulness supplies an actual Hopf-algebra isomorphism of its coordinate group algebra.
Mathlib identifies bialgebra maps of group algebras over domains with maps of their groups.
Thus the exponent is an endomorphism of the integers. The inverse gives a multiplicative
inverse for its value at one, forcing that value to be one or minus one. The negation map
on exponents agrees with the actual scheme inverse, rather than only its point function.

{docstring AclGeom.MultiplicativeRigidity.hopfIso_eq_id_or_neg}

{docstring AclGeom.MultiplicativeRigidity.groupIso_eq_id_or_inv}

Normality supplies a regular conjugation lift through the monic inclusion. Restricting at
a group point gives an actual group-object isomorphism: cancel through the inclusion to
prove multiplication and use conjugation by the inverse point for its inverse. This
argument works in any cartesian monoidal category.

{docstring AclGeom.NormalConjugation.exists_groupIso_conjugation_lift}

For the actual algebraic group, choose a multiplicative point distinct from its inverse.
This is possible over the ACF base even in characteristic two. Its orbit under conjugation
can take only those two point values, by the automorphism classification. The fibers are
closed. Density of closed points covers the actual group by these two closed fibers, and
irreducibility forces one of them to be the whole group. The unit chooses the identity
fiber. The selected point distinguishes identity from inversion, so every point slice is
identity. Finally the integral product is reduced; point extensionality upgrades these
identities to the actual joint scheme-morphism identity.

This proves the normal-Gm torus alternative. It does not identify an arbitrary one-dimensional
normal subgroup with Gm or Ga or prove its required finite-isogeny classification. Non-affine
and rational curve actions, regularization, completion/points identification, the full
classifier, original group/chunk/six-point results, algebraization/descent and every true
bypassed auxiliary remain owed. All eight original work items of
[#21](https://github.com/adamtopaz/acl_geom/issues/21) stay open; the full durable goal remains
active and incomplete.
