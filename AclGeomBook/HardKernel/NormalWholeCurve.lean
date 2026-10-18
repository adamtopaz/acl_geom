/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeNormalWholeCurve

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Retain every coefficient-algebra clause of the coupled existential theorem.
set_option pp.deepTerms true

#doc (Manual) "The whole curve from the actual normal subgroup's finite Ga cover" =>
%%%
tag := "whole-curve-from-normal-cover"
%%%

The genuine connected regular-affine action now gives an isomorphism of the ENTIRE
original curve with Ga, without assuming the original connected normal CLOSED subgroup
N is Ga or affine. The actual subgroup has dimension one; the curve is integral, affine,
locally finite type and dimension one over an ACF base. Group dimension at least two and
the global point-kernel criterion remain the genuine action hypotheses.

ONE existing coupled-model call chooses the SAME original generic-stalk generator t,
globally finite surjective point-injective affine morphism f, regular surjective multiplier
character chi, finite point-injective beta:N to Ga and actual normal conjugation lift.
The new theorem retains all of these data. Its global coordinate on the entire original
curve has generic value exactly t, and the global joint action uses the SAME f. Literal
affine multiplication, global ax+b, finite-coordinate conjugation and the new cover formula
hold over every commutative coefficient algebra in the base universe.

{docstring AclGeom.RegularAffineModel.exists_whole_curve_model}

The missing Ga parameter is constructed internally as a finite surjective GROUP morphism
alpha:Ga to N. Alpha followed by beta is relative Frobenius, T to T^(p^n), fixing the base
coefficients. Here p is the exponential characteristic; p=1 includes characteristic zero.
This is a finite cover, never a beta inverse. Neither alpha nor beta is assumed to be a
scheme monomorphism, and no N-isomorphic-to-Ga or degree-one assertion is made.

{docstring AclGeom.FiniteGaCover.exists_group_cover}

First, universal injectivity of an actual affine scheme map makes its fraction-field
extension purely inseparable. Two embeddings into an algebraic closure agree after
restriction to the coordinate algebra, by the universal field-point criterion. Fraction-
ring extensionality makes the embeddings equal. This avoids any unproved residue-field
comparison or degree-one argument.

{docstring AclGeom.FiniteGaCover.isPurelyInseparable_of_universallyInjective}

The finite extension has a common purely inseparable exponent. Raising coordinate-algebra
elements to that power puts them in the base fraction field. They are integral over the polynomial ring over k;
its integral closedness puts the powers in that ring itself. The resulting ring map acts
on base coefficients by Frobenius; applying inverse Frobenius to the coefficients makes
it a k-algebra map. Its composite with the original polynomial inclusion is T to T^(p^n).
Only that polynomial ring is required to be integrally closed; the original curve is not
assumed normal.

{docstring AclGeom.FiniteGaCover.exists_polynomial_frobenius_factor}

Transport through the actual affine spectrum presentation gives the scheme cover.
Its composite sends zero to zero and one to one, so the cover is nonconstant. The existing
line-to-curve criterion proves actual finiteness and surjectivity. No cover or polynomial
certificate is supplied by the caller.

{docstring AclGeom.FiniteGaCover.exists_line_cover}

Relative Frobenius is a genuine additive-group morphism, checked on universal points over
every coefficient algebra, including the zero ring. To prove alpha's group laws, compose
with beta and compare base-field points. Beta is injective on those points. Reduced-source
scheme extensionality on Ga and Ga times Ga then gives the actual unit and multiplication
diagrams. There is no categorical cancellation of beta as a monomorphism.

{docstring AclGeom.FiniteGaCover.relativeFrobenius}

{docstring AclGeom.FiniteGaCover.linePoint_comp_relativeFrobenius}

{docstring AclGeom.FiniteGaCover.relativeFrobenius_isMonHom}

The coordinate-one point of alpha has nontrivial image in the ambient group: its beta
coordinate is one, whereas the identity has coordinate zero. The actual Ga orbit criterion
needs only this nontrivial point. It gives a finite surjective orbit, hence transitivity.
Translated charts glue the SAME original rational generator over the whole curve; its
surjective line cover then proves the resulting global coordinate is an isomorphism.
The old two monic-Ga public statements retain their exact signatures as wrappers of the
weaker criteria.

{docstring AclGeom.AdditiveOrbit.exists_finite_orbit_cover_of_nontrivial_one}

{docstring AclGeom.CurveGlobalCoordinate.whole_curve_coordinate_of_affine_data_of_nontrivial_ga}

This removes the Ga-presentation premise in the new actual regular-affine source consumer.
It does not identify N with Ga or assert separability of the covers. The arbitrary rational
and non-affine classifier, regularization, completion/points, original group/chunk/six-point
results, algebraization/descent and every true bypassed auxiliary remain owed. All eight
original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the full durable
goal remain active and incomplete.
