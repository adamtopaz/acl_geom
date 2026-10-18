/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeAdditiveOrbit

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The actual finite additive orbit cover" =>
%%%
tag := "actual-additive-orbit-cover"
%%%

The orbit-cover step in the proof of Lemma 8.4 now has an actual regular-affine consumer.
Let an arbitrary algebraic group over an ACF base act regularly on an integral affine
locally finite-type curve of dimension one. The genuine global point-kernel criterion and
an actual monic Ga inclusion internally supply a moved base-field point. Its actual orbit
map from Ga to the original curve is finite and surjective, sends zero to the chosen point,
and satisfies the joint translation-action scheme diagram. On every commutative coefficient
algebra in the base universe, acting by the subgroup parameter b on the orbit point c gives
the orbit point b+c. This includes every characteristic, and allows inseparability.

No orbit, point, nonconstancy, dominance or finite-cover certificate is a caller premise.
Normality, connectedness and an ambient group-dimension bound are not needed for this
auxiliary result.

{docstring AclGeom.AdditiveOrbit.exists_finite_orbit_cover}

The point with Ga coordinate one is nonidentity. The monic inclusion and global kernel
criterion make its action nonidentity. Reduced finite-type point extensionality over the
ACF base then supplies a moved point internally. Its actual orbit separates zero and one.
The general categorical orbit identities give its origin and the joint scheme diagram.

{docstring AclGeom.AdditiveOrbit.orbitMap}

{docstring AclGeom.AdditiveOrbit.point_comp_orbitMap}

{docstring AclGeom.AdditiveOrbit.mul_comp_orbitMap}

The finite-surjective criterion works over any field. Recover the actual affine algebra
map using Spec full faithfulness and its genuine over-base equation. Separation of zero
and one forces a nonconstant polynomial image. Evaluation at that polynomial is finite,
so the actual algebra map is finite. In a dimension-one domain a nonzero prime kernel
would be maximal; integrality would then make the polynomial ring a field. Thus the map
is injective. Integral lying-over and the actual affine-spectrum isomorphism prove scheme
surjectivity onto the entire original curve.

{docstring AclGeom.AdditiveOrbit.exists_algHom_of_spec_hom}

{docstring AclGeom.AdditiveOrbit.finite_of_nonconstant_polynomial_image}

{docstring AclGeom.AdditiveOrbit.injective_finite_to_polynomial}

{docstring AclGeom.AdditiveOrbit.finite_surjective_of_separates_zero_one}

This covers a subgroup already presented as Ga in a regular-affine action. Arbitrary
one-dimensional normal-subgroup/isogeny classification, the orbit construction beyond this
case, rational/non-affine actions, regularization, completion/points, the full classifier,
original group/chunk/six-point statements, algebraization/descent and all true bypassed
auxiliaries remain owed. All eight original
[#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the full durable goal
remain active and incomplete.
