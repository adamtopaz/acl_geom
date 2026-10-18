/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeAffineWholeCurve

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The whole original affine curve in the actual action" =>
%%%
tag := "actual-whole-affine-curve"
%%%

The genuine connected regular action on an integral affine locally finite-type curve of
dimension one over an ACF base now gives a coordinate on the entire original curve.
Assume group dimension at least two, the global point-kernel criterion and an actual monic
Ga subgroup. One call to the existing producer chooses the same original generic-stalk
generator t and global group morphism f, injective on base-field points. The SAME t is the
generic value of an actual isomorphism V with Ga. The SAME f satisfies the global joint
scheme action diagram. On every commutative coefficient algebra in the base universe,
the literal coordinate formula is ax+b. Every characteristic is included, allowing
inseparability. No normality, chart, point, transitivity, regularity or isomorphism
certificate is supplied by the caller.

{docstring AclGeom.CurveGlobalCoordinate.exists_whole_curve_coordinate}

The actual finite surjective Ga orbit map is constructed internally. A surjective map of
locally finite-type schemes over an ACF base is surjective on base-field points: choose a
closed point in each nonempty closed fibre and use its residue-field point. The actual
orbit therefore supplies point transitivity of the original regular action. Translates
of the old pointed coordinate chart cover the entire curve by the Jacobson property.

{docstring AclGeom.CurveGlobalCoordinate.surjective_points_of_surjective}

{docstring AclGeom.CurveGlobalCoordinate.transitive_points_of_surjective_orbit}

{docstring AclGeom.CurveGlobalCoordinate.translatedCover}

The existing affine pullback formula for the SAME generic coordinate proves point
compatibility on translated charts. Reduced-source point extensionality turns this into
actual equality on their pullbacks. Mathlib gluing extends the old regular coordinate,
with its literal original generic value. General categorical point-action identities
prove equivariance. Product integrality then gives the joint scheme diagram everywhere.

{docstring AclGeom.CurveGlobalCoordinate.coordinate_points_eq}

{docstring AclGeom.CurveGlobalCoordinate.translated_coordinate_points_compatibility}

{docstring AclGeom.CurveGlobalCoordinate.pullback_eq_of_point_compatibility}

{docstring AclGeom.CurveGlobalCoordinate.point_comp_pointAct}

{docstring AclGeom.CurveGlobalCoordinate.point_equivariance_of_chart}

{docstring AclGeom.CurveGlobalCoordinate.exists_global_coordinate}

{docstring AclGeom.CurveGlobalCoordinate.joint_diagram_of_point_equivariance}

The global coordinate is an actual isomorphism. Ordinary Spec full faithfulness recovers
its coordinate algebra map and that of the actual surjective Ga orbit. A prime above
bottom makes the latter injective. The composite polynomial map is nonconstant, hence
finite. Integral elements in the original generated fraction field lie in its integrally
closed polynomial ring. Thus the coordinate algebra is exactly `k[t]`. This criterion
works over any field, with no normality, dimension or finiteness premise for the supplied
surjective line cover. The genuine action supplies the global coordinate and cover internally.

{docstring AclGeom.CurveGlobalCoordinate.fractionRing_of_generator}

{docstring AclGeom.CurveGlobalCoordinate.bijective_of_polynomial_cover}

{docstring AclGeom.CurveGlobalCoordinate.isIso_of_surjective_line_cover}

This completes the whole-curve coordinate and its actual action diagram for a subgroup
already presented as Ga in the regular-affine setting. Arbitrary one-dimensional normal-
subgroup/isogeny classification, remaining source parameter covers, rational/non-affine
actions, regularization, completion/points, the full classifier, original group/chunk/
six-point statements, algebraization/descent and all true bypassed auxiliaries remain owed.
All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the
full durable goal remain active and incomplete.
