/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeCurvePointPlaceModel

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Display complete stalk, inverse, automorphism and action clauses, including proof arguments.
set_option pp.deepTerms true
set_option pp.proofs true

#doc (Manual) "Closed points and places of an actual proper normal curve" =>
%%%
tag := "actual-curve-points-places"
%%%

For a given actual proper integral dimension-one curve over every field, with the actual
integral closedness of all stalks, ONE internally constructed equivalence identifies its
actual closed points with the existing valuation places of its actual generic-stalk field.
The generic point is excluded. The source point/place identification for that given model
now retains the literal canonical stalk embeddings, actual stalk ring isomorphisms, actual
proper centers and compatibility with actual curve automorphisms and regular actions at
base-field points. The one-variable class and Noetherianity are derived internally.
No point/place, center, local-ring comparison or transport certificate is supplied.

{docstring AclGeom.CurvePointsPlaces.exists_point_place_model}

A closed point determines exactly the image of its actual stalk in the actual function
field. The place ring is that subring, with its canonical field embedding retained.

{docstring AclGeom.CurvePointsPlaces.closedPointEquivPlace}

{docstring AclGeom.CurvePointsPlaces.mem_closedPointEquivPlace}

{docstring AclGeom.CurvePointsPlaces.closedPointStalkEquiv}

{docstring AclGeom.CurvePointsPlaces.coe_closedPointStalkEquiv}

Conversely, properness applies the valuative criterion to the spectrum of an actual place
ring, giving a unique morphism with the prescribed generic point. The image of its actual
closed point is the center. The stalk-to-place map commutes with the canonical field map;
the dimension-one valuation comparison identifies the subrings. The center is closed.

{docstring AclGeom.CurvePointsPlaces.existsUnique_placeModelMap}

{docstring AclGeom.CurvePointsPlaces.placeModelMap}

{docstring AclGeom.CurvePointsPlaces.placeModelMap_generic}

{docstring AclGeom.CurvePointsPlaces.placeCenter}

{docstring AclGeom.CurvePointsPlaces.placeModelMap_stalk_comp_subtype}

{docstring AclGeom.CurvePointsPlaces.stalkValuationSubring_placeCenter}

{docstring AclGeom.CurvePointsPlaces.placeCenter_isClosed}

The actual stalk ring equivalence and uniqueness of the proper valuation model prove the
other inverse identity. These constructions give one equivalence, rather than separately
chosen bijections for its different properties.

{docstring AclGeom.CurvePointsPlaces.placeCenter_closedPointPlace}

{docstring AclGeom.CurvePointsPlaces.closedPointEquivPlace_symm_val}

The topological and local algebra lemmas distinguish genuine closed points from the generic
point. The actual normal stalk valuation construction also covers the generic field stalk;
only its proper subrings give places. The constants are supplied by the actual structure map.

{docstring AclGeom.CurvePointsPlaces.isClosed_singleton_iff_isMin}

{docstring AclGeom.CurvePointsPlaces.isClosed_singleton_iff_ne_genericPoint}

{docstring AclGeom.CurvePointsPlaces.isField_stalk_iff_genericPoint}

{docstring AclGeom.CurvePointsPlaces.stalkValuationSubring}

{docstring AclGeom.CurvePointsPlaces.mem_stalkValuationSubring}

{docstring AclGeom.CurvePointsPlaces.stalkValuationSubring_krullDimLE}

{docstring AclGeom.CurvePointsPlaces.stalkValuationSubring_eq_top_iff}

{docstring AclGeom.CurvePointsPlaces.algebraMap_mem_stalkValuationSubring}

{docstring AclGeom.CurvePointsPlaces.closedPointPlace}

{docstring AclGeom.CurvePointsPlaces.mem_closedPointPlace}

For every actual curve automorphism, the actual closed-point image corresponds to comap by
its actual contravariant field automorphism. This follows from stalk-map naturality and
surjectivity of the actual stalk isomorphism. Applying the result to the automorphism of an
actual regular group action gives exactly the existing place action at every base-field point.

{docstring AclGeom.CurvePointsPlaces.functionFieldMap_stalkMap}

{docstring AclGeom.CurvePointsPlaces.mapClosedPoint}

{docstring AclGeom.CurvePointsPlaces.closedPointPlace_comap}

{docstring AclGeom.CurvePointsPlaces.closedPointEquivPlace_action}

This theorem takes the proper normal curve as an actual input. The later CurveCompletion
chapter now constructs that actual proper-normal model and the ORIGINAL-curve open embedding
for smooth separated integral ACF dimension-one curves, internally also for actual connected
curve groups. Projective presentation remains owed. For actual smooth integral dimension-one curves over an
ACF base, the following smooth-curve section now derives normality of every actual stalk
and DVRs at closed points internally.
The automorphism and action clauses concern base-field points; they do not construct a
jointly regular family of extended automorphisms or an action over all coefficient algebras.
The original rational/non-affine classifier, rational-action regularization, group/chunk/
six-point statements, algebraization/descent and every true bypassed auxiliary remain open.
All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and
the full durable goal remain active and incomplete. Original source statements and proofs
are unchanged.
