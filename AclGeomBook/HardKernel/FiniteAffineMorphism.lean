/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeAffineFinite

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The globally finite affine morphism for the same curve" =>
%%%
tag := "actual-global-finite-affine-morphism"
%%%

For the genuine connected regular-affine action above, the actual group morphism to the
standard affine group is now globally finite and surjective. Group dimension at least two
and the global point-kernel criterion are the genuine action hypotheses. This result needs
no Ga subgroup. The original generic-stalk generator, faithful point homomorphism and
literal affine field formula are chosen internally and retained.

{docstring AclGeom.SchemeAffineFinite.exists_finite_surjective_morphism}

With an actual monic Ga subgroup, the SAME chosen generator and globally finite surjective
morphism give the isomorphism of the entire original curve with Ga and its global joint
action diagram. The literal ax+b formula holds over every commutative coefficient algebra
in the base universe. One call to the parameter-cover producer supplies all data. No
coordinate, chart, finite map, transitivity, regularity or isomorphism is a caller premise.
Every characteristic is included, allowing inseparability.

{docstring AclGeom.SchemeAffineFinite.exists_finite_morphism_whole_curve}

The previous whole-curve proof is now a criterion for given affine action data, used by both
public existence theorems. Its original public existence signature is unchanged.

{docstring AclGeom.CurveGlobalCoordinate.whole_curve_coordinate_of_affine_data}

Here is the group argument. Nonempty parameter opens and their translates intersect because
the target is integral. A closed point in the intersection lifts to base-field points of
both opens and then through the finite parameter map. Taking their quotient proves
surjectivity of the group point map. Connectedness of the target is essential here.

{docstring AclGeom.GroupFinite.exists_point_of_nonempty}

{docstring AclGeom.GroupFinite.exists_point_lift}

{docstring AclGeom.GroupFinite.translated_open}

{docstring AclGeom.GroupFinite.surjective_points}

Point injectivity identifies the FULL inverse image of the target open with the given
source open. A nonempty difference would be locally closed and contain a closed point,
contradicting that injectivity. The resulting open-immersion isomorphism identifies the
finite parameter map with the actual target pullback. Translate this square by group
points. Those target opens cover, and finiteness and surjectivity are local at the target.

{docstring AclGeom.GroupFinite.preimage_open_eq}

{docstring AclGeom.GroupFinite.finite_surjective_pullback}

{docstring AclGeom.GroupFinite.leftMul_hom}

{docstring AclGeom.GroupFinite.finite_surjective}

No degree-one, separability or scheme-monomorphism conclusion is asserted. Arbitrary
one-dimensional normal-subgroup/isogeny classification, construction outside the
regular-affine case, rational/non-affine regularization, completion/points, the full original
classifier, group/chunk/algebraization/descent and all true bypassed auxiliaries remain owed.
All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the
full durable goal remain active and incomplete.
