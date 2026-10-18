/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.RegularAffineModel

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Retain the final coefficient-algebra clauses of the coupled existential theorem.
set_option pp.deepTerms true

#doc (Manual) "One coupled regular-affine curve and normal-subgroup model" =>
%%%
tag := "coupled-regular-affine-model"
%%%

The genuine regular-affine action now has one coupled model for the regular-affine case
of (8.4a,b). The ambient group is connected, has dimension at least two, and satisfies the
global point-kernel criterion on an integral affine locally finite-type dimension-one
curve over an ACF base. The actual connected normal CLOSED subgroup N has dimension one;
N is not assumed Ga or affine. Its inclusion has Mathlib's genuine joint normality.

ONE curve-cover producer call chooses the SAME original generic-stalk generator t and
regular group morphism f to the affine group. The same f is globally finite, surjective
and point-injective. The same t restricts to an actual isomorphism of nonempty curve and
line opens, with its generic value and joint action diagram. The chosen normal coordinate
beta:N to Ga is finite, surjective and point-injective and factors i followed by f through
the translation inclusion. No coordinate, finite map, chart or diagram is a caller premise.

{docstring AclGeom.RegularAffineModel.exists_model}

The multiplier projection of the standard affine group is a regular group morphism to Gm.
Its scaling section proves surjectivity. Its unit-coordinate formula is literal over every
commutative coefficient algebra in the base universe. The actual character chi is f
followed by this projection; its surjectivity follows from that of f.

{docstring AclGeom.AffineDilation.projection}

{docstring AclGeom.AffineDilation.groupPoint_comp_projection}

{docstring AclGeom.AffineDilation.scalingSection}

{docstring AclGeom.AffineDilation.scalingSection_comp_projection}

{docstring AclGeom.AdditiveRigidity.unitPoint_one}

{docstring AclGeom.AdditiveRigidity.unitPoint_mul}

{docstring AclGeom.AffineDilation.projection_isMonHom}

{docstring AclGeom.AffineDilation.projection_surjective}

{docstring AclGeom.AffineDilation.character}

{docstring AclGeom.AffineDilation.point_comp_projection}

The standard affine group conjugates translations by its multiplier as an actual joint
scheme identity. Reduced-source point extensionality promotes the ordinary conjugation
formula. The abstract commuting group-factorization identity transports the actual normal
conjugation lift through f and beta. Cancellation uses only the translation inclusion,
which is monic. Beta is never inverted or cancelled as a monomorphism.

{docstring AclGeom.AffineDilation.standard_conjugation}

{docstring AclGeom.NormalCoordinateConjugation.factor_conjugation}

{docstring AclGeom.NormalCoordinateConjugation.exists_character}

The coupled theorem retains the literal formulas over every coefficient algebra:
affine multiplication is (c,d)(a,b)=(ca,cb+d), the action in the chosen open coordinate is
x to ax+b, and the beta-coordinate of conjugation by an element of chi-coordinate a is
a times the beta-coordinate. The normal conjugation map itself is the actual lift chosen
from normality; this does not construct a scalar action on N by inverting beta.

This proves a coupled finite-coordinate model in the regular-affine case. No degree-one,
separability or N-isomorphic-to-Ga conclusion is asserted. The curve coordinate is an
isomorphism of opens; the old whole-curve theorem still requires a subgroup already
presented as Ga. Rational/non-affine regularization, completion/points, the full original
classifier, group/chunk/algebraization/descent and every true bypassed auxiliary remain
owed. All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items
and the full durable goal remain active and incomplete.
