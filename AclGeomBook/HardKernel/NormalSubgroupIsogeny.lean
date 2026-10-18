/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeNormalTranslations

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "An arbitrary normal subgroup has a finite isogeny to translations" =>
%%%
tag := "actual-normal-subgroup-isogeny"
%%%

The genuine regular-affine action now treats an arbitrary connected normal CLOSED subgroup
N of dimension one. N is not assumed Ga or affine. The ambient group is connected, has
dimension at least two, and satisfies the global point-kernel criterion on an integral
affine locally finite-type dimension-one curve over an ACF base. Normality is the actual
joint scheme conjugation property, and the closed immersion is the subgroup inclusion.

One producer call chooses the SAME original generic-stalk generator t and globally finite
surjective affine-group morphism f. It internally constructs a finite surjective group
morphism beta from N to Ga, injective on base-field points. The actual factorization is
beta followed by translations equals i followed by f. A subgroup point of beta-coordinate
b sends t to t+b. No coordinate, ambient affine morphism, translation or finite-map
certificate is a premise. Every characteristic is included, allowing inseparability.

{docstring AclGeom.SchemeNormalTranslations.exists_normal_subgroup_translation_isogeny}

First, a finite map that is injective on base-field points has a surjective relative
diagonal: every closed point of its relative product gives two equal base-field points.
The diagonal is closed, and Jacobson density covers the product. This proves universal
injectivity. With surjectivity, the actual affine morphism is a homeomorphism on underlying
spaces. The image of the closed inclusion N therefore has its original dimension one.

{docstring AclGeom.GroupFinite.universallyInjective_of_point_injective}

{docstring AclGeom.GroupFinite.isHomeomorph_of_finite_surjective_point_injective}

Every nontrivial normal subgroup of the ordinary affine transformation group contains all
translations. A nonunit multiplier gives them by commutators; a nonzero translation gives
the others by scalar conjugation. If the actual subgroup image were trivial, point
extensionality and injectivity would make N a singleton, contradicting dimension one.

{docstring AclGeom.AffineTransformation.translations_mem_of_normal_ne_bot}

The translation inclusion is closed, with its existing shift retraction. Jacobson density
puts the entire translation curve in the actual closed subgroup image. A strictly larger
irreducible closed image would contain a length-two chain: a closed point, the translation
curve and the larger image. Dimension one excludes that chain. Thus the image is exactly
translations. This uses the genuine joint normality premise, not a supplied classification.

{docstring AclGeom.NormalTranslation.closed_irreducible_eq_univ_of_two_points}

{docstring AclGeom.NormalTranslation.translation_isClosedImmersion}

{docstring AclGeom.NormalTranslation.point_inclusion}

{docstring AclGeom.NormalTranslation.image_eq_translations}

Compose the actual normal-subgroup map with the shift retraction. Reduced-source
extensionality proves its translation factorization. Cancel through the monic inclusion
to prove the group laws. The finite ambient morphism gives finiteness at the separated
target; equality of images gives surjectivity. The original point injectivity is retained.

{docstring AclGeom.NormalTranslation.exists_finite_isogeny}

This is an actual finite surjective N to Ga morphism in the regular-affine case. It does
not assert that beta has degree one or that N is isomorphic to Ga. The old whole-curve
isomorphism theorem still requires a subgroup already presented as Ga; the new finite
isogeny alone does not remove that premise. Rational/non-affine regularization,
completion/points, the full original classifier, group/chunk/algebraization/descent and
every true bypassed auxiliary remain owed. All eight original
[#21](https://github.com/adamtopaz/acl_geom/issues/21) items and the full durable goal remain
active and incomplete.
