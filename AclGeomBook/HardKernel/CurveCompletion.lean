/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.CurveCompletion.ConnectedGroupCompletion

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Display the actual scheme hypotheses, canonical base algebras and extension diagrams.
set_option pp.deepTerms true
set_option pp.proofs true

#doc (Manual) "Actual proper-normal completion of the original curve" =>
%%%
tag := "actual-proper-normal-completion"
%%%

The proper-normal part of the completion step in source Lemma 8.4 now has an actual scheme
construction. Every actual smooth separated integral dimension-one curve over an algebraically
closed field embeds openly into an internally constructed proper normal integral curve of
dimension one. The embedding retains the ORIGINAL curve. No completion, open embedding,
function-field identification or extension certificate is supplied by the caller.

{docstring AclGeom.CurveCompletion.exists_proper_normal_completion}

For an actual one-dimensional connected algebraic group, Mathlib supplies smoothness
internally. Every actual automorphism of the ORIGINAL group scheme then extends uniquely
to the constructed curve. This includes each individual translation and group automorphism.
The equation is the literal commuting diagram over the original base field.

{docstring AclGeom.CurveCompletion.connectedGroup_completion_and_extensions}

The source asks for a nonsingular PROJECTIVE completion. The present construction is PROPER
NORMAL. A projective presentation and smoothness of the completed model are not asserted here.
Joint regularity of extended parameter families is also a separate obligation: individual
extensions alone do not supply an action morphism on the product with the completed curve.

The actual generic-stalk function field of the original curve supplies a separating parameter
internally. Over a perfect base, the genuine one-variable function-field class gives a
transcendental parameter with a finite separable extension over its generated rational field.

{docstring AclGeom.CurveCompletion.exists_separating_parameter}

The actual polynomial parameter subalgebra and its integral closure live inside that SAME
field. The integral closure is finite over the polynomial ring, Dedekind and finite type
over the original base, and has the SAME field of fractions.

{docstring AclGeom.CurveCompletion.normalizedRing_properties}

The parameter and its inverse generate the literal Laurent overlap. The integral closure of
that actual overlap is proved to be the principal localization of BOTH normalization charts.
The inverse chart is mapped into the SAME overlap, with its actual transported scalar tower.

{docstring AclGeom.CurveCompletion.normalizedOverlap_isLocalization}

{docstring AclGeom.CurveCompletion.inverseNormalizedOverlap_isLocalization}

These are actual open immersions between spectra. They construct an actual gluing atlas;
no gluing data or compatibility certificate is supplied. Compatible chart structure morphisms
descend to the original base field. The actual model is integral, quasi-compact and locally
of finite type.

{docstring AclGeom.CurveCompletion.atlas}

{docstring AclGeom.CurveCompletion.model_integral}

{docstring AclGeom.CurveCompletion.modelHom_quasiCompact}

{docstring AclGeom.CurveCompletion.modelHom_locallyOfFiniteType}

Every actual chart stalk is a localization of a Dedekind normalization ring. Its actual stalk
isomorphism with the glued model proves integral closedness and dimension at most one at
EVERY actual point. The specialization-order formula for stalk dimension gives the global
topological dimension bound.

{docstring AclGeom.CurveCompletion.model_stalk_properties}

{docstring AclGeom.CurveCompletion.model_dimension_le_one}

For the existence half of the valuative criterion, a generic field-valued point factors
through an actual chart. A valuation contains the parameter or its inverse. In the first
case the integral chart map lifts into the valuation ring. In the second case its nonzero
parameter gives an actual map through the normalized overlap, and the opposite chart
parameter evaluates to the literal reciprocal. Integrality then supplies the other chart
lift. Every structure and generic-fibre diagram is a scheme-morphism equality.

{docstring AclGeom.CurveCompletion.existsUnique_integral_lift}

{docstring AclGeom.CurveCompletion.exists_chart_scheme_lift}

{docstring AclGeom.CurveCompletion.modelHom_valuative_existence}

For uniqueness, two maps from the valuation spectrum factor through actual charts using
the image of its closed point. In the same chart, fraction-field injectivity proves equality.
In opposite charts, the genuine gluing pullback identifies their generic points in the
actual common overlap. The reciprocal parameters multiply to one already in the valuation
ring, forcing an actual overlap lift. Affine fraction-field cancellation then proves equality.

{docstring AclGeom.WeilGluing.commonOverlap_isPullback}

{docstring AclGeom.CurveCompletion.chart_model_maps_eq_of_fraction_field}

{docstring AclGeom.CurveCompletion.modelHom_valuative_uniqueness}

The two valuative halves and the proved finite-type properties give properness of the ACTUAL
model. Local Noetherianity supplies quasi-separatedness internally.

{docstring AclGeom.CurveCompletion.modelHom_isProper}

The actual affine normalization chart identifies the model's generic stalk with the ORIGINAL
function field over the SAME canonical base algebra. This is an internally proved field
identification, rather than a new hypothesis on the source curve.

{docstring AclGeom.CurveCompletion.exists_model_functionField_equiv}

The earlier proper-target extension theorem constructs the map from the original normal
curve. To prove that this actual map is an open immersion, one compares its actual stalks.
A birational morphism
to a valuation stalk is an isomorphism on that actual stalk: valuation-ring maximality and
fraction-field injectivity prove surjectivity and injectivity internally.

{docstring AclGeom.CurveCompletion.stalkMap_isIso_of_target_valuation}

The actual inverse stalk map spreads to a rational inverse around each actual image point.
Consequently the rational inverse is defined on the whole image of the original curve.
Separatedness supplies actual inverse morphisms onto that open subscheme, proving the open
immersion. No original-curve embedding is assumed. The dimension of the original curve then
forces the completed model to have dimension exactly one.

{docstring AclGeom.CurveCompletion.inverse_domain_contains_image}

{docstring AclGeom.CurveCompletion.isOpenImmersion_of_inverse_domain}

{docstring AclGeom.CurveCompletion.isOpenImmersion_of_target_valuation}

All these helpers are consumed by the actual smooth-curve and connected-group results at
the start of this chapter. The construction excludes superseded restricted-scalar and
preliminary lift prototypes. The three scoped heartbeat allowances pay for concrete
integral-closure scalar-dictionary reduction; all kernel checking remains enabled.

Projective presentation, jointly regular extended rational families, rational-action
regularization and the full original rational/non-affine classifier remain owed. Original
group/chunk/six-point statements, algebraization/descent and every true bypassed auxiliary
remain obligations. All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21)
work items and the full durable goal remain active and incomplete. Original source statements,
proofs and TESTs are unchanged.
