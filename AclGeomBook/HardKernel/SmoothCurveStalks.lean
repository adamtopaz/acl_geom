/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SmoothCurveStalks

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Show actual scheme/stalk hypotheses, canonical algebras and the unique-extension diagram.
set_option pp.deepTerms true
set_option pp.proofs true

#doc (Manual) "Actual smooth curve stalks and proper extension" =>
%%%
tag := "actual-smooth-curve-stalks"
%%%

The local-normality assertion used before completion in source Lemma 8.4 now has an actual
scheme proof over an algebraically closed field. Every actual stalk of an actual smooth
integral dimension-one curve is integrally closed and a valuation ring. Every actual
closed-point stalk is a DVR. No normality, regular-local-ring, cotangent-rank or valuation
certificate is supplied. Smoothness provides local finite type and Noetherianity internally.

{docstring AclGeom.SmoothCurveStalks.stalk_integrallyClosed}

{docstring AclGeom.SmoothCurveStalks.stalk_valuationRing}

{docstring AclGeom.SmoothCurveStalks.stalk_isDiscreteValuationRing}

An actual one-dimensional connected algebraic group supplies its smoothness internally
through Mathlib's theorem for actual geometrically reduced group schemes. The group
consumer therefore asks for only the genuine group, the ACF base and its actual dimension.

{docstring AclGeom.SmoothCurveStalks.connectedGroup_stalks}

Every actual automorphism of a nonempty open in an actual proper smooth integral curve
extends uniquely to the entire curve. Normality of every actual stalk is derived internally
before applying the earlier proper-normal extension theorem. The displayed equation is the
literal open-immersion extension diagram in the category over the base field.

{docstring AclGeom.SmoothCurveStalks.properSmooth_existsUnique_iso_extension}

The argument uses the SAME actual generic-stalk function field and canonical base algebra
as the scheme/function-field bridge. The structure morphism gives an actual base algebra
on each actual stalk. It agrees with the global-section germ algebra and forms the actual
scalar tower with the function field. Actual scheme smoothness and local finite type give
the ring-theoretic smoothness and essential finite-type properties of that SAME algebra.

{docstring AclGeom.SmoothCurveStalks.stalkAlgebra}

{docstring AclGeom.SmoothCurveStalks.baseGerm_isIso}

{docstring AclGeom.SmoothCurveStalks.stalkAlgebra_eq_germ}

{docstring AclGeom.SmoothCurveStalks.stalk_formallySmooth}

{docstring AclGeom.SmoothCurveStalks.stalk_essFiniteType}

{docstring AclGeom.SmoothCurveStalks.stalk_functionField_isScalarTower}

The actual stalk structure map and residue-field map commute with the actual curve structure
morphism. The ACF closed-point residue is algebraic over this SAME stalk base algebra.
Algebraic closedness supplies an actual algebra section, giving an injective conormal map.

{docstring AclGeom.SmoothCurveStalks.SpecMap_stalkAlgebra}

{docstring AclGeom.SmoothCurveStalks.stalk_residue_isAlgebraic}

{docstring AclGeom.SmoothCurveStalks.kerCotangentToTensor_injective_of_section}

A separating transcendence basis of the actual one-variable fraction field gives a
one-dimensional differential space. Polynomial differentials, localization and the formally
etale comparison supply the basis. The existing one-variable class gives transcendence
degree one over arbitrary fields; the differential comparison uses perfectness.

{docstring AclGeom.SmoothCurveStalks.trdeg_eq_one_of_oneVar}

{docstring AclGeom.SmoothCurveStalks.finrank_differential_eq_one}

Formal smoothness makes the finite differential module projective, hence free over the
local ring. Base change compares its fraction-field and residue-field dimensions. The
conormal injection bounds the actual cotangent dimension by one. The maximal ideal is
principal, so the local domain is integrally closed. At the generic point the actual stalk
is a field; at every closed point it is a nonfield valuation ring and hence a DVR.

{docstring AclGeom.SmoothCurveStalks.finrank_cotangent_le_one}

{docstring AclGeom.SmoothCurveStalks.isIntegrallyClosed_of_smooth}

These actual scheme and group consumers are ACF dimension-one results. They do not assert
smooth-normality over arbitrary fields or in higher dimensions. The actual proper curve
is an input to this earlier individual-extension theorem. The later CurveCompletion chapter
now constructs the actual proper-normal model, ORIGINAL-curve open embedding and original-group
individual extensions internally. Projective presentation, jointly regular extensions of
rational families, rational-action regularization and the full original rational/non-affine
classifier remain owed. Original group/chunk/six-point statements,
algebraization/descent and every true bypassed auxiliary remain obligations. All eight
original [#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the full
durable goal remain active and incomplete. Original source statements and proofs are unchanged.
