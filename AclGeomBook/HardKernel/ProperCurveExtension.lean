/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.ProperCurveFunctionField
import AclGeom.Correspondence.ProperCurveOpenExtension

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Display the complete normality, uniqueness and generic-point clauses.
set_option pp.deepTerms true

#doc (Manual) "Unique extension on proper normal curves" =>
%%%
tag := "proper-normal-curve-extension"
%%%

Two individual extension assertions in the proof of source Lemma 8.4 are now proved:
an automorphism of an actual nonempty open extends uniquely to the whole proper normal
curve, and a birational morphism between proper normal curves is an isomorphism.
These theorems work over every field and allow dimension at most one. Normality is the
actual integral closedness of every stalk. Properness over the field supplies local
Noetherianity internally in the two source consumers.

{docstring AclGeom.ProperCurve.existsUnique_iso_extension}

The given open immersion and automorphism are genuine maps of schemes over the field.
The output is an actual global automorphism and its literal commuting square. Both inverse
identities follow by restricting to the dense open. No global extension, inverse, field
isomorphism or regularity certificate is supplied by the caller.

{docstring AclGeom.ProperCurve.existsUnique_morphism_extension_from_open}

The underlying extension theorem takes an actual rational map from an integral locally
Noetherian normal curve to a proper target over a separated base. Every point is in its
domain of definition. The local algebra first bounds the stalk dimension by the actual
scheme dimension. Normality and Noetherianity make each stalk a local Dedekind domain,
hence a valuation ring. The generic field stalk is included.

{docstring AclGeom.ProperCurve.stalk_valuationRing}

Mathlib's valuative criterion extends the generic-point map over each stalk. Its existing
spreading-out theorem then gives an actual map on a neighborhood of that point. These maps
fill the domain of the rational map. Separatedness glues the result and gives uniqueness.
No projective embedding, homogeneous coordinate choice or discrete-valuation certificate
is a premise.

{docstring AclGeom.ProperCurve.domain_eq_top}

{docstring AclGeom.ProperCurve.existsUnique_extension}

{docstring AclGeom.ProperCurve.hom_eq_of_toRationalMap_eq}

For two actual proper normal curves, a k-algebra isomorphism of their actual generic-stalk
fields produces inverse rational maps. The extension theorem makes them global; agreement
on generic points proves both inverse identities. The induced curve isomorphism has the
prescribed contravariant generic-point formula and is unique.

{docstring AclGeom.ProperCurve.existsUnique_iso_of_functionFieldEquiv}

For an actual dominant morphism, its actual field map supplies that isomorphism internally.
Generic-point uniqueness identifies the resulting global isomorphism with the original
morphism. This proves the birational-map assertion used in the source genus-zero proof;
finiteness need not be an extra hypothesis.

{docstring AclGeom.ProperCurve.isIso_of_isIso_functionFieldMap}

These are individual map and automorphism extension theorems. A jointly regular family
of extended automorphisms requires a separate proof. Construction of a proper normal
completion remains owed. Over an ACF base, the following smooth-curve section derives
normality of every actual stalk and individual extension for proper smooth curves internally.
For a given
actual proper normal dimension-one curve, the closed-point/place correspondence, literal
stalk embeddings and automorphism compatibility are now proved in the following section. The original rational/non-affine classifier, regularization,
group/chunk/six-point statements, algebraization/descent and every true bypassed auxiliary
remain open. All eight original [#21](https://github.com/adamtopaz/acl_geom/issues/21)
work items and the full durable goal remain active and incomplete.
