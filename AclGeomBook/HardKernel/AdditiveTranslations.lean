/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.SchemeAffineTranslations

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Actual additive subgroups in the regular-affine action" =>
%%%
tag := "actual-additive-translations"
%%%

The translation-identification step in the proof of Lemma 8.4 now has an actual consumer.
Start with the genuine connected regular action on an integral affine locally finite-type
curve of dimension one over an ACF base, the global point-kernel criterion, group dimension
at least two and an actual monic Ga group morphism into G. Internally choose the same
original generic-stalk generator t, faithful affine point map Phi and global group morphism
f from one call to the existing regular-affine producer. An actual finite surjective Ga
group map beta factors that subgroup through the standard translation inclusion. Its
base-field point map is injective. Inseparability is allowed.

One internally chosen nonconstant polynomial p with zero constant describes beta on every
commutative coefficient algebra in the base universe. It is additive on all of them. The
literal subgroup pullback on the actual generic-stalk field is t to t+p(b), with the same
t and f. No translation, polynomial, factorization, nontriviality or finiteness certificate
is a caller premise. Normality is not needed for this auxiliary statement.

{docstring AclGeom.SchemeAffineTranslations.exists_subgroup_translation_coordinate}

First construct the actual translation inclusion and its regular shift retraction. Their
composition is identity, so the inclusion is monic. Its group laws are checked on arbitrary
coefficient-algebra points of actual affine tensor spectra. This works over every field.

{docstring AclGeom.AdditiveTranslation.inclusion}

{docstring AclGeom.AdditiveTranslation.shift}

{docstring AclGeom.AdditiveTranslation.inclusion_comp_shift}

{docstring AclGeom.AdditiveTranslation.inclusion_mono}

{docstring AclGeom.AdditiveTranslation.inclusion_isMonHom}

{docstring AclGeom.AdditiveTranslation.groupInclusion}

{docstring AclGeom.AdditiveTranslation.linePoint_comp_inclusion}

{docstring AclGeom.AdditiveTranslation.linePoint_mul}

{docstring AclGeom.AdditiveTranslation.linePoint_zero}

Every actual Ga group morphism into the affine group has an invertible polynomial for
its multiplier. A polynomial unit over a field is constant, and preservation of the actual
group unit makes that constant one. Thus the morphism factors through translations.
Cancel through the monic inclusion to prove the factor's actual group laws. This theorem
also works over every field.

{docstring AclGeom.AdditiveTranslation.linePoint_comp_groupPoint}

{docstring AclGeom.AdditiveTranslation.exists_group_factor}

The actual symmetric-algebra line coordinates agree with ordinary polynomial coordinates.
Their evaluation and spectrum-map identities preserve the actual point maps.

{docstring AclGeom.AdditiveTranslation.polynomialCoordinates}

{docstring AclGeom.AdditiveTranslation.polynomialCoordinates_coordinate}

{docstring AclGeom.AdditiveTranslation.lineEval_polynomialCoordinates}

{docstring AclGeom.AdditiveTranslation.linePoint_comp_linePoint}

{docstring AclGeom.AdditiveTranslation.lineEval_ringHom_eq}

For a nonconstant polynomial, the variable is integral over the range of evaluation:
its leading coefficient is a unit, so an integral polynomial relation gives integrality
of the variable itself. Finite generation gives an actual finite ring map. Nonconstant
substitution is injective, and integral lying-over makes the actual scheme map surjective.
These proofs work over every field, in every characteristic.

{docstring AclGeom.AdditiveTranslation.polynomial_aeval_finite}

{docstring AclGeom.AdditiveTranslation.isFinite_linePoint}

{docstring AclGeom.AdditiveTranslation.surjective_linePoint}

An actual Ga endomorphism nontrivial at a base-field point therefore supplies its finite
surjective coordinate internally. Its group law gives polynomial additivity over every
coefficient algebra. In the actual action consumer, faithfulness and the monic subgroup
provide that nontrivial point internally. The factor and the original affine coordinate
then give the actual subgroup translation formula on the original generic-stalk field.

{docstring AclGeom.AdditiveTranslation.exists_finite_coordinate}

This identifies an actual subgroup already presented as Ga in the regular-affine setting.
Arbitrary one-dimensional normal-subgroup/isogeny classification, the dense-orbit coordinate
construction, non-affine/rational actions, regularization, completion/points, the full
classifier, original group/chunk/six-point statements, algebraization/descent and every
true bypassed auxiliary remain owed. All eight original
[#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the full durable goal
remain active and incomplete.
