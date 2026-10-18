/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.NormalAdditiveSubgroup

/-! Focused normal-subgroup/action section, split from HardKernel for #18.
The existing mathematical exposition and explicit section tag are preserved. -/
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The regular character of a normal additive subgroup" =>
%%%
tag := "normal-additive-character"
%%%

The normal-Ga case of equation (8.4b) now has an actual scheme theorem. From an actual
normal additive-subgroup morphism into a connected algebraic group over an ACF base, choose
a regular group character to Gm and prove that conjugation is multiplication by this
character as a joint scheme diagram. Its only inputs are the actual group, actual group
morphism and genuine normality. Coefficient, regularity, global invertibility and group
laws are proved internally. Every characteristic is covered; no group-dimension premise
is needed for this auxiliary statement.

{docstring AclGeom.AdditiveRigidity.normal_additiveGroup_conj}

Classify actual Ga group-scheme automorphisms over a field first. Hopf-Spec full faithfulness
gives a coordinate-algebra automorphism. In polynomial coordinates, its composition with
its inverse has degree one, so each has degree one. Preservation of the actual Hopf counit
removes the constant, leaving a nonzero scalar.

{docstring AclGeom.AdditiveRigidity.polynomialAlgEquiv_fix_zero}

{docstring AclGeom.AdditiveRigidity.groupIso_eq_scale}

{docstring AclGeom.AdditiveRigidity.scale}

{docstring AclGeom.AdditiveRigidity.linePoint_comp_scale}

The regular conjugation lift restricts at each group point to an actual Ga automorphism.
Evaluate this family at one. Its coefficient is regular on the whole group and is nonzero
at every base-field point. Pulling back the actual line coordinate gives a global section.
Jacobson density makes its basic open the whole scheme, and the local unit criterion makes
the section a global unit. The Laurent-algebra map determined by that unit gives the actual
regular character morphism. No affineness of the parameter group is assumed.

{docstring AclGeom.AdditiveRigidity.exists_spec_pullback}

{docstring AclGeom.AdditiveRigidity.fromGlobal}

{docstring AclGeom.AdditiveRigidity.isUnit_section_of_point_values}

{docstring AclGeom.AdditiveRigidity.exists_multiplicative_lift}

Actual Gm point coordinates agree with the existing multiplicative point equivalence.
The actual scalar scheme map has its literal multiplication formula over every commutative
coefficient algebra in the base universe.

{docstring AclGeom.AdditiveRigidity.unitPoint}

{docstring AclGeom.AdditiveRigidity.multiplicativeValue}

{docstring AclGeom.AdditiveRigidity.unitPoint_comp_multiplicativeValue}

{docstring AclGeom.AdditiveRigidity.unitPoint_eq_points}

{docstring AclGeom.AdditiveRigidity.scalarMul}

{docstring AclGeom.AdditiveRigidity.unitPoint_linePoint_scalarMul}

Cancel through the monic normal inclusion to derive multiplication of the conjugation
slices. Evaluation at one gives multiplicativity of the scalar. Product integrality makes
the actual group products reduced; equality on base-field points then proves the actual
regular character's unit and multiplication laws and joint conjugation diagram.

{docstring AclGeom.AdditiveRigidity.over_hom_ext_of_points}

The automorphism classification is over fields. The group parameter in the regular-family
argument is reduced; no classification of Ga automorphisms over arbitrary nonreduced
coefficient rings is asserted. Arbitrary one-dimensional normal-subgroup/isogeny
classification, the dense-orbit curve coordinate, non-affine/rational actions, regularization,
completion/points, the full classifier, original group/chunk/six-point statements,
algebraization/descent and every true bypassed auxiliary remain owed. All eight original
[#21](https://github.com/adamtopaz/acl_geom/issues/21) items stay open; the full durable goal
remains active and incomplete.
