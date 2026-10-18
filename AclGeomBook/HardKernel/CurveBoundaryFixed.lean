/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Correspondence.ProperCurveBoundaryFixed

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true
-- Display the complete actual-open, orbit-morphism, point and all-test-scheme clauses.
set_option pp.deepTerms true
set_option pp.proofs true

#doc (Manual) "The literal curve boundary is fixed jointly" =>
%%%
tag := "actual-curve-boundary-fixed"
%%%

The finite-boundary assertion in the proof of source Lemma 8.4 now has an actual scheme
proof. A connected algebraic group acts regularly on an actual integral separated finite-type
curve of dimension one over an algebraically closed field. An actual equivariant nonempty
open immersion gives the preserved open. Its literal complement is finite and consists
of actual closed points. For each such point, a field-point is constructed internally and
its orbit is a constant SCHEME morphism. Thus fixedness holds on every test scheme in the
base universe, including every commutative coefficient algebra there.

{docstring AclGeom.CurveBoundary.fixed_boundary}

The curve need not be affine, proper or normal. Faithfulness and a lower bound on the
group dimension are unnecessary. Finite type, recorded by local finite type and
quasi-compactness, supplies Noetherianity internally. Equivariance is the actual commutative
scheme-action square. Neither finiteness of the boundary nor fixedness is a caller premise.
The theorem includes every actual point of the complement, not just supplied field-points.

{docstring AclGeom.CurveBoundary.finite_closed_boundary}

The generic point lies in every nonempty open of an integral curve. Every point of the
complement is therefore closed and has coheight one. The actual closed complement is sober
and Noetherian. Mathlib's finite coheight-one theorem proves literal complement finiteness.
The purely finite-boundary theorem works over every field and needs no separatedness.

{docstring AclGeom.CurveBoundary.finite_closed_complement}

An actual equivariant map commutes with the actual automorphisms supplied by group points.
Using the inverse automorphism proves that the complement of its image is preserved.

{docstring AclGeom.CurveBoundary.pointAct_naturality}

{docstring AclGeom.CurveBoundary.pointAct_mem_complement}

The actual orbit morphism agrees with the point action after every base-field specialization.
Closed points of the group are dense. Their images lie in the closed finite boundary, so
the entire orbit morphism has image there. Connectedness of the algebraic group supplies
irreducibility here. A continuous map from an irreducible space into finitely many closed
points is constant; Mathlib's discrete-subset theorem handles the finite target.

{docstring AclGeom.CurveBoundary.orbitMap}

{docstring AclGeom.CurveBoundary.orbitMap_point}

{docstring AclGeom.CurveBoundary.constant_of_finite_closed_range}

Reduced-source closed-point detection upgrades this topological constancy to equality of
actual scheme morphisms. Evaluation at the group identity gives the SAME original boundary
point. Composing this actual identity with arbitrary test-scheme points proves fixedness
over all coefficient algebras in the base universe, in every characteristic.

{docstring AclGeom.CurveBoundary.orbitMap_eq_constant}

For a GIVEN proper normal integral curve, the existing actual point/place equivalence now
also identifies each place whose actual center is outside the open with a fixed actual
boundary point. The SAME place is fixed by the existing action of base-field group points.
Properness supplies the finite-type and separatedness hypotheses internally. Normality is
explicit integral closedness of the actual stalks. No affine open hypothesis is imposed.
The joint scheme fixedness concerns the boundary points; the place-action formula uses
base-field group points, as in the existing place API.

{docstring AclGeom.CurveBoundary.fixed_boundary_places}

The regular action on the ambient curve and the equivariant open are actual inputs.
Construction of a proper normal completion and joint regularity of extended rational
families remain owed. The smoothness-to-local-normality scheme API, the original rational/
non-affine classifier and regularization, group/chunk/six-point statements,
algebraization/descent and every true bypassed auxiliary remain open. All eight original
[#21](https://github.com/adamtopaz/acl_geom/issues/21) work items and the full durable goal
remain active and incomplete. Original source statements and proofs are unchanged.
