import AclGeom.Closure.ClosedLattice
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsPerfectClosure

/-!
# Perfected subfields and their membership API

The project-local `Perfection` bundle (chosen perfect closure with
`IsPerfectClosure`, uniform in the characteristic exponent) and the perfected
subfield `M^perf` of a closed intermediate field, with public membership
criterion `x ∈ M^perf ↔ ∃ n m, x ^ p ^ n = ι m`
(blueprint §type-correct statement and §Foundation III).

**Status:** skeleton (M0); contents arrive with M2 (checklist P1).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

end AclGeom
