/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Relative algebraic closure as a pregeometry

`racl k K S`: elements of `K` algebraic over `k(S)`, built from
`IntermediateField.adjoin` and `algebraicClosure` with restriction of scalars.
Public membership theorem, extensivity, monotonicity, idempotence, finite
character, exchange, equivariance, Frobenius invariance (blueprint Prop 4.1),
and the finite representative calculus (blueprint Lemma 4.2).

**Status:** skeleton (M0); contents arrive with M1 (checklist F1, F2).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

end AclGeom
