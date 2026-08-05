/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Equivalence
import AclGeom.Geometry.FiniteRank

/-!
# A small geometry language for finite configurations

Incidence (`P ∈ cl(Q₁,…,Qₙ)`), collinearity, lines, the partial quadrangle
(blueprint Def partialquad) with its permutation lemma, and the generic
recursion theorem: formulas built from equality, point-below-join, finite
joins/meets, Boolean operations, and point quantifiers are invariant under any
geometry equivalence.

**Status:** skeleton (M0); contents arrive with M4 (checklist G1).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

end AclGeom
