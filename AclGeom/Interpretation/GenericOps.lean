/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobClass

/-!
# Generic arithmetic on a fixed Frobenius class

`JAdd`, `JMul`, `JNeg`, and the totalized nonzero addition `JAddTotalNZ`, with
their semantic correctness on independent representatives
(blueprint Lemmas generic-arithmetic, total-nonzero-add).

**Status:** historical skeleton, superseded by the corrected implementation (#23).
`JArith`, `JArithSem` and `ClassArithmetic` implement coupled generic/fixed-class arithmetic;
`TotalOps` and `Field` give corrected totalization and the named transported field structure
under explicit completeness inputs. The literal projected arithmetic is refuted; unconditional
completeness, naturality and full reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

end AclGeom
