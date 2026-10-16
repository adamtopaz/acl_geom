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
under explicit completeness inputs. The literal projected arithmetic is refuted. Conditional
carrier/graph naturality is proved in `Interpretation.Naturality`
under explicit carrier inputs. The rank-five ACF input is supplied by `jCompletenessACF`;
these internal interfaces keep it explicit. `Main` supplies both inputs internally for the
public reconstruction theorem. Original literal construction obligations remain on #23.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

end AclGeom
