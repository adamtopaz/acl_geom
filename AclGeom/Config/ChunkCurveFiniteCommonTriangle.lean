/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveFiniteCommonTriangleE
import AclGeom.Config.ChunkCurveFiniteCommonTriangleA
import AclGeom.Config.ChunkCurveFiniteCommonTriangleB
import AclGeom.Config.ChunkCurveFiniteCommonTriangleC

/-!
# Strict semantic triangles on the finite semilinear source charts

This module collects the four strict composition triangles extended across
the finite semilinear `e/a/b/c` pullback sources.  The individual faces are
split into separate modules because their deeply dependent source-extension
types are expensive to serialize together.
-/
