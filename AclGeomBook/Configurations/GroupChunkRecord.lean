/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeomBook.Configurations.CorrespondenceFields
import AclGeomBook.Configurations.ParameterTransport
import AclGeomBook.Configurations.CommonSourceCovers
import AclGeomBook.Configurations.ReferenceBranches
import AclGeomBook.Configurations.SemilinearCommonFields
import AclGeomBook.Configurations.AlgebraizationPrerequisites

/-!
Focused section of the configuration book (#18). This preserves the frozen
M4a declaration record; the group/action and extraction conclusions remain
open as described by its parent section and issues #12/#19/#21/#22.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Selected correspondence composition and the group-chunk core" =>
%%%
tag := "group-chunk-core"
%%%

The following library records selected correspondence and field-transport
constructions.  The 2026-10-06 audit (issue #19) found that these do not yet
construct the algebraic group of blueprint Theorem 8.2 or prove affine-grid
extraction.  The historical group-chunk route is frozen while its target and
construction are re-planned (issues #12, #18, #22).  In particular, identities
obtained by defining a discrepancy between two lifts do not establish an
intrinsic parameter multiplication.


{include 0 AclGeomBook.Configurations.CorrespondenceFields}

{include 0 AclGeomBook.Configurations.ParameterTransport}

{include 0 AclGeomBook.Configurations.CommonSourceCovers}

{include 0 AclGeomBook.Configurations.ReferenceBranches}

{include 0 AclGeomBook.Configurations.SemilinearCommonFields}

{include 0 AclGeomBook.Configurations.AlgebraizationPrerequisites}
