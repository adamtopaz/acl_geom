import VersoManual
import Mathlib.Tactic.NormNum
import AclGeom

-- The manual genre, used for book-like documents with chapters, cross-references,
-- citations, and an index.
open Verso.Genre Manual
-- Support for Lean code samples that are elaborated in the same environment as the
-- document itself (`lean` code blocks, `{lean}`/`{name}` roles, `leanOutput`, …).
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Field Reconstruction from Algebraic-Dependence Geometry" =>

%%%
authors := ["Adam Topaz"]
%%%

This is a formalization, in Lean 4 and Mathlib, of the
Evans–Hrushovski–Gismatullin reconstruction theorem: recovering a field from
the combinatorial geometry of algebraic dependence over it.

The exposition is under construction; it will grow alongside the formalization
in the `AclGeom` library.

# About this document

This document is written in [Verso](https://github.com/leanprover/verso)'s
manual genre. Lean code shown here is elaborated against the very same library
that contains the formalization, so the statements displayed are guaranteed to
match the formal development.

```lean
example : 2 + 2 = 4 := by norm_num
```
