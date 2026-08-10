import VersoManual
import Mathlib.Tactic.NormNum
import AclGeom
import AclGeomBook.Foundations
import AclGeomBook.Perfection
import AclGeomBook.HardKernel
import AclGeomBook.Configurations
import AclGeomBook.Transfer
import AclGeomBook.Curves
import AclGeomBook.Interpretation

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
Evans–Hrushovski–Gismatullin reconstruction theorem: a relatively
algebraically closed field extension of transcendence degree at least five is
determined, up to perfection, by the combinatorial geometry of algebraic
dependence over it.

# The theorem
%%%
tag := "theorem"
%%%

Let $`k \subseteq K` be a field extension with $`k` relatively
algebraically closed in $`K`, and write $`\mathcal{G}(K/k)` for the
set of intermediate fields that are relatively algebraically closed in
$`K`, ordered by inclusion. This is a complete lattice — infima are
intersections, and suprema are relative algebraic closures of composita.

*Theorem (Evans–Hrushovski–Gismatullin, lattice form).*
Let $`K/k` and $`L/l` be relatively algebraically closed field
extensions with $`\operatorname{trdeg}(K/k) \ge 5`. Every order
isomorphism $`\phi : \mathcal{G}(K/k) \to \mathcal{G}(L/l)` is induced by
a field isomorphism $`\Phi : K^{\mathrm{perf}} \to L^{\mathrm{perf}}` of
perfections carrying $`k^{\mathrm{perf}}` onto $`l^{\mathrm{perf}}`,
in the sense that $`\phi(M) = \Phi(M^{\mathrm{perf}}) \cap L` for every
$`M`. Moreover $`\Phi` is unique up to composition with an integral
power of Frobenius — literally unique in characteristic zero — and conversely
every such $`\Phi` induces an order isomorphism of lattices.

Three qualifications, often omitted in informal statements, are part of the
theorem: the hypothesis $`\operatorname{trdeg} \ge 5`; the Frobenius
ambiguity in positive characteristic; and, consequently, that the geometry
functor on literal perfect-field isomorphisms is full but *not* faithful in
positive characteristic — the fully faithful statement requires quotienting
Hom-sets by integral Frobenius.

The formalization follows the self-contained blueprint in the project's
`sources/blueprint.tex`, which replaces the machinery of geometric stability
theory by direct proofs about irreducible loci, transcendence degree, finite
correspondences, and rational group chunks.

# Architecture of the formalization
%%%
tag := "architecture"
%%%

The development is organized in layers, mirroring the blueprint's dependency
architecture; no file in an earlier layer imports a later one, and the hard
kernel is independently buildable.

1. *Closure foundations* (`AclGeom.Closure.*`): the relative algebraic closure
   operator as a pregeometry, and the complete lattice of relatively
   algebraically closed intermediate fields.
2. *Point geometry* (`AclGeom.Geometry.*`): atoms, atomisticity, the
   equivalence between the lattice and point-geometry presentations, and
   finite rank.
3. *Perfection* (`AclGeom.Perfection.*`): perfected subfields and the
   invariance of the lattice under perfection.
4. *The hard kernel* (`AclGeom.Correspondence.*`): finite correspondences,
   the rational group chunk theorem, the additive and multiplicative
   correspondence theorems, and simultaneous Frobenius rigidity of the
   $`j`-configuration. This is the critical path.
5. *Configurations* (`AclGeom.Config.*`): the finite geometric predicates
   $`Q, Q', J` and their correctness against the semantic relations.
6. *Transfer* (`AclGeom.Transfer.*`): Gismatullin's one-quantifier transfer,
   descending correctness from algebraically closed to arbitrary perfect
   relatively algebraically closed extensions.
7. *Interpretation* (`AclGeom.Interpretation.*`): Frobenius classes of
   $`j`-tuples, generic arithmetic, and the interpreted ratio field.
8. *Reconstruction* (`AclGeom.Reconstruct.*`, `AclGeom.Functorial.*`,
   `AclGeom.Main`): base and point recovery, the Frobenius kernel, the main
   theorem, and its functorial fully faithful formulation.

As the formalization proceeds, each layer will receive a chapter of this book
presenting its main definitions and theorems, with all displayed Lean code
elaborated against the actual development.

{include 0 AclGeomBook.Foundations}

{include 0 AclGeomBook.Perfection}

{include 0 AclGeomBook.HardKernel}

{include 0 AclGeomBook.Configurations}

{include 0 AclGeomBook.Transfer}

{include 0 AclGeomBook.Curves}

{include 0 AclGeomBook.Interpretation}

# About this document
%%%
tag := "about"
%%%

This document is written in [Verso](https://github.com/leanprover/verso)'s
manual genre. Lean code shown here is elaborated against the very same library
that contains the formalization, so the statements displayed are guaranteed to
match the formal development.

```lean
example : 2 + 2 = 4 := by norm_num
```
