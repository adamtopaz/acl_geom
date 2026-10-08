/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Config.AffineGridNormalization
import AclGeom.Geometry.FreshSequences
import Mathlib.Data.Set.Finite.Basic

/-!
# Affine-grid coordinates over an ambient field of infinite transcendence degree

When `K` has infinite transcendence degree over `k`, the two supplied families of fresh inputs of
`QWitness.Psi.hasAffineGridCoordinates_of_chart_supplied_inputs` can be constructed in `K` by
`exists_fresh_sequence_of_aleph0_le_trdeg`, which now lives in `AclGeom.Geometry.FreshSequences`.

* `QWitness.Psi.hasAffineGridCoordinates_of_chart_of_aleph0_le_trdeg`: a `Ψ`-witness with
  `I ≠ D`, over algebraically closed `k ⊆ K` with `ℵ₀ ≤ trdeg_k K`, has affine-grid coordinates
  once an explicit independent initial chart for `A, B, C, S, T, U, X, Y, Z` is given.  Both
  input families are constructed by the fresh-sequence theorem, each after the corresponding
  original prime curve is fixed.

**Status:** fresh inputs constructed for an ambient field of infinite transcendence degree
(#27, P5). The actual PRIVATE consumer derives the grid before applying Q semantics.
The theorem is subsumed by `QWitness.Psi.hasAffineGridCoordinates_of_chart` (#27, P6), which
assumes neither the bound on the transcendence degree nor algebraic closedness of `K`.  There,
`Ψ`, the guard `I ≠ D`, the independent initial chart with its nine equalities and algebraic
closedness of `k` remain explicit hypotheses.  The initial chart for an arbitrary witness, the
action, classification and scheme bridges, extraction and completeness, #11 and frozen117 remain
open.  No guard `I ≠ P` is removed globally, and no common shift, uniqueness or constraint on the
six generator points is claimed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

/-- **Affine-grid coordinates over infinite transcendence degree** (#27, P5).  Let `w` satisfy
`Ψ` and `I ≠ D` over algebraically closed `k ⊆ K` with `ℵ₀ ≤ trdeg_k K`.  If independent
`a, b, c, d, x` give the joins `A, B, C` and the points `S, T, U, X, Y, Z` of the table, then `w`
has affine-grid coordinates.  The two families of fresh inputs are constructed, each after the
corresponding original prime curve is fixed; the chart and algebraic closedness are hypotheses. -/
theorem Psi.hasAffineGridCoordinates_of_chart_of_aleph0_le_trdeg [IsAlgClosed k] [IsAlgClosed K]
    (htr : Cardinal.aleph0 ≤ Algebra.trdeg k K)
    {w : QWitness k K} (hw : w.Psi) (hID : w.I ≠ w.D) {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hA : w.A = ClosedIF.point k a ⊔ ClosedIF.point k b)
    (hB : w.B = ClosedIF.point k c ⊔ ClosedIF.point k d)
    (hC : w.C = ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d))
    (hS : w.S.1 = ClosedIF.point k a) (hT : w.T.1 = ClosedIF.point k c)
    (hU : w.U.1 = ClosedIF.point k (a * c)) (hX : w.X.1 = ClosedIF.point k x)
    (hY : w.Y.1 = ClosedIF.point k (a * x + b))
    (hZ : w.Z.1 = ClosedIF.point k (c * (a * x + b) + d)) :
    w.HasAffineGridCoordinates := by
  obtain ⟨_, -, -, HP⟩ :=
    hw.hasAffineGridCoordinates_of_chart_supplied_inputs hID hind hA hB hC hS hT hU hX hY hZ
  -- The original prime curve of `F` is fixed; construct the first family.
  obtain ⟨tP, htP⟩ := exists_fresh_sequence_of_aleph0_le_trdeg htr
    (Set.Finite.insert a (Set.Finite.insert b (Set.Finite.insert x (Set.finite_singleton c))))
  obtain ⟨κ, _, -, -, HQ⟩ := HP tP fun n _ ↦ htP n
  -- The original prime curve of `H⁻¹` is fixed; construct the second family.
  obtain ⟨tQ, htQ⟩ := exists_fresh_sequence_of_aleph0_le_trdeg htr
    (Set.Finite.insert c (Set.Finite.insert (d + (c - 1) * algebraMap k K κ)
      (Set.Finite.insert (b + (a - 1) * algebraMap k K κ) (Set.finite_singleton (a * c)⁻¹))))
  exact HQ tQ fun n _ ↦ htQ n

end QWitness

end AclGeom
