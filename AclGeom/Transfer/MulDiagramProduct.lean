/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.MultiplicationConverse
import AclGeom.Transfer.LiftConfig

/-!
# The product point of a multiplication diagram over arbitrary fields

The product clause of blueprint Lemma `mul-diagram` says that a nondegenerate multiplication
diagram with bottom points `[x]`, `[y]`, `[x/y]` has `E = [xy]`. This module strengthens the
existing closed-field coordinate argument to arbitrary base and ambient fields, for actual
representatives `x, y` (`MulDiagram.product_point`).

The diagram lifts along `K → K̄` to the algebraically closed pair `k̄ ⊆ K̄`
(`MulDiagram.lift`), the lifted bottom points keep the actual representatives, and
`MulDiagram.exists_coordinates` gives `E = [xy]` there, with no ambient rank bound.  The lift of
closed fields is injective, so the equality reflects to `K/k`.  Only the product point is
reflected: the auxiliary corner representative found over `K̄` need not lie in `K`, so the
coordinate table of the remaining diagram points is not claimed over arbitrary fields.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the product clause of Lemma `mul-diagram` is proved over arbitrary fields (#25).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The product point of a multiplication diagram** (blueprint Lemma `mul-diagram`, product
clause of the converse): if the bottom points of a multiplication diagram are `[x]`, `[y]` and
`[x/y]` for actual representatives `x, y`, then its product point is `[xy]`.  No closedness,
perfection or rank hypothesis is needed. -/
theorem MulDiagram.product_point {X Y V E A B C D : Point k K} {x y : K}
    (hmul : MulDiagram X Y V E A B C D)
    (hX : X.1 = ClosedIF.point k x) (hY : Y.1 = ClosedIF.point k y)
    (hV : V.1 = ClosedIF.point k (x / y)) :
    E.1 = ClosedIF.point k (x * y) := by
  -- Lift to the algebraically closed pair `k̄ ⊆ K̄`.
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have halg : ∀ z ∈ algebraicClosure k (AlgebraicClosure K), IsAlgebraic k z :=
    fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz
  let ι : K →ₐ[k] AlgebraicClosure K := IsScalarTower.toAlgHom k K (AlgebraicClosure K)
  -- Lifted principal points keep their actual representatives.
  have hpt : ∀ {P : Point k K} {z : K}, P.1 = ClosedIF.point k z →
      (liftPoint halg ι P).1 = ClosedIF.point _ (ι z) := fun hP ↦ by
    rw [liftPoint_val, hP, liftClosed_point halg ι]
  -- The full coordinate table over `K̄`; only its product point is used.
  obtain ⟨-, -, -, -, -, -, hE⟩ := MulDiagram.exists_coordinates (hmul.lift halg ι)
    (hpt hX) (hpt hY) (by rw [hpt hV, map_div₀])
  -- Reflect `E = [xy]` along the injective lift of closed fields.
  apply liftClosed_injective halg ι
  rw [← liftPoint_val halg ι E, hE, liftClosed_point halg ι, map_mul]

end AclGeom
