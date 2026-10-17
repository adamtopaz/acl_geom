/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveFunctionFieldAlgebra

/-!
# Finite dimension bounds on an actual affine chart

Named consumer: the actual group parameter chart in `SchemeActionGenus`.

**Status:** proved for every scheme and finite lower bound. An affine open meeting the
smallest member of the irreducible closed chain retains its length.
-/

namespace AclGeom

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- Preserve a prescribed finite dimension lower bound on one nonempty affine chart.
Named consumer: the actual coefficient field has the group's required transcendence rank. -/
theorem exists_isAffineOpen_dimension_ge (X : Scheme) (n : ℕ)
    (hX : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ Nonempty U ∧
      (n : WithBot ℕ∞) ≤ topologicalKrullDim U := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp hX
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → X) U.isOpenEmbedding
  let q : Fin (p.length + 1) →
      {Z : IrreducibleCloseds X | ((Subtype.val : U → X) ⁻¹' Z).Nonempty} :=
    fun i ↦ ⟨p i, ⟨⟨x, hxU⟩, (p.head_le i) hx⟩⟩
  have hq : StrictMono q := fun _ _ hij ↦ p.strictMono hij
  let r : LTSeries (IrreducibleCloseds U) :=
    LTSeries.mk p.length (fun i ↦ e.symm (q i)) (e.symm.strictMono.comp hq)
  refine ⟨U, hU, ⟨⟨x, hxU⟩⟩, ?_⟩
  change (n : WithBot ℕ∞) ≤ Order.krullDim (IrreducibleCloseds U)
  calc
    (n : WithBot ℕ∞) = r.length := by
      change (n : WithBot ℕ∞) = (p.length : WithBot ℕ∞)
      rw [hp]
    _ ≤ _ := Order.LTSeries.length_le_krullDim r

end

end AclGeom
