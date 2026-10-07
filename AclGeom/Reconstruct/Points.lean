/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.CrossBase
import AclGeom.Geometry.Transport

/-!
# Recovery of all points and the atomistic extension

Blueprint Prop `all-points` and the atomistic extension after it (checklist R3, R4), conditional
on the outputs of base recovery (Prop `base-recovery`, R1) and of the scalar elimination
(Prop `scalar-one`, R2). Corrected conditional outputs for the actual `interpretedRingEquiv`
are proved in `Reconstruct.Base` and `Reconstruct.Scalar` under their explicit carrier/completeness
inputs, with RAC for compatibility. This general propagation theorem takes them as hypotheses:
a field isomorphism `σ : K ≃+* L` compatible with the bases, and the point formula
`φ([x]) = [σ x]` for every `x` outside `racl_k {a}`.

`eq_closedIFMap_of_point_eq` then shows `φ = CrossBase.closedIFMap σ`, that is
`φ(M) = σ(M)` for every closed `M`.  In particular `φ([x]) = [σ x]` for every `x`
(`CrossBase.closedIFMap_point`).  The proof differs from the blueprint's: instead of
Lemma `two-generic-intersection` and preservation of meets, it observes that
* every point other than `[a]` has all of its representatives outside `racl_k {a}`, because a
  transcendental `x ∈ racl_k {a}` has `[x] = [a]` by exchange; and
* two bijections of points that agree away from one point agree everywhere.
An order isomorphism of closed lattices is determined by its action on points
(`latticeIsoOfPointEquiv_unique`).  No rank hypothesis, relative algebraic closedness or
freshness is used.

**Status:** general conditional point propagation and lattice extension are proved (#9). The
actual corrected conditional base-recovery and outside-point inputs are proved separately, and
`Reconstruct.Existence` assembles the actual inducing equality and compatible inducing existence
for perfect fields under explicit RAC/completeness inputs. General unconditional R1/R2,
original-field chosen-perfection reconstruction and unconditional completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- Two bijections that agree away from one point agree everywhere. -/
private theorem equiv_apply_eq_of_forall_ne {α β : Type*} (f g : α ≃ β) (p : α)
    (h : ∀ q, q ≠ p → f q = g q) : f p = g p := by
  by_contra hne
  have hq : g.symm (f p) ≠ p := fun hqp ↦
    hne ((g.apply_symm_apply (f p)).symm.trans (congrArg g hqp))
  have h' := h _ hq
  rw [Equiv.apply_symm_apply] at h'
  exact hq (f.injective h')

/-- **Recovery of all points and the atomistic extension** (blueprint Prop `all-points` and the
paragraph after it; #9 R3, R4), conditional on base recovery and scalar elimination.  If a field
isomorphism `σ`, compatible with the bases, induces `φ` on every point `[x]` with `x` outside
`racl_k {a}`, then `φ` is the transport of closed fields along `σ`. -/
theorem eq_closedIFMap_of_point_eq (φ : ClosedIF k K ≃o ClosedIF l L) {σ : K ≃+* L}
    (hσ : CrossBase.Compatible (k := k) (l := l) σ) {a : K}
    (hφ : ∀ x : K, x ∉ racl k ({a} : Set K) →
      φ (ClosedIF.point k x) = ClosedIF.point l (σ x)) :
    φ = CrossBase.closedIFMap σ hσ := by
  -- The two point maps agree at every point with a representative outside `racl {a}`.
  have hpt : ∀ P : Point k K, P.rep ∉ racl k ({a} : Set K) →
      Point.map φ P = Point.map (CrossBase.closedIFMap σ hσ) P := by
    intro P hP
    apply Subtype.ext
    rw [Point.map_coe, Point.map_coe, ← P.point_rep, hφ _ hP, CrossBase.closedIFMap_point]
  -- A representative inside `racl {a}` generates the point `[a]`.
  have hin : ∀ P : Point k K, P.rep ∈ racl k ({a} : Set K) → P.1 = ClosedIF.point k a := by
    intro P hP
    rw [← P.point_rep]
    refine ClosedIF.point_eq_point_iff.2 ⟨hP, ?_⟩
    exact ClosedIF.mem_point_symm hP P.rep_notMem_bot
  -- So the two bijections of points agree away from at most one point, hence everywhere.
  have hmap : Point.map φ = Point.map (CrossBase.closedIFMap σ hσ) := by
    refine Equiv.ext fun P ↦ ?_
    by_cases hP : P.rep ∈ racl k ({a} : Set K)
    · refine equiv_apply_eq_of_forall_ne _ _ P fun Q hQ ↦ hpt Q fun hQa ↦ hQ ?_
      exact Subtype.ext ((hin Q hQa).trans (hin P hP).symm)
    · exact hpt P hP
  -- An order isomorphism of closed lattices is determined by its point map.
  exact (latticeIsoOfPointEquiv_unique _ (fun _ _ ↦ pointCl_map_iff _) φ hmap).trans
    (latticeIsoOfPointEquiv_unique _ (fun _ _ ↦ pointCl_map_iff _)
      (CrossBase.closedIFMap σ hσ) rfl).symm

end

end AclGeom
