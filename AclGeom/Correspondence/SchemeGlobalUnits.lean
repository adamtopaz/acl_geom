/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupSchemePoints

/-!
# Global units detected at base-field points

**Status:** over an ACF base, a section on a locally finite-type scheme is invertible if
its value at every base-field point is invertible. Jacobson density makes its basic open
the whole scheme; the local unit criterion gives a global unit. No affineness or reducedness
is assumed. Named consumer: `AdditiveRigidity.exists_multiplicative_lift` (#21).
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Named consumer: the actual normal additive-subgroup conjugation character. -/
theorem isUnit_section_of_point_values (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (s : Γ(X.left, ⊤))
    (h : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ X, IsUnit (q.left.appTop s)) : IsUnit s := by
  classical
  have hclosed (y : X.left) (hy : IsClosed ({y} : Set X.left)) : y ∈ X.left.basicOpen s := by
    let q : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom y hy) (pointOfClosedPoint_comp X.hom y hy)
    let q₀ : Spec (.of k) ⟶ X.left := q.left
    have hu : IsUnit (q₀.appTop s) := h q
    have hb := (Spec (.of k)).basicOpen_of_isUnit hu
    rw [← Scheme.preimage_basicOpen_top q₀] at hb
    have hq : q₀ (IsLocalRing.closedPoint k) ∈ X.left.basicOpen s := by
      change IsLocalRing.closedPoint k ∈ q₀ ⁻¹ᵁ X.left.basicOpen s
      rw [hb]
      trivial
    rwa [show q₀ (IsLocalRing.closedPoint k) = y from
      pointOfClosedPoint_apply X.hom y hy _] at hq
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let Z : Set X.left := (X.left.basicOpen s : Set X.left)ᶜ
  have hZ : IsClosed Z := (X.left.basicOpen s).isOpen.isClosed_compl
  have hinter : Z ∩ closedPoints X.left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy, hyc⟩
    exact hy (hclosed y hyc)
  have hZempty : Z = ∅ := by
    have hd := JacobsonSpace.closure_inter_closedPoints_eq_closure hZ.isLocallyClosed
    simpa only [hinter, closure_empty, hZ.closure_eq] using hd.symm
  apply X.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
  intro y hy
  apply (Scheme.mem_basicOpen X.left s y hy).mp
  by_contra hn
  have hz : y ∈ Z := hn
  rw [hZempty] at hz
  exact hz
end
end AclGeom.AdditiveRigidity
