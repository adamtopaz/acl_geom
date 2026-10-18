/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupSchemePoints

/-!
# Reduced-source scheme equality detected on base-field points

**Status:** over an ACF base, two maps from a reduced locally finite-type scheme to a
separated locally finite-type scheme agree if they agree on every base-field point.
The proof uses Mathlib's closed-point extensionality theorem. Named consumers: the regular
normal additive-subgroup character's group law and actual joint conjugation diagram (#21).
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Named consumer: the regular character's group law and actual joint conjugation diagram. -/
theorem over_hom_ext_of_points {X Y : Over (Spec (.of k))}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    {f g : X ⟶ Y} (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  refine AlgebraicGeometry.ext_of_apply_eq Y.hom Set.univ isClosed_univ.isLocallyClosed
    dense_univ ?_ ((Over.w f).trans (Over.w g).symm)
  intro y _ hy
  let p : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom y hy) (pointOfClosedPoint_comp X.hom y hy)
  have he := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) (h p)
  have hpy : p.left (IsLocalRing.closedPoint k) = y := pointOfClosedPoint_apply X.hom y hy _
  change f.left (p.left (IsLocalRing.closedPoint k)) =
    g.left (p.left (IsLocalRing.closedPoint k)) at he
  rwa [hpy] at he
end
end AclGeom.AdditiveRigidity
