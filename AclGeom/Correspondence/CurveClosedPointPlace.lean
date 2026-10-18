/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveStalkValuation
import AclGeom.Correspondence.SchemeGenericTranslate
import AclGeom.Curves.Places

/-!
# Places from actual closed points

**Status:** proved over every field for an actual proper normal integral curve of dimension
one. Every actual closed point gives an existing Place of the actual function field. Constants
lie in the canonical stalk image and Noetherianity follows internally from properness. Named
consumer: closedPointEquivPlace.

The given proper normal curve is an actual input. Projective presentation, joint regularity of
extended families, rational-action regularization and the full original classifier remain
owed, alongside group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary. All eight original #21 work items and the full durable goal remain active
and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Base constants lie in every actual stalk image. Named consumer: the genuine place
attached to a closed point. -/
theorem algebraMap_mem_stalkValuationSubring
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : X.left) (c : k) :
    algebraMap k X.left.functionField c ∈ stalkValuationSubring X.left hdim hnormal x := by
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  let r : Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom c
  apply (mem_stalkValuationSubring X.left hdim hnormal x _).mpr
  have hxTop : x ∈ (⊤ : X.left.Opens) := by trivial
  refine ⟨X.left.presheaf.germ ⊤ x hxTop r, ?_⟩
  refine (Scheme.algebraMap_germ_eq_germToFunctionField X.left hxTop r).trans ?_
  rw [ActionFunctionField.functionFieldAlgebra_eq_germ X]
  rfl

/-- The place of the actual generic-stalk field at an actual closed point of a proper
normal curve. Noetherianity is derived from properness over the field.
Named consumer: the closed-point/place equivalence. -/
def closedPointPlace
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) : Place k X.left.functionField := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact
    { val := stalkValuationSubring X.left hdim.le hnormal x.val
      algebraMap_mem' := algebraMap_mem_stalkValuationSubring X hdim.le hnormal x.val
      ne_top' := fun h ↦
        (isClosed_singleton_iff_ne_genericPoint X.left hdim x.val).mp x.property
          ((stalkValuationSubring_eq_top_iff X.left hdim.le hnormal x.val).mp h) }

/-- The place ring is literally the image of the actual local ring in the actual field.
Named consumers: both inverse identities and automorphism compatibility. -/
theorem mem_closedPointPlace
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    (x : {x : X.left // IsClosed ({x} : Set X.left)}) (z : X.left.functionField) :
    z ∈ (closedPointPlace X hdim hnormal x).val ↔
      ∃ r : X.left.presheaf.stalk x.val,
        algebraMap (X.left.presheaf.stalk x.val) X.left.functionField r = z := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact mem_stalkValuationSubring X.left hdim.le hnormal x.val z

end
end AclGeom.CurvePointsPlaces
