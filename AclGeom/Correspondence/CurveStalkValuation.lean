/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePointTopology
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Actual curve stalks as valuation subrings

**Status:** proved for actual normal integral locally Noetherian curves of dimension at most
one. The canonical stalk embedding determines the valuation subring, its dimension bound and
the generic-point criterion for being the entire function field. Named consumer:
closedPointPlace.

The given proper normal curve is an actual input. Completion construction, the scheme API from
smoothness to local normality, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] specializationOrder
universe u

/-- The actual stalk, as a valuation subring of the actual generic-stalk field.
Named consumer: the closed-point/place correspondence. -/
def stalkValuationSubring (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X) :
    ValuationSubring X.functionField := by
  have := hnormal x
  have := ProperCurve.stalk_valuationRing X hdim x
  exact (ValuationRing.valuation (X.presheaf.stalk x) X.functionField).valuationSubring

/-- Membership is literal membership in the image of the actual stalk embedding.
Named consumers: the place correspondence and its automorphism formula. -/
theorem mem_stalkValuationSubring
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X)
    (z : X.functionField) :
    z ∈ stalkValuationSubring X hdim hnormal x ↔
      ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = z := by
  have := hnormal x
  have := ProperCurve.stalk_valuationRing X hdim x
  exact ValuationRing.mem_integer_iff (X.presheaf.stalk x) X.functionField z

/-- The actual stalk-image valuation ring has dimension at most one.
Named consumer: equality with the valuation ring of a place centered there. -/
theorem stalkValuationSubring_krullDimLE
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X) :
    Ring.KrullDimLE 1 (stalkValuationSubring X hdim hnormal x) := by
  have := hnormal x
  have := ProperCurve.stalk_valuationRing X hdim x
  let e : (X.presheaf.stalk x) ≃+* stalkValuationSubring X hdim hnormal x :=
    ValuationRing.equivInteger (X.presheaf.stalk x) X.functionField
  have he : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  rw [Ring.krullDimLE_iff, ← e.ringKrullDim, ringKrullDim_stalk_eq_coheight]
  exact (Order.coheight_le_krullDim x).trans (he.trans_le hdim)

/-- The actual stalk valuation subring is the whole field exactly at the generic point.
Named consumer: turning every closed point into a genuine nontrivial place. -/
theorem stalkValuationSubring_eq_top_iff
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X) :
    stalkValuationSubring X hdim hnormal x = ⊤ ↔ x = genericPoint X := by
  constructor
  · intro h
    have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk x) X.functionField) := by
      intro z
      apply (mem_stalkValuationSubring X hdim hnormal x z).mp
      rw [h]
      trivial
    exact (isField_stalk_iff_genericPoint X x).mp
      (IsFractionRing.surjective_iff_isField.mp hsurj)
  · intro h
    have hfield := (isField_stalk_iff_genericPoint X x).mpr h
    have hsurj := (IsFractionRing.surjective_iff_isField
      (R := X.presheaf.stalk x) (K := X.functionField)).mpr hfield
    apply top_unique
    intro z _
    exact (mem_stalkValuationSubring X hdim hnormal x z).mpr (hsurj z)

end
end AclGeom.CurvePointsPlaces
