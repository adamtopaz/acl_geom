/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SmoothCurveStalkBase
import AclGeom.Correspondence.SmoothCurveLocalNormality
import AclGeom.Correspondence.CurvePointTopology
import AclGeom.Correspondence.NormalCurveStalks
import AclGeom.Correspondence.SchemeCurveFunctionField
import AclGeom.Correspondence.ProperCurveOpenExtension
import AclGeom.Correspondence.AlgebraicGroup
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Actual smooth curve stalks and proper extension

**Status:** proved over an ACF base for actual smooth integral dimension-one curves: every
actual stalk is integrally closed and a valuation ring; every closed-point stalk is a DVR.
Actual one-dimensional connected algebraic groups supply smoothness internally using Mathlib.
Every actual automorphism of a nonempty open in a proper smooth integral curve extends
uniquely to the entire curve, with normality internal. No local-normality, cotangent-rank,
valuation or extension certificate is a premise.

These are ACF dimension-one results. Projective presentation, joint regularity of extended
rational families, rational-action regularization and the full original classifier remain
owed. Original group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary remain obligations. All eight original #21 work items and the full durable
goal remain active and incomplete.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SmoothCurveStalks
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Every actual stalk of a smooth integral dimension-one curve over an algebraically
closed field is integrally closed. Smoothness, the actual function field and the
closed-point residue algebra supply all local inputs internally. Named consumers:
actual connected curve groups and individual proper smooth-curve extension. -/
theorem stalk_integrallyClosed
    (X : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom]
    (hdim : topologicalKrullDim X.left = 1) (x : X.left) :
    IsIntegrallyClosed (X.left.presheaf.stalk x) := by
  by_cases hx : x = genericPoint X.left
  · subst x
    exact inferInstanceAs (IsIntegrallyClosed X.left.functionField)
  have hclosed := (CurvePointsPlaces.isClosed_singleton_iff_ne_genericPoint X.left hdim x).2 hx
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let := stalkAlgebra X x
  have := stalk_formallySmooth X x
  have := stalk_essFiniteType X x
  have := stalk_functionField_isScalarTower X x
  have := stalk_residue_isAlgebraic X x hclosed
  have := scheme_functionField_isFunctionFieldOneVar k X hdim
  exact isIntegrallyClosed_of_smooth (F := X.left.functionField)
    (trdeg_eq_one_of_oneVar (k := k) (F := X.left.functionField))

/-- Every actual stalk of a smooth integral curve over an algebraically closed field
is a valuation ring, with normality proved internally. Named consumer: actual
one-dimensional connected algebraic groups. -/
theorem stalk_valuationRing
    (X : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom]
    (hdim : topologicalKrullDim X.left = 1) (x : X.left) :
    ValuationRing (X.left.presheaf.stalk x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := stalk_integrallyClosed X hdim x
  exact ProperCurve.stalk_valuationRing X.left hdim.le x

/-- Every actual closed-point stalk of a smooth integral dimension-one curve over an
algebraically closed field is a DVR. No normality or valuation certificate is supplied.
Named consumer: actual one-dimensional connected algebraic groups. -/
theorem stalk_isDiscreteValuationRing
    (X : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom]
    (hdim : topologicalKrullDim X.left = 1) (x : X.left)
    (hx : IsClosed ({x} : Set X.left)) :
    IsDiscreteValuationRing (X.left.presheaf.stalk x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hnotfield : ¬ IsField (X.left.presheaf.stalk x) := by
    intro hf
    exact ((CurvePointsPlaces.isClosed_singleton_iff_ne_genericPoint X.left hdim x).1 hx)
      ((CurvePointsPlaces.isField_stalk_iff_genericPoint X.left x).1 hf)
  exact ((IsDiscreteValuationRing.TFAE (X.left.presheaf.stalk x) hnotfield).out 2 1).mp
    (stalk_valuationRing X hdim x)

/-- An actual one-dimensional connected algebraic group over an algebraically closed
field has integrally closed valuation-ring stalks and DVRs at every closed point.
Mathlib supplies smoothness of the actual group scheme internally. This is the local
normality assertion used before completion in the source proof of `lem:affine-action`.
No smoothness, normality, cotangent-rank or valuation certificate is a premise. -/
theorem connectedGroup_stalks (G : ConnectedAlgebraicGroup k)
    (hdim : topologicalKrullDim G.toGroupScheme.X.left = 1) :
    (∀ x : G.toGroupScheme.X.left, IsIntegrallyClosed (G.toGroupScheme.X.left.presheaf.stalk x)) ∧
    (∀ x : G.toGroupScheme.X.left, ValuationRing (G.toGroupScheme.X.left.presheaf.stalk x)) ∧
    (∀ x : G.toGroupScheme.X.left, IsClosed ({x} : Set G.toGroupScheme.X.left) →
      IsDiscreteValuationRing (G.toGroupScheme.X.left.presheaf.stalk x)) := by
  have : GrpObj (Over.mk G.toGroupScheme.X.hom) := by
    change GrpObj G.toGroupScheme.X
    infer_instance
  have : Smooth G.toGroupScheme.X.hom := smooth_of_grpObj _
  exact ⟨stalk_integrallyClosed G.toGroupScheme.X hdim,
    stalk_valuationRing G.toGroupScheme.X hdim,
    stalk_isDiscreteValuationRing G.toGroupScheme.X hdim⟩

/-- An actual automorphism of a nonempty open in a proper smooth integral curve over an
algebraically closed field extends uniquely to the whole curve. Normality of every
actual stalk is proved internally. This proves individual extension in the source
`lem:affine-action`; completion and joint regularity of families remain separate. -/
theorem properSmooth_existsUnique_iso_extension
    (X U : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) [Nonempty U.left]
    (j : U ⟶ X) [IsOpenImmersion j.left] (a : U ≅ U) :
    ∃! F : X ≅ X, j ≫ F.hom = a.hom ≫ j := by
  exact ProperCurve.existsUnique_iso_extension X U hdim.le
    (stalk_integrallyClosed X hdim) j a

end
end AclGeom.SmoothCurveStalks
