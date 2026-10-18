/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.RationalityDescent
import AclGeom.Correspondence.SchemeActionGenus
import AclGeom.Correspondence.SchemeCurveFunctionField

/-!
# Original-base genus and rationality of an actual regular affine curve action

Named source consumer: the genus/rational-coordinate step of blueprint `lem:affine-action`
(#21).

**Status:** proved for an integral locally finite-type group of dimension at least two
acting regularly on an integral affine locally finite-type dimension-one curve over an
algebraically closed base, with the genuine global-point kernel criterion. The actual
generic-stalk field has genus zero and a transcendental generator over the original base.
Chart, parameter field, coefficients, rank, constants, one-variable instances, rationality
and descent are internal. Non-affine and rational-action cases, regularization, completion/
points identification, the normal subgroup and arbitrary-action classifier remain open;
all eight original #21 items and the full durable goal stay open.
-/

namespace AclGeom.SchemeCurveGenus

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A faithful regular action of an integral group of dimension at least two on an integral
 affine curve forces genus zero over the original algebraically closed base. The actual
 generic-stalk field, chart, coefficients, constant extension and descent are internal. -/
theorem genus_eq_zero
    (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.left)
    (hdimV : topologicalKrullDim V.left = 1) :
    letI := ActionFunctionField.functionFieldAlgebra V
    letI := scheme_functionField_isFunctionFieldOneVar k V hdimV
    genus k V.left.functionField = 0 := by
  let := ActionFunctionField.functionFieldAlgebra V
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdimV
  obtain ⟨K, hK, hAlg, hACF, hDom, hOne, hg⟩ :=
    SchemeGenericTranslate.exists_constantExtension_genus_eq_zero G V hker hdimG hdimV
  let := hK
  let := hAlg
  have := hACF
  have := hDom
  have := hOne
  exact RationalityDescent.genus_eq_zero_of_tensor hg

/-- The actual generic-stalk field of this regular affine curve has a transcendental
 generator over its original base. Named next consumer: the original-base fractional-linear
 description and affine-action classification. -/
theorem exists_generator
    (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.left)
    (hdimV : topologicalKrullDim V.left = 1) :
    letI := ActionFunctionField.functionFieldAlgebra V
    ∃ t : V.left.functionField, Transcendental k t ∧
      IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤ := by
  let := ActionFunctionField.functionFieldAlgebra V
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdimV
  exact genus_eq_zero_iff_exists_generator.1 (genus_eq_zero G V hker hdimG hdimV)

end

end AclGeom.SchemeCurveGenus
