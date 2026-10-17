/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.CurveCosetGroup
import AclGeom.Correspondence.CurveCosetGeneric
import AclGeom.Correspondence.IntegralProduct

/-!
# The curve-coset lemma from its generic-point hypothesis

Blueprint Lemma `curve-coset` for a group scheme `G` locally of finite type over an algebraically
closed field `k`, from the source hypothesis (`curveCoset_of_genericPoints`). Let `A`, `B` and `D`
be closed irreducible curves. Suppose every generic point of the product `A ×ₖ B` of the reduced
induced subschemes is sent into `D` by `(x, y) ↦ x * y`; this is the scheme form of "the product of
independent generic points of `A` and `B` lies in `D`". Then `A = g₁ H`, `B = H g₂` and
`D = g₁ H g₂` for a closed irreducible one-dimensional `H` whose closed points form a subgroup.

The product is integral because `A` and `B` are irreducible and `k` is algebraically closed
(`irreducibleSpace_reducedOver_tensor`). Its generic point therefore exists, and the closed-point
form of the hypothesis follows (`mul_mem_of_genericPoint_mem`). The stabilizer argument
(`curveCoset_of_closedPoints`) then gives the cosets. Since generic points are unique, the same
holds when one jointly generic point is sent into `D` (`curveCoset_of_exists_genericPoint`).

`H` is produced here as a closed set with a subgroup of closed points. `ClosedSubgroup` constructs
its actual connected closed algebraic subgroup, and `CurveCoset` composes both bridges.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the cosets are proved from the generic-point hypothesis, in universal and existential
form. The actual subgroup-scheme structure is supplied in `ClosedSubgroup` and the complete
source consumer is `curveCoset_of_genericProduct`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

namespace GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Over (Spec (.of k))}

/-- Over an algebraically closed field, the product of the reduced induced subschemes on two
irreducible closed sets is irreducible. Named consumer: `curveCoset_of_genericPoints`. -/
theorem irreducibleSpace_reducedOver_tensor {A B : Closeds G.left}
    (hA : IsIrreducible (A : Set G.left)) (hB : IsIrreducible (B : Set G.left)) :
    IrreducibleSpace (reducedOver G A ⊗ reducedOver G B).left := by
  have : IsIntegral (reducedOver G A).left := isIntegral_subscheme_vanishingIdeal A hA
  have : IsIntegral (reducedOver G B).left := isIntegral_subscheme_vanishingIdeal B hB
  exact @irreducibleSpace_of_isIntegral _
    (isIntegral_pullback_of_isAlgClosed (reducedOver G A).hom (reducedOver G B).hom)

variable [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **The curve-coset lemma from its generic-point hypothesis** (blueprint `curve-coset`, with
`H` as a closed set). Over an algebraically closed field, let `A`, `B` and `D` be closed
irreducible one-dimensional subsets of a group scheme locally of finite type. If every generic
point of the product of the reduced induced subschemes on `A` and `B` is sent into `D` by
`(x, y) ↦ x * y`, then there are a closed irreducible one-dimensional `H`, whose closed points
contain `1` and are closed under `h₁ * h₂⁻¹`, and `k`-points `g₁`, `g₂` with `A = g₁ H`,
`B = H g₂` and `D = g₁ H g₂`. A subgroup-scheme structure on `H` is not part of this statement. -/
theorem curveCoset_of_genericPoints {A B D : Set G.left}
    (hA : IsClosed A) (hAi : IsIrreducible A) (hAd : topologicalKrullDim A = 1)
    (hB : IsClosed B) (hBi : IsIrreducible B) (hBd : topologicalKrullDim B = 1)
    (hD : IsClosed D) (hDi : IsIrreducible D) (hDd : topologicalKrullDim D = 1)
    (hgen : ∀ ξ : (reducedOver G ⟨A, hA⟩ ⊗ reducedOver G ⟨B, hB⟩).left,
      closure {ξ} = Set.univ →
        ((reducedOverι G ⟨A, hA⟩ ⊗ₘ reducedOverι G ⟨B, hB⟩) ≫ μ[G]).left ξ ∈ D) :
    ∃ (H : Set G.left) (g₁ g₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G),
      IsClosed H ∧ IsIrreducible H ∧ topologicalKrullDim H = 1 ∧
      (pointsEquivClosedPoints (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G.left) ∈ H ∧
      (∀ h₁ h₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        (pointsEquivClosedPoints h₁ : G.left) ∈ H → (pointsEquivClosedPoints h₂ : G.left) ∈ H →
          (pointsEquivClosedPoints (h₁ * h₂⁻¹) : G.left) ∈ H) ∧
      A = leftMulHomeo g₁ '' H ∧ B = rightMulHomeo g₂ '' H ∧
      D = leftMulHomeo g₁ '' (rightMulHomeo g₂ '' H) := by
  have := irreducibleSpace_reducedOver_tensor (G := G) (A := ⟨A, hA⟩) (B := ⟨B, hB⟩) hAi hBi
  have hmem := hgen _ (genericPoint_closure _)
  refine curveCoset_of_closedPoints hA hAi hAd hB hBi hBd hD hDi hDd fun a b ha hb ↦ ?_
  rw [pointsEquivClosedPoints_apply] at ha hb ⊢
  exact mul_mem_of_genericPoint_mem hD hmem a b ha hb

/-- **The curve-coset lemma from a jointly generic point** (blueprint `curve-coset`, with `H` as a
closed set). The hypothesis is the source's: some generic point of the product of the reduced
induced subschemes on `A` and `B` is sent into `D` by `(x, y) ↦ x * y`. Generic points of the
product are unique, so this is the universal hypothesis of `curveCoset_of_genericPoints`. -/
theorem curveCoset_of_exists_genericPoint {A B D : Set G.left}
    (hA : IsClosed A) (hAi : IsIrreducible A) (hAd : topologicalKrullDim A = 1)
    (hB : IsClosed B) (hBi : IsIrreducible B) (hBd : topologicalKrullDim B = 1)
    (hD : IsClosed D) (hDi : IsIrreducible D) (hDd : topologicalKrullDim D = 1)
    (hgen : ∃ ξ : (reducedOver G ⟨A, hA⟩ ⊗ reducedOver G ⟨B, hB⟩).left,
      closure {ξ} = Set.univ ∧
        ((reducedOverι G ⟨A, hA⟩ ⊗ₘ reducedOverι G ⟨B, hB⟩) ≫ μ[G]).left ξ ∈ D) :
    ∃ (H : Set G.left) (g₁ g₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G),
      IsClosed H ∧ IsIrreducible H ∧ topologicalKrullDim H = 1 ∧
      (pointsEquivClosedPoints (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G.left) ∈ H ∧
      (∀ h₁ h₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        (pointsEquivClosedPoints h₁ : G.left) ∈ H → (pointsEquivClosedPoints h₂ : G.left) ∈ H →
          (pointsEquivClosedPoints (h₁ * h₂⁻¹) : G.left) ∈ H) ∧
      A = leftMulHomeo g₁ '' H ∧ B = rightMulHomeo g₂ '' H ∧
      D = leftMulHomeo g₁ '' (rightMulHomeo g₂ '' H) := by
  obtain ⟨ξ, hξ, hmem⟩ := hgen
  refine curveCoset_of_genericPoints hA hAi hAd hB hBi hBd hD hDi hDd fun ξ' hξ' ↦ ?_
  have heq : ξ' = ξ :=
    (show IsGenericPoint ξ' Set.univ from hξ').eq (show IsGenericPoint ξ Set.univ from hξ)
  rw [heq]
  exact hmem

end GroupScheme

end

end AclGeom
