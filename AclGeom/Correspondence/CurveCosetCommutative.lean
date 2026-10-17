/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.CurveCoset

/-!
# Generic products of curves in a commutative algebraic group

The last sentence of blueprint Lemma `curve-coset`: in a commutative group the three curves are
cosets of the same subgroup (`curveCoset_of_genericProduct_commutative`). For a commutative
group object, right translation by a `k`-point is left translation by it
(`rightMul_eq_leftMul`), so `H g₂ = g₂ H` and `g₁ H g₂ = (g₁ g₂) H`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the commutative clause of `curve-coset` is proved.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

namespace GroupScheme

/-- In a commutative group object, right translation by a `k`-point is left translation.
Named consumer: `curveCoset_of_genericProduct_commutative`. -/
theorem rightMul_eq_leftMul {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
    [IsCommMonObj G] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : rightMul G g = leftMul G g := by
  change 𝟙 G * (toUnit G ≫ g) = (toUnit G ≫ g) * 𝟙 G
  exact mul_comm _ _

end GroupScheme

open GroupScheme

/-- **Generic products of curves in a commutative algebraic group** (blueprint `lem:curve-coset`,
commutative clause). Under the hypotheses of `curveCoset_of_genericProduct`, if the ambient group
is commutative, then the three curves are the cosets `g₁ H`, `g₂ H` and `(g₁ g₂) H` of one
connected one-dimensional closed algebraic subgroup `H`. -/
theorem curveCoset_of_genericProduct_commutative {k : Type u} [Field k] [IsAlgClosed k]
    (G : AlgebraicGroup k) [IsCommMonObj G.toGroupScheme.X] {A B D : Set G.carrier}
    (hA : IsClosed A) (hAi : IsIrreducible A) (hAd : topologicalKrullDim A = 1)
    (hB : IsClosed B) (hBi : IsIrreducible B) (hBd : topologicalKrullDim B = 1)
    (hD : IsClosed D) (hDi : IsIrreducible D) (hDd : topologicalKrullDim D = 1)
    (hgen : ∃ ξ : (reducedOver G.toGroupScheme.X ⟨A, hA⟩ ⊗
        reducedOver G.toGroupScheme.X ⟨B, hB⟩).left,
      closure {ξ} = Set.univ ∧
        ((reducedOverι G.toGroupScheme.X ⟨A, hA⟩ ⊗ₘ
          reducedOverι G.toGroupScheme.X ⟨B, hB⟩) ≫ μ[G.toGroupScheme.X]).left ξ ∈ D) :
    ∃ (H : ConnectedAlgebraicGroup k) (inclusion : H.toAlgebraicGroup.Hom G)
        (g₁ g₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X),
      IsClosedImmersion inclusion.schemeHom ∧ topologicalKrullDim H.toAlgebraicGroup.carrier = 1 ∧
      A = leftMulHomeo g₁ '' Set.range inclusion.schemeHom ∧
      B = leftMulHomeo g₂ '' Set.range inclusion.schemeHom ∧
      D = leftMulHomeo (g₁ * g₂) '' Set.range inclusion.schemeHom := by
  obtain ⟨H, inclusion, g₁, g₂, hclosed, hdim, hAH, hBH, hDH⟩ :=
    curveCoset_of_genericProduct G hA hAi hAd hB hBi hBd hD hDi hDd hgen
  have hRL : ∀ x, rightMulHomeo g₂ x = leftMulHomeo g₂ x := fun x ↦ by
    rw [rightMulHomeo_apply, leftMulHomeo_apply, rightMul_eq_leftMul]
  have hR : ∀ Z : Set G.carrier, rightMulHomeo g₂ '' Z = leftMulHomeo g₂ '' Z := fun Z ↦
    Set.image_congr fun x _ ↦ hRL x
  have hLL : ∀ Z : Set G.carrier,
      leftMulHomeo g₁ '' (leftMulHomeo g₂ '' Z) = leftMulHomeo (g₁ * g₂) '' Z := fun Z ↦ by
    rw [Set.image_image]
    refine Set.image_congr fun x _ ↦ ?_
    rw [leftMulHomeo_apply, leftMulHomeo_apply, leftMulHomeo_apply, ← Scheme.Hom.comp_apply,
      ← Over.comp_left, leftMul_comp_leftMul]
  refine ⟨H, inclusion, g₁, g₂, hclosed, hdim, hAH, ?_, ?_⟩
  · rw [hBH, hR]
  · rw [hDH, hR, hLL]

end

end AclGeom
