/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.ClosedSubgroup
import AclGeom.Correspondence.CurveCosetSource

/-!
# Generic products of curves are algebraic subgroup cosets

Blueprint Lemma `curve-coset` for an algebraic group over an algebraically closed field.
Independent generic points are expressed by a jointly generic point of the actual scheme
product of the two reduced induced curves. Its product need only lie in the third curve;
the source's stronger condition that it is generic there implies this membership.

The conclusion constructs an actual connected algebraic group and a closed group-scheme
inclusion into the ambient group, not only a closed set of points. All three original curves
are its left, right and double cosets. The ambient group need not itself be connected.

**Status:** the general curve-coset theorem is proved, with an actual connected closed algebraic
subgroup. The commutative clause is in `CurveCosetCommutative`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open GroupScheme

universe u

/-- **Generic products of curves are cosets** (blueprint `lem:curve-coset`). Let `A`, `B`
and `D` be closed irreducible curves in an algebraic group over an algebraically closed field.
If a jointly generic point of the actual scheme product of `A` and `B` maps into `D` under
multiplication, then an actual connected one-dimensional closed algebraic subgroup has the
three curves as `g₁ H`, `H g₂` and `g₁ H g₂`. Connectedness of the ambient group is unnecessary.
The source assumes that the product is generic in `D`, which implies the membership used here. -/
theorem curveCoset_of_genericProduct {k : Type u} [Field k] [IsAlgClosed k]
    (G : AlgebraicGroup k) {A B D : Set G.carrier}
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
      B = rightMulHomeo g₂ '' Set.range inclusion.schemeHom ∧
      D = leftMulHomeo g₁ '' (rightMulHomeo g₂ '' Set.range inclusion.schemeHom) := by
  obtain ⟨Z, g₁, g₂, hZc, hZi, hZd, hZ1, hZdiv, hAZ, hBZ, hDZ⟩ :=
    curveCoset_of_exists_genericPoint hA hAi hAd hB hBi hBd hD hDi hDd hgen
  have hone : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X).left
      (IsLocalRing.closedPoint k) ∈ Z := hZ1
  have hdiv : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      a.left (IsLocalRing.closedPoint k) ∈ Z → b.left (IsLocalRing.closedPoint k) ∈ Z →
        (a * b⁻¹).left (IsLocalRing.closedPoint k) ∈ Z := hZdiv
  obtain ⟨H, inclusion, hclosed, hrange, hdim⟩ :=
    exists_connectedClosedSubgroup_of_points G ⟨Z, hZc⟩ hZi hone hdiv
  refine ⟨H, inclusion, g₁, g₂, hclosed, hdim.trans hZd, ?_, ?_, ?_⟩
  · rw [hrange]
    exact hAZ
  · rw [hrange]
    exact hBZ
  · rw [hrange]
    exact hDZ

end

end AclGeom
