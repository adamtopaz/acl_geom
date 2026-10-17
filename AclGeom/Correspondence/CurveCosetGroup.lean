/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.ClosedCurveDimension

/-!
# The stabilizer argument of the curve-coset lemma

Blueprint Lemma `curve-coset` for a group scheme `G` locally of finite type over an algebraically
closed field `k`, in its closed-point form (`curveCoset_of_closedPoints`). Let `A`, `B` and `D` be
closed irreducible subsets of dimension one, and suppose `a * b` is a closed point of `D` for all
closed points `a` of `A` and `b` of `B`. Then `H = a₀⁻¹ A` is a closed irreducible one-dimensional
set whose closed points form a subgroup of `G(k)`, and `A = a₀ H`, `B = H b₀`, `D = a₀ H b₀`.

Each right translate `A b` by a closed point of `B` is a curve inside `D`, hence equal to `D`.
So `B b₀⁻¹` lies in the right stabilizer of `A`, and the stabilizer lies in `a₀⁻¹ A`. The two
outer sets are curves, hence equal. No equations for the stabilizer are needed.

This is a conditional step toward the source lemma. Its product hypothesis is stated on closed
points, whereas the source states it for independent generic points. It gives `H` as a closed set
with a subgroup of closed points. `CurveCosetSource` supplies its generic-product input, and
`ClosedSubgroup` constructs the actual subgroup scheme. The complete source consumer is
`curveCoset_of_genericProduct`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the closed-point stabilizer argument is proved and consumed by the general source
theorem in `CurveCoset`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

namespace GroupScheme

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

/-- Left and right translations commute. Named consumer: `curveCoset_of_closedPoints`. -/
theorem leftMul_comp_rightMul (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    leftMul G a ≫ rightMul G b = rightMul G b ≫ leftMul G a := by
  rw [comp_rightMul, comp_leftMul]
  change (toUnit G ≫ a) * 𝟙 G * (toUnit G ≫ b) = (toUnit G ≫ a) * (𝟙 G * (toUnit G ≫ b))
  rw [_root_.mul_assoc]

variable [IsAlgClosed k] [LocallyOfFiniteType G.hom]

/-- **The stabilizer argument of the curve-coset lemma** (blueprint `curve-coset`, closed-point
form). Over an algebraically closed field, let `A`, `B` and `D` be closed irreducible
one-dimensional subsets of a group scheme locally of finite type. If the product of any closed
point of `A` and any closed point of `B` is a point of `D`, then there are a closed irreducible
one-dimensional `H`, whose closed points contain `1` and are closed under `h₁ * h₂⁻¹`, and
`k`-points `g₁`, `g₂` with `A = g₁ H`, `B = H g₂` and `D = g₁ H g₂`. The source hypothesis on
generic points, and an algebraic subgroup structure on `H`, are not part of this statement. -/
theorem curveCoset_of_closedPoints {A B D : Set G.left}
    (hA : IsClosed A) (hAi : IsIrreducible A) (hAd : topologicalKrullDim A = 1)
    (hB : IsClosed B) (hBi : IsIrreducible B) (hBd : topologicalKrullDim B = 1)
    (hD : IsClosed D) (hDi : IsIrreducible D) (hDd : topologicalKrullDim D = 1)
    (hAB : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      (pointsEquivClosedPoints a : G.left) ∈ A → (pointsEquivClosedPoints b : G.left) ∈ B →
        (pointsEquivClosedPoints (a * b) : G.left) ∈ D) :
    ∃ (H : Set G.left) (g₁ g₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G),
      IsClosed H ∧ IsIrreducible H ∧ topologicalKrullDim H = 1 ∧
      (pointsEquivClosedPoints (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G.left) ∈ H ∧
      (∀ h₁ h₂ : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        (pointsEquivClosedPoints h₁ : G.left) ∈ H → (pointsEquivClosedPoints h₂ : G.left) ∈ H →
          (pointsEquivClosedPoints (h₁ * h₂⁻¹) : G.left) ∈ H) ∧
      A = leftMulHomeo g₁ '' H ∧ B = rightMulHomeo g₂ '' H ∧
      D = leftMulHomeo g₁ '' (rightMulHomeo g₂ '' H) := by
  classical
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  -- Closed points determine closed sets.
  have subset_of_points : ∀ {Z W : Set G.left}, IsClosed Z → IsClosed W →
      (∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        (pointsEquivClosedPoints p : G.left) ∈ Z → (pointsEquivClosedPoints p : G.left) ∈ W) →
      Z ⊆ W := by
    intro Z W hZ hW h
    rw [← hZ.closure_eq, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hZ.isLocallyClosed]
    refine closure_minimal ?_ hW
    rintro x ⟨hxZ, hxc⟩
    obtain ⟨p, hp⟩ := pointsEquivClosedPoints.surjective (⟨x, hxc⟩ : closedPoints G.left)
    have hx : (pointsEquivClosedPoints p : G.left) = x := congrArg Subtype.val hp
    rw [← hx] at hxZ ⊢
    exact h p hxZ
  have exists_point : ∀ {Z : Set G.left}, IsClosed Z → Z.Nonempty →
      ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ G, (pointsEquivClosedPoints p : G.left) ∈ Z := by
    intro Z hZ hne
    obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
    obtain ⟨p, hp⟩ := pointsEquivClosedPoints.surjective (⟨x, hxc⟩ : closedPoints G.left)
    have hx : (pointsEquivClosedPoints p : G.left) = x := congrArg Subtype.val hp
    exact ⟨p, hx ▸ hxZ⟩
  -- Translates of curves are curves.
  have image_curve : ∀ (e : G.left ≃ₜ G.left) {Z : Set G.left}, IsClosed Z → IsIrreducible Z →
      topologicalKrullDim Z = 1 →
      IsClosed (e '' Z) ∧ IsIrreducible (e '' Z) ∧ topologicalKrullDim (e '' Z) = 1 := by
    intro e Z hZ hZi hZd
    refine ⟨e.isClosed_image.2 hZ, hZi.image e e.continuous.continuousOn, ?_⟩
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (e.image Z).isHomeomorph]
    exact hZd
  -- Translations of closed points.
  have hRpt : ∀ b p : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      rightMulHomeo b (pointsEquivClosedPoints p : G.left) = pointsEquivClosedPoints (p * b) :=
    fun b p ↦ (rightMulHomeo_apply b _).trans (rightMul_left_pointsEquivClosedPoints p b)
  have hLpt : ∀ a p : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      leftMulHomeo a (pointsEquivClosedPoints p : G.left) = pointsEquivClosedPoints (a * p) :=
    fun a p ↦ (leftMulHomeo_apply a _).trans (leftMul_left_pointsEquivClosedPoints p a)
  -- Composition of translations on sets.
  have hRR : ∀ (b b' : 𝟙_ (Over (Spec (.of k))) ⟶ G) (Z : Set G.left),
      rightMulHomeo b' '' (rightMulHomeo b '' Z) = rightMulHomeo (b * b') '' Z := by
    intro b b' Z
    rw [Set.image_image]
    refine Set.image_congr fun x _ ↦ ?_
    rw [rightMulHomeo_apply, rightMulHomeo_apply, rightMulHomeo_apply, ← Scheme.Hom.comp_apply,
      ← Over.comp_left, rightMul_comp_rightMul]
  have hLL : ∀ (a a' : 𝟙_ (Over (Spec (.of k))) ⟶ G) (Z : Set G.left),
      leftMulHomeo a' '' (leftMulHomeo a '' Z) = leftMulHomeo (a' * a) '' Z := by
    intro a a' Z
    rw [Set.image_image]
    refine Set.image_congr fun x _ ↦ ?_
    rw [leftMulHomeo_apply, leftMulHomeo_apply, leftMulHomeo_apply, ← Scheme.Hom.comp_apply,
      ← Over.comp_left, leftMul_comp_leftMul]
  have hLR : ∀ (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (Z : Set G.left),
      leftMulHomeo a '' (rightMulHomeo b '' Z) = rightMulHomeo b '' (leftMulHomeo a '' Z) := by
    intro a b Z
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun x _ ↦ ?_
    rw [leftMulHomeo_apply, leftMulHomeo_apply, rightMulHomeo_apply, rightMulHomeo_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
      leftMul_comp_rightMul]
  have hR1 : ∀ Z : Set G.left, rightMulHomeo (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) '' Z = Z := by
    intro Z
    refine Set.EqOn.image_eq_self fun x _ ↦ ?_
    rw [rightMulHomeo_apply, rightMul_one]
    rfl
  have hL1 : ∀ Z : Set G.left, leftMulHomeo (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) '' Z = Z := by
    intro Z
    refine Set.EqOn.image_eq_self fun x _ ↦ ?_
    rw [leftMulHomeo_apply, leftMul_one]
    rfl
  -- The preimage of a closed point under a right translation.
  have hRinv : ∀ {b p : 𝟙_ (Over (Spec (.of k))) ⟶ G} {x : G.left},
      rightMulHomeo b x = pointsEquivClosedPoints p → x = pointsEquivClosedPoints (p * b⁻¹) := by
    intro b p x hx
    rw [← (rightMulHomeo b).symm_apply_apply x, hx]
    exact rightMul_left_pointsEquivClosedPoints p b⁻¹
  -- Base points.
  obtain ⟨a₀, ha₀⟩ := exists_point hA hAi.nonempty
  obtain ⟨b₀, hb₀⟩ := exists_point hB hBi.nonempty
  -- Every right translate of `A` by a point of `B` is `D`.
  have hAb : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ G, (pointsEquivClosedPoints b : G.left) ∈ B →
      rightMulHomeo b '' A = D := by
    intro b hb
    obtain ⟨hc, -, hd⟩ := image_curve (rightMulHomeo b) hA hAi hAd
    refine eq_of_subset_of_finite_topologicalKrullDim hc hDi ?_ 1
      (hDd.trans Nat.cast_one.symm) (hd.trans Nat.cast_one.symm)
    refine subset_of_points hc hD fun p hp ↦ ?_
    obtain ⟨x, hxA, hx⟩ := hp
    have hx' := hRinv hx
    rw [hx'] at hxA
    have h := hAB _ _ hxA hb
    rwa [_root_.inv_mul_cancel_right] at h
  -- The right stabilizer of `A`.
  have stab_of_B : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ G, (pointsEquivClosedPoints b : G.left) ∈ B →
      rightMulHomeo (b * b₀⁻¹) '' A = A := by
    intro b hb
    rw [← hRR, hAb b hb, ← hAb b₀ hb₀, hRR, _root_.mul_inv_cancel, hR1]
  let H : Set G.left := leftMulHomeo a₀⁻¹ '' A
  obtain ⟨hHc, hHi, hHd⟩ := image_curve (leftMulHomeo a₀⁻¹) hA hAi hAd
  have mem_of_stab : ∀ h : 𝟙_ (Over (Spec (.of k))) ⟶ G, rightMulHomeo h '' A = A →
      (pointsEquivClosedPoints h : G.left) ∈ H := by
    intro h hh
    have h1 : (pointsEquivClosedPoints (a₀ * h) : G.left) ∈ A := by
      rw [← hh, ← hRpt]
      exact Set.mem_image_of_mem _ ha₀
    refine ⟨_, h1, ?_⟩
    rw [hLpt, _root_.inv_mul_cancel_left]
  -- `B b₀⁻¹ = H`.
  obtain ⟨hBc', -, hBd'⟩ := image_curve (rightMulHomeo b₀⁻¹) hB hBi hBd
  have hBH : rightMulHomeo b₀⁻¹ '' B = H := by
    refine eq_of_subset_of_finite_topologicalKrullDim hBc' hHi ?_ 1
      (hHd.trans Nat.cast_one.symm) (hBd'.trans Nat.cast_one.symm)
    refine subset_of_points hBc' hHc fun p hp ↦ ?_
    obtain ⟨y, hyB, hy⟩ := hp
    have hy' := hRinv hy
    rw [hy'] at hyB
    have h := mem_of_stab _ (stab_of_B _ hyB)
    rwa [_root_.inv_inv, _root_.mul_inv_cancel_right] at h
  have stab_of_mem : ∀ h : 𝟙_ (Over (Spec (.of k))) ⟶ G, (pointsEquivClosedPoints h : G.left) ∈ H →
      rightMulHomeo h '' A = A := by
    intro h hh
    rw [← hBH] at hh
    obtain ⟨y, hyB, hy⟩ := hh
    have hy' := hRinv hy
    rw [hy'] at hyB
    have h' := stab_of_B _ hyB
    rwa [_root_.inv_inv, _root_.mul_inv_cancel_right] at h'
  refine ⟨H, a₀, b₀, hHc, hHi, hHd, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_of_stab 1 (hR1 A)
  · intro h₁ h₂ hh₁ hh₂
    refine mem_of_stab _ ?_
    have hs₂ := stab_of_mem h₂ hh₂
    rw [← hRR, stab_of_mem h₁ hh₁]
    calc rightMulHomeo h₂⁻¹ '' A = rightMulHomeo h₂⁻¹ '' (rightMulHomeo h₂ '' A) := by rw [hs₂]
      _ = A := by rw [hRR, _root_.mul_inv_cancel, hR1]
  · change A = leftMulHomeo a₀ '' (leftMulHomeo a₀⁻¹ '' A)
    rw [hLL, _root_.mul_inv_cancel, hL1]
  · rw [← hBH, hRR, _root_.inv_mul_cancel, hR1]
  · rw [hLR]
    change D = rightMulHomeo b₀ '' (leftMulHomeo a₀ '' (leftMulHomeo a₀⁻¹ '' A))
    rw [hLL, _root_.mul_inv_cancel, hL1, hAb b₀ hb₀]

end GroupScheme

end

end AclGeom
