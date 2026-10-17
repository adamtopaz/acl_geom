/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AlgebraicGroup

/-!
# Points and translations of group schemes over a field

For a group object `G` over `Spec k`, the sections `𝟙_ ⟶ G` form the group `G(k)` of `k`-points
(Mathlib's `CategoryTheory.Hom.group`). A `k`-point `g` gives the left translation `x ↦ g * x`
(`leftMul`) and the right translation `x ↦ x * g` (`rightMul`). These are morphisms over `Spec k`.
They compose as `G(k)` multiplies, so they are isomorphisms (`leftMulIso`, `rightMulIso`) and
homeomorphisms of the underlying space (`leftMulHomeo`, `rightMulHomeo`). On `k`-points they are
multiplication in `G(k)`.

Over an algebraically closed field, the `k`-points of a group scheme locally of finite type
correspond to its closed points (`pointsEquivClosedPoints`, from Mathlib's
`pointEquivClosedPoint`). Translation by `g` moves the closed point of `p` to that of `g * p`, or of
`p * g`.

These supply the stabilizer argument for blueprint Lemma `curve-coset`. The complete source
consumer, including the actual algebraic subgroup, is `curveCoset_of_genericProduct`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the point group, translations and closed-point correspondence are defined and proved.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

namespace GroupScheme

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- Left translation `x ↦ g * x` by a `k`-point `g`. Named consumer: the stabilizer argument for
the general curve-coset lemma. -/
def leftMul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  (toUnit G ≫ g) * 𝟙 G

/-- Right translation `x ↦ x * g` by a `k`-point `g`. -/
def rightMul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  𝟙 G * (toUnit G ≫ g)

variable {G}

/-- Left translation of a generalized point `p : X ⟶ G`. -/
theorem comp_leftMul {X : Over (Spec (.of k))} (p : X ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : p ≫ leftMul G g = (toUnit X ≫ g) * p := by
  change p ≫ ((toUnit G ≫ g) * 𝟙 G) = _
  rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id]

/-- Right translation of a generalized point `p : X ⟶ G`. -/
theorem comp_rightMul {X : Over (Spec (.of k))} (p : X ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : p ≫ rightMul G g = p * (toUnit X ≫ g) := by
  change p ≫ (𝟙 G * (toUnit G ≫ g)) = _
  rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id]

/-- On `k`-points, left translation is left multiplication in `G(k)`. -/
theorem point_comp_leftMul (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    p ≫ leftMul G g = g * p := by
  rw [comp_leftMul, toUnit_unit, Category.id_comp]

/-- On `k`-points, right translation is right multiplication in `G(k)`. -/
theorem point_comp_rightMul (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    p ≫ rightMul G g = p * g := by
  rw [comp_rightMul, toUnit_unit, Category.id_comp]

theorem leftMul_comp_leftMul (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    leftMul G g ≫ leftMul G h = leftMul G (h * g) := by
  rw [comp_leftMul]
  change (toUnit G ≫ h) * ((toUnit G ≫ g) * 𝟙 G) = (toUnit G ≫ (h * g)) * 𝟙 G
  rw [← _root_.mul_assoc, MonObj.comp_mul]

theorem rightMul_comp_rightMul (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    rightMul G g ≫ rightMul G h = rightMul G (g * h) := by
  rw [comp_rightMul]
  change (𝟙 G * (toUnit G ≫ g)) * (toUnit G ≫ h) = 𝟙 G * (toUnit G ≫ (g * h))
  rw [_root_.mul_assoc, MonObj.comp_mul]

theorem leftMul_one : leftMul G 1 = 𝟙 G := by
  change (toUnit G ≫ 1) * 𝟙 G = 𝟙 G
  rw [MonObj.comp_one, _root_.one_mul]

theorem rightMul_one : rightMul G 1 = 𝟙 G := by
  change 𝟙 G * (toUnit G ≫ 1) = 𝟙 G
  rw [MonObj.comp_one, _root_.mul_one]

/-- Left translation by a `k`-point is an automorphism of `G` over `Spec k`. -/
def leftMulIso (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ≅ G where
  hom := leftMul G g
  inv := leftMul G g⁻¹
  hom_inv_id := by rw [leftMul_comp_leftMul, inv_mul_cancel, leftMul_one]
  inv_hom_id := by rw [leftMul_comp_leftMul, mul_inv_cancel, leftMul_one]

/-- Right translation by a `k`-point is an automorphism of `G` over `Spec k`. -/
def rightMulIso (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ≅ G where
  hom := rightMul G g
  inv := rightMul G g⁻¹
  hom_inv_id := by rw [rightMul_comp_rightMul, mul_inv_cancel, rightMul_one]
  inv_hom_id := by rw [rightMul_comp_rightMul, inv_mul_cancel, rightMul_one]

/-- Left translation as a homeomorphism of the underlying space. -/
def leftMulHomeo (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G.left ≃ₜ G.left :=
  Scheme.homeoOfIso ((Over.forget _).mapIso (leftMulIso g))

/-- Right translation as a homeomorphism of the underlying space. -/
def rightMulHomeo (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G.left ≃ₜ G.left :=
  Scheme.homeoOfIso ((Over.forget _).mapIso (rightMulIso g))

theorem leftMulHomeo_apply (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) (x : G.left) :
    leftMulHomeo g x = (leftMul G g).left x :=
  rfl

theorem rightMulHomeo_apply (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) (x : G.left) :
    rightMulHomeo g x = (rightMul G g).left x :=
  rfl

/-- Left translation moves the image point of a `k`-point `p` to that of `g * p`. -/
theorem leftMul_left_apply (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (x : (𝟙_ (Over (Spec (.of k)))).left) :
    (leftMul G g).left (p.left x) = (g * p).left x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, point_comp_leftMul]

/-- Right translation moves the image point of a `k`-point `p` to that of `p * g`. -/
theorem rightMul_left_apply (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (x : (𝟙_ (Over (Spec (.of k)))).left) :
    (rightMul G g).left (p.left x) = (p * g).left x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, point_comp_rightMul]

section AlgClosed

variable [IsAlgClosed k] [LocallyOfFiniteType G.hom]

/-- Over an algebraically closed field, the `k`-points of a group scheme locally of finite type
correspond to its closed points. -/
def pointsEquivClosedPoints : (𝟙_ (Over (Spec (.of k))) ⟶ G) ≃ closedPoints G.left where
  toFun p := pointEquivClosedPoint G.hom ⟨p.left, Over.w p⟩
  invFun x := Over.homMk ((pointEquivClosedPoint G.hom).symm x).1
    ((pointEquivClosedPoint G.hom).symm x).2
  left_inv p := by
    refine Over.OverMorphism.ext ?_
    change ((pointEquivClosedPoint G.hom).symm
      (pointEquivClosedPoint G.hom ⟨p.left, Over.w p⟩)).1 = p.left
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    change pointEquivClosedPoint G.hom ⟨((pointEquivClosedPoint G.hom).symm x).1,
      ((pointEquivClosedPoint G.hom).symm x).2⟩ = x
    rw [Subtype.coe_eta, Equiv.apply_symm_apply]

omit [GrpObj G] in
theorem pointsEquivClosedPoints_apply (p : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (pointsEquivClosedPoints p : G.left) = p.left (IsLocalRing.closedPoint k) :=
  rfl

/-- Left translation by `g` moves the closed point of `p` to the closed point of `g * p`. -/
theorem leftMul_left_pointsEquivClosedPoints (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (leftMul G g).left (pointsEquivClosedPoints p : G.left) =
      (pointsEquivClosedPoints (g * p) : G.left) :=
  leftMul_left_apply p g _

/-- Right translation by `g` moves the closed point of `p` to the closed point of `p * g`. -/
theorem rightMul_left_pointsEquivClosedPoints (p g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (rightMul G g).left (pointsEquivClosedPoints p : G.left) =
      (pointsEquivClosedPoints (p * g) : G.left) :=
  rightMul_left_apply p g _

end AlgClosed

end GroupScheme

end

end AclGeom
