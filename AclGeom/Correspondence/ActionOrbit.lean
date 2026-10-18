/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ActionFunctionField

/-!
# Actual orbit maps and their joint action diagram

**Status:** actual orbit maps, their base-point slices and joint translation diagram are
proved in any Cartesian monoidal category. Named consumer: the finite Ga orbit cover in
`AdditiveOrbit.exists_finite_orbit_cover` (#21). These categorical identities alone make no
claim about finiteness, surjectivity or existence of a moved point.
-/

namespace AclGeom.AdditiveOrbit
noncomputable section
open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N X : C} [MonObj M] [ModObj M X]

/-- The actual regular orbit map. Named consumer: the finite Ga orbit cover. -/
def orbitMap (i : N ⟶ M) (p : 𝟙_ C ⟶ X) : N ⟶ X :=
  i • (toUnit N ≫ p)

/-- Named consumer: the internally chosen moved point makes the actual orbit nonconstant. -/
theorem point_comp_orbitMap (i : N ⟶ M) (p : 𝟙_ C ⟶ X) (q : 𝟙_ C ⟶ N) :
    q ≫ orbitMap i p = p ≫ ModObj.pointAct X (q ≫ i) := by
  change q ≫ (i • (toUnit N ≫ p)) = p ≫ ((toUnit X ≫ (q ≫ i)) • 𝟙 X)
  simp only [ModObj.comp_smul, Category.comp_id]
  simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]

/-- The actual joint translation-action diagram. Named consumer: the finite Ga orbit cover. -/
theorem mul_comp_orbitMap [MonObj N] (i : N ⟶ M) [IsMonHom i] (p : 𝟙_ C ⟶ X) :
    μ[N] ≫ orbitMap i p =
      lift (fst N N ≫ i) (snd N N ≫ orbitMap i p) ≫ γ[M, X] := by
  have hmul : μ[N] ≫ i = (fst N N ≫ i) * (snd N N ≫ i) := by
    rw [IsMonHom.mul_hom, Hom.mul_def, lift_fst_comp_snd_comp]
  change μ[N] ≫ (i • (toUnit N ≫ p)) =
    (fst N N ≫ i) • (snd N N ≫ (i • (toUnit N ≫ p)))
  rw [ModObj.comp_smul, ModObj.comp_smul, hmul]
  simp only [← Category.assoc, comp_toUnit]
  exact mul_smul _ _ _
end
end AclGeom.AdditiveOrbit
