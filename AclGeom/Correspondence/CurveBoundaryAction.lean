/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveBoundaryTopology
import AclGeom.Correspondence.ActionFunctionField

/-!
# Actual equivariant curve opens preserve their boundary

**Status:** proved over every field for actual equivariant maps of schemes with regular group
actions. Every actual point automorphism preserves the complement of the image. The actual
orbit morphism specializes to the actual point action. Named consumer: joint boundary
fixedness.

The regular action on the ambient curve is an actual input. Completion construction, the
scheme API from smoothness to local normality, joint regularity of extended rational families,
rational-action regularization and the full original classifier remain owed. Original
group/chunk/six-point statements, algebraization/descent and every true bypassed auxiliary
remain obligations. All eight original #21 work items and the full durable goal remain active
and incomplete.
-/

namespace AclGeom.CurveBoundary
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k]

/-- Actual equivariant morphisms commute with every actual point automorphism.
Named consumer: invariance of the literal open boundary. -/
theorem pointAct_naturality
    {G U V : Over (Spec (.of k))} [GrpObj G] [ModObj G U] [ModObj G V]
    (j : U ⟶ V) [IsModHom G j] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ModObj.pointAct U g ≫ j = j ≫ ModObj.pointAct V g := by
  change ((toUnit U ≫ g) • 𝟙 U) ≫ j = j ≫ ((toUnit V ≫ g) • 𝟙 V)
  rw [IsModHom.map_smul, ModObj.comp_smul]
  simp only [Category.id_comp, Category.comp_id, comp_toUnit_assoc]

/-- The actual complement of an equivariant image is stable under every point automorphism.
Named consumer: boundary orbit maps of a connected actual algebraic group. -/
theorem pointAct_mem_complement
    {G U V : Over (Spec (.of k))} [GrpObj G] [ModObj G U] [ModObj G V]
    (j : U ⟶ V) [IsModHom G j] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (x : V.left) (hx : x ∉ Set.range j.left) :
    (ModObj.pointAct V g).left x ∉ Set.range j.left := by
  rintro ⟨y, hy⟩
  apply hx
  refine ⟨(ModObj.pointAct U g⁻¹).left y, ?_⟩
  have hn := congrArg (fun f : U ⟶ V ↦ f.left y) (pointAct_naturality j g⁻¹)
  have hi := congrArg (fun f : V ⟶ V ↦ f.left x) (ModObj.pointAut V g).hom_inv_id
  exact hn.trans ((congrArg (ModObj.pointAct V g⁻¹).left hy).trans hi)

/-- The actual orbit morphism of a base-field point. Named consumer: joint boundary fixedness. -/
def orbitMap
    (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [ModObj G.toGroupScheme.X V]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ V) : G.toGroupScheme.X ⟶ V :=
  lift (𝟙 _) (toUnit G.toGroupScheme.X ≫ p) ≫ γ[G.toGroupScheme.X, V]

/-- Specializing the actual orbit morphism is the actual action on points.
Named consumer: the actual joint fixed-boundary theorem. -/
theorem orbitMap_point
    (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [ModObj G.toGroupScheme.X V]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ V)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    g ≫ orbitMap G V p = p ≫ ModObj.pointAct V g := by
  change g ≫ lift (𝟙 _) (toUnit G.toGroupScheme.X ≫ p) ≫ _ =
    p ≫ ((toUnit V ≫ g) • 𝟙 V)
  rw [comp_lift_assoc, ModObj.comp_smul]
  simp only [Category.comp_id, comp_toUnit_assoc, toUnit_unit, Category.id_comp,
    Hom.smul_def]

end
end AclGeom.CurveBoundary
