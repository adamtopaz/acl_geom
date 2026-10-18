/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.PlaceAction
import AclGeom.Correspondence.SchemeCurveFunctionField

/-!
# Places of an actual curve and the action of a regular scheme action

For an integral curve `V` over an algebraically closed field `k`, locally of finite type and of
scheme dimension one, every place of its function field is a discrete valuation ring
(`isDiscreteValuationRing_place`). The one-variable hypothesis is derived from the curve.

A regular action of an algebraic group `G` on `V` moves the places of the function field:
the `k`-point `g` sends a place to its pullback along the field automorphism of `g`
(`placeAction`). The field action is contravariant and pulling back valuation rings reverses
composition again, so this is a genuine left action. When `V` is affine, the action preserves
the global sections (`map_globalSections`), and therefore permutes the finitely many places
at which some global section has a pole (`placeAction_mem_boundary_iff`, `boundary_finite`).

The function field carries the base algebra derived from the structure morphism, shared with the
curve theorem and the function-field action.

Scope. The action is a regular scheme action. This does not identify closed points with places,
construct a completion, regularize a rational action, or show that a connected group fixes the
boundary; the classification of `lem:affine-action` remains open.

**Status:** proved; the actual scheme and affine-curve consumers are checked independently.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SchemePlaceAction

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj ActionFunctionField

universe u

variable {k : Type u} [Field k]

attribute [local instance] functionFieldAlgebra isIso_hom_left isIso_inv_left

/-- **Places of an actual curve are discrete valuation rings.** The one-variable hypothesis is
derived from the curve itself. -/
theorem isDiscreteValuationRing_place [IsAlgClosed k] (V : Over (Spec (.of k)))
    [IsIntegral V.left] [LocallyOfFiniteType V.hom] (hdim : topologicalKrullDim V.left = 1)
    (P : Place k V.left.functionField) : IsDiscreteValuationRing P.val :=
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdim
  Place.isDiscreteValuationRing P

/-- The `k`-points of `G` act on the places of the function field of `V`. -/
def placeAction (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V] :
    (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →*
      Equiv.Perm (Place k V.left.functionField) :=
  (MulAction.toPermHom _ _).comp (functionFieldAction G V)

/-- A point sends a place to its pullback along the point's field automorphism. -/
theorem placeAction_apply (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    (P : Place k V.left.functionField) :
    placeAction G V g P = P.comap (functionFieldAction G V g).unop :=
  rfl

/-- The global sections of an integral scheme over `Spec k`, as a subalgebra of its function
field. -/
def globalSections (V : Over (Spec (.of k))) [IsIntegral V.left] :
    Subalgebra k V.left.functionField where
  carrier := Set.range (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)).hom
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ a b⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  algebraMap_mem' c := ⟨V.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c), by
    rw [functionFieldAlgebra_eq_germ V]
    rfl⟩

/-- For an affine scheme of finite type over `k`, the global sections are finitely generated. -/
theorem globalSections_fg (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] : (globalSections V).FG := by
  let f : CommRingCat.of k ⟶ Γ(V.left, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop
  have happ := V.hom.finiteType_appLE (isAffineOpen_top (Spec (.of k)))
    (V := V.hom ⁻¹ᵁ ⊤) (isAffineOpen_top V.left) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at happ
  have hf : f.hom.FiniteType := happ.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let _ : Algebra k Γ(V.left, ⊤) := f.hom.toAlgebra
  have : Algebra.FiniteType k Γ(V.left, ⊤) := hf
  let g : Γ(V.left, ⊤) →ₐ[k] V.left.functionField :=
    { (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)).hom with
      commutes' := fun c ↦ by
        rw [functionFieldAlgebra_eq_germ V]
        rfl }
  have hg : globalSections V = g.range := Subalgebra.ext fun _ ↦ Iff.rfl
  rw [hg, ← Algebra.map_top]
  exact Subalgebra.FG.map g Algebra.FiniteType.out

/-- An automorphism over `Spec k` preserves the global sections inside the function field. -/
lemma map_globalSections_algEquivOfIso (V : Over (Spec (.of k))) [IsIntegral V.left]
    (e : V ≅ V) :
    (globalSections V).map (algEquivOfIso e : V.left.functionField →ₐ[k] V.left.functionField) =
      globalSections V := by
  have hc := Scheme.Hom.germToFunctionField_top_comp e.hom.left
  apply le_antisymm
  · rintro _ ⟨x, ⟨r, rfl⟩, rfl⟩
    exact ⟨e.hom.left.appTop.hom r, (congrArg (fun φ ↦ φ.hom r) hc).symm⟩
  · rintro _ ⟨r, rfl⟩
    refine ⟨_, ⟨e.inv.left.appTop.hom r, rfl⟩, ?_⟩
    have hr : e.hom.left.appTop.hom (e.inv.left.appTop.hom r) = r := by
      change (e.inv.left.appTop ≫ e.hom.left.appTop).hom r = r
      rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id, Over.id_left]
      rfl
    exact (congrArg (fun φ ↦ φ.hom (e.inv.left.appTop.hom r)) hc).trans
      (congrArg (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)).hom hr)

/-- The action of a point preserves the global sections inside the function field. -/
theorem map_globalSections (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    (globalSections V).map
        ((functionFieldAction G V g).unop : V.left.functionField →ₐ[k] V.left.functionField) =
      globalSections V :=
  map_globalSections_algEquivOfIso V (ModObj.pointAut V g)

/-- The action of a point permutes the places at which some global section has a pole. -/
theorem placeAction_mem_boundary_iff (G : AlgebraicGroup k) (V : Over (Spec (.of k)))
    [IsIntegral V.left] [ModObj G.toGroupScheme.X V]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) (P : Place k V.left.functionField) :
    placeAction G V g P ∈ Place.boundary (globalSections V) ↔
      P ∈ Place.boundary (globalSections V) :=
  Place.comap_mem_boundary_iff (map_globalSections G V g)

/-- **The boundary of an affine curve is finite.** For an affine integral curve over an
algebraically closed field, only finitely many places of its function field fail to contain the
global sections. Finite generation and the one-variable hypothesis are derived from the curve. -/
theorem boundary_finite [IsAlgClosed k] (V : Over (Spec (.of k))) [IsIntegral V.left]
    [IsAffine V.left] [LocallyOfFiniteType V.hom] (hdim : topologicalKrullDim V.left = 1) :
    (Place.boundary (globalSections V)).Finite :=
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdim
  Place.boundary_finite (globalSections_fg V)

end

end AclGeom.SchemePlaceAction
