/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AlgebraicGroup
import AclGeom.Correspondence.FunctionFieldEquivalence
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Regular scheme actions and function-field automorphisms

A regular action of an algebraic group `G` on an integral scheme `V` over `Spec k` is a Mathlib
`ModObj G.X V`. A `k`-point `g` of `G` then acts on `V` by the automorphism `x ↦ g • x`
(`CategoryTheory.ModObj.pointAut`, built on Mathlib's action of `T ⟶ G.X` on `T ⟶ V`).

Pulling back functions along these automorphisms gives an action of the `k`-points of `G` on
the function field of `V` by `k`-algebra automorphisms (`functionFieldAction`). Pullback reverses
composition, so the action lands in the opposite group. The `k`-algebra structure of the function
field is derived from the structure morphism of `V` (`functionFieldAlgebra`). If `V` is separated
over `k` and no nontrivial `k`-point acts as the identity of `V`, then the action on the function
field is faithful (`functionFieldAction_injective`).

Scope. The input is a regular scheme action. The source lemma `lem:affine-action` assumes only a
rational action; nothing here regularizes rational actions. The faithfulness hypothesis is the
`k`-point kernel criterion. In characteristic `p` it is weaker than scheme-theoretic faithfulness,
because a non-reduced kernel can have no nontrivial `k`-points.
The actual curve function field is supplied by
`SchemeCurveFunctionField` using the same base algebra. The action on places and the
classification remain open.

**Status:** the regular-action function-field homomorphism and its point-kernel injectivity
criterion are proved. Rational-action regularization and classification remain open.
-/

/-! ### Function-field maps of dominant morphisms -/

namespace AlgebraicGeometry.Scheme

noncomputable section

open CategoryTheory

universe u

variable {X Y Z : Scheme.{u}}

/-- The generic-point morphism of a dominant partial map is the spectrum of its function-field
map. Named consumers: the composition and identity laws below and faithfulness. -/
lemma PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom] :
    f.fromFunctionField = functionFieldMorphismOfHom f.functionFieldMap :=
  functionFieldMorphism_eq_of_functionFieldMapOfMorphism_eq f.fromFunctionField_closedPoint
    (functionFieldMorphismOfHom_closedPoint _)
    (functionFieldMap_functionFieldMorphismOfHom f.functionFieldMap).symm

/-- The generic-point morphism of a morphism is its restriction to the generic stalk. -/
lemma Hom.fromFunctionField_toPartialMap [IrreducibleSpace X] (f : X ⟶ Y) :
    f.toPartialMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f :=
  PartialMap.fromSpecStalkOfMem_toPartialMap f _

/-- Equal dominant morphisms have equal function-field maps. -/
lemma Hom.functionFieldMap_congr [IrreducibleSpace X] [IrreducibleSpace Y] {f g : X ⟶ Y}
    [IsDominant f] [IsDominant g] (h : f = g) :
    f.toPartialMap.functionFieldMap = g.toPartialMap.functionFieldMap := by
  subst h
  rfl

/-- Function-field maps are contravariant: pulling back along `f ≫ g` is pulling back along `g`
and then along `f`. -/
lemma Hom.functionFieldMap_comp [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    (f ≫ g).toPartialMap.functionFieldMap =
      g.toPartialMap.functionFieldMap ≫ f.toPartialMap.functionFieldMap := by
  apply PartialMap.functionFieldMap_eq_of_fromFunctionField_eq_hom
  have hf := PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom f.toPartialMap
  have hg := PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom g.toPartialMap
  rw [Hom.fromFunctionField_toPartialMap] at hf hg ⊢
  change _ = Spec.map _ ≫ Z.fromSpecStalk (genericPoint Z)
  change _ = Spec.map _ ≫ Y.fromSpecStalk (genericPoint Y) at hf
  change _ = Spec.map _ ≫ Z.fromSpecStalk (genericPoint Z) at hg
  rw [← Category.assoc, hf, Category.assoc, hg, Spec.map_comp, Category.assoc]

/-- The identity induces the identity of the function field. -/
lemma Hom.functionFieldMap_id [IsIntegral X] :
    (𝟙 X : X ⟶ X).toPartialMap.functionFieldMap = 𝟙 X.functionField := by
  apply PartialMap.functionFieldMap_eq_of_fromFunctionField_eq_hom
  rw [Hom.fromFunctionField_toPartialMap]
  change _ = Spec.map (𝟙 _) ≫ _
  rw [Spec.map_id, Category.id_comp, Category.comp_id]

/-- The inclusion of the generic stalk of an irreducible scheme is dominant. -/
lemma isDominant_fromSpecStalk_genericPoint [IrreducibleSpace X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) :=
  ⟨by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_closure X]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, fromSpecStalk_closedPoint⟩)⟩

end

end AlgebraicGeometry.Scheme

/-! ### Global points of a group object act by automorphisms -/

namespace CategoryTheory.ModObj

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {M : C} [MonObj M]
  (X : C) [ModObj M X]

/-- A global point `g` of `M` acts on `X` by the endomorphism `x ↦ g • x`. -/
def pointAct (g : 𝟙_ C ⟶ M) : X ⟶ X :=
  (toUnit X ≫ g) • 𝟙 X

lemma pointAct_one : pointAct X (1 : 𝟙_ C ⟶ M) = 𝟙 X := by
  change (toUnit X ≫ (1 : 𝟙_ C ⟶ M)) • 𝟙 X = 𝟙 X
  rw [MonObj.comp_one, _root_.one_smul]

/-- `(g * h) • x = g • (h • x)`; diagrammatically, first `h` and then `g`. -/
lemma pointAct_mul (g h : 𝟙_ C ⟶ M) :
    pointAct X (g * h) = pointAct X h ≫ pointAct X g := by
  change (toUnit X ≫ (g * h)) • 𝟙 X = ((toUnit X ≫ h) • 𝟙 X) ≫ ((toUnit X ≫ g) • 𝟙 X)
  rw [MonObj.comp_mul, ← smul_smul, ModObj.comp_smul, ← Category.assoc, comp_toUnit,
    Category.comp_id]

end

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {M : C} [GrpObj M]
  (X : C) [ModObj M X]

/-- Global points of a group object act on `X` by automorphisms. -/
def pointAut : (𝟙_ C ⟶ M) →* Aut X where
  toFun g :=
    { hom := pointAct X g
      inv := pointAct X g⁻¹
      hom_inv_id := by rw [← pointAct_mul, inv_mul_cancel, pointAct_one]
      inv_hom_id := by rw [← pointAct_mul, mul_inv_cancel, pointAct_one] }
  map_one' := Iso.ext (pointAct_one X)
  map_mul' g h := Iso.ext (pointAct_mul X g h)

end CategoryTheory.ModObj

/-! ### The function-field action -/

namespace AclGeom.ActionFunctionField

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

universe u

variable {k : Type u} [Field k]

/-- The structure morphism of a nonempty scheme over a field is dominant. -/
lemma isDominant_hom (V : Over (Spec (.of k))) [Nonempty V.left] : IsDominant V.hom :=
  have : Surjective V.hom := ⟨fun _ ↦ ⟨Classical.arbitrary V.left, Subsingleton.elim _ _⟩⟩
  inferInstance

/-- Mathlib's fraction-field algebra structure on the function field of `Spec k`. Instance
search does not find it at `CommRingCat.of k`, so it is instantiated here. -/
@[instance_reducible]
def specFunctionFieldAlgebra : Algebra k (Spec (.of k)).functionField :=
  (fun (R : CommRingCat.{u}) [IsDomain R] ↦ (inferInstance : Algebra R (Spec R).functionField))
    (.of k)

attribute [local instance] specFunctionFieldAlgebra

/-- The `k`-algebra structure of the function field of an integral scheme over `Spec k`, pulled
back from the function field of `Spec k` along the structure morphism. -/
@[instance_reducible]
def functionFieldAlgebra (V : Over (Spec (.of k))) [IsIntegral V.left] :
    Algebra k V.left.functionField :=
  have := isDominant_hom V
  (V.hom.toPartialMap.functionFieldMap.hom.comp
    (algebraMap k (Spec (.of k)).functionField)).toAlgebra

attribute [local instance] functionFieldAlgebra

/-- The scheme isomorphism underlying an isomorphism over `Spec k`. -/
lemma isIso_hom_left {V W : Over (Spec (.of k))} (e : V ≅ W) : IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget _).map e.hom))

/-- The inverse scheme isomorphism underlying an isomorphism over `Spec k`. -/
lemma isIso_inv_left {V W : Over (Spec (.of k))} (e : V ≅ W) : IsIso e.inv.left :=
  inferInstanceAs (IsIso ((Over.forget _).map e.inv))

attribute [local instance] isIso_hom_left isIso_inv_left

/-- Pulling back functions along a dominant morphism over `Spec k` is `k`-linear. -/
lemma functionFieldMap_algebraMap {V W : Over (Spec (.of k))} [IsIntegral V.left]
    [IsIntegral W.left] (f : V ⟶ W) [IsDominant f.left] (c : k) :
    f.left.toPartialMap.functionFieldMap.hom (algebraMap k W.left.functionField c) =
      algebraMap k V.left.functionField c := by
  have := isDominant_hom V
  have := isDominant_hom W
  change (W.hom.toPartialMap.functionFieldMap ≫ f.left.toPartialMap.functionFieldMap).hom
      (algebraMap k (Spec (.of k)).functionField c) =
    V.hom.toPartialMap.functionFieldMap.hom (algebraMap k (Spec (.of k)).functionField c)
  rw [← Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_congr (Over.w f)]

/-- The function-field isomorphism induced by an automorphism over `Spec k`. -/
def fieldIso {V : Over (Spec (.of k))} [IsIntegral V.left] (e : V ≅ V) :
    V.left.functionField ≅ V.left.functionField where
  hom := e.hom.left.toPartialMap.functionFieldMap
  inv := e.inv.left.toPartialMap.functionFieldMap
  hom_inv_id := (Scheme.Hom.functionFieldMap_comp e.inv.left e.hom.left).symm.trans
    ((Scheme.Hom.functionFieldMap_congr
      (by rw [← Over.comp_left, e.inv_hom_id, Over.id_left])).trans Scheme.Hom.functionFieldMap_id)
  inv_hom_id := (Scheme.Hom.functionFieldMap_comp e.hom.left e.inv.left).symm.trans
    ((Scheme.Hom.functionFieldMap_congr
      (by rw [← Over.comp_left, e.hom_inv_id, Over.id_left])).trans Scheme.Hom.functionFieldMap_id)

/-- The `k`-algebra automorphism of the function field induced by an automorphism over
`Spec k`. -/
def algEquivOfIso {V : Over (Spec (.of k))} [IsIntegral V.left] (e : V ≅ V) :
    V.left.functionField ≃ₐ[k] V.left.functionField :=
  AlgEquiv.ofRingEquiv (f := (fieldIso e).commRingCatIsoToRingEquiv)
    (functionFieldMap_algebraMap e.hom)

/-- `algEquivOfIso e` pulls back functions along `e`. -/
theorem algEquivOfIso_apply {V : Over (Spec (.of k))} [IsIntegral V.left] (e : V ≅ V)
    (x : V.left.functionField) :
    algEquivOfIso e x = e.hom.left.toPartialMap.functionFieldMap.hom x :=
  rfl

lemma algEquivOfIso_refl {V : Over (Spec (.of k))} [IsIntegral V.left] :
    algEquivOfIso (Iso.refl V) = 1 :=
  AlgEquiv.ext fun x ↦
    congrArg (fun φ ↦ φ.hom x) (Scheme.Hom.functionFieldMap_id (X := V.left))

/-- Pullback reverses composition. -/
lemma algEquivOfIso_trans {V : Over (Spec (.of k))} [IsIntegral V.left] (e e' : V ≅ V) :
    algEquivOfIso (e ≪≫ e') = algEquivOfIso e * algEquivOfIso e' :=
  AlgEquiv.ext fun x ↦
    congrArg (fun φ ↦ φ.hom x) (Scheme.Hom.functionFieldMap_comp e.hom.left e'.hom.left)

/-- An automorphism over `Spec k` of an integral separated scheme which is the identity on the
function field is the identity. -/
lemma eq_refl_of_algEquivOfIso_eq_one {V : Over (Spec (.of k))} [IsIntegral V.left]
    [IsSeparated V.hom] (e : V ≅ V) (he : algEquivOfIso e = 1) : e = Iso.refl V := by
  have hK : e.hom.left.toPartialMap.functionFieldMap = 𝟙 V.left.functionField := by
    ext x
    exact congrArg (fun σ : V.left.functionField ≃ₐ[k] V.left.functionField ↦ σ x) he
  have h1 := Scheme.PartialMap.fromFunctionField_eq_functionFieldMorphismOfHom
    e.hom.left.toPartialMap
  rw [Scheme.Hom.fromFunctionField_toPartialMap, hK] at h1
  change _ = Spec.map (𝟙 _) ≫ _ at h1
  rw [Spec.map_id, Category.id_comp] at h1
  have := Scheme.isDominant_fromSpecStalk_genericPoint (X := V.left)
  have he' : e.hom.left = 𝟙 V.left :=
    ext_of_isDominant_of_isSeparated V.hom ((Over.w e.hom).trans (Category.id_comp _).symm)
      (V.left.fromSpecStalk (genericPoint V.left)) (h1.trans (Category.comp_id _).symm)
  exact Iso.ext (Over.OverMorphism.ext he')

/-- Automorphisms of an integral scheme over `Spec k` act on its function field by pullback.
Pullback reverses composition, so the action lands in the opposite group. -/
def autFunctionField (V : Over (Spec (.of k))) [IsIntegral V.left] :
    Aut V →* (V.left.functionField ≃ₐ[k] V.left.functionField)ᵐᵒᵖ where
  toFun e := MulOpposite.op (algEquivOfIso e)
  map_one' := by
    change MulOpposite.op (algEquivOfIso (Iso.refl V)) = 1
    rw [algEquivOfIso_refl, MulOpposite.op_one]
  map_mul' e e' :=
    (congrArg MulOpposite.op (algEquivOfIso_trans e' e)).trans (MulOpposite.op_mul _ _)

/-- **The function-field action of a regular scheme action.** A `k`-point `g` of `G` acts on the
function field of `V` by pulling back functions along `x ↦ g • x`. -/
def functionFieldAction (G : AlgebraicGroup k) (V : Over (Spec (.of k))) [IsIntegral V.left]
    [ModObj G.toGroupScheme.X V] :
    (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →*
      (V.left.functionField ≃ₐ[k] V.left.functionField)ᵐᵒᵖ :=
  (autFunctionField V).comp (ModObj.pointAut V)

/-- An automorphism over `Spec k` of an integral separated scheme is determined by its action on
the function field. -/
theorem autFunctionField_injective (V : Over (Spec (.of k))) [IsIntegral V.left]
    [IsSeparated V.hom] : Function.Injective (autFunctionField V) := by
  rw [injective_iff_map_eq_one]
  intro e he
  exact eq_refl_of_algEquivOfIso_eq_one e (MulOpposite.op_injective he)

/-- **Faithfulness transfers to the function field.** If `V` is separated over `k` and no
nontrivial `k`-point of `G` acts as the identity of `V`, then `G(k)` acts faithfully on the
function field of `V`. The hypothesis is the `k`-point kernel criterion, not scheme-theoretic
faithfulness. -/
theorem functionFieldAction_injective (G : AlgebraicGroup k) (V : Over (Spec (.of k)))
    [IsIntegral V.left] [IsSeparated V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X, ModObj.pointAct V g = 𝟙 V →
      g = 1) :
    Function.Injective (functionFieldAction G V) := by
  have h2 : Function.Injective
      (ModObj.pointAut V : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* Aut V) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact hker g (congrArg Iso.hom hg)
  exact (autFunctionField_injective V).comp h2

end

end AclGeom.ActionFunctionField
