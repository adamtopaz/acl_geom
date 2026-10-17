/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.SchemeParameterAction
import AclGeom.Correspondence.SchemeFunctionFieldBase
import AclGeom.Correspondence.RegularACF
import AclGeom.Curves.TensorFractionFields

/-!
# The actual generic translate of a regular scheme action

The generic point of an integral group scheme supplies its parameter over its own function
field. An actual regular action on an affine scheme consequently gives the generic translate
on the total fraction ring of the tensor product with its global sections.
Named consumer: the coefficient-field reparametrization in the curve-action genus argument.

**Status:** proved for regular actions on integral affine schemes over an ACF base.
`SchemeEffectiveFunctionField` constructs the effective-field action and faithful coefficient
variation for a given family and field evaluation. `SchemeActionGenus` chooses the actual chart
and proves genus zero after constants in the faithful regular-affine curve case. Original-base
genus descent and arbitrary-action classification remain open.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-- The actual base algebra on global sections. Named consumer: `sectionsSpecIso`. -/
@[instance_reducible]
def sectionsAlgebra (V : Over (Spec (.of k))) : Algebra k Γ(V.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop).hom.toAlgebra

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra

/-- The affine spectrum presentation respects the actual base morphism.
Named consumer: transporting the actual regular action to its coordinate ring. -/
def sectionsSpecIso (V : Over (Spec (.of k))) [IsAffine V.left] :
    V ≅ (Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k)) := by
  refine Over.isoMk V.left.isoSpec ?_
  change V.left.isoSpec.hom ≫
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop) = V.hom
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The actual generic point, over the original base field with its derived base algebra.
Named consumer: `genericTranslate`. -/
def genericParameter (H : Over (Spec (.of k))) [IsIntegral H.left] :
    (Spec H.left.functionField).asOver (Spec (.of k)) ⟶ H := by
  have : Nonempty (⊤ : H.left.Opens) := ⟨⟨genericPoint H.left, trivial⟩⟩
  refine Over.homMk (H.left.fromSpecStalk (genericPoint H.left)) ?_
  change H.left.fromSpecStalk (genericPoint H.left) ≫ H.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k H.left.functionField))
  rw [ActionFunctionField.functionFieldAlgebra_eq_germ H]
  change H.left.fromSpecStalk (genericPoint H.left) ≫ H.hom =
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ H.hom.appTop ≫
      H.left.germToFunctionField ⊤)
  apply (cancel_mono (Spec (.of k)).toSpecΓ).mp
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ]
  change Spec.map (H.left.germToFunctionField ⊤) ≫ Spec.map H.hom.appTop =
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ H.hom.appTop ≫
      H.left.germToFunctionField ⊤) ≫ (Spec (.of k)).isoSpec.hom
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp, ← Spec.map_comp,
    Iso.hom_inv_id_assoc]

/-- The tensor-coordinate action from the given action on the actual affine scheme.
Named consumer: the coefficient-field reparametrization of the generic translate. -/
def sectionsTensorAut {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    (A ⊗[k] Γ(V.left, ⊤)) ≃ₐ[A] (A ⊗[k] Γ(V.left, ⊤)) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  let : ModObj G ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) :=
    ModObj.ofIso (Iso.refl G) (sectionsSpecIso V)
  exact SchemeParameterAction.tensorAut (R := Γ(V.left, ⊤)) g

/-- The actual generic translate, with its parameter chosen internally from the group.
Named consumer: the curve-action genus producer. -/
def genericTranslate (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V] :
    FractionRing (G.left.functionField ⊗[k] Γ(V.left, ⊤)) ≃ₐ[G.left.functionField]
      FractionRing (G.left.functionField ⊗[k] Γ(V.left, ⊤)) :=
  IsFractionRing.algEquivOfAlgEquiv (sectionsTensorAut V (genericParameter G))

/-- The canonical global-section and generic-stalk base algebras form a scalar tower.
Named consumer: the actual affine scheme/function-field comparison. -/
theorem sections_functionField_isScalarTower (V : Over (Spec (.of k))) [IsIntegral V.left] :
    letI : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
    IsScalarTower k Γ(V.left, ⊤) V.left.functionField := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  rw [ActionFunctionField.functionFieldAlgebra_eq_germ V]
  let : Algebra k V.left.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop ≫
      V.left.germToFunctionField ⊤).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := k) (S := Γ(V.left, ⊤))
    (A := V.left.functionField) (fun _ ↦ rfl)

/-- The fraction field of the actual affine coordinate ring, as a base-field algebra.
Named consumer: comparing the actual generic translate with the curve field library. -/
def sectionsFunctionFieldEquiv (V : Over (Spec (.of k))) [IsIntegral V.left]
    [IsAffine V.left] : FractionRing Γ(V.left, ⊤) ≃ₐ[k] V.left.functionField := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsScalarTower k Γ(V.left, ⊤) V.left.functionField :=
    sections_functionField_isScalarTower V
  exact (IsLocalization.algEquiv (nonZeroDivisors Γ(V.left, ⊤))
    (FractionRing Γ(V.left, ⊤)) V.left.functionField).restrictScalars k

/-- The actual field comparison sends a coordinate fraction to its generic germ.
Named consumer: the tensor-function-field comparison. -/
theorem sectionsFunctionFieldEquiv_algebraMap (V : Over (Spec (.of k))) [IsIntegral V.left]
    [IsAffine V.left] (r : Γ(V.left, ⊤)) :
    sectionsFunctionFieldEquiv V (algebraMap Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤)) r) =
      V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsScalarTower k Γ(V.left, ⊤) V.left.functionField :=
    sections_functionField_isScalarTower V
  change (IsLocalization.algEquiv (nonZeroDivisors Γ(V.left, ⊤))
      (FractionRing Γ(V.left, ⊤)) V.left.functionField)
        (algebraMap Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤)) r) =
    algebraMap Γ(V.left, ⊤) V.left.functionField r
  exact AlgEquiv.commutes _ r

/-- The actual affine coordinate domain stays a domain under field extension of an ACF base.
Named consumer: the actual generic-action tensor-function-field comparison. -/
theorem isDomain_tensor_sections [IsAlgClosed k] (C : Type u) [Field C] [Algebra k C]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left] :
    IsDomain (C ⊗[k] Γ(V.left, ⊤)) := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsScalarTower k Γ(V.left, ⊤) V.left.functionField :=
    sections_functionField_isScalarTower V
  have : IsDomain (C ⊗[k] V.left.functionField) := isDomain_tensorProduct_of_isAlgClosed
  let f : Γ(V.left, ⊤) →ₐ[k] V.left.functionField :=
    IsScalarTower.toAlgHom k Γ(V.left, ⊤) V.left.functionField
  let g : C ⊗[k] Γ(V.left, ⊤) →ₐ[k] C ⊗[k] V.left.functionField :=
    Algebra.TensorProduct.map (AlgHom.id k C) f
  have hg : Function.Injective g := Module.Flat.lTensor_preserves_injective_linearMap
    (M := C) f.toLinearMap (IsFractionRing.injective Γ(V.left, ⊤) V.left.functionField)
  exact Function.Injective.isDomain g hg

/-- Extending constants before or after passing to the actual affine function field gives
one field, with the literal generic-germ formula. Named consumer: the actual generic translate. -/
theorem exists_tensorSections_functionFieldEquiv [IsAlgClosed k]
    (C : Type u) [Field C] [Algebra k C]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left] :
    ∃ e : FractionRing (C ⊗[k] V.left.functionField) ≃ₐ[C]
        FractionRing (C ⊗[k] Γ(V.left, ⊤)),
      ∀ (c : C) (r : Γ(V.left, ⊤)),
        e (algebraMap (C ⊗[k] V.left.functionField) _
          (c ⊗ₜ[k] V.left.germToFunctionField ⊤
            (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r)) =
          algebraMap (C ⊗[k] Γ(V.left, ⊤)) _ (c ⊗ₜ[k] r) := by
  have : IsDomain (C ⊗[k] Γ(V.left, ⊤)) := isDomain_tensor_sections C V
  obtain ⟨_, e₂, he₂⟩ := isDomain_and_exists_tensorFractionEquiv
    (k := k) (C := C) (A := Γ(V.left, ⊤))
  let et : C ⊗[k] V.left.functionField ≃ₐ[C] C ⊗[k] FractionRing Γ(V.left, ⊤) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) (sectionsFunctionFieldEquiv V).symm
  let el : FractionRing (C ⊗[k] V.left.functionField) ≃ₐ[C]
      FractionRing (C ⊗[k] FractionRing Γ(V.left, ⊤)) :=
    IsFractionRing.algEquivOfAlgEquiv et
  refine ⟨el.trans e₂, fun c r ↦ ?_⟩
  have hh : (sectionsFunctionFieldEquiv V).symm
      (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r) =
        algebraMap Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤)) r := by
    rw [← sectionsFunctionFieldEquiv_algebraMap V r, AlgEquiv.symm_apply_apply]
  change e₂ (IsFractionRing.algEquivOfAlgEquiv et
    (algebraMap (C ⊗[k] V.left.functionField) _ _)) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change e₂ (algebraMap (C ⊗[k] FractionRing Γ(V.left, ⊤)) _
    (c ⊗ₜ[k] (sectionsFunctionFieldEquiv V).symm
      (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r))) = _
  rw [hh]
  exact he₂ c r

/-- Construct the actual generic action on the formal constant extension of the same curve
function field. Both the generic parameter and the coordinate-field comparison are internal.
Named consumer: the source curve-action genus producer. -/
theorem exists_functionField_genericTranslate [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left] [ModObj G V] :
    ∃ (σ : FractionRing (G.left.functionField ⊗[k] V.left.functionField) ≃ₐ[G.left.functionField]
          FractionRing (G.left.functionField ⊗[k] V.left.functionField))
      (e : FractionRing (G.left.functionField ⊗[k] V.left.functionField) ≃ₐ[G.left.functionField]
          FractionRing (G.left.functionField ⊗[k] Γ(V.left, ⊤))),
      (∀ (c : G.left.functionField) (r : Γ(V.left, ⊤)),
        e (algebraMap (G.left.functionField ⊗[k] V.left.functionField) _
          (c ⊗ₜ[k] V.left.germToFunctionField ⊤
            (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r)) =
          algebraMap (G.left.functionField ⊗[k] Γ(V.left, ⊤)) _ (c ⊗ₜ[k] r)) ∧
      ∀ x, e (σ x) = genericTranslate G V (e x) := by
  obtain ⟨e, he⟩ := exists_tensorSections_functionFieldEquiv G.left.functionField V
  refine ⟨e.trans ((genericTranslate G V).trans e.symm), e, he, fun x ↦ ?_⟩
  change e (e.symm (genericTranslate G V (e x))) = _
  exact e.apply_symm_apply _

end

end AclGeom.SchemeGenericTranslate
