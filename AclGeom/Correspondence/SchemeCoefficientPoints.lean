/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.AffineCoefficientSpecialization
import AclGeom.Correspondence.SchemeParameterBaseChange
import AclGeom.Correspondence.SchemeGenericTranslate
import AclGeom.Correspondence.AffineSchemeAction
import AclGeom.Correspondence.HopfSpecPoints

/-!
# Actual coactions and point-action germs

**Status:** proved for regular actions on affine schemes over any field (#21). The actual
global-section tensor action commutes with parameter base change, and its specialization
agrees with the actual point pullback on generic germs for integral schemes. Named consumer:
`SchemeAffineCoefficients` derives its affine specialization hypotheses from these formulas.
-/

namespace AclGeom.AffineCoefficients

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  ActionFunctionField.isIso_hom_left

/-- Base change of the actual global-section tensor action.
 Named consumer: the literal generic-translate/coefficient comparison. -/
theorem sectionsTensorAut_baseChange {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G)
    (z : A ⊗[k] Γ(V.left, ⊤)) :
    Algebra.TensorProduct.map φ (AlgHom.id k Γ(V.left, ⊤)) (sectionsTensorAut V g z) =
      sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)
        (Algebra.TensorProduct.map φ (AlgHom.id k Γ(V.left, ⊤)) z) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  let : ModObj G ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) :=
    ModObj.ofIso (Iso.refl G) (sectionsSpecIso V)
  exact SchemeParameterAction.tensorAut_baseChange φ g z

private theorem sectionsTensorAut_point {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) (φ : A →ₐ[k] k)
    (r : Γ(V.left, ⊤)) :
    (ModObj.pointAct V ((unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).left.appTop r =
        tensorPointEval φ (sectionsTensorAut V g (1 ⊗ₜ[k] r)) := by
  let R : Type u := Γ(V.left, ⊤)
  let W := (Spec (.of R)).asOver (Spec (.of k))
  let e := sectionsSpecIso V
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  let : ModObj G W := ModObj.ofIso (Iso.refl G) e
  have : IsModHom G e.hom := by
    constructor
    change γ[G, V] ≫ e.hom =
      (𝟙 G ⊗ₘ e.hom) ≫ (𝟙 G ⊗ₘ e.inv) ≫ γ[G, V] ≫ e.hom
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, e.hom_inv_id, tensorHom_id, id_whiskerRight]
  let T := (Spec (.of A)).asOver (Spec (.of k))
  let Φ : T ⊗ W ⟶ V := (fst T W ≫ g) • (snd T W ≫ e.inv)
  let ψ : R →+* A ⊗[k] R := (sectionsTensorAut V g).toRingHom.comp
    (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom
  have hΦ : Φ ≫ e.hom = (fst T W ≫ g) • snd T W := by
    change ((fst T W ≫ g) • (snd T W ≫ e.inv)) ≫ e.hom = _
    rw [IsModHom.map_smul, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hψ : Spec.map (CommRingCat.ofHom ψ) =
      ((AffineSchemeAction.tensorSpecIso k A R).inv ≫ Φ ≫ e.hom).left := by
    let f : Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) ⟶ Spec (.of R) :=
      (Φ ≫ e.hom).left
    change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom ≫
      CommRingCat.ofHom (SchemeParameterAction.tensorAut g).toRingHom) =
        (pullbackSpecIso k A R).inv ≫ f
    let p : Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) ⟶
        Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) :=
      (ModObj.parameterAct W g).left
    have hp := SchemeParameterAction.spec_map_tensorAut (R := R) g
    change Spec.map (CommRingCat.ofHom (SchemeParameterAction.tensorAut g).toRingHom) =
      (pullbackSpecIso k A R).inv ≫ p ≫ (pullbackSpecIso k A R).hom at hp
    have hsnd := pullbackSpecIso_hom_snd k A R
    change (pullbackSpecIso k A R).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom) =
        Limits.pullback.snd _ _ at hsnd
    rw [Spec.map_comp, hp, Category.assoc, Category.assoc, hsnd]
    have h := congrArg (fun f : T ⊗ W ⟶ W ↦ f.left)
      (ModObj.parameterAct_snd W g)
    rw [← hΦ] at h
    change p ≫ Limits.pullback.snd _ _ = f at h
    exact congrArg (fun f ↦ (pullbackSpecIso k A R).inv ≫ f) h
  let q : 𝟙_ (Over (Spec (.of k))) ⟶ G := (unitIsoSpecAsOver k).hom ≫
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
  have hpt : q.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.left := by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.left = _
    rw [Category.id_comp]
  let ev : A →ₐ[k] R := (Algebra.ofId k R).comp φ
  have hevH : CommRingCat.ofHom ev.toRingHom =
      CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom (algebraMap k R) := rfl
  have hv : V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = V.hom :=
    Over.w e.hom
  have ha : e.hom ≫ (Spec.map (CommRingCat.ofHom ev.toRingHom)).asOver
      (Spec (.of k)) ≫ g = toUnit V ≫ q := by
    apply Over.OverMorphism.ext
    let g' : Spec (.of A) ⟶ G.left := g.left
    let q' : Spec (.of k) ⟶ G.left := q.left
    have hq' : q' = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g' := hpt
    change V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ g' =
      V.hom ≫ q'
    rw [hevH, Spec.map_comp]
    calc
      _ = (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫
          (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g') := by
        simp only [Category.assoc]
      _ = _ := by rw [hv, hq']
  have hb : e.hom ≫ (Spec.map
      (CommRingCat.ofHom (AlgHom.id k R).toRingHom)).asOver (Spec (.of k)) ≫ e.inv = 𝟙 V := by
    apply Over.OverMorphism.ext
    change V.left.isoSpec.hom ≫ Spec.map (𝟙 _) ≫ V.left.isoSpec.inv = 𝟙 V.left
    rw [Spec.map_id, Category.id_comp, Iso.hom_inv_id]
  have hleft : (ModObj.pointAct V q).left = V.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.lift ev (AlgHom.id k R)
          (fun _ _ ↦ Commute.all _ _)).toRingHom) ≫ V.left.isoSpec.inv := by
    have hh : ModObj.pointAct V q = e.hom ≫
        (lift ((Spec.map (CommRingCat.ofHom ev.toRingHom)).asOver (Spec (.of k)))
          ((Spec.map (CommRingCat.ofHom (AlgHom.id k R).toRingHom)).asOver (Spec (.of k))) ≫
          (AffineSchemeAction.tensorSpecIso k A R).hom) ≫
        ((AffineSchemeAction.tensorSpecIso k A R).inv ≫ Φ ≫ e.hom) ≫ e.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      change (toUnit V ≫ q) • 𝟙 V = e.hom ≫ _ ≫
        ((fst T W ≫ g) • (snd T W ≫ e.inv))
      rw [ModObj.comp_smul, ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc, ha, hb]
    rw [hh, AffineSchemeAction.lift_tensorSpecIso_hom, Spec.map_comp, hψ]
    rfl
  have happ : (ModObj.pointAct V q).left.appTop = CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom (Algebra.TensorProduct.lift ev (AlgHom.id k R)
        (fun _ _ ↦ Commute.all _ _)).toRingHom := by
    apply Spec.map_injective
    rw [← cancel_mono V.left.isoSpec.inv, Scheme.isoSpec_inv_naturality, hleft,
      Iso.inv_hom_id_assoc]
  change ((ModObj.pointAct V q).left.appTop).hom r = _
  rw [happ]
  rfl


/-- The actual parameter coaction specializes to the genuine point action on generic germs.
 Named consumer: pointwise affine hypotheses in the actual rational-coefficient producer. -/
theorem sectionsTensorAut_point_germ (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [ModObj G.toGroupScheme.X V]
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) (φ : A →ₐ[k] k)
    (r : Γ(V.left, ⊤)) :
    (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r) =
      tensorPointEval φ (Algebra.TensorProduct.map (AlgHom.id k A)
        ((sectionsFunctionFieldEquiv V).toAlgHom.comp
          (IsScalarTower.toAlgHom k Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤))))
        (sectionsTensorAut V g (1 ⊗ₜ[k] r))) := by
  let R : Type u := Γ(V.left, ⊤)
  let F : Type u := V.left.functionField
  let f : R →ₐ[k] F := (sectionsFunctionFieldEquiv V).toAlgHom.comp
    (IsScalarTower.toAlgHom k R (FractionRing R))
  have hf (r : R) : f r =
      V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r :=
    sectionsFunctionFieldEquiv_algebraMap V r
  have hnat (z : A ⊗[k] R) : f (tensorPointEval φ z) =
      tensorPointEval φ (Algebra.TensorProduct.map (AlgHom.id k A) f z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a r =>
      change f (algebraMap k R (φ a) * r) = algebraMap k F (φ a) * f r
      rw [map_mul, f.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  let q := (unitIsoSpecAsOver k).hom ≫ (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
  have : IsIso (ModObj.pointAut V q).hom.left :=
    ActionFunctionField.isIso_hom_left (ModObj.pointAut V q)
  have : IsDominant (ModObj.pointAut V q).hom.left := inferInstance
  have hgerm := congrArg (fun z ↦ z.hom r)
    (Scheme.Hom.germToFunctionField_top_comp (ModObj.pointAut V q).hom.left)
  change (ActionFunctionField.functionFieldAction G V q).unop
      (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r) =
    V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)
      ((ModObj.pointAct V q).left.appTop r) at hgerm
  change _ = tensorPointEval φ (Algebra.TensorProduct.map (AlgHom.id k A) f _)
  rw [hgerm, sectionsTensorAut_point V g φ r, ← hf]
  exact hnat _

end

end AclGeom.AffineCoefficients
