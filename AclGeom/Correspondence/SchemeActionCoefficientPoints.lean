/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeGenericTranslate
import AclGeom.Correspondence.HopfSpecPoints
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Actual action coefficients determine field-valued chart points

Named consumer: coefficient-field algebraicity and rank in the actual regular-affine
curve genus theorem.

**Status:** the generic finite-matrix criterion is proved over every field. Its matrix and
generator premises are supplied internally by `SchemeActionGenus`; its faithfulness premise
is the genuine global-point kernel criterion, not infinitesimal faithfulness.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

private theorem parameterAct_injective_of_point_kernel
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {G : C} [GrpObj G] (X : C) [ModObj G X] {T : C}
    (e : 𝟙_ C ≅ T)
    (hker : ∀ q : 𝟙_ C ⟶ G, ModObj.pointAct X q = 𝟙 X → q = 1) :
    Function.Injective (ModObj.parameterAct X : (T ⟶ G) → (T ⊗ X ⟶ T ⊗ X)) := by
  have hinj : Function.Injective
      (ModObj.pointAut X : (𝟙_ C ⟶ G) →* Aut X) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    exact hker q (congrArg Iso.hom hq)
  have hq (q : T ⟶ G) :
      (λ_ X).inv ≫ (e.hom ⊗ₘ 𝟙 X) ≫ ModObj.parameterAct X q ≫ snd T X =
        ModObj.pointAct X (e.hom ≫ q) := by
    change (λ_ X).inv ≫ (e.hom ⊗ₘ 𝟙 X) ≫ ModObj.parameterAct X q ≫ snd T X =
      (toUnit X ≫ e.hom ≫ q) • 𝟙 X
    rw [ModObj.parameterAct_snd, ModObj.comp_smul, ModObj.comp_smul]
    simp only [tensorHom_fst_assoc, tensorHom_snd, Category.comp_id,
      leftUnitor_inv_fst_assoc, leftUnitor_inv_snd]
  intro a b hab
  apply (cancel_epi e.hom).mp
  apply hinj
  apply Iso.ext
  change ModObj.pointAct X (e.hom ≫ a) = ModObj.pointAct X (e.hom ≫ b)
  rw [← hq a, ← hq b, hab]

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

private theorem sectionsTensorAut_injective_of_point_kernel
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1) :
    Function.Injective (sectionsTensorAut V :
      ((Spec (.of k)).asOver (Spec (.of k)) ⟶ G) →
        (k ⊗[k] Γ(V.left, ⊤) ≃ₐ[k] k ⊗[k] Γ(V.left, ⊤))) := by
  let W := (Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))
  let e := sectionsSpecIso V
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  let : ModObj G W := ModObj.ofIso (Iso.refl G) e
  have : IsModHom G e.hom := by
    constructor
    change γ[G, V] ≫ e.hom =
      (𝟙 G ⊗ₘ e.hom) ≫ (𝟙 G ⊗ₘ e.inv) ≫ γ[G, V] ≫ e.hom
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, e.hom_inv_id, tensorHom_id, id_whiskerRight]
  have hkerW (q : 𝟙_ (Over (Spec (.of k))) ⟶ G)
      (hq : ModObj.pointAct W q = 𝟙 W) : q = 1 := by
    apply hker q
    apply (cancel_mono e.hom).mp
    have he : ModObj.pointAct V q ≫ e.hom = e.hom ≫ ModObj.pointAct W q := by
      change (((toUnit V) ≫ q) • 𝟙 V) ≫ e.hom =
        e.hom ≫ (((toUnit W) ≫ q) • 𝟙 W)
      rw [IsModHom.map_smul, ModObj.comp_smul, Category.id_comp, Category.comp_id,
        ← Category.assoc, comp_toUnit]
    rw [he, hq, Category.comp_id, Category.id_comp]
  intro a b hab
  apply parameterAct_injective_of_point_kernel W (unitIsoSpecAsOver k) hkerW
  apply Over.OverMorphism.ext
  have hmap := congrArg (fun τ : k ⊗[k] Γ(V.left, ⊤) ≃ₐ[k]
      k ⊗[k] Γ(V.left, ⊤) ↦ Spec.map (CommRingCat.ofHom τ.toRingHom)) hab
  change SchemeParameterAction.tensorAut a = SchemeParameterAction.tensorAut b at hab
  change Spec.map (CommRingCat.ofHom (SchemeParameterAction.tensorAut a).toRingHom) =
    Spec.map (CommRingCat.ofHom (SchemeParameterAction.tensorAut b).toRingHom) at hmap
  rw [SchemeParameterAction.spec_map_tensorAut,
    SchemeParameterAction.spec_map_tensorAut] at hmap
  apply (cancel_epi (pullbackSpecIso k k Γ(V.left, ⊤)).inv).mp
  apply (cancel_mono (pullbackSpecIso k k Γ(V.left, ⊤)).hom).mp
  exact (Category.assoc _ _ _).trans (hmap.trans (Category.assoc _ _ _).symm)

/-- Agreement on the actual raw coefficient algebra determines a chart point, under the genuine
point-action kernel criterion. Named consumer: algebraicity and rank of the actual coefficient
field. The finite matrix is constructed internally in that consumer. -/
theorem coefficient_points_injective
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) [Mono g]
    (s : Finset Γ(V.left, ⊤)) (hs : Algebra.adjoin k (s : Set Γ(V.left, ⊤)) = ⊤)
    {n : ℕ} (v : Fin n → Γ(V.left, ⊤)) (cA : Bool → s → Fin n → A)
    (hc : ∀ (φ : A →ₐ[k] k) (i : s),
      sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)
        (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) = ∑ j, φ (cA true i j) ⊗ₜ[k] v j) :
    let B := Algebra.adjoin k (Set.range fun p : Bool × s × Fin n ↦ cA p.1 p.2.1 p.2.2)
    Function.Injective (fun φ : A →ₐ[k] k ↦ φ.comp B.val) := by
  classical
  let B := Algebra.adjoin k (Set.range fun p : Bool × s × Fin n ↦ cA p.1 p.2.1 p.2.2)
  change Function.Injective (fun φ : A →ₐ[k] k ↦ φ.comp B.val)
  intro φ ψ h
  have he (e : Bool) (i : s) (j : Fin n) : φ (cA e i j) = ψ (cA e i j) := by
    let b : B := ⟨cA e i j, Algebra.subset_adjoin ⟨(e, i, j), rfl⟩⟩
    exact AlgHom.congr_fun h b
  let a : (Spec (.of k)).asOver (Spec (.of k)) ⟶ G :=
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
  let b : (Spec (.of k)).asOver (Spec (.of k)) ⟶ G :=
    (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op ≫ g
  have haut : sectionsTensorAut V a = sectionsTensorAut V b := by
    have hright : (sectionsTensorAut V a).toAlgHom.comp Algebra.TensorProduct.includeRight =
        (sectionsTensorAut V b).toAlgHom.comp Algebra.TensorProduct.includeRight := by
      apply AlgHom.ext_of_adjoin_eq_top hs
      intro r hr
      change sectionsTensorAut V a (1 ⊗ₜ[k] r) = sectionsTensorAut V b (1 ⊗ₜ[k] r)
      rw [hc φ ⟨r, hr⟩, hc ψ ⟨r, hr⟩]
      apply Finset.sum_congr rfl
      intro j _
      rw [he true ⟨r, hr⟩ j]
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c r =>
      have hr := AlgHom.congr_fun hright r
      change sectionsTensorAut V a (1 ⊗ₜ[k] r) =
        sectionsTensorAut V b (1 ⊗ₜ[k] r) at hr
      have hfactor : c ⊗ₜ[k] r = c • (1 ⊗ₜ[k] r : k ⊗[k] Γ(V.left, ⊤)) := by
        change c ⊗ₜ[k] r = (c • (1 : k)) ⊗ₜ[k] r
        simp only [smul_eq_mul, _root_.mul_one]
      rw [hfactor, map_smul, map_smul, hr]
  have hab := sectionsTensorAut_injective_of_point_kernel V hker haut
  have hf := (cancel_mono g).mp hab
  have hspec := congrArg Over.Hom.left hf
  change Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) at hspec
  have hf' := Spec.map_injective hspec
  ext z
  exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of k ↦ f.hom z) hf'

end

end AclGeom.SchemeGenericTranslate
