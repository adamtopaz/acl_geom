/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.NormalTranslationImage

/-!
# A finite isogeny from the actual normal subgroup to Ga

**Status:** proved criterion over an ACF base (#21). The actual connected normal closed
subgroup of dimension one has a finite surjective group morphism to Ga, injective on
base-field points, factoring the SAME supplied finite affine-group morphism through the
translation inclusion. No presentation of N as Ga is used. Its shift retraction defines
the morphism; reduced-source extensionality proves the factorization, and monic
cancellation gives the group laws. Finiteness is cancelled at the separated target.
Named consumer: `SchemeNormalTranslations.exists_normal_subgroup_translation_isogeny`
constructs the ambient affine morphism internally from the genuine regular-affine action.
No Ga-isomorphism, separability or degree-one conclusion is asserted.
-/

namespace AclGeom.NormalTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The genuine normal subgroup has a finite isogeny to translations, without being
presented as Ga. Named consumer: the actual regular-affine action chooses f internally. -/
theorem exists_finite_isogeny
    (G : AlgebraicGroup k) (N : ConnectedAlgebraicGroup k)
    (i : N.toAlgebraicGroup.Hom G) [IsMonHom.Normal i.hom.hom]
    [IsClosedImmersion i.hom.hom.left]
    (hdimN : topologicalKrullDim N.toAlgebraicGroup.carrier = 1)
    (f : G.Hom (AffineGroupScheme.algebraicGroup k))
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left]
    (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦ q ≫ f.hom.hom)) :
    ∃ β : N.toAlgebraicGroup.Hom (AdditiveGroupScheme.algebraicGroup k 1),
      IsFinite β.hom.hom.left ∧ Surjective β.hom.hom.left ∧
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ N.toGroupScheme.X ↦
        q ≫ β.hom.hom) ∧
      β.hom.hom ≫ AdditiveTranslation.inclusion k = i.hom.hom ≫ f.hom.hom := by
  let NX := N.toGroupScheme.X
  let AX := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let v : NX ⟶ AX := i.hom.hom ≫ f.hom.hom
  let βraw : NX ⟶ L := v ≫ AdditiveTranslation.shift k
  have hrange := image_eq_translations G N i hdimN f hinj
  have hfactor : βraw ≫ AdditiveTranslation.inclusion k = v := by
    apply Over.OverMorphism.ext
    have : LocallyOfFiniteType ((βraw ≫ AdditiveTranslation.inclusion k).left ≫ AX.hom) := by
      rw [Over.w]
      infer_instance
    refine AlgebraicGeometry.ext_of_apply_eq AX.hom Set.univ isClosed_univ.isLocallyClosed
      dense_univ ?_ ((Over.w (βraw ≫ AdditiveTranslation.inclusion k)).trans (Over.w v).symm)
    intro x _ _
    have hx : v.left x ∈ Set.range (AdditiveTranslation.inclusion k).left := by
      rw [← hrange]
      exact Set.mem_range_self x
    obtain ⟨z, hz⟩ := hx
    change (AdditiveTranslation.inclusion k).left
      ((AdditiveTranslation.shift k).left (v.left x)) = v.left x
    rw [← hz]
    have he := congrArg (fun q : L ⟶ L ↦ q.left z)
      (AdditiveTranslation.inclusion_comp_shift k)
    exact congrArg (AdditiveTranslation.inclusion k).left he
  have : IsMonHom βraw := by
    constructor
    · apply (cancel_mono (AdditiveTranslation.inclusion k)).mp
      simp only [Category.assoc, hfactor, IsMonHom.one_hom]
    · apply (cancel_mono (AdditiveTranslation.inclusion k)).mp
      calc
        (μ[NX] ≫ βraw) ≫ AdditiveTranslation.inclusion k = μ[NX] ≫ v := by
          rw [Category.assoc, hfactor]
        _ = (v ⊗ₘ v) ≫ μ[AX] := IsMonHom.mul_hom _
        _ = ((βraw ≫ AdditiveTranslation.inclusion k) ⊗ₘ
            (βraw ≫ AdditiveTranslation.inclusion k)) ≫ μ[AX] := by rw [hfactor]
        _ = (βraw ⊗ₘ βraw) ≫ (AdditiveTranslation.inclusion k ⊗ₘ
            AdditiveTranslation.inclusion k) ≫ μ[AX] := by
          rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
        _ = ((βraw ⊗ₘ βraw) ≫ μ[L]) ≫ AdditiveTranslation.inclusion k := by
          rw [Category.assoc, IsMonHom.mul_hom]
  let β : N.toAlgebraicGroup.Hom (AdditiveGroupScheme.algebraicGroup k 1) := Grp.homMk βraw
  have : IsClosedImmersion (AdditiveTranslation.inclusion k).left :=
    translation_isClosedImmersion
  have : IsFinite (βraw.left ≫ (AdditiveTranslation.inclusion k).left) := by
    have he : βraw.left ≫ (AdditiveTranslation.inclusion k).left = v.left :=
      congrArg (fun q : NX ⟶ AX ↦ q.left) hfactor
    rw [he]
    change IsFinite (i.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  have hfinite : IsFinite βraw.left := IsFinite.of_comp _ (AdditiveTranslation.inclusion k).left
  have hsurj : Surjective βraw.left := by
    constructor
    intro z
    have hz : (AdditiveTranslation.inclusion k).left z ∈ Set.range v.left := by
      rw [hrange]
      exact Set.mem_range_self z
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, (AdditiveTranslation.inclusion k).left.injective ?_⟩
    exact (congrArg (fun q : NX ⟶ AX ↦ q.left x) hfactor).trans hx
  have hβinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ NX ↦ q ≫ βraw) := by
    intro q r hqr
    change q ≫ βraw = r ≫ βraw at hqr
    have he : q ≫ v = r ≫ v := by
      calc
        _ = (q ≫ βraw) ≫ AdditiveTranslation.inclusion k := by rw [Category.assoc, hfactor]
        _ = (r ≫ βraw) ≫ AdditiveTranslation.inclusion k := by rw [hqr]
        _ = _ := by rw [Category.assoc, hfactor]
    apply (cancel_mono i.hom.hom).mp
    apply hinj
    exact (Category.assoc q i.hom.hom f.hom.hom).trans
      (he.trans (Category.assoc r i.hom.hom f.hom.hom).symm)
  exact ⟨β, hfinite, hsurj, hβinj, hfactor⟩

end
end AclGeom.NormalTranslation
