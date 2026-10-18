/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FinitePointInjectivity
import AclGeom.Correspondence.AffineNormalTranslations
import AclGeom.Correspondence.NormalConjugation
import AclGeom.Correspondence.AffineTranslationSubgroup
import AclGeom.Correspondence.SchemePointExt
import Mathlib.Topology.KrullDimension

/-!
# The actual closed normal image is the translation curve

**Status:** proved criterion over an ACF base (#21). For a finite surjective group morphism
G to the standard affine group, injective on base-field points, every actual connected
one-dimensional normal CLOSED subgroup N has image exactly the translation curve. N is
not assumed Ga or affine. Normality is Mathlib's genuine joint conjugation property.

The finite point-injective morphism is a homeomorphism. The closed subgroup image has N's
actual dimension one. Its nontrivial normal point subgroup contains all translations;
Jacobson density gives the entire translation curve in the image. A proper larger image
would give a length-two chain of irreducible closed subsets, contradicting dimension one.
Named consumer: `NormalTranslation.exists_finite_isogeny`, then the actual regular-affine
source consumer. Rational/non-affine actions and the full classifier remain obligations.
-/

namespace AclGeom.NormalTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Order
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u

/-- Named consumer: the one-dimensional closed normal image is exactly translations. -/
theorem closed_irreducible_eq_univ_of_two_points
    {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 1)
    (Z : Set X) (hZc : IsClosed Z) (hZi : IsIrreducible Z)
    (z w : X) (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z ≠ w)
    (hzc : IsClosed ({z} : Set X)) : Z = Set.univ := by
  by_contra hne
  let C0 : IrreducibleCloseds X := ⟨{z}, isIrreducible_singleton, hzc⟩
  let C1 : IrreducibleCloseds X := ⟨Z, hZi, hZc⟩
  let C2 : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h01 : C0 < C1 := by
    refine lt_iff_le_not_ge.mpr ⟨Set.singleton_subset_iff.mpr hz, ?_⟩
    intro h
    exact hzw (h hw).symm
  have h12 : C1 < C2 := by
    refine lt_iff_le_not_ge.mpr ⟨Set.subset_univ Z, ?_⟩
    intro h
    exact hne (Set.Subset.antisymm (Set.subset_univ Z) h)
  let p : LTSeries (IrreducibleCloseds X) :=
    RelSeries.fromListIsChain [C0, C1, C2] (List.cons_ne_nil _ _)
      (List.IsChain.cons_cons h01 (List.isChain_pair.mpr h12))
  have hh : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    have hh := p.length_le_krullDim
    have hlen : p.length = 2 := rfl
    rw [hlen] at hh
    exact hh
  rw [hdim] at hh
  norm_num at hh

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The actual translation inclusion is a closed immersion. Named consumer: its image
is a closed irreducible curve inside the actual normal subgroup image. -/
theorem translation_isClosedImmersion :
    IsClosedImmersion (AdditiveTranslation.inclusion k).left := by
  let s := AdditiveTranslation.shift k
  have hs : IsSeparated (s.left ≫
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X.hom) := by
    rw [Over.w s]
    infer_instance
  have : IsSeparated s.left := IsSeparated.of_comp s.left
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X.hom
  have : IsClosedImmersion ((AdditiveTranslation.inclusion k).left ≫ s.left) := by
    have he : (AdditiveTranslation.inclusion k).left ≫ s.left = 𝟙 _ :=
      congrArg (fun q ↦ q.left) (AdditiveTranslation.inclusion_comp_shift k)
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ s.left

omit [IsAlgClosed k] in
/-- Named consumer: pass from normal affine point subgroups to the actual translation curve. -/
theorem point_inclusion (b : k) :
    ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b) ≫
      AdditiveTranslation.inclusion k =
        (AffineGroupScheme.pointsMulEquiv k).symm (AffineTransformation.translation b) := by
  rw [Category.assoc, AdditiveTranslation.linePoint_comp_inclusion]
  apply Over.OverMorphism.ext
  exact (AffineGroupScheme.pointsMulEquiv_symm_apply_left k
    (AffineTransformation.translation b)).symm

/-- The actual image of a connected normal closed subgroup of dimension one is translations.
Named consumer: its finite isogeny to Ga in the genuine regular-affine curve action. -/
theorem image_eq_translations
    (G : AlgebraicGroup k) (N : ConnectedAlgebraicGroup k)
    (i : N.toAlgebraicGroup.Hom G) [IsMonHom.Normal i.hom.hom]
    [IsClosedImmersion i.hom.hom.left]
    (hdimN : topologicalKrullDim N.toAlgebraicGroup.carrier = 1)
    (f : G.Hom (AffineGroupScheme.algebraicGroup k))
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left]
    (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦ q ≫ f.hom.hom)) :
    Set.range (i.hom.hom ≫ f.hom.hom).left =
      Set.range (AdditiveTranslation.inclusion k).left := by
  classical
  let NX := N.toGroupScheme.X
  let AX := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let v : NX ⟶ AX := i.hom.hom ≫ f.hom.hom
  let E := AffineGroupScheme.pointsMulEquiv k
  let I := IsMonHom.monoidHom i.hom.hom (𝟙_ (Over (Spec (.of k))))
  let F := E.toMonoidHom.comp (IsMonHom.monoidHom f.hom.hom (𝟙_ (Over (Spec (.of k)))))
  let Ψ := F.comp I
  let H := Ψ.range
  have hFsurj : Function.Surjective F := by
    intro a
    obtain ⟨q, hq⟩ := CurveGlobalCoordinate.surjective_points_of_surjective f.hom.hom (E.symm a)
    change q ≫ f.hom.hom = E.symm a at hq
    refine ⟨q, ?_⟩
    change E (q ≫ f.hom.hom) = a
    rw [hq, MulEquiv.apply_symm_apply]
  have hInormal : I.range.Normal :=
    (IsMonHom.normal_iff_normal_monoidHom.mp inferInstance) _
  have : H.Normal := by
    change (F.comp I).range.Normal
    rw [MonoidHom.range_comp]
    exact hInormal.map F hFsurj
  have hfhomeo := GroupFinite.isHomeomorph_of_finite_surjective_point_injective
    f.hom.hom hinj
  have hvemb : Topology.IsClosedEmbedding v.left :=
    (hfhomeo.homeomorph f.hom.hom.left).isClosedEmbedding.comp
      i.hom.hom.left.isClosedEmbedding
  have hH : H ≠ ⊥ := by
    intro hbot
    have hconst : v = toUnit NX ≫ (1 : 𝟙_ (Over (Spec (.of k))) ⟶ AX) := by
      apply AdditiveRigidity.over_hom_ext_of_points
      intro p
      have hm : Ψ p ∈ H := ⟨p, rfl⟩
      rw [hbot] at hm
      have he : E (p ≫ v) = 1 := Subgroup.mem_bot.mp hm
      have hp : p ≫ v = 1 := E.injective (he.trans E.map_one.symm)
      calc
        _ = 1 := hp
        _ = _ := by
          symm
          rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    have : Subsingleton NX.left := ⟨fun x y ↦ hvemb.injective (by
      have he : (toUnit NX).left x = (toUnit NX).left y :=
        Subsingleton.elim (α := PrimeSpectrum k) _ _
      calc
        _ = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ AX).left ((toUnit NX).left x) :=
          congrArg (fun q : NX ⟶ AX ↦ q.left x) hconst
        _ = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ AX).left ((toUnit NX).left y) :=
          congrArg _ he
        _ = _ := (congrArg (fun q : NX ⟶ AX ↦ q.left y) hconst).symm)⟩
    have : DiscreteTopology NX.left := inferInstance
    have hd := topologicalKrullDim_zero_of_discreteTopology NX.left
    rw [hdimN] at hd
    norm_num at hd
  have : IsClosedImmersion (AdditiveTranslation.inclusion k).left :=
    translation_isClosedImmersion
  have hsub : Set.range (AdditiveTranslation.inclusion k).left ⊆ Set.range v.left := by
    have : JacobsonSpace L.left := LocallyOfFiniteType.jacobsonSpace L.hom
    have hclosed (w : L.left) (hw : IsClosed {w}) :
        (AdditiveTranslation.inclusion k).left w ∈ Set.range v.left := by
      let p : 𝟙_ (Over (Spec (.of k))) ⟶ L :=
        Over.homMk (pointOfClosedPoint L.hom w hw) (pointOfClosedPoint_comp L.hom w hw)
      obtain ⟨b, hb⟩ := AffineSchemeAction.exists_linePoint k ((unitIsoSpecAsOver k).inv ≫ p)
      have hp : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b = p := by
        rw [hb, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      obtain ⟨n, hn⟩ := AffineTransformation.translations_mem_of_normal_ne_bot H hH b
      have hn : E (n ≫ v) = AffineTransformation.translation b := hn
      have he : n ≫ v = p ≫ AdditiveTranslation.inclusion k := by
        rw [← hp, ← Category.assoc, point_inclusion]
        apply E.injective
        rw [MulEquiv.apply_symm_apply]
        exact hn
      have hh := congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ AX ↦
        q.left (IsLocalRing.closedPoint k)) he
      refine ⟨n.left (IsLocalRing.closedPoint k), ?_⟩
      exact hh.trans (congrArg (AdditiveTranslation.inclusion k).left
        (pointOfClosedPoint_apply L.hom w hw _))
    have hc : closure (closedPoints L.left) ⊆
        (AdditiveTranslation.inclusion k).left ⁻¹' Set.range v.left :=
      closure_minimal (fun w hw ↦ hclosed w hw)
        (hvemb.isClosed_range.preimage (AdditiveTranslation.inclusion k).left.continuous)
    have hd : closure (closedPoints L.left) = Set.univ := by
      simpa only [Set.univ_inter, closure_univ] using
        closure_inter_closedPoints (isClosed_univ : IsClosed (Set.univ : Set L.left))
    rw [hd] at hc
    rintro _ ⟨w, rfl⟩
    exact hc (Set.mem_univ w)
  let S := Set.range v.left
  let e := hvemb.isEmbedding.toHomeomorph
  have : IrreducibleSpace S := e.irreducibleSpace_iff.mp inferInstance
  have hdimS : topologicalKrullDim S = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
    exact hdimN
  let J : L.left → S := fun w ↦ ⟨(AdditiveTranslation.inclusion k).left w, hsub ⟨w, rfl⟩⟩
  have hJ : Topology.IsClosedEmbedding J :=
    Topology.IsClosedEmbedding.of_comp .subtypeVal
      (AdditiveTranslation.inclusion k).left.isClosedEmbedding
  let P (b : k) : 𝟙_ (Over (Spec (.of k))) ⟶ L :=
    (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b
  let z := J ((P 0).left (IsLocalRing.closedPoint k))
  let w := J ((P 1).left (IsLocalRing.closedPoint k))
  have hzw : z ≠ w := by
    intro he
    have he' := hJ.injective he
    have hp : P 0 = P 1 := GroupScheme.pointsEquivClosedPoints.injective (Subtype.ext he')
    apply (zero_ne_one : (0 : k) ≠ 1)
    apply AffineSchemeAction.linePoint_injective k
    exact (cancel_epi (unitIsoSpecAsOver k).hom).mp hp
  have hzc : IsClosed ({z} : Set S) := by
    have h0 : IsClosed ({(P 0).left (IsLocalRing.closedPoint k)} : Set L.left) :=
      (GroupScheme.pointsEquivClosedPoints (P 0)).property
    simpa only [Set.image_singleton] using hJ.isClosedMap _ h0
  have : IsIntegral L.left := by
    change IsIntegral (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1)))
    infer_instance
  have hZi : IsIrreducible (Set.range J) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ L.left).image J hJ.continuous.continuousOn
  have hfull := closed_irreducible_eq_univ_of_two_points hdimS (Set.range J)
    hJ.isClosed_range hZi z w (Set.mem_range_self _) (Set.mem_range_self _) hzw hzc
  apply Set.Subset.antisymm
  · intro a ha
    have hm : (⟨a, ha⟩ : S) ∈ Set.range J := by rw [hfull]; trivial
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, congrArg Subtype.val hb⟩
  · exact hsub

end
end AclGeom.NormalTranslation
