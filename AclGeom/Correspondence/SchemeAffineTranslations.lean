/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveAffineFactor
import AclGeom.Correspondence.AdditiveIsogeny
import AclGeom.Correspondence.SchemeAffineMorphism

/-!
# Actual additive subgroups act by translations in the regular-affine coordinate

**Status:** the translation-identification step in the proof of Lemma 8.4 is proved for the
genuine connected regular affine curve action over an ACF base, in every characteristic.
From that action and an actual monic Ga group morphism into G, internally choose the SAME
original generic-stalk generator t, faithful point map Phi and global group morphism f.
An actual finite surjective Ga group map beta factors the subgroup through the standard
translation inclusion. Its base-field point map is injective; inseparability is allowed.
A single nonconstant polynomial p with zero constant gives beta's point formula and
additivity over every commutative coefficient algebra in the base universe. The actual
subgroup function-field action sends t to t+p(b), with these SAME t and f.

The existing regular-affine producer is called once. No coordinate, translation,
polynomial, factorization, nontriviality or finiteness certificate is a caller premise.
Normality is not needed for this auxiliary statement. Arbitrary one-dimensional subgroup
classification, the dense-orbit coordinate construction, non-affine/rational actions,
regularization, projective presentation, the full classifier, original group/chunk/six-point
statements, algebraization/descent and all true bypassed auxiliaries remain owed. All eight
original #21 work items and the full durable goal stay open.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SchemeAffineTranslations
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
open AdditiveTranslation
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The actual Ga subgroup acts by translations after an internally constructed finite
isogeny, in the SAME coordinate of the genuine regular-affine action. No translation,
polynomial, factorization or finiteness certificate is supplied by the caller. -/
theorem exists_subgroup_translation_coordinate
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.toAlgebraicGroup.carrier)
    (hdimV : topologicalKrullDim V.left = 1)
    (i : (AdditiveGroupScheme.algebraicGroup k 1).Hom G.toAlgebraicGroup)
    [Mono i.hom.hom] :
    ∃ t : V.left.functionField, Transcendental k t ∧
      IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤ ∧
      ∃ Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k,
        Function.Injective Φ ∧
        (∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
          algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
            algebraMap k V.left.functionField (Φ q).shift) ∧
      ∃ f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k),
        Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦
          q ≫ f.hom.hom) ∧
        (∀ q, AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom) = Φ q) ∧
      ∃ β : (AdditiveGroupScheme.algebraicGroup k 1).Hom (AdditiveGroupScheme.algebraicGroup k 1),
        β.hom.hom ≫ (groupInclusion k).hom.hom = i.hom.hom ≫ f.hom.hom ∧
        Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶
          (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ↦ q ≫ β.hom.hom) ∧
        IsFinite β.hom.hom.left ∧ Surjective β.hom.hom.left ∧
      ∃ p : Polynomial k, Polynomial.eval 0 p = 0 ∧ p.natDegree ≠ 0 ∧
        (∀ (C : Type u) [CommRing C] [Algebra k C] (b : C),
          AffineSchemeAction.linePoint k b ≫ β.hom.hom =
            AffineSchemeAction.linePoint k (Polynomial.aeval b p)) ∧
        (∀ (C : Type u) [CommRing C] [Algebra k C] (x y : C),
          Polynomial.aeval (x + y) p = Polynomial.aeval x p + Polynomial.aeval y p) ∧
        ∀ b : k,
          (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V
            ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b ≫ i.hom.hom)).unop t =
              t + algebraMap k V.left.functionField (Polynomial.eval b p) := by
  classical
  obtain ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint, _⟩ :=
    SchemeAffineMorphism.exists_affine_morphism G V hker hdimG hdimV
  obtain ⟨β, hβ⟩ := exists_group_factor k (i ≫ f)
  change β.hom.hom ≫ inclusion k = i.hom.hom ≫ f.hom.hom at hβ
  have hβinj : Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ↦ q ≫ β.hom.hom) := by
    intro q r hqr
    change q ≫ β.hom.hom = r ≫ β.hom.hom at hqr
    apply (cancel_mono i.hom.hom).mp
    apply hfinj
    change (q ≫ i.hom.hom) ≫ f.hom.hom = (r ≫ i.hom.hom) ≫ f.hom.hom
    rw [Category.assoc, Category.assoc, ← hβ, ← Category.assoc, ← Category.assoc, hqr]
  have hq₁ : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (1 : k) ≠
      (1 : 𝟙_ (Over (Spec (.of k))) ⟶
        (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) := by
    intro h
    have hz : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (0 : k) = 1 := by
      rw [linePoint_zero, comp_one]
    exact one_ne_zero (AffineSchemeAction.linePoint_injective k
      ((cancel_epi (unitIsoSpecAsOver k).hom).mp (h.trans hz.symm)))
  obtain ⟨p, hp₀, hp, hβfin, hβsurj, hpoly, hadd⟩ := exists_finite_coordinate k β
    ⟨(unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (1 : k), fun h ↦ by
      apply hq₁
      apply hβinj
      change ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (1 : k)) ≫
        β.hom.hom = (1 : 𝟙_ (Over (Spec (.of k))) ⟶
          (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) ≫ β.hom.hom
      rw [h, one_comp]⟩
  have htranslation (c : k) : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.groupPoint k 1 c =
      (AffineGroupScheme.pointsMulEquiv k).symm (AffineTransformation.translation c) := by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k 1 c).toRingHom) = _
    rw [Category.id_comp]
    exact (AffineGroupScheme.pointsMulEquiv_symm_apply_left k
      (AffineTransformation.translation c)).symm
  refine ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint, β, hβ, hβinj,
    hβfin, hβsurj, p, hp₀, hp, hpoly, hadd, ?_⟩
  intro b
  let q := (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b
  have himage : (q ≫ i.hom.hom) ≫ f.hom.hom =
      (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.groupPoint k 1 (Polynomial.eval b p) := by
    rw [Category.assoc, ← hβ, ← Category.assoc]
    change ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b) ≫
      β.hom.hom ≫ inclusion k = _
    rw [Category.assoc, ← Category.assoc _ β.hom.hom, hpoly k b,
      linePoint_comp_inclusion]
    simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
  have hΦq : Φ (q ≫ i.hom.hom) = AffineTransformation.translation (Polynomial.eval b p) := by
    apply (AffineGroupScheme.pointsMulEquiv k).symm.injective
    rw [← hpoint, MulEquiv.symm_apply_apply, himage, htranslation]
  change (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V
    (q ≫ i.hom.hom)).unop t = _
  rw [hΦ, hΦq, AffineTransformation.translation_multiplier,
    AffineTransformation.translation_shift, Units.val_one, map_one, _root_.one_mul]
end
end AclGeom.SchemeAffineTranslations
