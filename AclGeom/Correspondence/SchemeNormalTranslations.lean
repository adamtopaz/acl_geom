/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.NormalTranslationIsogeny
import AclGeom.Correspondence.SchemeAffineFinite

/-!
# The original normal subgroup in the actual regular-affine action

**Status:** the genuine connected regular action on an integral affine locally finite-type
dimension-one curve over an ACF base, group dimension at least two and the global
point-kernel criterion internally give a finite surjective isogeny N to Ga for every actual
connected one-dimensional normal CLOSED subgroup N. N is not assumed Ga or affine. The
normality premise is the actual joint conjugation property, and the closed immersion is
the genuine subgroup inclusion.

One existing producer call chooses the SAME original generic-stalk generator t and globally
finite surjective affine-group morphism f. The actual N to Ga morphism is point-injective,
factors i followed by f through translations, and gives the literal field formula t to
t+b for every subgroup point with coordinate b. No coordinate, affine morphism, translation
or finite-map certificate is supplied by the caller. All characteristics are included;
no degree-one, separability or N-isomorphic-to-Ga conclusion is asserted.

This proves the finite-isogeny normal-subgroup step in the regular-affine case. The old
whole-curve isomorphism theorem still requires a subgroup already presented as Ga; this
new isogeny alone does not remove that premise. Rational/non-affine regularization,
projective presentation, the full original classifier, group/chunk/algebraization/descent and
all true bypassed auxiliaries remain owed. All eight original #21 items and the full
durable goal stay open.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SchemeNormalTranslations
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The actual connected normal subgroup of dimension one has a finite surjective
isogeny to Ga, factoring the SAME internally chosen finite affine morphism. The subgroup
is not assumed to be Ga. No coordinate, affine morphism, translation or finite-map
certificate is supplied by the caller. -/
theorem exists_normal_subgroup_translation_isogeny
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.toAlgebraicGroup.carrier)
    (hdimV : topologicalKrullDim V.left = 1)
    (N : ConnectedAlgebraicGroup k)
    (i : N.toAlgebraicGroup.Hom G.toAlgebraicGroup)
    [IsMonHom.Normal i.hom.hom] [IsClosedImmersion i.hom.hom.left]
    (hdimN : topologicalKrullDim N.toAlgebraicGroup.carrier = 1) :
    ∃ t : V.left.functionField, Transcendental k t ∧
      IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤ ∧
    ∃ f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k),
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦
        q ≫ f.hom.hom) ∧
      IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      (∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift) ∧
    ∃ β : N.toAlgebraicGroup.Hom (AdditiveGroupScheme.algebraicGroup k 1),
      IsFinite β.hom.hom.left ∧ Surjective β.hom.hom.left ∧
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ N.toGroupScheme.X ↦
        q ≫ β.hom.hom) ∧
      β.hom.hom ≫ AdditiveTranslation.inclusion k = i.hom.hom ≫ f.hom.hom ∧
      ∀ (q : 𝟙_ (Over (Spec (.of k))) ⟶ N.toGroupScheme.X) (b : k),
        q ≫ β.hom.hom = (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b →
        (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V (q ≫ i.hom.hom)).unop t =
          t + algebraMap k V.left.functionField b := by
  obtain ⟨t, ht, htop, Φ, _, hΦ, f, hfinj, hpoint, hfinite, hsurj⟩ :=
    SchemeAffineFinite.exists_finite_surjective_morphism G V hker hdimG hdimV
  have := hfinite
  have := hsurj
  obtain ⟨β, hβfinite, hβsurj, hβinj, hβfactor⟩ :=
    NormalTranslation.exists_finite_isogeny G.toAlgebraicGroup N i hdimN f hfinj
  have hf (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift := by
    rw [hpoint]
    exact hΦ q
  refine ⟨t, ht, htop, f, hfinj, hfinite, hsurj, hf,
    β, hβfinite, hβsurj, hβinj, hβfactor, ?_⟩
  intro q b hqb
  have hqf : (q ≫ i.hom.hom) ≫ f.hom.hom =
      (AffineGroupScheme.pointsMulEquiv k).symm (AffineTransformation.translation b) := by
    calc
      _ = q ≫ (β.hom.hom ≫ AdditiveTranslation.inclusion k) := by
        rw [Category.assoc, hβfactor]
      _ = (q ≫ β.hom.hom) ≫ AdditiveTranslation.inclusion k :=
        (Category.assoc _ _ _).symm
      _ = _ := by rw [hqb, NormalTranslation.point_inclusion]
  rw [hf, hqf, MulEquiv.apply_symm_apply]
  simp only [AffineTransformation.translation_multiplier, Units.val_one, map_one,
    _root_.one_mul, AffineTransformation.translation_shift]

end
end AclGeom.SchemeNormalTranslations
