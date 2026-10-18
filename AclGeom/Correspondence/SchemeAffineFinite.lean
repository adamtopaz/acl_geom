/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupFiniteMorphism
import AclGeom.Correspondence.WholeCurveCoordinateCriterion
import AclGeom.Correspondence.SchemeAffineParameterCover

/-!
# The actual globally finite affine morphism and the same whole curve

**Status:** the genuine connected regular-affine action on an integral locally finite-type
dimension-one curve over an ACF base, group dimension at least two and the global
point-kernel criterion internally produce a globally finite surjective group morphism to
the standard affine group. This result needs no Ga subgroup. Its generic-stalk generator,
faithful point homomorphism and literal affine field formula are retained.

With an actual monic Ga subgroup, the SAME generator and globally finite surjective group
morphism also give an isomorphism of the ENTIRE original curve with Ga, the actual global
joint action diagram and ax+b over every commutative coefficient algebra in the base
universe. One parameter-cover producer supplies all data internally. No coordinate,
parameter open, finite map, transitivity, regularity or isomorphism certificate is a premise.
Every characteristic is included; no separability or scheme monomorphism is asserted.

Arbitrary one-dimensional normal-subgroup/isogeny classification, rational/non-affine
regularization, projective presentation, the full original classifier, group/chunk/algebraization/
descent and all true bypassed auxiliaries remain owed. All eight original #21 items and
the full durable goal remain open.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SchemeAffineFinite
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The actual regular-affine action internally supplies a globally finite surjective
morphism to the standard affine group. No monic Ga subgroup is needed for this result. -/
theorem exists_finite_surjective_morphism
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.toAlgebraicGroup.carrier)
    (hdimV : topologicalKrullDim V.left = 1) :
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
      IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  obtain ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    U, T, jU, jT, π, hjU, hjT, _, hT, hfinite, hsurj, hsq, _⟩ :=
    SchemeAffineParameterCover.exists_finite_parameter_cover G V hker hdimG hdimV
  have hglobal := @GroupFinite.finite_surjective k _ _ G.toAlgebraicGroup
    (AffineGroupScheme.connectedAlgebraicGroup k) f hfinj U T jU jT π
      hjU hjT hT hfinite hsurj hsq
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint, hglobal⟩

/-- The same generator and globally finite surjective morphism give the whole-curve
isomorphism and literal action formula. All data are chosen internally in one producer call. -/
theorem exists_finite_morphism_whole_curve
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
    ∃ f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k),
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦
        q ≫ f.hom.hom) ∧
      IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      (∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift) ∧
    ∃ e : V ≅ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X,
      SchemeGenericTranslate.genericParameter V ≫ e.hom = AffineSchemeAction.linePoint k t ∧
      γ[G.toGroupScheme.X, V] ≫ e.hom =
        lift (fst G.toGroupScheme.X V ≫ f.hom.hom)
          (snd G.toGroupScheme.X V ≫ e.hom) ≫ AffineSchemeAction.smul k ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C]
        (q : (Spec (.of C)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
        (z : (Spec (.of C)).asOver (Spec (.of k)) ⟶ V) (a : Cˣ) (b c : C),
        q ≫ f.hom.hom = AffineSchemeAction.groupPoint k a b →
        z ≫ e.hom = AffineSchemeAction.linePoint k c →
        (lift q z ≫ γ[G.toGroupScheme.X, V]) ≫ e.hom =
          AffineSchemeAction.linePoint k ((a : C) * c + b) := by
  obtain ⟨t, ht, htop, Φ, _, hΦ, f, hfinj, hpoint, hfinite, hsurj⟩ :=
    exists_finite_surjective_morphism G V hker hdimG hdimV
  have hf (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift := by
    rw [hpoint]
    exact hΦ q
  exact ⟨t, ht, htop, f, hfinj, hfinite, hsurj, hf,
    CurveGlobalCoordinate.whole_curve_coordinate_of_affine_data
      G V hker hdimV i t ht htop Φ hΦ f hpoint⟩

end
end AclGeom.SchemeAffineFinite
