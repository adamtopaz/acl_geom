/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.WholeCurveCoordinateCriterion

/-!
# The whole original affine curve in the actual regular action

**Status:** proved for a genuine connected regular action on an integral affine locally
finite-type dimension-one curve over an ACF base, with group dimension at least two,
the global point-kernel criterion and an actual monic Ga subgroup (#21). One call to the
existing producer chooses the SAME original generic-stalk generator t and global group
morphism f, injective on base-field points. That t is now the generic value of an actual
isomorphism of the ENTIRE original curve with Ga. The SAME f satisfies the actual global
joint action diagram; its literal ax+b formula holds over every commutative coefficient
algebra in the base universe. Every characteristic is included; inseparability is allowed.

The actual Ga orbit cover supplies point transitivity internally. Its translates extend
the old coordinate chart over the whole curve. Polynomial-cover integrality identifies
the global coordinate ring with k[t]. No coordinate, chart, point, transitivity, regularity,
normality or isomorphism certificate is supplied by the caller. Normality of the Ga
subgroup is not needed for this auxiliary. Identifying arbitrary one-dimensional normal
subgroups with Ga or Gm, their required isogeny classification, remaining source parameter
covers, rational and non-affine actions, regularization, projective presentation, the full original
classifier and all true bypassed auxiliaries remain owed. All eight original #21 work
items and the full durable goal stay open.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The SAME actual regular-affine coordinate is an isomorphism of the whole curve with Ga,
with the SAME group morphism and global joint action diagram. The actual monic Ga subgroup
supplies transitivity internally. No coordinate, point, regularity, transitivity or
isomorphism certificate is supplied by the caller. -/
theorem exists_whole_curve_coordinate
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
  classical
  obtain ⟨t, ht, htop, Φ, _, hΦ, f, hfinj, hpoint, _⟩ :=
    SchemeAffineMorphism.exists_affine_morphism G V hker hdimG hdimV
  have hf (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift := by
    rw [hpoint]
    exact hΦ q
  exact ⟨t, ht, htop, f, hfinj, hf,
    whole_curve_coordinate_of_affine_data G V hker hdimV i t ht htop Φ hΦ f hpoint⟩
end
end AclGeom.CurveGlobalCoordinate
