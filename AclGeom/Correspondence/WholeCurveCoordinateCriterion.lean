/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GlobalCurveCoordinate
import AclGeom.Correspondence.CurveCoordinateIsomorphism
import AclGeom.Correspondence.SchemeAffineMorphism
import AclGeom.Correspondence.CurveAffineDiagram

/-!
# The whole-curve coordinate for prescribed affine action data

**Status:** for prescribed original generator and actual affine field-action data, the
Ga parameter morphism need only have nontrivial coordinate-one image, not be a scheme
monomorphism. The actual finite Ga orbit gives transitivity and the same whole-curve
coordinate internally. Its generic value, global joint action and all-coefficient ax+b
formula are retained. The old monic-Ga public signature is unchanged as a wrapper.
Named consumer: `RegularAffineModel.exists_whole_curve_model` chooses the generator,
affine morphism and finite Ga cover internally from the actual normal subgroup (#21).
The arbitrary rational/non-affine classifier and original source obligations remain owed.
-/

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- Named consumer: the same-data whole-curve model with the actual normal subgroup.
The Ga parameter morphism need only have a nontrivial coordinate-one point; it need not
be a scheme monomorphism. The given generator and affine morphism are retained. -/
theorem whole_curve_coordinate_of_affine_data_of_nontrivial_ga
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimV : topologicalKrullDim V.left = 1)
    (i : (AdditiveGroupScheme.algebraicGroup k 1).Hom G.toAlgebraicGroup)
    (hi : ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (1 : k)) ≫
      i.hom.hom ≠ 1)
    (t : V.left.functionField) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hΦ : ∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
      algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
        algebraMap k V.left.functionField (Φ q).shift)
    (f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k))
    (hpoint : ∀ q, AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom) = Φ q) :
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
  have hf (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift := by
    rw [hpoint]
    exact hΦ q
  obtain ⟨U, j, xU, gU, hj, hU, hgj, hgx, _⟩ :=
    CurveAffineCoordinate.exists_joint_diagram G V t f.hom.hom hf
  have := hj
  have : LocallyOfFiniteType U.hom := by rw [← Over.w j]; infer_instance
  have : JacobsonSpace U.left := LocallyOfFiniteType.jacobsonSpace U.hom
  have : Nonempty U.left := hU
  obtain ⟨z, _, hzc⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U.left).Nonempty) isClosed_univ.isLocallyClosed
  have hzc₀ : IsClosed ({z} : Set U.left) := hzc
  let p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U :=
    Over.homMk (pointOfClosedPoint U.hom z hzc₀) (pointOfClosedPoint_comp U.hom z hzc₀)
  obtain ⟨p, _, hsurj, _⟩ :=
    AdditiveOrbit.exists_finite_orbit_cover_of_nontrivial_one G.toAlgebraicGroup V
      hker hdimV i hi
  have : Surjective (AdditiveOrbit.orbitMap i.hom.hom p).left := hsurj
  have htrans := transitive_points_of_surjective_orbit G.toAlgebraicGroup
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X V i.hom.hom p
  obtain ⟨x, _, hgen, heq⟩ := exists_global_coordinate G.toAlgebraicGroup V U j p0 xU t
    gU hgj hgx Φ hΦ htrans
  have : IsIso x := isIso_of_surjective_line_cover V x t ht htop hgen
    (AdditiveOrbit.orbitMap i.hom.hom p)
  let e := asIso x
  have haction (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      ModObj.pointAct V q ≫ x = x ≫
        ModObj.pointAct (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
          (q ≫ f.hom.hom) := by
    have hq : q ≫ f.hom.hom = (AffineGroupScheme.pointsMulEquiv k).symm (Φ q) := by
      apply (AffineGroupScheme.pointsMulEquiv k).injective
      rw [MulEquiv.apply_symm_apply]
      exact hpoint q
    rw [hq]
    exact heq q
  have hjoint := joint_diagram_of_point_equivariance G V f.hom.hom x haction
  refine ⟨e, hgen, hjoint, ?_⟩
  intro C _ _ q z a b c hq hz
  change z ≫ x = AffineSchemeAction.linePoint k c at hz
  have hh := congrArg (fun h ↦ lift q z ≫ h) hjoint
  simp only [comp_lift_assoc, lift_fst_assoc, lift_snd_assoc] at hh
  rw [hq, hz] at hh
  exact hh.trans (AffineSchemeAction.lift_groupPoint_linePoint_smul k a b c)

/-- Named consumer: the whole-curve coordinate for the same globally finite group morphism.
The given generator and morphism satisfy the actual function-field action formula. -/
theorem whole_curve_coordinate_of_affine_data
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimV : topologicalKrullDim V.left = 1)
    (i : (AdditiveGroupScheme.algebraicGroup k 1).Hom G.toAlgebraicGroup)
    [Mono i.hom.hom]
    (t : V.left.functionField) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hΦ : ∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
      algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
        algebraMap k V.left.functionField (Φ q).shift)
    (f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k))
    (hpoint : ∀ q, AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom) = Φ q) :
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
  refine whole_curve_coordinate_of_affine_data_of_nontrivial_ga G V hker hdimV i
    ?_ t ht htop Φ hΦ f hpoint
  intro h
  have h₁ : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (1 : k) = 1 := by
    apply (cancel_mono i.hom.hom).mp
    rw [one_comp]
    exact h
  have h₀ : (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (0 : k) = 1 := by
    rw [AdditiveTranslation.linePoint_zero, comp_one]
  apply (one_ne_zero : (1 : k) ≠ 0)
  apply AffineSchemeAction.linePoint_injective k
  exact (cancel_epi (unitIsoSpecAsOver k).hom).mp (h₁.trans h₀.symm)

end
end AclGeom.CurveGlobalCoordinate
