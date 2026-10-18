/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteGaGroupCover
import AclGeom.Correspondence.WholeCurveCoordinateCriterion
import AclGeom.Correspondence.RegularAffineModel

/-!
# The whole original curve from its actual normal subgroup

**Status:** proved for the genuine connected regular-affine action over an ACF base, with
the global point-kernel criterion, group dimension at least two, integral affine locally
finite-type curve of dimension one and actual connected normal CLOSED subgroup N of
dimension one (#21). N is not assumed Ga or affine. ONE existing coupled-model call chooses
the SAME original generic-stalk generator t, globally finite surjective point-injective f,
regular surjective multiplier character chi, finite point-injective beta:N to Ga and actual
normal conjugation diagram. The curve coordinate is now an isomorphism of the ENTIRE
original curve with Ga, with that SAME t/f and the global joint action diagram.

An actual finite surjective GROUP cover alpha:Ga to N is constructed internally. Its
composite with beta is relative Frobenius and its coordinate-one image in G is nontrivial.
The Ga orbit criterion needs only that nontrivial point, not a scheme-monic Ga inclusion.
The original two monic-Ga public signatures are preserved as wrappers of the weaker
criteria. No caller supplies a Ga presentation, cover, point, coordinate, finite map,
transitivity or isomorphism. Beta is never inverted or cancelled as a scheme mono.
Literal affine multiplication, global action, finite-coordinate conjugation and Frobenius
cover formulas hold over every coefficient algebra in the base universe.

N is classified here up to actual finite Ga covers; no N-isomorphism, degree-one or
separability conclusion is asserted. The arbitrary rational/non-affine classifier,
regularization, completion/points, original group/chunk/six-point results,
algebraization/descent and every true bypassed auxiliary remain owed. All eight original
#21 work items and the full durable goal remain active and incomplete.
-/

namespace AclGeom.RegularAffineModel
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The SAME actual regular-affine data give the whole original curve as Ga, without
assuming the original normal subgroup is Ga. Its finite Ga cover is constructed internally;
the composite with beta is relative Frobenius, never an inverse. The regular character,
normal conjugation diagram and all-coefficient affine formulas are retained. -/
theorem exists_whole_curve_model
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.toAlgebraicGroup.carrier)
    (hdimV : topologicalKrullDim V.left = 1)
    (N : ConnectedAlgebraicGroup k) (i : N.toAlgebraicGroup.Hom G.toAlgebraicGroup)
    [IsMonHom.Normal i.hom.hom] [IsClosedImmersion i.hom.hom.left]
    (hdimN : topologicalKrullDim N.toAlgebraicGroup.carrier = 1) :
    ∃ t : V.left.functionField, Transcendental k t ∧
      IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤ ∧
    ∃ f : G.toAlgebraicGroup.Hom (AffineGroupScheme.algebraicGroup k),
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦
        q ≫ f.hom.hom) ∧ IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      (∀ q, (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField
          ((AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).multiplier : k) * t +
        algebraMap k V.left.functionField
          (AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom)).shift) ∧
      (∀ (C : Type u) [CommRing C] [Algebra k C]
        (q r : (Spec (.of C)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
        (c a : Cˣ) (d b : C),
        q ≫ f.hom.hom = AffineSchemeAction.groupPoint k c d →
        r ≫ f.hom.hom = AffineSchemeAction.groupPoint k a b →
        (q * r) ≫ f.hom.hom =
          AffineSchemeAction.groupPoint k (c * a) ((c : C) * b + d)) ∧
    ∃ (χ : G.toAlgebraicGroup.Hom (multiplicativeGroup k))
      (β : N.toAlgebraicGroup.Hom (AdditiveGroupScheme.algebraicGroup k 1)),
      Surjective χ.hom.hom.left ∧
      χ.hom.hom = f.hom.hom ≫ AffineDilation.projection k ∧
      IsFinite β.hom.hom.left ∧ Surjective β.hom.hom.left ∧
      Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ N.toGroupScheme.X ↦
        q ≫ β.hom.hom) ∧
      β.hom.hom ≫ AdditiveTranslation.inclusion k = i.hom.hom ≫ f.hom.hom ∧
    ∃ ψ : G.toGroupScheme.X ⊗ N.toGroupScheme.X ⟶ N.toGroupScheme.X,
      ψ ≫ i.hom.hom = G.toGroupScheme.X ◁ i.hom.hom ≫ conj G.toGroupScheme.X ∧
      ψ ≫ β.hom.hom = lift
        (fst G.toGroupScheme.X N.toGroupScheme.X ≫ χ.hom.hom)
        (snd G.toGroupScheme.X N.toGroupScheme.X ≫ β.hom.hom) ≫
          AdditiveRigidity.scalarMul k ∧
      (∀ (C : Type u) [CommRing C] [Algebra k C]
        (q : (Spec (.of C)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
        (n : (Spec (.of C)).asOver (Spec (.of k)) ⟶ N.toGroupScheme.X)
        (a : Cˣ) (b : C),
        q ≫ χ.hom.hom = AdditiveRigidity.unitPoint k a →
        n ≫ β.hom.hom = AffineSchemeAction.linePoint k b →
        (lift q n ≫ ψ) ≫ β.hom.hom =
          AffineSchemeAction.linePoint k ((a : C) * b)) ∧
    ∃ p : ℕ, ExpChar k p ∧
    ∃ (n : ℕ) (α : (AdditiveGroupScheme.algebraicGroup k 1).Hom N.toAlgebraicGroup),
      IsFinite α.hom.hom.left ∧ Surjective α.hom.hom.left ∧
      α.hom.hom ≫ β.hom.hom = FiniteGaCover.relativeFrobenius k p n ∧
      (∀ (C : Type u) [CommRing C] [Algebra k C] (c : C),
        AffineSchemeAction.linePoint k c ≫ α.hom.hom ≫ β.hom.hom =
          AffineSchemeAction.linePoint k (c ^ p ^ n)) ∧
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
  obtain ⟨t, ht, htop, f, hfinj, hfinite, hsurj, hfield, hmul,
    χ, β, hχsurj, hχ, hβfin, hβsurj, hβinj, hβfactor, ψ, hψ, hβconj, hconjC, _⟩ :=
    exists_model G V hker hdimG hdimV N i hdimN
  have : IsFinite β.hom.hom.left := hβfin
  have : Surjective β.hom.hom.left := hβsurj
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have := hp
  obtain ⟨n, α, hαfin, hαsurj, hαβ, hαC⟩ :=
    FiniteGaCover.exists_group_cover N hdimN β hβinj p
  let jGa : (AdditiveGroupScheme.algebraicGroup k 1).Hom G.toAlgebraicGroup := α ≫ i
  let Q (c : k) : 𝟙_ (Over (Spec (.of k))) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
    (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k c
  have hQ₀ : Q 0 = 1 := by
    change (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (0 : k) = 1
    rw [AdditiveTranslation.linePoint_zero, comp_one]
  have hjGa : Q 1 ≫ jGa.hom.hom ≠ 1 := by
    intro h
    have hα : Q 1 ≫ α.hom.hom = 1 := by
      apply (cancel_mono i.hom.hom).mp
      rw [one_comp]
      exact (Category.assoc (Q 1) α.hom.hom i.hom.hom).trans h
    have hh := congrArg (fun z ↦ z ≫ β.hom.hom) hα
    rw [Category.assoc, one_comp] at hh
    have hQ₁ : Q 1 ≫ α.hom.hom ≫ β.hom.hom = Q 1 := by
      dsimp only [Q]
      rw [Category.assoc, hαC, one_pow]
    apply (one_ne_zero : (1 : k) ≠ 0)
    apply AffineSchemeAction.linePoint_injective k
    apply (cancel_epi (unitIsoSpecAsOver k).hom).mp
    exact (hQ₁.symm.trans hh).trans hQ₀.symm
  let Φ := (AffineGroupScheme.pointsMulEquiv k).toMonoidHom.comp
    (IsMonHom.monoidHom f.hom.hom (𝟙_ (Over (Spec (.of k)))))
  have hΦ (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
          algebraMap k V.left.functionField (Φ q).shift := hfield q
  have hpoint (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom) = Φ q := rfl
  obtain ⟨e, hgen, haction, hactionC⟩ :=
    CurveGlobalCoordinate.whole_curve_coordinate_of_affine_data_of_nontrivial_ga G V
      hker hdimV jGa hjGa t ht htop Φ hΦ f hpoint
  exact ⟨t, ht, htop, f, hfinj, hfinite, hsurj, hfield, hmul,
    χ, β, hχsurj, hχ, hβfin, hβsurj, hβinj, hβfactor, ψ, hψ, hβconj, hconjC,
    p, hp, n, α, hαfin, hαsurj, hαβ, hαC, e, hgen, haction, hactionC⟩

end
end AclGeom.RegularAffineModel
