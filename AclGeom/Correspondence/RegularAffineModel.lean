/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.NormalCoordinateCharacter
import AclGeom.Correspondence.SchemeAffineCurveCover
import AclGeom.Correspondence.GroupFiniteMorphism
import AclGeom.Correspondence.NormalTranslationIsogeny

/-!
# One coupled model of the genuine regular-affine curve action

**Status:** proved for the genuine connected regular action on an integral affine locally
finite-type dimension-one curve over an ACF base, group dimension at least two and the
global point-kernel criterion (#21). An arbitrary actual connected one-dimensional normal
CLOSED subgroup N is supplied with its genuine inclusion. N is not assumed Ga or affine.

ONE `SchemeAffineCurveCover.exists_curve_coordinate_cover` call chooses the SAME original
generic-stalk generator t and group morphism f. This f is globally finite, surjective and
point-injective. The same t has an actual isomorphism of nonempty curve/line opens, with its
generic value and joint action diagram. A finite surjective point-injective beta:N to Ga
factors the same f through translations. A regular surjective character chi:G to Gm is
its actual multiplier. The actual normal conjugation lift satisfies the joint scalar
diagram after beta. Literal ax+b, affine multiplication and beta-coordinate conjugation
hold over every commutative coefficient algebra in the base universe.

No coordinate, finite morphism, chart, intertwining or conjugation certificate is a caller
premise. Beta is never inverted or cancelled as a mono. No N-isomorphic-to-Ga, degree-one
or separability conclusion is asserted. The curve coordinate is an isomorphism of opens;
the old whole-curve theorem still requires an actual monic Ga subgroup. Rational/non-affine
regularization, projective presentation, the full classifier, group/chunk/algebraization/descent
and every true bypassed auxiliary remain owed. All eight original #21 work items and the
full durable goal remain active and incomplete.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.RegularAffineModel
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- One actual regular-affine action supplies a coupled finite affine-group model,
curve-open coordinate and normal-subgroup coordinate with regular conjugation character.
All coordinates and diagrams use the SAME internally chosen generator and group morphism.
The curve coordinate is an isomorphism of opens; β is a finite isogeny, never inverted.
This is the regular-affine case of (8.4a,b), not the arbitrary rational classifier. -/
theorem exists_model
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
    ∃ (U T : Over (Spec (.of k))) (j : U ⟶ V)
      (jLine : T ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
      (e : U ≅ T) (g : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ U),
      IsOpenImmersion j.left ∧ IsOpenImmersion jLine.left ∧
      Nonempty U.left ∧ Nonempty T.left ∧
      g ≫ j = SchemeGenericTranslate.genericParameter V ∧
      g ≫ e.hom ≫ jLine = AffineSchemeAction.linePoint k t ∧
    ∃ (D : Over (Spec (.of k))) (jD : D ⟶ G.toGroupScheme.X ⊗ V)
      (s z : D ⟶ U), IsOpenImmersion jD.left ∧ Nonempty D.left ∧
      s ≫ j = jD ≫ snd G.toGroupScheme.X V ∧
      z ≫ j = jD ≫ γ[G.toGroupScheme.X, V] ∧
      z ≫ e.hom ≫ jLine = lift (jD ≫ fst G.toGroupScheme.X V ≫ f.hom.hom)
        (s ≫ e.hom ≫ jLine) ≫ AffineSchemeAction.smul k ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C]
        (p : (Spec (.of C)).asOver (Spec (.of k)) ⟶ D) (a : Cˣ) (b c : C),
        p ≫ jD ≫ fst G.toGroupScheme.X V ≫ f.hom.hom =
          AffineSchemeAction.groupPoint k a b →
        p ≫ s ≫ e.hom ≫ jLine = AffineSchemeAction.linePoint k c →
        p ≫ z ≫ e.hom ≫ jLine = AffineSchemeAction.linePoint k ((a : C) * c + b) := by
  obtain ⟨t, ht, htop, Φ, _, hΦ, f, hfinj, hpoint,
    V₀, jV, x, gV, hjV, _, hgjV, hgx, _, _, _, _, _, _, _, _, _,
    V₁, T₁, j₁, jLine, eV, g₁, hj₁, hjLine, hV₁, hT₁, _, _, hcoord, hgj₁,
    D₁, i₁, s₁, z₁, hi₁, hD₁, hs₁, hz₁, hact₁,
    U, T, jU, jT, π, hjU, hjT, _, hT, hπfin, hπsurj, hsq, _⟩ :=
    SchemeAffineCurveCover.exists_curve_coordinate_cover G V hker hdimG hdimV
  have hglobal := @GroupFinite.finite_surjective k _ _ G.toAlgebraicGroup
    (AffineGroupScheme.connectedAlgebraicGroup k) f hfinj U T jU jT π
      hjU hjT hT hπfin hπsurj hsq
  have : IsFinite f.hom.hom.left := hglobal.1
  have : Surjective f.hom.hom.left := hglobal.2
  obtain ⟨β, hβfin, hβsurj, hβinj, hβfactor⟩ :=
    NormalTranslation.exists_finite_isogeny G.toAlgebraicGroup N i hdimN f hfinj
  obtain ⟨χ, hχsurj, hχ, ψ, hψ, hβconj, hconjC⟩ :=
    NormalCoordinateConjugation.exists_character G.toAlgebraicGroup N.toAlgebraicGroup
      i f β hβfactor
  have hj : IsOpenImmersion (j₁ ≫ jV).left := by
    have := hj₁
    have := hjV
    change IsOpenImmersion (j₁.left ≫ jV.left)
    infer_instance
  have hgj : g₁ ≫ (j₁ ≫ jV) = SchemeGenericTranslate.genericParameter V := by
    rw [← Category.assoc, hgj₁, hgjV]
  have hgt : g₁ ≫ eV.hom ≫ jLine = AffineSchemeAction.linePoint k t := by
    rw [← hcoord, ← Category.assoc, hgj₁, hgx]
  have hact : z₁ ≫ eV.hom ≫ jLine =
      lift (i₁ ≫ fst G.toGroupScheme.X V ≫ f.hom.hom)
        (s₁ ≫ eV.hom ≫ jLine) ≫ AffineSchemeAction.smul k := by
    rw [← hcoord]
    exact hact₁
  refine ⟨t, ht, htop, f, hfinj, hglobal.1, hglobal.2, ?_, ?_,
    χ, β, hχsurj, hχ, hβfin, hβsurj, hβinj, hβfactor, ψ, hψ, hβconj, hconjC,
    V₁, T₁, j₁ ≫ jV, jLine, eV, g₁, hj, hjLine, hV₁, hT₁, hgj, hgt,
    D₁, i₁, s₁, z₁, hi₁, hD₁, hs₁, hz₁, hact, ?_⟩
  · intro q
    simpa only [hpoint] using hΦ q
  · intro C _ _ q r c a d b hq hr
    rw [MonObj.mul_comp, hq, hr, AffineSchemeAction.groupPoint_mul]
  · intro C _ _ p a b c hq hc
    rw [hact, comp_lift_assoc, hq, hc,
      AffineSchemeAction.lift_groupPoint_linePoint_smul]

end
end AclGeom.RegularAffineModel
