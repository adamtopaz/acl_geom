/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCoordinateCover
import AclGeom.Correspondence.SchemeAffineCurveDiagram

/-!
# The actual same-coordinate curve cover and action diagram

**Status:** proved for the genuine connected regular affine curve action (#21). The GIVEN
old coordinate restricts to an isomorphism between internally chosen nonempty curve and
line opens, hence a finite surjective map onto the line open. The SAME t and group morphism
satisfy the joint action diagram on the restricted coordinate. The parent is called once;
every original field, coordinate, diagram, finite group cover, chart and tensor datum is
retained. No normality, birationality or coordinate certificate is a caller premise.

This proves the curve-coordinate cover in the regular-affine case of (8.4a). Finiteness
onto the whole affine line is not asserted. Non-affine and rational-action cases,
regularization, completion/points identification, the normal subgroup and full classifier,
original group/chunk/six-point results, algebraization/descent and every true bypassed
auxiliary remain owed. All eight original #21 items and the full durable goal stay open.
-/

namespace AclGeom.SchemeAffineCurveCover
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  isDomain_tensorProduct_of_isAlgClosed

set_option maxHeartbeats 600000 in
-- A finite budget supports the retained dependent data and two actual curve opens.
/-- The genuine regular-affine action supplies the SAME curve-coordinate cover in (8.4a).
 The parent is called once and every datum is retained. The GIVEN old coordinate restricts
 to an isomorphism between nonempty opens, finite and surjective onto the line open. The
 SAME generator and group morphism give the joint action diagram on the restricted
 coordinate. No coordinate, normality or birationality certificate is a caller premise.
 Non-affine/rational actions and the full source classifier remain open. -/
theorem exists_curve_coordinate_cover
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
      ∃ (V₀ : Over (Spec (.of k))) (jV : V₀ ⟶ V)
        (x : V₀ ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
        (gV : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ V₀),
        IsOpenImmersion jV.left ∧ Nonempty V₀.left ∧
        gV ≫ jV = SchemeGenericTranslate.genericParameter V ∧
        gV ≫ x = AffineSchemeAction.linePoint k t ∧
      ∃ (D : Over (Spec (.of k))) (i : D ⟶ G.toGroupScheme.X ⊗ V)
        (s z : D ⟶ V₀), IsOpenImmersion i.left ∧ Nonempty D.left ∧
        s ≫ jV = i ≫ snd G.toGroupScheme.X V ∧
        z ≫ jV = i ≫ γ[G.toGroupScheme.X, V] ∧
        z ≫ x = lift (i ≫ fst G.toGroupScheme.X V ≫ f.hom.hom) (s ≫ x) ≫
          AffineSchemeAction.smul k ∧
      ∃ (V₁ T₁ : Over (Spec (.of k))) (j₁ : V₁ ⟶ V₀)
        (jLine : T₁ ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
        (eV : V₁ ≅ T₁) (g₁ : (Spec V.left.functionField).asOver (Spec (.of k)) ⟶ V₁),
        IsOpenImmersion j₁.left ∧ IsOpenImmersion jLine.left ∧
        Nonempty V₁.left ∧ Nonempty T₁.left ∧
        IsFinite eV.hom.left ∧ Surjective eV.hom.left ∧
        j₁ ≫ x = eV.hom ≫ jLine ∧ g₁ ≫ j₁ = gV ∧
      ∃ (D₁ : Over (Spec (.of k))) (i₁ : D₁ ⟶ G.toGroupScheme.X ⊗ V)
        (s₁ z₁ : D₁ ⟶ V₁), IsOpenImmersion i₁.left ∧ Nonempty D₁.left ∧
        s₁ ≫ j₁ ≫ jV = i₁ ≫ snd G.toGroupScheme.X V ∧
        z₁ ≫ j₁ ≫ jV = i₁ ≫ γ[G.toGroupScheme.X, V] ∧
        z₁ ≫ j₁ ≫ x = lift (i₁ ≫ fst G.toGroupScheme.X V ≫ f.hom.hom)
          (s₁ ≫ j₁ ≫ x) ≫ AffineSchemeAction.smul k ∧
      ∃ (U T : Over (Spec (.of k))) (jU : U ⟶ G.toGroupScheme.X)
        (jT : T ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X) (π : U ⟶ T),
        IsOpenImmersion jU.left ∧ IsOpenImmersion jT.left ∧
        Nonempty U.left ∧ Nonempty T.left ∧ IsFinite π.left ∧ Surjective π.left ∧
        jU ≫ f.hom.hom = π ≫ jT ∧
          ∃ (W : Over (Spec (.of k))) (hI : IsIntegral W.left) (hA : IsAffine W.left)
            (j : W ⟶ G.toGroupScheme.X) (_ : IsOpenImmersion j.left),
            letI := hI
            letI := hA
            letI := sectionsAlgebra W
            let A : Type u := Γ(W.left, ⊤)
            let C := FractionRing A
            let F : Type u := V.left.functionField
            let E := FractionRing (C ⊗[k] F)
            let g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X :=
              (sectionsSpecIso W).inv ≫ j
            let evC : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
            let τ := sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom evC).op ≫ g)
            let T := algebraMap (C ⊗[k] F) E (1 ⊗ₜ[k] t)
            Algebra.FiniteType k A ∧
              ∃ d a b : A, d ≠ 0 ∧ a ≠ 0 ∧
                FiniteDimensional
                  (IntermediateField.adjoin k ({evC a / evC d, evC b / evC d} : Set C)) C ∧
                IsTranscendenceBasis k (![evC a / evC d, evC b / evC d] : Fin 2 → C) ∧
                (∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
                  (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V
                    ((unitIsoSpecAsOver k).hom ≫
                      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
                        algebraMap k F (φ a / φ d) * t + algebraMap k F (φ b / φ d)) ∧
                ∃ hCF : IsDomain (C ⊗[k] F),
                  letI := hCF
                  ∃ hCR : IsDomain (C ⊗[k] Γ(V.left, ⊤)),
                    letI := hCR
                    ∃ (σ : E ≃ₐ[C] E) (e : E ≃ₐ[C] FractionRing (C ⊗[k] Γ(V.left, ⊤))),
                      (∀ (c : C) (r : Γ(V.left, ⊤)),
                        e (algebraMap (C ⊗[k] F) E
                          (c ⊗ₜ[k] V.left.germToFunctionField ⊤
                            (h := ⟨⟨genericPoint _, trivial⟩⟩) r)) =
                              algebraMap (C ⊗[k] Γ(V.left, ⊤)) _ (c ⊗ₜ[k] r)) ∧
                      (∀ x, e (σ x) = IsFractionRing.algEquivOfAlgEquiv τ (e x)) ∧
                      σ T = algebraMap C E (evC a / evC d) * T +
                        algebraMap C E (evC b / evC d) := by
  classical
  obtain ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    V₀, jV, x, gV, hjV, hV₀, hgjV, hgx, D, i, s, z, hi, hD, hsj, hzj, hdiagram,
    U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis,
    hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩ :=
    SchemeAffineCurveDiagram.exists_curve_action_diagram G V hker hdimG hdimV
  have := hjV
  obtain ⟨V₁, T₁, j₁, jLine, eV, g₁, hj₁, hjLine, hV₁, hT₁, hsq, hg₁⟩ :=
    CurveCoordinateCover.exists_coordinate_restriction_iso V V₀ jV x t ht htop gV hgjV hgx
  have := hj₁
  have : IsOpenImmersion (j₁ ≫ jV).left := by
    change IsOpenImmersion (j₁.left ≫ jV.left)
    infer_instance
  have hgj₁ : g₁ ≫ (j₁ ≫ jV) = SchemeGenericTranslate.genericParameter V := by
    rw [← Category.assoc, hg₁, hgjV]
  have hgx₁ : g₁ ≫ (j₁ ≫ x) = AffineSchemeAction.linePoint k t := by
    rw [← Category.assoc, hg₁, hgx]
  obtain ⟨D₁, i₁, s₁, z₁, hi₁, hD₁, hsj₁, hzj₁, hdiagram₁⟩ :=
    CurveAffineCoordinate.exists_joint_diagram_on_coordinate G V t V₁ (j₁ ≫ jV)
      (j₁ ≫ x) g₁ hgj₁ hgx₁ f.hom.hom (fun q ↦ by simpa only [hpoint] using hΦ q)
  have : IsIso eV.hom.left := ActionFunctionField.isIso_hom_left eV
  have hfinV : IsFinite eV.hom.left := inferInstance
  have hsurjV : Surjective eV.hom.left := inferInstance
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    V₀, jV, x, gV, hjV, hV₀, hgjV, hgx, D, i, s, z, hi, hD, hsj, hzj, hdiagram,
    V₁, T₁, j₁, jLine, eV, g₁, hj₁, hjLine, hV₁, hT₁, hfinV, hsurjV, hsq, hg₁,
    D₁, i₁, s₁, z₁, hi₁, hD₁, hsj₁, hzj₁, hdiagram₁,
    U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis, hformula,
    hCF, hCR, σ, e, he, hcompare, hgeneric⟩
end
end AclGeom.SchemeAffineCurveCover
