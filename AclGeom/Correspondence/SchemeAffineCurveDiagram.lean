/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveAffineDiagram
import AclGeom.Correspondence.SchemeAffineParameterCover

/-!
# The actual same-coordinate curve-action diagram

**Status:** proved for the genuine connected regular affine curve action (#21). An actual
nonempty curve open has a regular coordinate whose generic value is the SAME original
transcendental generator. On an actual nonempty open of the group times the curve, the
original action and standard affine scheme action commute with that coordinate and the
SAME global group morphism. The parent is called once; all faithful point, finite group-
parameter cover, chart, rational coefficient and tensor data are retained. No coordinate,
generic lift, normality or intertwining certificate is a caller premise.

`SchemeAffineCurveCover` restricts this SAME coordinate to an open isomorphism and gives
the joint diagram on that restriction. Remaining source finite covers,
 non-affine and rational-action cases, regularization,
completion/points identification, the normal subgroup and full classifier, original group/
chunk/six-point results, algebraization/descent and every true bypassed auxiliary remain
owed. All eight original #21 items and the full durable goal stay open.
-/

namespace AclGeom.SchemeAffineCurveDiagram
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
-- A finite budget supports the retained dependent fields and chart.
/-- A genuine connected regular action on an integral affine curve gives an actual
 same-coordinate joint scheme action diagram on a nonempty open of the original group
 times the curve. The parent is called once; the SAME generic-stalk generator, faithful
 point homomorphism, global group morphism, parameter cover and all chart/tensor data
 are retained. No coordinate, generic lift or intertwining certificate is a premise.
 This proves the regular-affine diagram of blueprint (8.4a); the full classifier stays open. -/
theorem exists_curve_action_diagram
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
    U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis,
    hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩ :=
    SchemeAffineParameterCover.exists_finite_parameter_cover G V hker hdimG hdimV
  obtain ⟨V₀, jV, x, gV, hjV, hV₀, hgjV, hgx, D, i, s, z, hi, hD, hsj, hzj, hdiagram⟩ :=
    CurveAffineCoordinate.exists_joint_diagram G V t f.hom.hom (fun q ↦ by
      simpa only [hpoint] using hΦ q)
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    V₀, jV, x, gV, hjV, hV₀, hgjV, hgx, D, i, s, z, hi, hD, hsj, hzj, hdiagram,
    U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis, hformula,
    hCF, hCR, σ, e, he, hcompare, hgeneric⟩
end
end AclGeom.SchemeAffineCurveDiagram
