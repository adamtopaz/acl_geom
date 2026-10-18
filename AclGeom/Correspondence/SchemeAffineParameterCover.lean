/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineParameterCover
import AclGeom.Correspondence.SchemeAffineMorphism

/-!
# The actual finite affine-group parameter cover

**Status:** proved for the genuine connected regular affine curve action (#21). Nonempty
opens of the original group and the standard affine group have an actual finite surjective
scheme map whose square commutes with the SAME global group-scheme morphism. The original
generic-stalk generator, faithful point homomorphism, chart, rational coefficients, finite
parameter field, transcendence basis and every generic/specialized formula are retained.
Both tensor-domain witnesses stay internal and bound. The parent producer is called once;
no coordinate, dominance, algebraicity or finite-cover certificate is a caller premise.

This is the GROUP PARAMETER cover. Inseparability is allowed. `SchemeAffineCurveDiagram`
adds the actual SAME-coordinate joint scheme action diagram. Remaining source finite covers,
including finiteness or an open-immersion property of the curve coordinate, non-affine/rational
actions,
regularization, completion/points identification, the normal subgroup and full classifier,
original group/chunk/six-point results, algebraization/descent and every true bypassed
auxiliary remain owed. All eight original #21 items and the full durable goal stay open.
-/

namespace AclGeom.SchemeAffineParameterCover
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
-- A finite budget supports the retained dependent fields, chart and literal coefficient comparison.
/-- A genuine connected regular affine curve action gives an actual finite surjective
 coordinate map on nonempty opens, commuting with the SAME global group morphism. All
 original field, chart and finite parameter data are retained; no cover is a premise. -/
theorem exists_finite_parameter_cover
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
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis,
    hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩ :=
    SchemeAffineMorphism.exists_affine_morphism G V hker hdimG hdimV
  have := hI
  have := hA
  have := hOpen
  let A : Type u := Γ(W.left, ⊤)
  let : Algebra k A := sectionsAlgebra W
  have : Algebra.FiniteType k A := hft
  let g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X :=
    (sectionsSpecIso W).inv ≫ j
  have : IsIso (sectionsSpecIso W).inv.left :=
    ActionFunctionField.isIso_inv_left (sectionsSpecIso W)
  have : IsOpenImmersion g.left := by
    change IsOpenImmersion ((sectionsSpecIso W).inv.left ≫ j.left)
    infer_instance
  have hraw (φ : A →ₐ[k] k) (hdφ : φ d ≠ 0) :
      ((Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).multiplier : k) =
          φ a / φ d ∧
      (Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).shift = φ b / φ d := by
    let q := (unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
    have hp : algebraMap k V.left.functionField ((Φ q).multiplier : k) * t +
        algebraMap k V.left.functionField (Φ q).shift =
      algebraMap k V.left.functionField (φ a / φ d) * t +
        algebraMap k V.left.functionField (φ b / φ d) :=
      (hΦ q).symm.trans (hformula φ hdφ)
    have hpoly : Polynomial.C ((Φ q).multiplier : k) * Polynomial.X +
        Polynomial.C (Φ q).shift =
      Polynomial.C (φ a / φ d) * Polynomial.X + Polynomial.C (φ b / φ d) := by
      apply transcendental_iff_injective.mp ht
      simpa only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] using hp
    constructor
    · simpa using congrArg (fun p : Polynomial k ↦ p.coeff 1) hpoly
    · simpa using congrArg (fun p : Polynomial k ↦ p.coeff 0) hpoly
  obtain ⟨U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ⟩ :=
    AffineGroupScheme.exists_finite_chart G.toAlgebraicGroup f Φ hΦinj hpoint
      g d a b hd hbasis.1 hraw
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    U, T, jU, jT, π, hjU, hjT, hU, hT, hπfin, hπsurj, hπ,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis, hformula,
    hCF, hCR, σ, e, he, hcompare, hgeneric⟩

end
end AclGeom.SchemeAffineParameterCover
