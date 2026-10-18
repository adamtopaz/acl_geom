/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.GroupMorphismExtension
import AclGeom.Correspondence.AffineCoefficientMorphism
import AclGeom.Correspondence.SchemeAffineParameters

/-!
# The global affine-group morphism of an actual curve action

**Status:** proved for a connected algebraic-group package of dimension at least two acting
regularly on an integral affine locally finite-type dimension-one curve over an ACF base,
with the genuine global k-point kernel criterion (#21). An actual group-scheme morphism to
the standard affine group is constructed internally and its k-point map is injective. The
SAME original generic-stalk generator, faithful affine point homomorphism, actual chart,
rational coefficients, finite parameter-field extension, transcendence basis and literal
generic/specialized formulas are retained. Both tensor-domain witnesses stay internal and
bound. No coordinate, local regular model, gluing, extension or morphism is a caller premise.

Unit and multiplication are actual scheme-morphism identities. The theorem asserts
injectivity on k-points; it does not assert a scheme monomorphism. Inseparability is allowed.
Scheme finite-cover coordinate maps, non-affine/rational actions, regularization, completion/
points identification, the normal subgroup and full classifier, original group/chunk/six-
point results, algebraization/descent and all true bypassed auxiliaries remain owed. All
eight original #21 items and the full durable goal remain open.
-/

namespace AclGeom.SchemeAffineMorphism

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate AffineCoefficients RegularGroupMorphism

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  isDomain_tensorProduct_of_isAlgClosed

set_option maxHeartbeats 600000 in
-- A finite budget supports the retained dependent chart, fields and actual morphism data.
-- Kernel, strict synthesis-depth and lint checking remain enabled.
/-- A genuine connected regular affine curve action gives an actual global group-scheme
 morphism into the standard affine group, injective on k-points. The SAME original field
 generator, faithful point representation, chart and finite parameter-field data are retained.
 No coordinate, local regular model, extension or scheme morphism is a caller premise. -/
theorem exists_affine_morphism
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
  obtain ⟨t, ht, htop, Φ, hΦinj, hΦ, W, hI, hA, j, hOpen, hft,
    d, a, b, hd, ha, hfinite, hbasis, hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩ :=
    SchemeAffineParameters.exists_affine_parameters G V hker hdimG hdimV
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
  have hfield (φ : A →ₐ[k] k) (hdφ : φ d ≠ 0) :
      algebraMap k V.left.functionField ((Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).multiplier : k) * t +
      algebraMap k V.left.functionField (Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).shift =
        algebraMap k V.left.functionField (φ a / φ d) * t +
          algebraMap k V.left.functionField (φ b / φ d) :=
    (hΦ _).symm.trans (hformula φ hdφ)
  obtain ⟨U, jU, hJU, p0, fU, hU⟩ :=
    exists_local_model G.toAlgebraicGroup ht Φ g d a b hd ha hfield
  have := hJU
  let Ψ := (AffineGroupScheme.pointsMulEquiv k).symm.toMonoidHom.comp Φ
  obtain ⟨f, hf⟩ := exists_extension G (AffineGroupScheme.algebraicGroup k) U jU p0 Ψ fU hU
  have hpoint (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      AffineGroupScheme.pointsMulEquiv k (q ≫ f.hom.hom) = Φ q := by
    rw [hf]
    exact (AffineGroupScheme.pointsMulEquiv k).apply_symm_apply (Φ q)
  have hfinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦ q ≫ f.hom.hom) := by
    intro q r hqr
    change q ≫ f.hom.hom = r ≫ f.hom.hom at hqr
    apply hΦinj
    exact (hpoint q).symm.trans
      ((congrArg (AffineGroupScheme.pointsMulEquiv k) hqr).trans (hpoint r))
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, f, hfinj, hpoint,
    W, hI, hA, j, hOpen, hft, d, a, b, hd, ha, hfinite, hbasis, hformula,
    hCF, hCR, σ, e, he, hcompare, hgeneric⟩

end

end AclGeom.SchemeAffineMorphism
