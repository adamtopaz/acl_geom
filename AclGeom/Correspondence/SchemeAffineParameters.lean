/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeAffineCoefficients
import AclGeom.Correspondence.AffineCoefficientFaithfulness
import AclGeom.Correspondence.SchemeAffineParameter
import AclGeom.Correspondence.SchemeAffinePointAction

/-!
# Rational affine parameters for actual connected curve actions

**Status:** proved for a connected algebraic-group package of dimension at least two acting
regularly on an integral affine locally finite-type dimension-one curve over an ACF base,
with the genuine global k-point kernel criterion (#21). The original generic-stalk coordinate,
global injective affine point homomorphism, actual affine group chart and rational coefficient
functions are chosen internally. The chart fraction field is finite over the two coefficients,
which form a transcendence basis. Literal generic and specialized action formulas are retained.
Both tensor-domain witnesses are proved internally and bound in the result.
No coordinate, coefficient, specialization, rank or finiteness certificate is a caller premise.

This is rational coefficient and parameter-field evidence. `SchemeAffineMorphism` lifts
these SAME data to an actual global regular group-scheme morphism to the standard affine
group, injective on k-points, with actual unit and multiplication identities. Scheme
finite-cover coordinate maps remain owed. Non-affine and rational-action cases, regularization,
completion/points
identification, the normal subgroup and full classifier, original group/chunk/six-point
results, algebraization/descent and true bypassed auxiliaries remain open. All eight original
#21 items and the full durable goal stay open.
-/

namespace AclGeom.SchemeAffineParameters

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate AffineCoefficients

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  isDomain_tensorProduct_of_isAlgClosed

set_option maxHeartbeats 800000 in
-- A finite budget accommodates the dependent actual chart and fraction-field witnesses.
-- Kernel, strict synthesis-depth and lint checking are unchanged.
/-- A genuine connected regular affine curve action internally supplies two independent
 rational group parameters, a finite extension of their field, and their literal actual
 generic and specialized affine formulas. No parameter or rank certificate is a premise.
 The tensor-domain witnesses are derived internally and bound in the result. -/
theorem exists_affine_parameters
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
  obtain ⟨t, ht, htop, Φ, hΦinj, hΦ⟩ :=
    SchemeAffinePointAction.exists_faithful_affine_coordinates G V hker hdimG hdimV
  have hpoint (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) : ∃ a b : k,
      (ActionFunctionField.functionFieldAction G.toAlgebraicGroup V q).unop t =
        algebraMap k V.left.functionField a * t + algebraMap k V.left.functionField b :=
    ⟨((Φ q).multiplier : k), (Φ q).shift, hΦ q⟩
  obtain ⟨W, hI, hA, j, hOpen, hft, hrank⟩ :=
    exists_affine_parameter G.toGroupScheme.X 2 hdimG
  have := hI
  have := hA
  have := hOpen
  let A : Type u := Γ(W.left, ⊤)
  let : Algebra k A := sectionsAlgebra W
  have : Algebra.FiniteType k A := hft
  let C := FractionRing A
  let g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X :=
    (sectionsSpecIso W).inv ≫ j
  have : Mono j := Over.mono_of_mono_left j
  have : Mono g := inferInstance
  obtain ⟨d, a, b, hd, ha, hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩ :=
    exists_generic_family_coefficients G.toAlgebraicGroup V ht hpoint g
  let aa := algebraMap A C a / algebraMap A C d
  let bb := algebraMap A C b / algebraMap A C d
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k ({aa, bb} : Set C)) C :=
    isAlgebraic_of_affine_specializations G.toAlgebraicGroup V hker htop g d a b hd hformula
  have : Algebra.EssFiniteType A C :=
    Algebra.EssFiniteType.of_isLocalization C (nonZeroDivisors A)
  have : Algebra.EssFiniteType k C := Algebra.EssFiniteType.comp k A C
  obtain ⟨hfinite, hbasis⟩ := finite_pair_parameters aa bb hrank
  exact ⟨t, ht, htop, Φ, hΦinj, hΦ, W, hI, hA, j, hOpen, hft, d, a, b, hd, ha,
    hfinite, hbasis, hformula, hCF, hCR, σ, e, he, hcompare, hgeneric⟩

end

end AclGeom.SchemeAffineParameters
