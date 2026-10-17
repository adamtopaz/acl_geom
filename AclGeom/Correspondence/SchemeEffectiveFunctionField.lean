/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.SchemeEffectiveCoefficients
import AclGeom.Curves.TensorCoefficientFractions
import AclGeom.Curves.CoefficientVariationFaithfulness

/-!
# The actual effective coefficient-field action on the function field

Named consumer: faithful coefficient variation and the actual curve-action genus theorem.

**Status:** the actual effective-field action and faithful coefficient variation are proved
for a given family and field evaluation over an ACF base. `SchemeActionGenus` internally chooses
the actual group chart and parameter field, derives coefficient rank and independent regular
variations, and proves genus zero after constants for faithful regular affine curve actions.
Original-base descent, non-affine and rational-action cases and classification remain open.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra

set_option maxHeartbeats 600000 in
-- The dependent scheme/section comparisons need a larger elaboration resource budget.
-- This finite bound changes neither kernel checking nor the standard lint/synthesis settings.
/-- Extend the actual effective tensor-ring action to the formal constant extension of the
same curve function field, keeping the original matrix, coefficient field and literal germ
comparison. All domains and field comparisons are derived internally. Named consumer:
faithful coefficient variation and the actual curve-action genus producer. -/
theorem exists_effective_functionFieldAut [IsAlgClosed k]
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G V]
    {A C : Type u} [CommRing A] [Algebra k A] [Field C] [Algebra k C]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) (φ : A →ₐ[k] C) :
    let f_eval : (Spec (.of C)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) :=
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
    let σC : C ⊗[k] Γ(V.left, ⊤) ≃ₐ[C] C ⊗[k] Γ(V.left, ⊤) :=
      sectionsTensorAut V (f_eval ≫ g)
    ∃ s : Finset Γ(V.left, ⊤), Algebra.adjoin k (s : Set Γ(V.left, ⊤)) = ⊤ ∧
      ∃ (n : ℕ) (v : Fin n → Γ(V.left, ⊤)) (cA : Bool → s → Fin n → A),
        LinearIndependent k v ∧
        (∀ (B : Type u) [CommRing B] [Algebra k B] (ψ : A →ₐ[k] B) (e : Bool) (i : s),
          let f : (Spec (.of B)).asOver (Spec (.of k)) ⟶
              (Spec (.of A)).asOver (Spec (.of k)) :=
            (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op
          sectionsTensorAut V (f ≫ (if e then g else g⁻¹))
              (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) = ∑ j, ψ (cA e i j) ⊗ₜ[k] v j) ∧
        ∃ (C0 : IntermediateField k C) (c0 : Bool → s → Fin n → C0),
          C0 = IntermediateField.adjoin k
            (Set.range fun p : Bool × s × Fin n ↦ φ (cA p.1 p.2.1 p.2.2)) ∧
          Algebra.EssFiniteType k C0 ∧
          IntermediateField.adjoin k
            (Set.range fun p : Bool × s × Fin n ↦ c0 p.1 p.2.1 p.2.2) = ⊤ ∧
          (∀ e i j, (c0 e i j : C) = φ (cA e i j)) ∧
          ∃ τ : C0 ⊗[k] Γ(V.left, ⊤) ≃ₐ[C0] C0 ⊗[k] Γ(V.left, ⊤),
            (∀ x, Algebra.TensorProduct.map (Algebra.ofId C0 C)
                (AlgHom.id k Γ(V.left, ⊤)) (τ x) =
              σC
                (Algebra.TensorProduct.map (Algebra.ofId C0 C)
                  (AlgHom.id k Γ(V.left, ⊤)) x)) ∧
            (∀ (e : Bool) (i : s),
              (if e then τ else τ.symm) (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) =
                ∑ j, c0 e i j ⊗ₜ[k] v j) ∧
            ∃ (h0 : IsDomain (C0 ⊗[k] Γ(V.left, ⊤)))
              (hC : IsDomain (C ⊗[k] Γ(V.left, ⊤)))
              (hF : IsDomain (C0 ⊗[k] V.left.functionField)),
            letI := h0
            letI := hC
            letI := hF
            ∃ (τF : FractionRing (C0 ⊗[k] V.left.functionField) ≃ₐ[C0]
                FractionRing (C0 ⊗[k] V.left.functionField))
              (e0 : FractionRing (C0 ⊗[k] V.left.functionField) ≃ₐ[C0]
                FractionRing (C0 ⊗[k] Γ(V.left, ⊤)))
              (J : FractionRing (C0 ⊗[k] Γ(V.left, ⊤)) →ₐ[C0]
                FractionRing (C ⊗[k] Γ(V.left, ⊤))),
              Function.Injective (coefficientVariationLinear (k := k) τF) ∧
              Function.Injective J ∧
              (∀ (c : C0) (r : Γ(V.left, ⊤)),
                e0 (algebraMap (C0 ⊗[k] V.left.functionField) _
                  (c ⊗ₜ[k] V.left.germToFunctionField ⊤
                    (h := ⟨⟨genericPoint V.left, trivial⟩⟩) r)) =
                  algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _ (c ⊗ₜ[k] r)) ∧
              (∀ x, J (algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _ x) =
                algebraMap (C ⊗[k] Γ(V.left, ⊤)) _
                  (Algebra.TensorProduct.map (Algebra.ofId C0 C)
                    (AlgHom.id k Γ(V.left, ⊤)) x)) ∧
              (∀ x, J (e0 (τF x)) =
                (IsFractionRing.algEquivOfAlgEquiv σC :
                    FractionRing (C ⊗[k] Γ(V.left, ⊤)) ≃ₐ[C]
                      FractionRing (C ⊗[k] Γ(V.left, ⊤))) (J (e0 x))) ∧
              ∀ (e : Bool) (i : s),
                (if e then τF else τF.symm)
                    (algebraMap (C0 ⊗[k] V.left.functionField) _
                      (1 ⊗ₜ[k] V.left.germToFunctionField ⊤
                        (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (i : Γ(V.left, ⊤)))) =
                  ∑ j, algebraMap (C0 ⊗[k] V.left.functionField) _
                    (c0 e i j ⊗ₜ[k] V.left.germToFunctionField ⊤
                      (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (v j)) := by
  dsimp only
  obtain ⟨s, hs, n, v, cA, hv, hcA, C0, c0, hC0, hfg, hgen, hcoe, τ, hτ, hmat⟩ :=
    exists_effective_sectionsTensorAut V g φ
  refine ⟨s, hs, n, v, cA, hv, hcA, C0, c0, hC0, hfg, hgen, hcoe, τ, hτ, hmat, ?_⟩
  have : IsDomain (C ⊗[k] Γ(V.left, ⊤)) := isDomain_tensor_sections C V
  let f : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
  let σ : C ⊗[k] Γ(V.left, ⊤) ≃ₐ[C] C ⊗[k] Γ(V.left, ⊤) :=
    sectionsTensorAut V (f ≫ g)
  obtain ⟨h0, J, τR, hJinj, hJ, hτR, hcomm⟩ :=
    TensorCoefficientDescent.exists_fractionTensorAut_comparison C0 τ σ hτ
  have := h0
  obtain ⟨e0, he0⟩ := exists_tensorSections_functionFieldEquiv C0 V
  let τF := e0.trans (τR.trans e0.symm)
  have hconj (e : Bool) (x : FractionRing (C0 ⊗[k] V.left.functionField)) :
      e0 ((if e then τF else τF.symm) x) = (if e then τR else τR.symm) (e0 x) := by
    cases e with
    | false =>
      change e0 (e0.symm (τR.symm (e0 x))) = _
      exact e0.apply_symm_apply _
    | true =>
      change e0 (e0.symm (τR (e0 x))) = _
      exact e0.apply_symm_apply _
  have hτRinv (x : C0 ⊗[k] Γ(V.left, ⊤)) :
      τR.symm (algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _ x) =
        algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _ (τ.symm x) := by
    apply τR.injective
    rw [τR.apply_symm_apply, hτR, τ.apply_symm_apply]
  have hmatF : ∀ (e : Bool) (i : s),
      (if e then τF else τF.symm)
          (algebraMap (C0 ⊗[k] V.left.functionField) _
            (1 ⊗ₜ[k] V.left.germToFunctionField ⊤
              (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (i : Γ(V.left, ⊤)))) =
        ∑ j, algebraMap (C0 ⊗[k] V.left.functionField) _
          (c0 e i j ⊗ₜ[k] V.left.germToFunctionField ⊤
            (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (v j)) := by
    intro e i
    apply e0.injective
    rw [hconj, he0]
    simp only [map_sum, he0]
    cases e with
    | false =>
      change τR.symm (algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _
        (1 ⊗ₜ[k] (i : Γ(V.left, ⊤)))) = _
      rw [hτRinv]
      simpa only [Bool.false_eq_true, ↓reduceIte, map_sum] using
        congrArg (algebraMap (C0 ⊗[k] Γ(V.left, ⊤))
          (FractionRing (C0 ⊗[k] Γ(V.left, ⊤)))) (hmat false i)
    | true =>
      change τR (algebraMap (C0 ⊗[k] Γ(V.left, ⊤)) _
        (1 ⊗ₜ[k] (i : Γ(V.left, ⊤)))) = _
      rw [hτR]
      simpa only [↓reduceIte, map_sum] using
        congrArg (algebraMap (C0 ⊗[k] Γ(V.left, ⊤))
          (FractionRing (C0 ⊗[k] Γ(V.left, ⊤)))) (hmat true i)
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsScalarTower k Γ(V.left, ⊤) V.left.functionField :=
    sections_functionField_isScalarTower V
  let fV : Γ(V.left, ⊤) →ₐ[k] V.left.functionField :=
    IsScalarTower.toAlgHom k Γ(V.left, ⊤) V.left.functionField
  have hvF : LinearIndependent k (fun j ↦
      V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (v j)) :=
    hv.map' fV.toLinearMap (LinearMap.ker_eq_bot.mpr
      (IsFractionRing.injective Γ(V.left, ⊤) V.left.functionField))
  have hF : IsDomain (C0 ⊗[k] V.left.functionField) :=
    isDomain_tensorProduct_of_isAlgClosed
  have hfaithful : Function.Injective (coefficientVariationLinear (k := k) τF) := by
    exact coefficientVariationLinear_injective_of_generating_coefficients τF
      (fun i : s ↦ V.left.germToFunctionField ⊤
        (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (i : Γ(V.left, ⊤)))
      (fun j ↦ V.left.germToFunctionField ⊤
        (h := ⟨⟨genericPoint V.left, trivial⟩⟩) (v j)) hvF c0 hgen hmatF
  refine ⟨h0, inferInstance, hF, τF, e0, J, hfaithful, hJinj, he0, hJ, ?_, hmatF⟩
  intro x
  rw [show e0 (τF x) = τR (e0 x) from hconj true x]
  exact hcomm (e0 x)

end

end AclGeom.SchemeGenericTranslate
