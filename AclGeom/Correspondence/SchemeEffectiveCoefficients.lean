/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.ParameterCoefficients
import AclGeom.Curves.TensorCoefficientDescent

/-!
# The effective coefficient field of an actual parameter action

The same finite coefficients give a finitely generated subfield of every parameter field,
and the actual action and inverse descend to its tensor product with the curve sections.
Named consumer: faithful coefficient variation and the actual curve-action genus producer.

**Status:** the effective coefficient field and both tensor-ring action directions are proved
for a given actual family and parameter-field evaluation. `SchemeEffectiveFunctionField` proves
the field action and faithful coefficient variation. `SchemeActionGenus` derives the actual chart,
rank and genus zero after constants. `SchemeCurveGenus` proves original-base genus and rationality
for faithful regular affine curve actions. Non-affine and rational-action cases and arbitrary-
action classification remain open.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

/-- Construct the effective coefficient field and its tensor automorphism for a given actual
regular-action family and parameter-field evaluation. The finite matrix, its independent
sections and generators, finite generation and both descents are all constructed internally.
Named consumer: the effective-field variation and rank steps of the source genus argument. -/
theorem exists_effective_sectionsTensorAut
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [LocallyOfFiniteType V.hom] [ModObj G V]
    {A C : Type u} [CommRing A] [Algebra k A] [Field C] [Algebra k C]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) (φ : A →ₐ[k] C) :
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
              sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)
                (Algebra.TensorProduct.map (Algebra.ofId C0 C)
                  (AlgHom.id k Γ(V.left, ⊤)) x)) ∧
            ∀ (e : Bool) (i : s),
              (if e then τ else τ.symm) (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) =
                ∑ j, c0 e i j ⊗ₜ[k] v j := by
  obtain ⟨s, hs, n, v, cA, hv, hc⟩ := exists_generating_sectionsCoefficients V g
  refine ⟨s, hs, n, v, cA, hv, hc, ?_⟩
  let f : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
  let σ : C ⊗[k] Γ(V.left, ⊤) ≃ₐ[C] C ⊗[k] Γ(V.left, ⊤) :=
    sectionsTensorAut V (f ≫ g)
  apply TensorCoefficientDescent.exists_effective_tensorAut σ s hs v (fun e i j ↦ φ (cA e i j))
  intro e i
  have h := hc C φ e i
  cases e with
  | false =>
    change sectionsTensorAut V (f ≫ g⁻¹) (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) = _ at h
    rw [GrpObj.comp_inv] at h
    have hinv : sectionsTensorAut V (f ≫ g)⁻¹ = σ.symm := by
      ext x
      rfl
    rw [hinv] at h
    exact h
  | true => exact h

end

end AclGeom.SchemeGenericTranslate
