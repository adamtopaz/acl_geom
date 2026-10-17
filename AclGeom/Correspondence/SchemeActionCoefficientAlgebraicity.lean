/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeActionCoefficientPoints
import AclGeom.Correspondence.PointwiseFaithfulness

/-!
# Algebraicity over the actual action coefficient field

Named consumer: the actual regular-affine curve genus theorem
`AclGeom.SchemeGenericTranslate.exists_constantExtension_genus_eq_zero`.

**Status:** the compatible coefficient field and actual point-action criterion imply
algebraicity of the parameter fraction field, allowing purely inseparable extensions.
The actual consumer constructs the finite matrix and coefficient containment internally.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] sectionsAlgebra

/-- A compatible field containing the same actual coefficients makes the parameter fraction
field algebraic. Named consumer: the internally generated actual coefficient field has full
parameter rank; pure inseparability is allowed. -/
theorem isAlgebraic_of_faithful_coefficients
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    {A C : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Field C] [Algebra k C] [Algebra A C] [IsScalarTower k A C] [IsFractionRing A C]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) [Mono g]
    (s : Finset Γ(V.left, ⊤)) (hs : Algebra.adjoin k (s : Set Γ(V.left, ⊤)) = ⊤)
    {n : ℕ} (v : Fin n → Γ(V.left, ⊤)) (cA : Bool → s → Fin n → A)
    (hc : ∀ (φ : A →ₐ[k] k) (i : s),
      sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)
        (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) = ∑ j, φ (cA true i j) ⊗ₜ[k] v j)
    (C0 : IntermediateField k C)
    (hmem : ∀ (e : Bool) (i : s) (j : Fin n), algebraMap A C (cA e i j) ∈ C0) :
    Algebra.IsAlgebraic C0 C := by
  let B := Algebra.adjoin k (Set.range fun p : Bool × s × Fin n ↦ cA p.1 p.2.1 p.2.2)
  let φ : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  have hle : B ≤ C0.toSubalgebra.comap φ := by
    apply Algebra.adjoin_le
    rintro a ⟨p, rfl⟩
    exact hmem p.1 p.2.1 p.2.2
  let f : B →ₐ[k] C0 :=
    (φ.comp B.val).codRestrict C0.toSubalgebra (fun b ↦ hle b.property)
  let : Algebra B C0 := f.toAlgebra
  have : IsScalarTower B C0 C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact isAlgebraic_fractionRing_of_injective_points
    (coefficient_points_injective V hker g s hs v cA hc)

end

end AclGeom.SchemeGenericTranslate
