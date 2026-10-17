/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.SchemeParameterBaseChange
import AclGeom.Correspondence.SchemeGenericTranslate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.FiniteType

/-!
# Finite coefficients of the actual parameter action

Finite algebra generators and both action directions have coefficients in one common finite
family of linearly independent curve sections. The same coefficients evaluate correctly over
every commutative parameter algebra. All finite data are constructed from the given action.
Named consumer: its effective coefficient field and the actual point-map faithfulness proof.

**Status:** the finite coefficient family is proved for regular actions on affine finite-type
schemes over arbitrary fields. Its effective field and tensor-ring descent are proved in
`SchemeEffectiveCoefficients`; rank, faithful variation and the genus producer remain open.
-/

namespace AclGeom.SchemeParameterAction

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {A R : Type u} [CommRing A] [CommRing R]
  [Algebra k A] [Algebra k R] {G : Over (Spec (.of k))} [GrpObj G]
  [ModObj G ((Spec (.of R)).asOver (Spec (.of k)))]

/-- Construct finite generators and a common independent family of sections for both actual
action directions, uniformly under evaluation. Named consumer: the effective coefficient field
and its actual point-map faithfulness. -/
theorem exists_generating_tensorCoefficients [Algebra.FiniteType k R]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    ∃ s : Finset R, Algebra.adjoin k (s : Set R) = ⊤ ∧
      ∃ (n : ℕ) (v : Fin n → R) (c : Bool → s → Fin n → A),
        LinearIndependent k v ∧
        ∀ (B : Type u) [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (e : Bool) (i : s),
          let f : (Spec (.of B)).asOver (Spec (.of k)) ⟶
              (Spec (.of A)).asOver (Spec (.of k)) :=
            (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
          tensorAut (R := R) (f ≫ (if e then g else g⁻¹)) (1 ⊗ₜ[k] (i : R)) =
            ∑ j, φ (c e i j) ⊗ₜ[k] v j := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := R)
  refine ⟨s, hs, ?_⟩
  let b := Module.Free.chooseBasis k R
  let d : Bool → s → Module.Free.ChooseBasisIndex k R →₀ A := fun e i ↦
    TensorProduct.equivFinsuppOfBasisRight b
      (tensorAut (R := R) (if e then g else g⁻¹) (1 ⊗ₜ[k] (i : R)))
  let I : Finset (Module.Free.ChooseBasisIndex k R) :=
    Finset.univ.biUnion fun p : Bool × s ↦ (d p.1 p.2).support
  refine ⟨I.card, (fun j ↦ b (I.equivFin.symm j).val),
    (fun e i j ↦ d e i (I.equivFin.symm j).val), ?_, ?_⟩
  · exact b.linearIndependent.comp _
      (Subtype.val_injective.comp I.equivFin.symm.injective)
  · intro B _ _ φ e i
    have hsupp : (d e i).support ⊆ I := by
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨(e, i), Finset.mem_univ _, ha⟩
    have hpad : (d e i).sum (fun j a ↦ a ⊗ₜ[k] b j) =
        ∑ j ∈ I, d e i j ⊗ₜ[k] b j := by
      apply Finset.sum_subset hsupp
      intro a _ ha
      rw [Finsupp.notMem_support_iff.mp ha]
      change (0 : A) ⊗ₜ[k] b a = 0
      simp only [TensorProduct.zero_tmul]
    have hrepr := (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply
      (tensorAut (R := R) (if e then g else g⁻¹) (1 ⊗ₜ[k] (i : R)))
    change (TensorProduct.equivFinsuppOfBasisRight b).symm (d e i) = _ at hrepr
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hrepr
    have hsum : tensorAut (R := R) (if e then g else g⁻¹) (1 ⊗ₜ[k] (i : R)) =
        ∑ j : Fin I.card, d e i (I.equivFin.symm j).val ⊗ₜ[k]
          b (I.equivFin.symm j).val := by
      calc
        _ = (d e i).sum (fun j a ↦ a ⊗ₜ[k] b j) := hrepr.symm
        _ = ∑ j : I, d e i j.val ⊗ₜ[k] b j.val := by
          exact hpad.trans (Finset.sum_coe_sort I
            (fun j ↦ d e i j ⊗ₜ[k] b j)).symm
        _ = _ := (Equiv.sum_comp I.equivFin.symm
          (fun j : I ↦ d e i j.val ⊗ₜ[k] b j.val)).symm
    calc
      _ = Algebra.TensorProduct.map φ (AlgHom.id k R)
          (tensorAut (R := R) (if e then g else g⁻¹) (1 ⊗ₜ[k] (i : R))) := by
        simpa only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using
          (tensorAut_baseChange φ (if e then g else g⁻¹) (1 ⊗ₜ[k] (i : R))).symm
      _ = _ := by
        rw [hsum]
        simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end

end AclGeom.SchemeParameterAction

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

/-- The actual regular action on an affine finite-type scheme has one finite independent
coefficient family for generators and inverse generators, uniform under every parameter
evaluation. Finite generation and the coordinate action are derived from the given scheme.
Named consumer: the actual effective coefficient field in the source genus argument. -/
theorem exists_generating_sectionsCoefficients
    {G : Over (Spec (.of k))} [GrpObj G]
    (V : Over (Spec (.of k))) [IsAffine V.left] [LocallyOfFiniteType V.hom] [ModObj G V]
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    ∃ s : Finset Γ(V.left, ⊤), Algebra.adjoin k (s : Set Γ(V.left, ⊤)) = ⊤ ∧
      ∃ (n : ℕ) (v : Fin n → Γ(V.left, ⊤)) (c : Bool → s → Fin n → A),
        LinearIndependent k v ∧
        ∀ (B : Type u) [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (e : Bool) (i : s),
          let f : (Spec (.of B)).asOver (Spec (.of k)) ⟶
              (Spec (.of A)).asOver (Spec (.of k)) :=
            (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
          sectionsTensorAut V (f ≫ (if e then g else g⁻¹))
              (1 ⊗ₜ[k] (i : Γ(V.left, ⊤))) =
            ∑ j, φ (c e i j) ⊗ₜ[k] v j := by
  have : Algebra.FiniteType k Γ(V.left, ⊤) := by
    have h := (V.hom.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top V.left)
      (by simp)).comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
    have htop : V.hom.appLE ⊤ ⊤ (by simp) = V.hom.appTop :=
      Scheme.Hom.appLE_eq_app V.hom
    rw [htop] at h
    exact h
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  let : ModObj G ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) :=
    ModObj.ofIso (Iso.refl G) (sectionsSpecIso V)
  exact SchemeParameterAction.exists_generating_tensorCoefficients (R := Γ(V.left, ⊤)) g

end

end AclGeom.SchemeGenericTranslate
