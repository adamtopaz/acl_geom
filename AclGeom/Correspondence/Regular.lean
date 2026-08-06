/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.AlgebraTower

/-!
# Toward regularity: tensor products of field extensions

Blueprint Lemma `generic-extension` (8.1(a)) asserts that over an
algebraically closed base `k`, the tensor product `E ⊗[k] F` of two field
extensions is a domain. This is the load-bearing fact for the hard kernel
(independent generic points, correspondence composition, the stabilizer
argument). See the tracking issue for the full plan.

This file provides the first reduction:

* `isDomain_tensorProduct_of_fg`: it suffices to prove domain-ness when the
  left factor is finitely generated — zero divisors live in a finitely
  generated leg, and tensoring with `F` preserves the inclusion by flatness.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, toward checklist C2/C3 prerequisites).
-/

namespace AclGeom

open TensorProduct IntermediateField

noncomputable section

variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

/-- The canonical map `E' ⊗[k] F → E ⊗[k] F` induced by an intermediate
field `E' ≤ E` is injective (`F` is flat over the field `k`). -/
theorem tensorProduct_map_val_injective (E' : IntermediateField k E) :
    Function.Injective
      (Algebra.TensorProduct.map E'.val (AlgHom.id k F)) := by
  have hinj : Function.Injective (E'.val.toLinearMap) := Subtype.val_injective
  have h := Module.Flat.rTensor_preserves_injective_linearMap
    (M := F) E'.val.toLinearMap hinj
  exact h

/-- Reduction of domain-ness of `E ⊗[k] F` to finitely generated
subextensions of `E` (first step of blueprint Lemma 8.1(a)): a zero divisor
has finitely many tensor legs, hence lives in a finitely generated leg. -/
theorem isDomain_tensorProduct_of_fg
    (h : ∀ E' : IntermediateField k E, E'.FG → IsDomain (E' ⊗[k] F)) :
    IsDomain (E ⊗[k] F) := by
  classical
  haveI : Nontrivial (E ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k E F
      (algebraMap k E).injective (algebraMap k F).injective
  -- No zero divisors: any relation lives in a finitely generated leg.
  haveI : NoZeroDivisors (E ⊗[k] F) := by
    refine ⟨fun {x y} hxy ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hy0⟩ := hcon
    -- Write both elements with finitely many tensor legs.
    obtain ⟨sx, hsx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hsy⟩ := TensorProduct.exists_finset y
    -- The finitely generated subextension containing all left legs.
    set T : Finset E := sx.image Prod.fst ∪ sy.image Prod.fst with hT
    set E' : IntermediateField k E := adjoin k (T : Set E) with hE'
    haveI hdom : IsDomain (E' ⊗[k] F) := h E' ⟨T, rfl⟩
    set φ := Algebra.TensorProduct.map E'.val (AlgHom.id k F) with hφ
    have hφinj : Function.Injective φ := tensorProduct_map_val_injective E'
    -- Both elements are in the image of `E' ⊗[k] F`.
    have hmem : ∀ (s : Finset (E × F)), (↑(s.image Prod.fst) : Set E) ⊆ T →
        ∃ z : E' ⊗[k] F, φ z = ∑ p ∈ s, p.1 ⊗ₜ[k] p.2 := by
      intro s hs
      refine ⟨∑ p ∈ s.attach, (⟨p.1.1, subset_adjoin k _ (hs (by
        simpa using Finset.mem_image_of_mem Prod.fst p.2))⟩ : E') ⊗ₜ[k] p.1.2, ?_⟩
      rw [map_sum, ← Finset.sum_attach s fun p ↦ p.1 ⊗ₜ[k] p.2]
      exact Finset.sum_congr rfl fun p _ ↦ rfl
    obtain ⟨x', hx'⟩ := hmem sx (by intro e he; simp only [hT, Finset.coe_union]; left; exact he)
    obtain ⟨y', hy'⟩ := hmem sy (by intro e he; simp only [hT, Finset.coe_union]; right; exact he)
    rw [← hsx] at hx'
    rw [← hsy] at hy'
    -- Transport the relation and contradict.
    have hxy' : x' * y' = 0 := by
      refine hφinj ?_
      rw [map_mul, hx', hy', hxy, map_zero]
    rcases mul_eq_zero.1 hxy' with h0 | h0
    · exact hx0 (by rw [← hx', h0, map_zero])
    · exact hy0 (by rw [← hy', h0, map_zero])
  exact NoZeroDivisors.to_isDomain _

section PurelyTranscendental

open MvPolynomial

namespace RegularAux

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (σ : Type*)

/-- The coefficient-extension map, as an algebra structure (scoped to this
construction). -/
noncomputable scoped instance : Algebra (MvPolynomial σ k) (MvPolynomial σ F) :=
  (MvPolynomial.map (algebraMap k F)).toAlgebra

theorem algebraMap_eq :
    algebraMap (MvPolynomial σ k) (MvPolynomial σ F) =
      MvPolynomial.map (algebraMap k F) := rfl

scoped instance : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ F) :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext c
    rw [RingHom.comp_apply, algebraMap_eq]
    simp [MvPolynomial.algebraMap_eq]

/-- The comparison map `k[T] ⊗[k] F →ₐ[k[T]] F[T]`. -/
noncomputable def fwd :
    (MvPolynomial σ k) ⊗[k] F →ₐ[MvPolynomial σ k] MvPolynomial σ F :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom k F (MvPolynomial σ F)) fun _ _ ↦ Commute.all _ _

theorem fwd_tmul (p : MvPolynomial σ k) (f : F) :
    fwd σ (p ⊗ₜ[k] f) = MvPolynomial.map (algebraMap k F) p * MvPolynomial.C f := by
  simp [fwd, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, algebraMap_eq,
    IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq]

/-- `fwd` is bijective: it matches the monomial-tensor basis with the
scalar-tower basis of `F[T]`. -/
theorem fwd_bijective : Function.Bijective (fwd (k := k) (F := F) σ) := by
  classical
  let bF := Module.Basis.ofVectorSpace k F
  let bRF := (MvPolynomial.basisMonomials σ k).tensorProduct bF
  let bT := bF.smulTower (MvPolynomial.basisMonomials σ F)
  let eLin : ((MvPolynomial σ k) ⊗[k] F) ≃ₗ[k] MvPolynomial σ F :=
    bRF.equiv bT (Equiv.prodComm _ _)
  have heq : LinearMap.restrictScalars k (fwd (k := k) (F := F) σ).toLinearMap
      = (eLin : ((MvPolynomial σ k) ⊗[k] F) →ₗ[k] MvPolynomial σ F) := by
    refine bRF.ext fun p ↦ ?_
    rcases p with ⟨d, β⟩
    have h1 : bRF (d, β) = (MvPolynomial.monomial d 1) ⊗ₜ[k] bF β := by
      simp [bRF, Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials]
    have h2 : eLin (bRF (d, β)) = MvPolynomial.monomial d (bF β) := by
      simp only [eLin, Module.Basis.equiv_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
      simp [bT, Module.Basis.smulTower_apply, MvPolynomial.coe_basisMonomials,
        MvPolynomial.smul_monomial]
    change fwd σ (bRF (d, β)) = eLin (bRF (d, β))
    rw [h2, h1, fwd_tmul, MvPolynomial.map_monomial, map_one, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  have hfun : ∀ z, fwd (k := k) (F := F) σ z = eLin z := fun z ↦ by
    have h3 := congrArg (fun (f : ((MvPolynomial σ k) ⊗[k] F) →ₗ[k] MvPolynomial σ F) ↦ f z) heq
    simpa using h3
  constructor
  · intro x y hxy
    exact eLin.injective ((hfun x).symm.trans (hxy.trans (hfun y)))
  · intro p
    exact ⟨eLin.symm p, (hfun _).trans (eLin.apply_symm_apply p)⟩

/-- The comparison equivalence `k[T] ⊗[k] F ≃ₐ[k[T]] F[T]`. -/
noncomputable def tensorEquiv :
    ((MvPolynomial σ k) ⊗[k] F) ≃ₐ[MvPolynomial σ k] MvPolynomial σ F :=
  AlgEquiv.ofBijective (fwd (k := k) (F := F) σ) (fwd_bijective σ)

end RegularAux

open RegularAux in
/-- The purely transcendental step of blueprint Lemma 8.1(a): the tensor
product of a purely transcendental extension `k(T)` with any extension `F/k`
is a domain — it is a localization of the polynomial ring `F[T]`. -/
theorem isDomain_fractionRing_mvPolynomial_tensor
    {k F : Type*} [Field k] [Field F] [Algebra k F] (σ : Type*) :
    IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] F) := by
  classical
  set R := MvPolynomial σ k
  set T := MvPolynomial σ F
  set L := FractionRing R
  -- `L ⊗[R] T` is the localization of `T` at the nonzero polynomials over `k`.
  letI : Algebra T (L ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  haveI hloc : IsLocalization
      (Algebra.algebraMapSubmonoid T (nonZeroDivisors R)) (L ⊗[R] T) :=
    (Algebra.isLocalization_iff_isPushout (R := R) (S := nonZeroDivisors R)
      (A := L) (T := T) (B := L ⊗[R] T)).2 inferInstance
  haveI hdom : IsDomain (L ⊗[R] T) := by
    refine IsLocalization.isDomain_of_le_nonZeroDivisors
      (M := Algebra.algebraMapSubmonoid T (nonZeroDivisors R)) (L ⊗[R] T) ?_
    rintro - ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hrne : r ≠ 0 := nonZeroDivisors.ne_zero hr
    rw [RegularAux.algebraMap_eq]
    exact fun h0 ↦ hrne (MvPolynomial.map_injective _
      (FaithfulSMul.algebraMap_injective k F) (by rwa [map_zero]))
  -- Transport along `L ⊗[R] T ≃ L ⊗[R] (R ⊗[k] F) ≃ L ⊗[k] F`.
  have iso : (L ⊗[R] T) ≃ₐ[L] (L ⊗[k] F) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (A₁ := L) (R := L))
      (RegularAux.tensorEquiv (k := k) (F := F) σ).symm).trans
      (Algebra.TensorProduct.cancelBaseChange k R L L F)
  exact MulEquiv.isDomain (L ⊗[R] T) iso.symm.toMulEquiv

end PurelyTranscendental

end

end AclGeom
