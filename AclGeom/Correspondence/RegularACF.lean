/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tensor products of field extensions over an algebraically closed field

The proof of blueprint Lemma `generic-extension` (8.1(a)) uses that over an algebraically closed
base `k` the tensor product `E ⊗[k] F` of two field extensions is a domain.

* `isDomain_tensorProduct_of_isAlgClosed`: if `k` is algebraically closed, then `E ⊗[k] F` is a
  domain for all field extensions `E` and `F` of `k`.

The proof differs from the blueprint's sketch, which uses a separating transcendence basis and
linear disjointness.  Here a zero divisor in `E ⊗[k] F` already lives in `A ⊗[k] F` for a
finitely generated `k`-subalgebra `A` of `E`, because `F` is flat over `k`.  The ring `A` is a
domain of finite type over `k`, hence a Jacobson ring whose residue fields at maximal ideals are
finite over `k` (Zariski's lemma), hence equal to `k`.  So a nonzero element of `A` has a
nonzero value at some `k`-point `φ : A →ₐ[k] k`.  In coordinates for a `k`-basis of `F`, the
specialization `A ⊗[k] F → F` along `φ` keeps a nonzero coordinate of each of two given nonzero
elements, and `F` is a field.  Finitely generated intermediate fields are not used: they need
not be of finite type as algebras.

**Status:** the domain statement is proved (#11), with no hypothesis beyond the algebraic
closedness of `k`.  This module proves only that statement; the remaining assertions of the
blueprint lemma are not addressed here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open TensorProduct

noncomputable section

variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

/-- A nonzero element of a domain of finite type over an algebraically closed field `k` has a
nonzero value at some `k`-point: otherwise it lies in every maximal ideal, hence in the
Jacobson radical of `⊥`, which is `⊥`. -/
private theorem exists_algHom_ne_zero_of_finiteType [IsAlgClosed k] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {a : A} (ha : a ≠ 0) :
    ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
  classical
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  by_contra h
  have ha' : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro M hM
    let : M.IsMaximal := hM.2
    let : Field (A ⧸ M) := Ideal.Quotient.field M
    let : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
    let φ : (A ⧸ M) →ₐ[k] k := IsAlgClosed.lift
    by_contra ham
    apply h
    refine ⟨φ.comp (Ideal.Quotient.mkₐ k M), ?_⟩
    intro hz
    apply ham
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply φ.injective
    simpa using hz
  have hj : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (inferInstance : (⊥ : Ideal A).IsPrime).isRadical
  exact ha (by simpa only [hj, Ideal.mem_bot] using ha')

/-- In coordinates for a `k`-basis of `F`, the specialization of `A ⊗[k] F` along a `k`-point
`φ` of `A` applies `φ` to each coordinate. -/
private theorem repr_specialize {A : Type*} [CommRing A] [Algebra k A] {ι : Type*}
    [DecidableEq ι] (b : Module.Basis ι k F) (φ : A →ₐ[k] k) (z : A ⊗[k] F) (i : ι) :
    b.repr ((Algebra.TensorProduct.lid k F)
      (Algebra.TensorProduct.map φ (AlgHom.id k F) z)) i =
      φ (TensorProduct.equivFinsuppOfBasisRight b z i) := by
  classical
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a f
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      mul_comm]
  · intro x y hx hy
    simp only [map_add, Finsupp.add_apply, hx, hy]

/-- If `A` is a domain of finite type over an algebraically closed field `k`, then `A ⊗[k] F`
has no zero divisors.  For nonzero `x` and `y`, a `k`-point of `A` keeping a nonzero coordinate
of each specializes `x * y` to a product of two nonzero elements of the field `F`. -/
private theorem mul_ne_zero_of_finiteType [IsAlgClosed k] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {x y : A ⊗[k] F} (hx : x ≠ 0)
    (hy : y ≠ 0) : x * y ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k F
  obtain ⟨i, hi⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisRight b x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply (TensorProduct.equivFinsuppOfBasisRight b).injective
    ext i
    rw [h i, map_zero, Finsupp.zero_apply]
  obtain ⟨j, hj⟩ : ∃ j, TensorProduct.equivFinsuppOfBasisRight b y j ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    apply (TensorProduct.equivFinsuppOfBasisRight b).injective
    ext j
    rw [h j, map_zero, Finsupp.zero_apply]
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero_of_finiteType (k := k) (mul_ne_zero hi hj)
  rw [map_mul] at hφ
  let ψ : A ⊗[k] F →ₐ[k] F :=
    (Algebra.TensorProduct.lid k F).toAlgHom.comp (Algebra.TensorProduct.map φ (AlgHom.id k F))
  have hψx : ψ x ≠ 0 := by
    intro h0
    apply left_ne_zero_of_mul hφ
    rw [← repr_specialize b φ x i]
    change b.repr (ψ x) i = 0
    rw [h0, map_zero, Finsupp.zero_apply]
  have hψy : ψ y ≠ 0 := by
    intro h0
    apply right_ne_zero_of_mul hφ
    rw [← repr_specialize b φ y j]
    change b.repr (ψ y) j = 0
    rw [h0, map_zero, Finsupp.zero_apply]
  intro hxy
  apply mul_ne_zero hψx hψy
  rw [← map_mul ψ x y, hxy, map_zero]

/-- **Tensor products of field extensions over an algebraically closed field are domains**
(#11; the domain statement used in the proof of blueprint Lemma `generic-extension` (8.1(a))).
If `k` is algebraically closed, then `E ⊗[k] F` is a domain for all field extensions `E` and
`F` of `k`. -/
theorem isDomain_tensorProduct_of_isAlgClosed [IsAlgClosed k] : IsDomain (E ⊗[k] F) := by
  classical
  have : Nontrivial (E ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k E F
      (algebraMap k E).injective (algebraMap k F).injective
  -- No zero divisors: both factors live in `A ⊗[k] F` for a finite-type subalgebra `A` of `E`.
  have : NoZeroDivisors (E ⊗[k] F) := by
    refine ⟨fun {x y} hxy ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hy0⟩ := hcon
    obtain ⟨sx, hsx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hsy⟩ := TensorProduct.exists_finset y
    set T : Finset E := sx.image Prod.fst ∪ sy.image Prod.fst with hT
    set A : Subalgebra k E := Algebra.adjoin k (T : Set E)
    have : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite T.finite_toSet
    set φ := Algebra.TensorProduct.map A.val (AlgHom.id k F)
    have hφinj : Function.Injective φ := by
      have hinj : Function.Injective A.val.toLinearMap := Subtype.val_injective
      exact Module.Flat.rTensor_preserves_injective_linearMap (M := F) A.val.toLinearMap hinj
    -- Both elements are in the image of `A ⊗[k] F`.
    have hmem : ∀ (s : Finset (E × F)), (↑(s.image Prod.fst) : Set E) ⊆ T →
        ∃ z : A ⊗[k] F, φ z = ∑ p ∈ s, p.1 ⊗ₜ[k] p.2 := by
      intro s hs
      refine ⟨∑ p ∈ s.attach, (⟨p.1.1, Algebra.subset_adjoin (hs (by
        simpa using Finset.mem_image_of_mem Prod.fst p.2))⟩ : A) ⊗ₜ[k] p.1.2, ?_⟩
      rw [map_sum, ← Finset.sum_attach s fun p ↦ p.1 ⊗ₜ[k] p.2]
      exact Finset.sum_congr rfl fun p _ ↦ rfl
    obtain ⟨x', hx'⟩ := hmem sx (by intro e he; simp only [hT, Finset.coe_union]; left; exact he)
    obtain ⟨y', hy'⟩ := hmem sy (by intro e he; simp only [hT, Finset.coe_union]; right; exact he)
    rw [← hsx] at hx'
    rw [← hsy] at hy'
    have hx'0 : x' ≠ 0 := fun h0 ↦ hx0 (by rw [← hx', h0, map_zero])
    have hy'0 : y' ≠ 0 := fun h0 ↦ hy0 (by rw [← hy', h0, map_zero])
    apply mul_ne_zero_of_finiteType hx'0 hy'0
    refine hφinj ?_
    rw [map_mul, hx', hy', hxy, map_zero]
  exact NoZeroDivisors.to_isDomain _

end

end AclGeom
