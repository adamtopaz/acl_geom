/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent through an invariant tensor image

Finite generator images in both directions suffice to descend a tensor-coordinate
automorphism to a coefficient subfield. Named consumer: the actual effective coefficient
field constructed from the uniform coefficient family of a regular scheme action.

**Status:** proved; the actual regular-action consumer is `SchemeEffectiveCoefficients`.
-/

namespace AclGeom.TensorCoefficientDescent

noncomputable section

open scoped TensorProduct

universe u

variable {k C R : Type u} [Field k] [Field C] [Algebra k C]
  [CommRing R] [Algebra k R]

/-- Restrict an actual tensor automorphism when the forward and inverse images of finite
algebra generators lie in the coefficient-subfield tensor image. Named consumer: constructing
the effective coefficient field from the proved actual finite coefficient family. -/
theorem exists_tensorAut_of_generator_images (C0 : IntermediateField k C)
    (σ : C ⊗[k] R ≃ₐ[C] C ⊗[k] R) (s : Finset R)
    (hs : Algebra.adjoin k (s : Set R) = ⊤) :
    let j : C0 ⊗[k] R →ₐ[C0] C ⊗[k] R :=
      Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R)
    (∀ r ∈ s, σ (1 ⊗ₜ[k] r) ∈ j.range) →
    (∀ r ∈ s, σ.symm (1 ⊗ₜ[k] r) ∈ j.range) →
      ∃ τ : C0 ⊗[k] R ≃ₐ[C0] C0 ⊗[k] R, ∀ x, j (τ x) = σ (j x) := by
  let j : C0 ⊗[k] R →ₐ[C0] C ⊗[k] R :=
    Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R)
  dsimp only
  intro hσ hσinv
  let S : Subalgebra C0 (C ⊗[k] R) := j.range
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) C0.val.toLinearMap
      C0.val.injective
  have stable (τ : C ⊗[k] R ≃ₐ[C0] C ⊗[k] R)
      (hτ : ∀ r ∈ s, τ (1 ⊗ₜ[k] r) ∈ S) :
      ∀ x : C0 ⊗[k] R, τ (j x) ∈ S := by
    let f : R →ₐ[k] C ⊗[k] R :=
      (τ.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeRight
    let T : Subalgebra k R := (S.restrictScalars k).comap f
    have hT : Algebra.adjoin k (s : Set R) ≤ T := by
      apply Algebra.adjoin_le
      intro r hr
      exact hτ r hr
    have hright (r : R) : τ (1 ⊗ₜ[k] r) ∈ S := by
      change r ∈ T
      apply hT
      rw [hs]
      trivial
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [map_add] using S.add_mem hx hy
    | tmul c r =>
      change τ (Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R)
        (c ⊗ₜ[k] r)) ∈ S
      rw [Algebra.TensorProduct.map_tmul]
      change τ ((algebraMap C0 C c) ⊗ₜ[k] r) ∈ S
      have hfactor : (algebraMap C0 C c) ⊗ₜ[k] r =
          c • (1 ⊗ₜ[k] r : C ⊗[k] R) := by
        change (algebraMap C0 C c) ⊗ₜ[k] r = (c • (1 : C)) ⊗ₜ[k] r
        simp only [Algebra.smul_def, mul_one]
      rw [hfactor, map_smul]
      exact S.smul_mem (hright r) c
  let a := σ.restrictScalars C0
  have ha := stable a hσ
  have hb := stable a.symm hσinv
  have hS : S.map a.toAlgHom = S := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := hy
      exact ha z
    · rintro x ⟨z, rfl⟩
      exact ⟨a.symm (j z), hb z, a.apply_symm_apply (j z)⟩
  let eD := AlgEquiv.ofInjective j hj
  let eS := (AlgEquiv.subalgebraMap a S).trans (Subalgebra.equivOfEq _ _ hS)
  refine ⟨eD.trans (eS.trans eD.symm), fun x ↦ ?_⟩
  have hback (y : S) : j (eD.symm y) = (y : C ⊗[k] R) := by
    exact congrArg (fun z : S ↦ (z : C ⊗[k] R)) (eD.apply_symm_apply y)
  change j (eD.symm (eS (eD x))) = σ (j x)
  rw [hback]
  rfl

/-- Build a finitely generated effective coefficient field and descend the two directions of
an automorphism using their common finite matrix. Named consumer: the actual regular
scheme action, whose matrix is constructed internally rather than supplied by the caller. -/
theorem exists_effective_tensorAut
    (σ : C ⊗[k] R ≃ₐ[C] C ⊗[k] R) (s : Finset R)
    (hs : Algebra.adjoin k (s : Set R) = ⊤)
    {n : ℕ} (v : Fin n → R) (c : Bool → s → Fin n → C)
    (hc : ∀ (e : Bool) (i : s),
      (if e then σ else σ.symm) (1 ⊗ₜ[k] (i : R)) = ∑ j, c e i j ⊗ₜ[k] v j) :
    ∃ (C0 : IntermediateField k C) (c0 : Bool → s → Fin n → C0),
      C0 = IntermediateField.adjoin k
        (Set.range fun p : Bool × s × Fin n ↦ c p.1 p.2.1 p.2.2) ∧
      Algebra.EssFiniteType k C0 ∧
      IntermediateField.adjoin k
        (Set.range fun p : Bool × s × Fin n ↦ c0 p.1 p.2.1 p.2.2) = ⊤ ∧
      (∀ e i j, (c0 e i j : C) = c e i j) ∧
      ∃ τ : C0 ⊗[k] R ≃ₐ[C0] C0 ⊗[k] R,
        (∀ x, Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R) (τ x) =
          σ (Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R) x)) ∧
        ∀ (e : Bool) (i : s),
          (if e then τ else τ.symm) (1 ⊗ₜ[k] (i : R)) = ∑ j, c0 e i j ⊗ₜ[k] v j := by
  classical
  let d : Bool × s × Fin n → C := fun p ↦ c p.1 p.2.1 p.2.2
  let C0 := IntermediateField.adjoin k (Set.range d)
  let c0 : Bool → s → Fin n → C0 := fun e i j ↦
    ⟨c e i j, IntermediateField.subset_adjoin k _ ⟨(e, i, j), rfl⟩⟩
  have hfg : Algebra.EssFiniteType k C0 := by
    apply IntermediateField.essFiniteType_iff.mpr
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      (IntermediateField.fg_adjoin_finset (F := k) (Finset.univ.image d))
  have hgen : IntermediateField.adjoin k
      (Set.range fun p : Bool × s × Fin n ↦ c0 p.1 p.2.1 p.2.2) = ⊤ := by
    apply IntermediateField.lift_injective C0
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    rw [← Set.range_comp]
    rfl
  let j : C0 ⊗[k] R →ₐ[C0] C ⊗[k] R :=
    Algebra.TensorProduct.map (Algebra.ofId C0 C) (AlgHom.id k R)
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) C0.val.toLinearMap
      C0.val.injective
  have hsum (e : Bool) (i : s) :
      j (∑ l, c0 e i l ⊗ₜ[k] v l) = ∑ l, c e i l ⊗ₜ[k] v l := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    exact Algebra.TensorProduct.map_tmul (Algebra.ofId C0 C) (AlgHom.id k R)
      (c0 e i l) (v l)
  have himg (e : Bool) : ∀ r ∈ s,
      (if e then σ else σ.symm) (1 ⊗ₜ[k] r) ∈ j.range := by
    intro r hr
    refine ⟨∑ l, c0 e ⟨r, hr⟩ l ⊗ₜ[k] v l, ?_⟩
    exact (hsum e ⟨r, hr⟩).trans (hc e ⟨r, hr⟩).symm
  obtain ⟨τ, hτ⟩ := exists_tensorAut_of_generator_images C0 σ s hs
    (himg true)
    (himg false)
  refine ⟨C0, c0, rfl, hfg, hgen, fun _ _ _ ↦ rfl, τ, hτ, ?_⟩
  have hτinv (x : C0 ⊗[k] R) : j (τ.symm x) = σ.symm (j x) := by
    apply σ.injective
    rw [σ.apply_symm_apply, ← hτ, τ.apply_symm_apply]
  intro e i
  apply hj
  have htmul : j (1 ⊗ₜ[k] (i : R)) = 1 ⊗ₜ[k] (i : R) := by
    exact (Algebra.TensorProduct.map_tmul (Algebra.ofId C0 C) (AlgHom.id k R)
      (1 : C0) (i : R)).trans (by rw [map_one]; rfl)
  cases e with
  | false =>
    change j (τ.symm (1 ⊗ₜ[k] (i : R))) = _
    rw [hτinv, htmul, hsum]
    exact hc false i
  | true =>
    change j (τ (1 ⊗ₜ[k] (i : R))) = _
    rw [hτ, htmul, hsum]
    exact hc true i

end

end AclGeom.TensorCoefficientDescent
