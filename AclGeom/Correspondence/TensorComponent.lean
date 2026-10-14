/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteCover
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Tensor components of selected correspondence chains

Finite branch fields over the common middle function field select a
minimal-prime tensor component. Its quotient is the actual chain field,
even when the middle function field is not algebraically closed.
-/

namespace AclGeom

open IntermediateField
open scoped TensorProduct

/-- Finite subextensions select a minimal-prime component of their tensor
product, whose quotient is their actual compositum in the ambient field. -/
private theorem finite_tensor_component
    {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    (F G : IntermediateField E Ω) [FiniteDimensional E F] [FiniteDimensional E G] :
    let φ := Algebra.TensorProduct.productMap F.val G.val
    RingHom.ker φ ∈ (⊥ : Ideal (F ⊗[E] G)).minimalPrimes ∧
      Nonempty (((F ⊗[E] G) ⧸ RingHom.ker φ) ≃ₐ[E] ↥(F ⊔ G)) := by
  let φ := Algebra.TensorProduct.productMap F.val G.val
  let : IsArtinianRing (F ⊗[E] G) := IsArtinianRing.of_finite E _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  refine ⟨IsArtinianRing.mem_minimalPrimes bot_le, ?_⟩
  have hr : φ.range = (F ⊔ G).toSubalgebra := by
    rw [Algebra.TensorProduct.productMap_range, F.range_val, G.range_val,
      sup_toSubalgebra_of_left]
  exact ⟨(Ideal.quotientKerEquivRange φ).trans (Subalgebra.equivOfEq _ _ hr)⟩

/-- The compositum over a branch's middle field, restricted to the original
base, is exactly the existing field of its three coordinates. -/
theorem FiniteCorrespondencePair.tensor_compositum_eq_chainField
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (P Q : FiniteCorrespondencePair k Ω) :
    ((adjoin (↥P.targetField) {P.source}) ⊔
      (adjoin (↥P.targetField) {Q.target})).restrictScalars k = P.chainField Q := by
  rw [← restrictScalars_sup]
  change (adjoin (↥(adjoin k {P.target})) {P.source}).restrictScalars k ⊔
    (adjoin (↥(adjoin k {P.target})) {Q.target}).restrictScalars k =
      adjoin k {P.source, P.target, Q.target}
  rw [adjoin_adjoin_left, adjoin_adjoin_left, ← adjoin_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Actual finite-correspondence branches sharing a middle coordinate
select a minimal-prime component of the tensor product over that middle field. -/
theorem FiniteCorrespondencePair.tensor_ker_mem_minimalPrimes
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    let E := P.targetField
    let F := adjoin (↥E) {P.source}
    let G := adjoin (↥E) {Q.target}
    let φ := Algebra.TensorProduct.productMap F.val G.val
    RingHom.ker φ ∈ (⊥ : Ideal (F ⊗[↥E] G)).minimalPrimes := by
  intro E F G φ
  let : FiniteDimensional (↥E) F :=
    IntermediateField.adjoin.finiteDimensional
      ((mem_racl_iff k).mp P.source_mem_target).isIntegral
  have hz : IsAlgebraic (↥E) Q.target := by
    change IsAlgebraic (adjoin k {P.target}) Q.target
    rw [h]
    exact (mem_racl_iff k).mp Q.target_mem_source
  let : FiniteDimensional (↥E) G :=
    IntermediateField.adjoin.finiteDimensional hz.isIntegral
  exact (finite_tensor_component F G).1

/-- The tensor product of two actual shared-middle branch fields, modulo
the kernel of their ambient multiplication map, is their compositum. Its
restriction to the original base is identified by `tensor_compositum_eq_chainField`.
No algebraic closedness or tensor-domain hypothesis is needed. -/
theorem FiniteCorrespondencePair.tensor_quotient_equiv_compositum
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    let E := P.targetField
    let F := adjoin (↥E) {P.source}
    let G := adjoin (↥E) {Q.target}
    let φ := Algebra.TensorProduct.productMap F.val G.val
    let : Algebra (↥E) ((F ⊗[↥E] G) ⧸ RingHom.ker φ) := Ideal.Quotient.algebra _
    Nonempty (((F ⊗[↥E] G) ⧸ RingHom.ker φ) ≃ₐ[↥E] ↥(F ⊔ G)) := by
  intro E F G φ quotientAlgebra
  let : FiniteDimensional (↥E) F :=
    IntermediateField.adjoin.finiteDimensional
      ((mem_racl_iff k).mp P.source_mem_target).isIntegral
  have hz : IsAlgebraic (↥E) Q.target := by
    change IsAlgebraic (adjoin k {P.target}) Q.target
    rw [h]
    exact (mem_racl_iff k).mp Q.target_mem_source
  let : FiniteDimensional (↥E) G :=
    IntermediateField.adjoin.finiteDimensional hz.isIntegral
  exact (finite_tensor_component F G).2

end AclGeom
