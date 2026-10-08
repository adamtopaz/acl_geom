/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.GeometricPrime
import AclGeom.Correspondence.FunctionField
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Generic points after scalar extension

Blueprint Lemma `generic-extension` (a) asks for a generic point over an extension
with the original base-field relations and relative independence. The theorem here
constructs such a point in a quotient-fraction field over any extension `E/k` of an
algebraically closed `k`. Its ideal over `E` is exactly the extended original ideal,
and its ideal over `k` is exactly the original tuple's ideal.

Every coordinate subfamily that is independent over `k` remains independent over
`E`. Flatness preserves polynomial-evaluation injectivity, and tensor polynomial
and quotient equivalences identify the resulting map with evaluation at the new
point. This proves relative independence directly, without cancelling infinite
cardinals in the original absolute transcendence-degree equality. The inference
gap is reported on issue #5; the original source statement and proof are retained.

All three private helpers are consumed. The private validation consumer
`GenericSubfamilies` derives maximal coordinate independence over `E` and tests a
truly dependent duplicated tuple with an independent singleton subfamily.
Explicit rank/dimension and rational-field freeness bridges, ambient automorphisms
and the full generic-extension lemma remain separate obligations.

**Status:** constructive scalar-extension points with exact ideals and preservation
of every coordinate-independent subfamily (#5, coordinate form of `generic-extension` (a)).
-/

namespace AclGeom

open TensorProduct

noncomputable section

/-- The quotient-fraction tuple has exactly its defining ideal.
Consumed by `exists_genericPoint_baseChange`. -/
private theorem kernel_fraction_tuple {E : Type*} [Field E] {ι : Type*}
    (I : Ideal (MvPolynomial ι E)) [I.IsPrime] :
    let A := MvPolynomial ι E ⧸ I
    let F := FractionRing A
    let a : ι → F := fun i ↦ algebraMap A F (Ideal.Quotient.mk I (MvPolynomial.X i))
    AclGeom.idealOf E a = I := by
  classical
  dsimp only
  ext p
  rw [AclGeom.mem_idealOf_iff]
  have h : MvPolynomial.aeval
      (fun i ↦ algebraMap (MvPolynomial ι E ⧸ I) (FractionRing (MvPolynomial ι E ⧸ I))
        (Ideal.Quotient.mk I (MvPolynomial.X i))) p =
      algebraMap (MvPolynomial ι E ⧸ I) (FractionRing (MvPolynomial ι E ⧸ I))
        (Ideal.Quotient.mk I p) := by
    let φ : (MvPolynomial ι E ⧸ I) →ₐ[E] FractionRing (MvPolynomial ι E ⧸ I) :=
      IsScalarTower.toAlgHom E (MvPolynomial ι E ⧸ I) (FractionRing (MvPolynomial ι E ⧸ I))
    have hc : MvPolynomial.aeval
        (fun i ↦ algebraMap (MvPolynomial ι E ⧸ I) (FractionRing (MvPolynomial ι E ⧸ I))
          (Ideal.Quotient.mk I (MvPolynomial.X i))) = φ.comp (Ideal.Quotient.mkₐ E I) := by
      ext i
      simp [φ]
    exact congrArg (fun g ↦ g p) hc
  rw [h, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]


/-- Scalar extension of any ideal contracts to the original ideal over a field.
Consumed by `exists_genericPoint_baseChange`; no primeness or ACF is required here. -/
private theorem contraction {k E : Type*} [Field k] [Field E] [Algebra k E]
    {ι : Type*} (I : Ideal (MvPolynomial ι k)) :
    (I.map (MvPolynomial.map (algebraMap k E))).comap
      (MvPolynomial.map (algebraMap k E)) = I := by
  let e := MvPolynomial.algebraTensorAlgEquiv k E (σ := ι)
  let J := I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
  let q : E ⊗[k] (MvPolynomial ι k ⧸ I) ≃ₐ[E] ((E ⊗[k] MvPolynomial ι k) ⧸ J) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := k) E (MvPolynomial ι k) E I
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom =
      MvPolynomial.map (algebraMap k E) := by
    ext i <;> simp [e]
  have hi : I.map (MvPolynomial.map (algebraMap k E)) = J.map e.toRingHom := by
    change I.map (MvPolynomial.map (algebraMap k E)) =
      (I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom).map e.toRingHom
    rw [Ideal.map_map, he]
  ext p
  rw [Ideal.mem_comap, hi]
  change MvPolynomial.map (algebraMap k E) p ∈ J.map e.toRingEquiv.toRingHom ↔ p ∈ I
  have hm : J.map e.toRingHom = J.comap e.symm.toRingHom :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  rw [hm, Ideal.mem_comap]
  change e.symm (MvPolynomial.map (algebraMap k E) p) ∈ J ↔ p ∈ I
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, ← Ideal.Quotient.eq_zero_iff_mem]
  have hz : q.symm (Ideal.Quotient.mk J ((1 : E) ⊗ₜ[k] p)) = 0 ↔
      Ideal.Quotient.mk J ((1 : E) ⊗ₜ[k] p) = 0 :=
    map_eq_zero_iff q.symm q.symm.injective
  rw [← hz]
  change (1 : E) ⊗ₜ[k] Ideal.Quotient.mk I p = 0 ↔ p ∈ I
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


/-- Flat scalar extension preserves polynomial-evaluation injectivity.
Consumed by the coordinate-subfamily argument in `exists_genericPoint_baseChange`. -/
private theorem independent_tensor {k E A : Type*} [Field k] [CommRing E]
    [CommRing A] [Algebra k E] [Algebra k A] {ι : Type*} (x : ι → A)
    (hx : AlgebraicIndependent k x) :
    AlgebraicIndependent E (fun i ↦ (1 : E) ⊗ₜ[k] x i) := by
  let e := MvPolynomial.algebraTensorAlgEquiv k E (σ := ι)
  let f : E ⊗[k] MvPolynomial ι k →ₐ[E] E ⊗[k] A :=
    Algebra.TensorProduct.map (AlgHom.id E E) (MvPolynomial.aeval x)
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := E)
      (MvPolynomial.aeval x).toLinearMap hx
  have h : MvPolynomial.aeval (fun i ↦ (1 : E) ⊗ₜ[k] x i) =
      f.comp e.symm.toAlgHom := by
    ext i
    simp [f, e]
  rw [AlgebraicIndependent, h]
  exact hf.comp e.symm.injective

universe u v w z

/-- **Generic scalar-extension points preserve all coordinate-independent subfamilies.**
The constructed tuple has the exact extended ideal over `E` and the original ideal over `k`.
Only the base field must be algebraically closed; extension fields and variables are arbitrary. -/
theorem exists_genericPoint_baseChange {k : Type u} {E : Type v} {F : Type w}
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] [IsAlgClosed k]
    {ι : Type z} (a : ι → F) :
    ∃ (K : Type (max v z)) (_ : Field K) (_ : Algebra E K) (_ : Algebra k K)
      (_ : IsScalarTower k E K) (b : ι → K),
      idealOf E b = (idealOf k a).map (MvPolynomial.map (algebraMap k E)) ∧
      idealOf k b = idealOf k a ∧
      ∀ S : Set ι, AlgebraicIndependent k (fun j : S ↦ a j) →
        AlgebraicIndependent E (fun j : S ↦ b j) := by
  let I := idealOf k a
  let J := I.map (MvPolynomial.map (algebraMap k E))
  have : J.IsPrime := isPrime_map_of_isAlgClosed I
  let A := MvPolynomial ι E ⧸ J
  let K := FractionRing A
  let b : ι → K := fun i ↦ algebraMap A K (Ideal.Quotient.mk J (MvPolynomial.X i))
  have hE : idealOf E b = J := kernel_fraction_tuple J
  have hk : idealOf k b = I := by
    have hbase : idealOf k b = (idealOf E b).comap
        (MvPolynomial.map (algebraMap k E)) := by
      ext p
      rw [mem_idealOf_iff, Ideal.mem_comap, mem_idealOf_iff,
        MvPolynomial.aeval_map_algebraMap]
    rw [hbase, hE]
    exact contraction I
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, b, hE, hk, ?_⟩
  intro S hS
  let C := MvPolynomial ι k ⧸ I
  let c : ι → C := fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)
  have hc : AlgebraicIndependent k (fun j : S ↦ c j) := by
    apply AlgebraicIndependent.of_comp
      (Ideal.kerLiftAlg (MvPolynomial.aeval a : MvPolynomial ι k →ₐ[k] F))
    have hfun : (Ideal.kerLiftAlg (MvPolynomial.aeval a : MvPolynomial ι k →ₐ[k] F)) ∘
        (fun j : S ↦ c j) = fun j : S ↦ a j := by
      funext j
      exact (Ideal.kerLiftAlg_mk
        (MvPolynomial.aeval a : MvPolynomial ι k →ₐ[k] F) (MvPolynomial.X (j : ι))).trans
        (MvPolynomial.aeval_X (R := k) a (j : ι))
    rw [hfun]
    exact hS
  have ht := independent_tensor (E := E) (fun j : S ↦ c j) hc
  let e := MvPolynomial.algebraTensorAlgEquiv k E (σ := ι)
  let D := I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom =
      MvPolynomial.map (algebraMap k E) := by
    ext i <;> simp [e]
  have hi : J = D.map (e : E ⊗[k] MvPolynomial ι k →+* MvPolynomial ι E) := by
    change I.map (MvPolynomial.map (algebraMap k E)) =
      (I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom).map e.toRingHom
    rw [Ideal.map_map, he]
  let q : E ⊗[k] C ≃ₐ[E] A :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E (MvPolynomial ι k) E I).trans
      (Ideal.quotientEquivAlg D J e hi)
  let φ : A →ₐ[E] K := IsScalarTower.toAlgHom E A K
  have hb := ht.map' (f := φ.comp q.toAlgHom)
    ((IsFractionRing.injective A K).comp q.injective)
  have hq (i : ι) : q ((1 : E) ⊗ₜ[k] c i) = Ideal.Quotient.mk J (MvPolynomial.X i) := by
    change Ideal.quotientEquivAlg D J e hi
      (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E (MvPolynomial ι k) E I
        ((1 : E) ⊗ₜ[k] Ideal.Quotient.mk I (MvPolynomial.X i))) = _
    rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
    change Ideal.quotientEquivAlg D J e hi
      (Ideal.Quotient.mk D ((1 : E) ⊗ₜ[k] MvPolynomial.X i)) = _
    rw [Ideal.quotientEquivAlg_mk]
    simp [e]
  have hfun : (φ.comp q.toAlgHom) ∘ (fun j : S ↦ (1 : E) ⊗ₜ[k] c j) =
      fun j : S ↦ b j := by
    funext j
    change φ (q ((1 : E) ⊗ₜ[k] c j)) = b j
    rw [hq]
    rfl
  rw [hfun] at hb
  exact hb

end

end AclGeom
