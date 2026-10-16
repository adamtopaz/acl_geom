/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Closure.Ambient
import AclGeom.Correspondence.TensorComponent
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Realization of prime function-field tensor components

Every prime component of a tensor product of finite field extensions is
realized by two embeddings into an algebraically closed ambient extension.
For actual branches, these embeddings give a represented composite of the
original germs with the selected tensor kernel. The generic
`exists_productMap_ker_of_isPrime` is also consumed by `LocusJointComponent`
to realize every middle-dominating incidence component for finite outer
tuples with the two source algebraicity clauses in an algebraically closed
ambient field. The existing scalar public statements are unchanged.
-/

namespace AclGeom

open IntermediateField
open scoped TensorProduct

/-- Every prime tensor component of two finite extensions embeds in an
algebraically closed ambient extension of the base: there are embeddings of the two factors over
the base whose multiplication map has exactly the given prime as kernel. -/
theorem exists_productMap_ker_of_isPrime
    {E F G Ω : Type*} [Field E] [Field F] [Field G] [Field Ω]
    [Algebra E F] [Algebra E G] [Algebra E Ω] [IsAlgClosed Ω]
    [FiniteDimensional E F] [FiniteDimensional E G]
    (I : Ideal (F ⊗[E] G)) [I.IsPrime] :
    ∃ (f : F →ₐ[E] Ω) (g : G →ₐ[E] Ω),
      RingHom.ker (Algebra.TensorProduct.productMap f g) = I := by
  let : IsArtinianRing (F ⊗[E] G) := IsArtinianRing.of_finite E _
  let : Field ((F ⊗[E] G) ⧸ I) := Ideal.Quotient.field I
  let e : ((F ⊗[E] G) ⧸ I) →ₐ[E] Ω := IsAlgClosed.lift
  let φ := e.comp (Ideal.Quotient.mkₐ E I)
  refine ⟨φ.comp Algebra.TensorProduct.includeLeft,
    φ.comp Algebra.TensorProduct.includeRight, ?_⟩
  have hφ : Algebra.TensorProduct.productMap
      (φ.comp Algebra.TensorProduct.includeLeft)
      (φ.comp Algebra.TensorProduct.includeRight) = φ := by
    ext <;> simp [← Algebra.TensorProduct.one_def]
  rw [hφ]
  change RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk I)) = I
  rw [RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]

/-- Every minimal-prime tensor component of actual shared-middle branch fields
is realized by embeddings into an algebraically closed ambient field fixing
the middle field. This is a function-field realization; no geometric
coordinate-ring or localization identification is asserted here. -/
theorem FiniteCorrespondencePair.exists_tensor_component_embeddings
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    let E := P.targetField
    let F := adjoin (↥E) {P.source}
    let G := adjoin (↥E) {Q.target}
    ∀ I : Ideal (F ⊗[↥E] G), I ∈ (⊥ : Ideal (F ⊗[↥E] G)).minimalPrimes →
      ∃ (f : F →ₐ[↥E] Ω) (g : G →ₐ[↥E] Ω),
        RingHom.ker (Algebra.TensorProduct.productMap f g) = I := by
  intro E F G I hI
  let : FiniteDimensional (↥E) F :=
    IntermediateField.adjoin.finiteDimensional
      ((mem_racl_iff k).mp P.source_mem_target).isIntegral
  have hz : IsAlgebraic (↥E) Q.target := by
    change IsAlgebraic (adjoin k {P.target}) Q.target
    rw [h]
    exact (mem_racl_iff k).mp Q.target_mem_source
  let : FiniteDimensional (↥E) G :=
    IntermediateField.adjoin.finiteDimensional hz.isIntegral
  have : I.IsPrime := hI.isPrime
  exact exists_productMap_ker_of_isPrime I

/-- Transport a represented branch through a field embedding after lifting
its coordinates into a common field of definition. -/
private theorem realize_pair
    {k Ω K : Type*} [Field k] [Field Ω] [Field K] [Algebra k Ω] [Algebra k K]
    (P : FiniteCorrespondencePair k Ω) (ι f : K →ₐ[k] Ω) (x y : K)
    (hx : ι x = P.source) (hy : ι y = P.target) :
    ∃ R : FiniteCorrespondencePair k Ω,
      R.source = f x ∧ R.target = f y ∧ R.ideal = P.ideal := by
  have hgen : x ∉ racl k (∅ : Set K) := by
    intro hxalg
    apply P.source_generic
    rw [← hx]
    exact (algHom_mem_racl_empty_iff ι).mpr hxalg
  have hyx : y ∈ racl k {x} :=
    (algHom_mem_racl_singleton_iff ι).mp (by simpa [hx, hy] using P.target_mem_source)
  have hxy : x ∈ racl k {y} :=
    (algHom_mem_racl_singleton_iff ι).mp (by simpa [hx, hy] using P.source_mem_target)
  let R : FiniteCorrespondencePair k Ω :=
    { source := f x
      target := f y
      source_generic := (algHom_mem_racl_empty_iff f).not.mpr hgen
      target_mem_source := (algHom_mem_racl_singleton_iff f).mpr hyx
      source_mem_target := (algHom_mem_racl_singleton_iff f).mpr hxy }
  refine ⟨R, rfl, rfl, ?_⟩
  have tuple_comp (j : K →ₐ[k] Ω) :
      (⇑j ∘ ![x, y]) = (![j x, j y] : Fin 2 → Ω) := by
    funext i
    fin_cases i <;> rfl
  have hf := idealOf_comp_algHom k f (![x, y] : Fin 2 → K)
  have hi := idealOf_comp_algHom k ι (![x, y] : Fin 2 → K)
  rw [tuple_comp] at hf
  rw [tuple_comp, hx, hy] at hi
  exact hf.trans hi.symm

/-- Every minimal-prime tensor component is realized by an actual composite
of the original correspondence germs. The endpoint representatives are the
images of the two outer coordinates under embeddings fixing the middle field.
This realizes each function-field component by a represented composite; the
geometric coordinate-ring and localization bridge is a separate obligation. -/
theorem FiniteCorrespondencePair.exists_composite_of_tensor_component
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    let E := P.targetField
    let F := adjoin (↥E) {P.source}
    let G := adjoin (↥E) {Q.target}
    let x : F := ⟨P.source, subset_adjoin (↥E) {P.source} rfl⟩
    let z : G := ⟨Q.target, subset_adjoin (↥E) {Q.target} rfl⟩
    ∀ I : Ideal (F ⊗[↥E] G), I ∈ (⊥ : Ideal (F ⊗[↥E] G)).minimalPrimes →
      ∃ (f : F →ₐ[↥E] Ω) (g : G →ₐ[↥E] Ω) (R : FiniteCorrespondencePair k Ω),
        RingHom.ker (Algebra.TensorProduct.productMap f g) = I ∧
          R.source = f x ∧ R.target = g z ∧
          FiniteCorrespondenceGerm.Composes (FiniteCorrespondenceGerm.ofPair P)
            (FiniteCorrespondenceGerm.ofPair Q) (FiniteCorrespondenceGerm.ofPair R) := by
  intro E F G x z I hI
  obtain ⟨f, g, hfg⟩ := P.exists_tensor_component_embeddings Q h I hI
  let y : E := ⟨P.target, subset_adjoin k {P.target} rfl⟩
  obtain ⟨P', hx, hy, hP⟩ := realize_pair P (F.val.restrictScalars k)
    (f.restrictScalars k) x (algebraMap (↥E) F y) rfl rfl
  obtain ⟨Q', hy', hz, hQ⟩ := realize_pair Q (G.val.restrictScalars k)
    (g.restrictScalars k) (algebraMap (↥E) G y) z h rfl
  have hPmid : P'.target = P.target := hy.trans (f.commutes y)
  have hQmid : Q'.source = P.target := hy'.trans (g.commutes y)
  have hmid : P'.target = Q'.source := hPmid.trans hQmid.symm
  refine ⟨f, g, P'.comp Q' hmid, hfg, hx, hz, ?_⟩
  exact ⟨P', Q', hmid, hP.symm, hQ.symm, rfl⟩

/-- Equal kernels give the same polynomial relations on the images of any
fixed tuple, even when the source algebra is not a domain. -/
private theorem idealOf_comp_eq_of_ker_eq
    {k Ω A ι : Type*} [Field k] [Field Ω] [CommRing A]
    [Algebra k Ω] [Algebra k A] (f g : A →ₐ[k] Ω)
    (h : RingHom.ker f = RingHom.ker g) (a : ι → A) :
    idealOf k (⇑f ∘ a) = idealOf k (⇑g ∘ a) := by
  ext p
  have hf : MvPolynomial.aeval (⇑f ∘ a) p = f (MvPolynomial.aeval a p) := by
    rw [Function.comp_def, ← MvPolynomial.comp_aeval_apply]
  have hg : MvPolynomial.aeval (⇑g ∘ a) p = g (MvPolynomial.aeval a p) := by
    rw [Function.comp_def, ← MvPolynomial.comp_aeval_apply]
  rw [mem_idealOf_iff, mem_idealOf_iff, hf, hg, ← RingHom.mem_ker,
    ← RingHom.mem_ker, h]

/-- Realizations of the same tensor component have the same endpoint ideal.
Thus the composite germ does not depend on the chosen embeddings. No
injectivity of the map from tensor components to endpoint germs is asserted. -/
theorem FiniteCorrespondencePair.tensor_component_endpoint_ideal_eq
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (P Q : FiniteCorrespondencePair k Ω) :
    let E := P.targetField
    let F := adjoin (↥E) {P.source}
    let G := adjoin (↥E) {Q.target}
    let x : F := ⟨P.source, subset_adjoin (↥E) {P.source} rfl⟩
    let z : G := ⟨Q.target, subset_adjoin (↥E) {Q.target} rfl⟩
    ∀ (f₁ f₂ : F →ₐ[↥E] Ω) (g₁ g₂ : G →ₐ[↥E] Ω),
      RingHom.ker (Algebra.TensorProduct.productMap f₁ g₁) =
        RingHom.ker (Algebra.TensorProduct.productMap f₂ g₂) →
      idealOf k ![f₁ x, g₁ z] = idealOf k ![f₂ x, g₂ z] := by
  intro E F G x z f₁ f₂ g₁ g₂ h
  let a : Fin 2 → F ⊗[↥E] G := ![x ⊗ₜ[↥E] 1, 1 ⊗ₜ[↥E] z]
  have tuple_product (f : F →ₐ[↥E] Ω) (g : G →ₐ[↥E] Ω) :
      (⇑((Algebra.TensorProduct.productMap f g).restrictScalars k) ∘ a) =
        (![f x, g z] : Fin 2 → Ω) := by
    funext i
    fin_cases i <;> simp [a]
  have heq := idealOf_comp_eq_of_ker_eq
    ((Algebra.TensorProduct.productMap f₁ g₁).restrictScalars k)
    ((Algebra.TensorProduct.productMap f₂ g₂).restrictScalars k) h a
  rwa [tuple_product, tuple_product] at heq

end AclGeom
