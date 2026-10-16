/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Minimal primes of a relative tensor product of domains

For domains `A → B` and `A → C` with fraction fields `K`, `L`, `M`, the minimal primes of
`B ⊗[A] C` meeting no nonzero element of `A` are exactly the pullbacks of the minimal primes of
`L ⊗[K] M` (`minimalPrimes_tensorProduct_fractionRing`).  No Noetherian, algebraicity,
separability, reducedness or algebraic-closedness hypothesis is used.

The proof localizes in two steps.  Inverting `B∖0` and then `C∖0` gives `L ⊗[A] M`
(`IsLocalization.tensorProduct_tensorProduct` and its right version), which is `L ⊗[K] M`
(`IsLocalization.algebraTensorEquiv`).  The second step loses no minimal prime: `L` is flat
over `A`, so `1 ⊗ c` is a nonzerodivisor.  In the first step, a minimal prime meeting no
nonzero element of `A` avoids every `b ⊗ 1`: localizing at `A∖0` through the `C` side gives
`B ⊗[A] (C ⊗[A] K)`, which is flat over `B` because `C ⊗[A] K` is flat over `A`.

This theorem is consumed by `ComponentGeometry` and, through it, the canonical tuple-locus
fiber product of blueprint §8.1 (#5). `LocusPullback` proves the actual affine-scheme
middle-dominating components, and
`LocusEndDominance` proves their endpoint-density criterion under the source closure clauses.
The literal relative quotient maps, tuple germs/associativity and the higher-dimensional
family generic-component argument remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/

open scoped TensorProduct

namespace AclGeom


/-- Under a localization, the minimal primes of the localized ring pull back exactly to the
minimal primes avoiding the inverted submonoid. -/
private theorem comap_minimalPrimes_eq {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (U : Submonoid R) [IsLocalization U T] :
    Ideal.comap (algebraMap R T) '' minimalPrimes T =
      {P | P ∈ minimalPrimes R ∧ Disjoint (U : Set R) P} := by
  have hker : ∀ P : Ideal R, P.IsPrime → Disjoint (U : Set R) P →
      Ideal.comap (algebraMap R T) ⊥ ≤ P := by
    intro P hP hd r hr
    rw [Ideal.mem_comap, Ideal.mem_bot, IsLocalization.map_eq_zero_iff U T] at hr
    obtain ⟨m, hm⟩ := hr
    exact (hP.mem_or_mem (hm ▸ P.zero_mem)).resolve_left (Set.disjoint_left.1 hd m.2)
  have key := IsLocalization.minimalPrimes_comap U T (⊥ : Ideal T)
  change Ideal.comap (algebraMap R T) '' (⊥ : Ideal T).minimalPrimes = _
  rw [← key]
  ext P
  constructor
  · intro hP
    have hd : Disjoint (U : Set R) P := by
      obtain ⟨Q, hQ, rfl⟩ := key ▸ hP
      refine Set.disjoint_left.2 fun u hu huQ ↦ hQ.1.1.ne_top ?_
      exact Ideal.eq_top_of_isUnit_mem _ huQ (IsLocalization.map_units T ⟨u, hu⟩)
    exact ⟨⟨⟨hP.1.1, bot_le⟩, fun Q hQ hQP ↦ hP.2 ⟨hQ.1, hker Q hQ.1 (hd.mono_right hQP)⟩ hQP⟩,
      hd⟩
  · rintro ⟨hP, hd⟩
    exact ⟨⟨hP.1.1, hker P hP.1.1 hd⟩, fun Q hQ hQP ↦ hP.2 ⟨hQ.1, bot_le⟩ hQP⟩

/-- Over a flat right factor, `b ⊗ 1` is a nonzerodivisor for every nonzero `b` of a domain. -/
private theorem tmul_one_mem_nonZeroDivisors {A B X : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [CommRing X] [Algebra A X] [Module.Flat A X] {b : B} (hb : b ≠ 0) :
    b ⊗ₜ[A] (1 : X) ∈ nonZeroDivisors (B ⊗[A] X) := by
  have hmul : ∀ x : B ⊗[A] X, x * (b ⊗ₜ 1) = LinearMap.rTensor X (LinearMap.mulRight A b) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul y z => simp
    | add x y hx hy => rw [add_mul, hx, hy, map_add]
  have hinj : Function.Injective (LinearMap.rTensor X (LinearMap.mulRight A b)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  refine mem_nonZeroDivisors_iff_right.2 fun x hx ↦ hinj ?_
  rw [← hmul, hx, map_zero]

/-- Over a flat left factor, `1 ⊗ c` is a nonzerodivisor for every nonzero `c` of a domain. -/
private theorem one_tmul_mem_nonZeroDivisors {A X C : Type*} [CommRing A] [CommRing C] [IsDomain C]
    [Algebra A C] [CommRing X] [Algebra A X] [Module.Flat A X] {c : C} (hc : c ≠ 0) :
    (1 : X) ⊗ₜ[A] c ∈ nonZeroDivisors (X ⊗[A] C) := by
  have hmul : ∀ x : X ⊗[A] C, x * (1 ⊗ₜ c) = LinearMap.lTensor X (LinearMap.mulRight A c) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul y z => simp
    | add x y hx hy => rw [add_mul, hx, hy, map_add]
  have hinj : Function.Injective (LinearMap.lTensor X (LinearMap.mulRight A c)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hc)
  refine mem_nonZeroDivisors_iff_right.2 fun x hx ↦ hinj ?_
  rw [← hmul, hx, map_zero]

/-- **Generic components of a relative tensor product of domains.**  Let `A → B` and `A → C` be
algebras over a domain `A`, all three domains, with fraction fields `K`, `L`, `M` compatible with
`A → K → L` and `A → K → M`.  Pulling back along `B ⊗[A] C → L ⊗[A] M ≃ L ⊗[K] M` identifies
the minimal primes of `L ⊗[K] M` with the minimal primes of `B ⊗[A] C` that meet no nonzero
element of `A`.

Injectivity of `A → B` and `A → C` follows from the fraction-field data and is not assumed. -/
theorem minimalPrimes_tensorProduct_fractionRing
    {A B C K L M : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra A C] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra C M] [IsFractionRing C M]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra A M] [Algebra K M] [IsScalarTower A C M] [IsScalarTower A K M] :
    Ideal.comap ((IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L M).symm.toRingHom.comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L)
          (IsScalarTower.toAlgHom A C M)).toRingHom) '' minimalPrimes (L ⊗[K] M) =
      {P | P ∈ minimalPrimes (B ⊗[A] C) ∧ ∀ a : A, a ≠ 0 → algebraMap A (B ⊗[A] C) a ∉ P} := by
  have hAK : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have hAL : Module.Flat A L := Module.Flat.trans A K L
  have hinjB : Function.Injective (algebraMap A B) := by
    have h : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L, RingHom.coe_comp] at h
    exact h.of_comp
  let f := IsScalarTower.toAlgHom A B L
  let g := IsScalarTower.toAlgHom A C M
  let φ1 : B ⊗[A] C →ₐ[A] L ⊗[A] C := Algebra.TensorProduct.map f (AlgHom.id A C)
  let φ2 : L ⊗[A] C →ₐ[A] L ⊗[A] M := Algebra.TensorProduct.map (AlgHom.id A L) g
  let _ : Algebra (B ⊗[A] C) (L ⊗[A] C) := φ1.toAlgebra
  let _ : Algebra (L ⊗[A] C) (L ⊗[A] M) := φ2.toAlgebra
  have : IsScalarTower B (B ⊗[A] C) (L ⊗[A] C) := .of_algebraMap_eq fun b ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ1, f, Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower L (L ⊗[A] C) (L ⊗[A] M) := .of_algebraMap_eq fun l ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ2, Algebra.TensorProduct.algebraMap_apply]
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[A] C) (nonZeroDivisors B))
      (L ⊗[A] C) :=
    IsLocalization.tensorProduct_tensorProduct A C (nonZeroDivisors B) L (by
      ext c; simp [RingHom.algebraMap_toAlgebra, φ1])
  have h2 : IsLocalization ((nonZeroDivisors C).map
      (Algebra.TensorProduct.includeRight (R := A) (A := L))) (L ⊗[A] M) :=
    IsLocalization.tensorProduct_tensorProduct_right A L (nonZeroDivisors C) M (by
      ext c; simp [RingHom.algebraMap_toAlgebra, φ2, g])
  -- The A∖0-localization, through the C side.
  let X := C ⊗[A] K
  have hAX : Module.Flat A X := by
    have : Module.Flat A (K ⊗[A] C) := Module.Flat.trans A K (K ⊗[A] C)
    exact Module.Flat.of_linearEquiv (TensorProduct.comm A C K)
  let ψ : B ⊗[A] C →ₐ[A] B ⊗[A] X :=
    Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A C X)
  let _ : Algebra (B ⊗[A] C) (B ⊗[A] X) := ψ.toAlgebra
  have : IsScalarTower B (B ⊗[A] C) (B ⊗[A] X) := .of_algebraMap_eq fun b ↦ by
    simp [RingHom.algebraMap_toAlgebra, ψ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have h3 : IsLocalization ((Algebra.algebraMapSubmonoid C (nonZeroDivisors A)).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B))) (B ⊗[A] X) :=
    IsLocalization.tensorProduct_tensorProduct_right A B
      (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) X (by
        ext c; simp [RingHom.algebraMap_toAlgebra, ψ])
  -- Minimal primes avoiding `A∖0` avoid `B∖0`.
  have hP2 : ∀ P ∈ minimalPrimes (B ⊗[A] C),
      (∀ a : A, a ≠ 0 → algebraMap A (B ⊗[A] C) a ∉ P) →
        ∀ b : B, b ≠ 0 → algebraMap B (B ⊗[A] C) b ∉ P := by
    intro P hP ha b hb hbP
    have hd : Disjoint (((Algebra.algebraMapSubmonoid C (nonZeroDivisors A)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)) : Submonoid (B ⊗[A] C)) :
          Set (B ⊗[A] C)) P := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨_, ⟨a, ha0, rfl⟩, rfl⟩
      have : algebraMap A (B ⊗[A] C) a =
          Algebra.TensorProduct.includeRight (R := A) (A := B) (algebraMap A C a) := by
        simp
      rw [← this]
      exact ha a (nonZeroDivisors.ne_zero ha0)
    have hset := comap_minimalPrimes_eq (T := B ⊗[A] X)
      ((Algebra.algebraMapSubmonoid C (nonZeroDivisors A)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)))
    obtain ⟨Q, hQ, rfl⟩ :
        P ∈ Ideal.comap (algebraMap (B ⊗[A] C) (B ⊗[A] X)) '' minimalPrimes _ := by
      rw [hset]
      exact ⟨hP, hd⟩
    have hmem : (b ⊗ₜ[A] (1 : X)) ∈ Q := by
      have := Ideal.mem_comap.1 hbP
      simpa [RingHom.algebraMap_toAlgebra, ψ, Algebra.TensorProduct.algebraMap_apply] using this
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQ) hmem
      (tmul_one_mem_nonZeroDivisors hb)
  -- The target map factors through the two one-sided localizations.
  have hφ : (Algebra.TensorProduct.map f g).toRingHom = φ2.toRingHom.comp φ1.toRingHom := by
    have h := Algebra.TensorProduct.map_comp (AlgHom.id A L) f g (AlgHom.id A C)
    rw [AlgHom.id_comp, AlgHom.comp_id] at h
    exact congrArg AlgHom.toRingHom h
  let e := (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L M).symm
  have he : Ideal.comap e.toRingHom '' minimalPrimes (L ⊗[K] M) = minimalPrimes (L ⊗[A] M) := by
    have h := Ideal.comap_minimalPrimes_eq_of_surjective (f := e.toRingHom) e.surjective ⊥
    rw [Ideal.comap_bot_of_injective (f := e.toRingHom) e.injective] at h
    exact h.symm
  -- Every minimal prime of `L ⊗[A] C` avoids `1 ⊗ (C∖0)`.
  have hstep2 : Ideal.comap φ2.toRingHom '' minimalPrimes (L ⊗[A] M) =
      minimalPrimes (L ⊗[A] C) := by
    rw [show φ2.toRingHom = algebraMap (L ⊗[A] C) (L ⊗[A] M) from rfl,
      comap_minimalPrimes_eq ((nonZeroDivisors C).map
        (Algebra.TensorProduct.includeRight (R := A) (A := L)))]
    ext Q
    refine ⟨fun h ↦ h.1, fun hQ ↦ ⟨hQ, Set.disjoint_left.2 ?_⟩⟩
    rintro _ ⟨c, hc, rfl⟩ hcQ
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQ) hcQ
      (one_tmul_mem_nonZeroDivisors (X := L) (nonZeroDivisors.ne_zero hc))
  have hstep1 : Ideal.comap φ1.toRingHom '' minimalPrimes (L ⊗[A] C) =
      {P | P ∈ minimalPrimes (B ⊗[A] C) ∧ Disjoint
        ((Algebra.algebraMapSubmonoid (B ⊗[A] C) (nonZeroDivisors B) : Submonoid _) :
          Set (B ⊗[A] C)) P} :=
    comap_minimalPrimes_eq (Algebra.algebraMapSubmonoid (B ⊗[A] C) (nonZeroDivisors B))
  rw [hφ]
  have himg : Ideal.comap (e.toRingHom.comp (φ2.toRingHom.comp φ1.toRingHom)) ''
      minimalPrimes (L ⊗[K] M) = Ideal.comap φ1.toRingHom '' (Ideal.comap φ2.toRingHom ''
        (Ideal.comap e.toRingHom '' minimalPrimes (L ⊗[K] M))) := by
    simp only [Set.image_image, Ideal.comap_comap, RingHom.comp_assoc]
  rw [himg, he, hstep2, hstep1]
  ext P
  constructor
  · rintro ⟨hP, hd⟩
    refine ⟨hP, fun a ha haP ↦ Set.disjoint_left.1 hd ⟨algebraMap A B a,
      mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinjB).2 ha), ?_⟩ haP⟩
    exact (IsScalarTower.algebraMap_apply A B (B ⊗[A] C) a).symm
  · rintro ⟨hP, ha⟩
    refine ⟨hP, Set.disjoint_left.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hP2 P hP ha b (nonZeroDivisors.ne_zero hb)

end AclGeom
