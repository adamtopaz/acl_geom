/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.LocusQuotient
import AclGeom.Correspondence.ComponentGeometry
import AclGeom.Correspondence.LocusEndDominance

/-!
# Components and endpoint density on the literal quotient tensor spectrum

For tuples `x`, `y`, `z` in a field `Ω` over `k`, let `T` be the literal relative tensor product
`k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z)`, whose base maps are induced by the inclusions
of the variables `Y`. Its endpoint maps from `k[X] ⧸ I(x)` and `k[Z] ⧸ I(z)` are induced in the same
way by the inclusions of the variables `X` and `Z`.

* `exists_locusQuotient_dominatingComponents`: the irreducible components of `Spec T` with dense
  image in `Spec (k[Y] ⧸ I(y))` are exactly the zero loci of the contractions of the minimal primes
  of `k(x, y) ⊗[k(y)] k(y, z)` along the map acting on pure tensors by the coordinate-ring
  identifications followed by the inclusions into the function fields.
* `locusQuotient_endDominance`: under the algebraicity clauses of (8.1), a subset of
  `Spec T` has dense image in `Spec (k[Y] ⧸ I(y))` if and only if it has dense image in
  `Spec (k[X] ⧸ I(x))`, and if and only if it has dense image in `Spec (k[Z] ⧸ I(z))`.

Both are transported along the homeomorphism of spectra induced by
`exists_locusQuotientTensor_algEquiv` from the canonical generated-ring results
`dominatingComponents_tensorProduct_fractionRing` and `denseImage_iff_of_isAlgebraic`. Only the
tuples are data, and the index types, the base field and the ambient field may lie in independent
universes.

This is the literal-quotient form of the middle-base component and endpoint-density clauses of
the geometric fiber-product bridge of blueprint §8.1 (8.4c, 8.6) (#5). The incidence quotient of
the joint polynomial ring by the sum of the two extended vanishing ideals, its relation to the
vanishing ideal of a joint tuple, the tuple germ layer with relational associativity and the
higher-dimensional family generic-component argument remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open MvPolynomial

namespace AclGeom

/-- Density of a spectrum image is invariant under ring isomorphisms of the source and of the target
that are compatible with the two maps. -/
private theorem closure_image_comap_eq_univ_iff_of_ringEquiv {A A' T T' : Type*} [CommRing A]
    [CommRing A'] [CommRing T] [CommRing T'] (Φ : T ≃+* T') (e : A ≃+* A') (f : A →+* T)
    (f' : A' →+* T') (hf : ∀ a, Φ (f a) = f' (e a)) (Z : Set (PrimeSpectrum T)) :
    closure (PrimeSpectrum.comap f '' Z) = Set.univ ↔
      closure (PrimeSpectrum.comap f' '' (PrimeSpectrum.homeomorphOfRingEquiv Φ '' Z)) =
        Set.univ := by
  have hcomp : (Φ.symm : T' →+* T).comp f' = f.comp (e.symm : A' →+* A) := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [Φ.symm_apply_eq, hf, e.apply_symm_apply]
  have himg : PrimeSpectrum.comap f' '' (PrimeSpectrum.homeomorphOfRingEquiv Φ '' Z) =
      PrimeSpectrum.homeomorphOfRingEquiv e '' (PrimeSpectrum.comap f '' Z) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun p _ ↦ ?_
    change PrimeSpectrum.comap f' (PrimeSpectrum.comap (Φ.symm : T' →+* T) p) =
      PrimeSpectrum.comap (e.symm : A' →+* A) (PrimeSpectrum.comap f p)
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hcomp]
  rw [himg, ← Homeomorph.image_closure]
  constructor
  · intro h
    rw [h, Set.image_univ_of_surjective (Homeomorph.surjective _)]
  · intro h
    apply (Homeomorph.injective (PrimeSpectrum.homeomorphOfRingEquiv e)).image_injective
    rw [h, Set.image_univ_of_surjective (Homeomorph.surjective _)]

/-- The irreducible components of a tensor spectrum with dense image in the base spectrum,
transported along a ring isomorphism to a tensor product of domains with compatible fraction fields
that is compatible with pure tensors and the base maps. -/
private theorem exists_dominatingComponents_of_ringEquiv {A B C A' B' C' K L M : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [CommRing A'] [IsDomain A'] [CommRing B'] [IsDomain B'] [CommRing C'] [IsDomain C']
    [Field K] [Field L] [Field M] [Algebra A' B'] [Algebra A' C'] [Algebra A' K]
    [IsFractionRing A' K] [Algebra B' L] [IsFractionRing B' L] [Algebra C' M] [IsFractionRing C' M]
    [Algebra A' L] [Algebra K L] [IsScalarTower A' B' L] [IsScalarTower A' K L]
    [Algebra A' M] [Algebra K M] [IsScalarTower A' C' M] [IsScalarTower A' K M]
    (Φ : B ⊗[A] C ≃+* B' ⊗[A'] C') (eA : A ≃+* A') (eB : B ≃+* B') (eC : C ≃+* C')
    (htmul : ∀ b c, Φ (b ⊗ₜ c) = eB b ⊗ₜ eC c)
    (hbase : ∀ a, Φ (algebraMap A (B ⊗[A] C) a) = algebraMap A' (B' ⊗[A'] C') (eA a)) :
    ∃ ψ : B ⊗[A] C →+* L ⊗[K] M,
      (∀ b c, ψ (b ⊗ₜ c) = algebraMap B' L (eB b) ⊗ₜ algebraMap C' M (eC c)) ∧
      {Z | Z ∈ irreducibleComponents (PrimeSpectrum (B ⊗[A] C)) ∧
          closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' Z) = Set.univ} =
        (fun Q : Ideal (L ⊗[K] M) ↦ PrimeSpectrum.zeroLocus (Ideal.comap ψ Q : Set (B ⊗[A] C))) ''
          minimalPrimes (L ⊗[K] M) := by
  let φ : B' ⊗[A'] C' →+* L ⊗[K] M :=
    (IsLocalization.algebraTensorEquiv (nonZeroDivisors A') K L M).symm.toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' B' L)
        (IsScalarTower.toAlgHom A' C' M)).toRingHom
  have hφ : (fun Q : Ideal (L ⊗[K] M) ↦
      PrimeSpectrum.zeroLocus (Ideal.comap φ Q : Set (B' ⊗[A'] C'))) '' minimalPrimes (L ⊗[K] M) =
      {W | W ∈ irreducibleComponents (PrimeSpectrum (B' ⊗[A'] C')) ∧
        closure (PrimeSpectrum.comap (algebraMap A' (B' ⊗[A'] C')) '' W) = Set.univ} :=
    dominatingComponents_tensorProduct_fractionRing
  let h := PrimeSpectrum.homeomorphOfRingEquiv Φ
  have hd (Z : Set (PrimeSpectrum (B ⊗[A] C))) :
      closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' Z) = Set.univ ↔
        closure (PrimeSpectrum.comap (algebraMap A' (B' ⊗[A'] C')) '' (h '' Z)) = Set.univ :=
    closure_image_comap_eq_univ_iff_of_ringEquiv Φ eA _ _ hbase Z
  have hzero (Q : Ideal (L ⊗[K] M)) :
      h ⁻¹' PrimeSpectrum.zeroLocus (Ideal.comap φ Q : Set (B' ⊗[A'] C')) =
        PrimeSpectrum.zeroLocus
          (Ideal.comap (φ.comp (Φ : B ⊗[A] C →+* B' ⊗[A'] C')) Q : Set (B ⊗[A] C)) := by
    change PrimeSpectrum.comap (Φ.symm : B' ⊗[A'] C' →+* B ⊗[A] C) ⁻¹' _ = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    congr 1
    ext t
    simp only [Set.mem_image, SetLike.mem_coe, Ideal.mem_comap, RingHom.comp_apply,
      RingEquiv.coe_toRingHom]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Φ.apply_symm_apply]
    · exact fun ht ↦ ⟨Φ t, ht, Φ.symm_apply_apply t⟩
  refine ⟨φ.comp (Φ : B ⊗[A] C →+* B' ⊗[A'] C'), fun b c ↦ (congrArg φ (htmul b c)).trans rfl,
    ?_⟩
  ext Z
  constructor
  · rintro ⟨hZ, hdZ⟩
    have hW : h '' Z ∈ {W | W ∈ irreducibleComponents (PrimeSpectrum (B' ⊗[A'] C')) ∧
        closure (PrimeSpectrum.comap (algebraMap A' (B' ⊗[A'] C')) '' W) = Set.univ} := by
      refine ⟨?_, (hd Z).1 hdZ⟩
      obtain ⟨z, hz⟩ := hZ.1.nonempty
      rw [h.image_eq_preimage_symm]
      exact preimage_mem_irreducibleComponents hZ h.symm.isOpenEmbedding
        ⟨z, hz, h.symm.surjective z⟩
    rw [← hφ] at hW
    obtain ⟨Q, hQ, hQZ⟩ := hW
    refine ⟨Q, hQ, ?_⟩
    change PrimeSpectrum.zeroLocus
      (Ideal.comap (φ.comp (Φ : B ⊗[A] C →+* B' ⊗[A'] C')) Q : Set (B ⊗[A] C)) = Z
    change PrimeSpectrum.zeroLocus (Ideal.comap φ Q : Set (B' ⊗[A'] C')) = h '' Z at hQZ
    rw [← hzero, hQZ, h.preimage_image]
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hirr, hdense⟩ := hφ ▸ Set.mem_image_of_mem
      (fun Q : Ideal (L ⊗[K] M) ↦ PrimeSpectrum.zeroLocus (Ideal.comap φ Q : Set (B' ⊗[A'] C'))) hQ
    refine ⟨?_, ?_⟩
    · change PrimeSpectrum.zeroLocus
        (Ideal.comap (φ.comp (Φ : B ⊗[A] C →+* B' ⊗[A'] C')) Q : Set (B ⊗[A] C)) ∈
          irreducibleComponents (PrimeSpectrum (B ⊗[A] C))
      rw [← hzero]
      obtain ⟨w, hw⟩ := hirr.1.nonempty
      exact preimage_mem_irreducibleComponents hirr h.isOpenEmbedding ⟨w, hw, h.surjective w⟩
    · change closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' PrimeSpectrum.zeroLocus
        (Ideal.comap (φ.comp (Φ : B ⊗[A] C →+* B' ⊗[A'] C')) Q : Set (B ⊗[A] C))) = Set.univ
      rw [hd, ← hzero, h.image_preimage]
      exact hdense

/-- Endpoint density on a tensor spectrum, transported along a ring isomorphism to a tensor product
of domains whose endpoint extensions are injective and algebraic. -/
private theorem endDominance_of_ringEquiv {A B C X Z A' B' C' X' Z' : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing X] [CommRing Z] [Algebra A B] [Algebra A C]
    [CommRing A'] [CommRing B'] [CommRing C'] [CommRing X'] [CommRing Z']
    [IsDomain A'] [IsDomain B'] [IsDomain C'] [IsDomain X'] [IsDomain Z']
    [Algebra A' B'] [Algebra A' C'] [Algebra X' B'] [Algebra Z' C']
    [Algebra.IsAlgebraic A' B'] [Algebra.IsAlgebraic X' B'] [Algebra.IsAlgebraic A' C']
    [Algebra.IsAlgebraic Z' C']
    (hAB : Function.Injective (algebraMap A' B')) (hXB : Function.Injective (algebraMap X' B'))
    (hAC : Function.Injective (algebraMap A' C')) (hZC : Function.Injective (algebraMap Z' C'))
    (Φ : B ⊗[A] C ≃+* B' ⊗[A'] C') (eA : A ≃+* A') (eB : B ≃+* B') (eC : C ≃+* C')
    (eX : X ≃+* X') (eZ : Z ≃+* Z') (fX : X →+* B) (fZ : Z →+* C)
    (htmul : ∀ b c, Φ (b ⊗ₜ c) = eB b ⊗ₜ eC c)
    (hbase : ∀ a, Φ (algebraMap A (B ⊗[A] C) a) = algebraMap A' (B' ⊗[A'] C') (eA a))
    (hX : ∀ u, eB (fX u) = algebraMap X' B' (eX u)) (hZ : ∀ u, eC (fZ u) = algebraMap Z' C' (eZ u))
    (W : Set (PrimeSpectrum (B ⊗[A] C))) :
    (closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' W) = Set.univ ↔
      closure (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom.comp fX) '' W) =
        Set.univ) ∧
    (closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' W) = Set.univ ↔
      closure (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom.comp fZ) '' W) =
        Set.univ) := by
  -- `X'` acts on `B' ⊗[A'] C'` through the left factor by Mathlib's `leftAlgebra`; `C'` and `Z'`
  -- act through the right factor.
  have : IsScalarTower A' B' (B' ⊗[A'] C') := .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra C' (B' ⊗[A'] C') := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra Z' (B' ⊗[A'] C') :=
    ((algebraMap C' (B' ⊗[A'] C')).comp (algebraMap Z' C')).toAlgebra
  have : IsScalarTower Z' C' (B' ⊗[A'] C') := .of_algebraMap_eq' rfl
  have hY := closure_image_comap_eq_univ_iff_of_ringEquiv Φ eA (algebraMap A (B ⊗[A] C))
    (algebraMap A' (B' ⊗[A'] C')) hbase W
  have hXd := closure_image_comap_eq_univ_iff_of_ringEquiv Φ eX
    (Algebra.TensorProduct.includeLeftRingHom.comp fX) (algebraMap X' (B' ⊗[A'] C'))
    (fun u ↦ by
      change Φ (fX u ⊗ₜ[A] 1) = algebraMap X' B' (eX u) ⊗ₜ[A'] 1
      rw [htmul, hX, map_one]) W
  have hZd := closure_image_comap_eq_univ_iff_of_ringEquiv Φ eZ
    ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom.comp fZ)
    (algebraMap Z' (B' ⊗[A'] C'))
    (fun u ↦ by
      change Φ (1 ⊗ₜ[A] fZ u) = 1 ⊗ₜ[A'] algebraMap Z' C' (eZ u)
      rw [htmul, map_one, hZ]) W
  exact ⟨hY.trans (((denseImage_iff_of_isAlgebraic hAB _).trans
      (denseImage_iff_of_isAlgebraic hXB _).symm).trans hXd.symm),
    hY.trans (((denseImage_iff_of_isAlgebraic hAC _).trans
      (denseImage_iff_of_isAlgebraic hZC _).symm).trans hZd.symm)⟩

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {α β γ : Type*}
  (x : α → Ω) (y : β → Ω) (z : γ → Ω)

local notation "𝒜" => MvPolynomial β k ⧸ idealOf k y
local notation "ℬ" => MvPolynomial (α ⊕ β) k ⧸ idealOf k (Sum.elim x y)
local notation "𝒞" => MvPolynomial (β ⊕ γ) k ⧸ idealOf k (Sum.elim y z)
local notation "𝔛" => Algebra.adjoin k (Set.range x)
local notation "𝔄" => Algebra.adjoin k (Set.range y)
local notation "ℨ" => Algebra.adjoin k (Set.range z)
local notation "𝔅" => Algebra.adjoin k (Set.range (Sum.elim x y))
local notation "ℭ" => Algebra.adjoin k (Set.range (Sum.elim y z))
local notation "𝔎" => IntermediateField.adjoin k (Set.range y)
local notation "𝔏" => IntermediateField.adjoin k (Set.range (Sum.elim x y))
local notation "𝔐" => IntermediateField.adjoin k (Set.range (Sum.elim y z))

/-- **Dominating components of the literal quotient tensor spectrum.** The irreducible components
of `Spec (k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z))` with dense image in
`Spec (k[Y] ⧸ I(y))` are exactly the zero loci of the contractions of the minimal primes of
`k(x, y) ⊗[k(y)] k(y, z)` along the ring map that sends `a ⊗ b` to the images of `a` and `b` under
the coordinate-ring identifications and the inclusions into the function fields. -/
theorem exists_locusQuotient_dominatingComponents :
    letI : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
      (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
        rfl).le).toAlgebra
    letI : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
      (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
        rfl).le).toAlgebra
    letI : Algebra 𝔎 𝔏 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
      (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toRingHom.toAlgebra
    letI : Algebra 𝔎 𝔐 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
      (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toRingHom.toAlgebra
    ∃ ψ : ℬ ⊗[𝒜] 𝒞 →+* 𝔏 ⊗[𝔎] 𝔐,
      (∀ (a : ℬ) (b : 𝒞), ψ (a ⊗ₜ b) =
        algebraMap 𝔅 𝔏 (locusCoordinateRingEquiv (Sum.elim x y) a) ⊗ₜ
          algebraMap ℭ 𝔐 (locusCoordinateRingEquiv (Sum.elim y z) b)) ∧
      {Z : Set (PrimeSpectrum (ℬ ⊗[𝒜] 𝒞)) | Z ∈ irreducibleComponents _ ∧
          closure (PrimeSpectrum.comap (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞)) '' Z) = Set.univ} =
        (fun Q : Ideal (𝔏 ⊗[𝔎] 𝔐) ↦
          PrimeSpectrum.zeroLocus (Ideal.comap ψ Q : Set (ℬ ⊗[𝒜] 𝒞))) ''
          minimalPrimes (𝔏 ⊗[𝔎] 𝔐) := by
  -- Term-mode `letI` inlines its values; the same structures are declared locally here.
  let _ : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
    (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
      rfl).le).toAlgebra
  let _ : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
    (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
      rfl).le).toAlgebra
  let _ : Algebra 𝔎 𝔏 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toRingHom.toAlgebra
  let _ : Algebra 𝔎 𝔐 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toRingHom.toAlgebra
  let _ : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
  let _ : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
  let _ : Algebra 𝔄 𝔏 := ((algebraMap 𝔎 𝔏).comp (algebraMap 𝔄 𝔎)).toAlgebra
  let _ : Algebra 𝔄 𝔐 := ((algebraMap 𝔎 𝔐).comp (algebraMap 𝔄 𝔎)).toAlgebra
  have : IsScalarTower 𝔄 𝔎 𝔏 := .of_algebraMap_eq' rfl
  have : IsScalarTower 𝔄 𝔎 𝔐 := .of_algebraMap_eq' rfl
  have : IsScalarTower 𝔄 𝔅 𝔏 := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower 𝔄 ℭ 𝔐 := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨Φ, htmul, hbase⟩ := exists_locusQuotientTensor_algEquiv (k := k) x y z
  exact exists_dominatingComponents_of_ringEquiv Φ.toRingEquiv
    (locusCoordinateRingEquiv (k := k) y).toRingEquiv
    (locusCoordinateRingEquiv (k := k) (Sum.elim x y)).toRingEquiv
    (locusCoordinateRingEquiv (k := k) (Sum.elim y z)).toRingEquiv htmul hbase

/-- **Endpoint density on the literal quotient tensor spectrum.** Under the algebraicity clauses
of (8.1) for `(x, y)` and `(y, z)`, a subset of
`Spec (k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z))` has dense image in `Spec (k[Y] ⧸ I(y))`
if and only if it has dense image in `Spec (k[X] ⧸ I(x))`, and if and only if it has dense image in
`Spec (k[Z] ⧸ I(z))`, along the maps induced by the inclusions of the variables. -/
theorem locusQuotient_endDominance (hxy : ∀ i, x i ∈ racl k (Set.range y))
    (hyx : ∀ j, y j ∈ racl k (Set.range x)) (hzy : ∀ i, z i ∈ racl k (Set.range y))
    (hyz : ∀ j, y j ∈ racl k (Set.range z)) :
    letI : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
      (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
        rfl).le).toAlgebra
    letI : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
      (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
        rfl).le).toAlgebra
    ∀ W : Set (PrimeSpectrum (ℬ ⊗[𝒜] 𝒞)),
      (closure (PrimeSpectrum.comap (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞)) '' W) = Set.univ ↔
        closure (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom.comp
          (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inl)
            (idealOf_eq_comap_rename (a := Sum.elim x y) (b := x) (g := Sum.inl)
              rfl).le).toRingHom) '' W) = Set.univ) ∧
      (closure (PrimeSpectrum.comap (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞)) '' W) = Set.univ ↔
        closure (PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : 𝒞 →ₐ[𝒜] ℬ ⊗[𝒜] 𝒞).toRingHom.comp
            (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inr)
              (idealOf_eq_comap_rename (a := Sum.elim y z) (b := z) (g := Sum.inr)
                rfl).le).toRingHom) '' W) = Set.univ) := by
  -- Term-mode `letI` inlines its values; the same structures are declared locally here.
  let _ : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
    (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
      rfl).le).toAlgebra
  let _ : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
    (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
      rfl).le).toAlgebra
  let _ : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
  let _ : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
  let _ : Algebra 𝔛 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range x y ▸ Set.subset_union_left))).toAlgebra
  let _ : Algebra ℨ ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range y z ▸ Set.subset_union_right))).toAlgebra
  -- The algebraicity of the four coordinate extensions, from the closure hypotheses.
  have : Algebra.IsAlgebraic 𝔄 𝔅 := isAlgebraic_adjoin_of_subset_racl (k := k) _ _
    (Set.Sum.elim_range x y ▸ Set.subset_union_right) (by
      rw [Set.Sum.elim_range]
      exact Set.union_subset (Set.range_subset_iff.2 hxy) (subset_racl k _))
  have : Algebra.IsAlgebraic 𝔛 𝔅 := isAlgebraic_adjoin_of_subset_racl (k := k) _ _
    (Set.Sum.elim_range x y ▸ Set.subset_union_left) (by
      rw [Set.Sum.elim_range]
      exact Set.union_subset (subset_racl k _) (Set.range_subset_iff.2 hyx))
  have : Algebra.IsAlgebraic 𝔄 ℭ := isAlgebraic_adjoin_of_subset_racl (k := k) _ _
    (Set.Sum.elim_range y z ▸ Set.subset_union_left) (by
      rw [Set.Sum.elim_range]
      exact Set.union_subset (subset_racl k _) (Set.range_subset_iff.2 hzy))
  have : Algebra.IsAlgebraic ℨ ℭ := isAlgebraic_adjoin_of_subset_racl (k := k) _ _
    (Set.Sum.elim_range y z ▸ Set.subset_union_right) (by
      rw [Set.Sum.elim_range]
      exact Set.union_subset (Set.range_subset_iff.2 hyz) (subset_racl k _))
  obtain ⟨Φ, htmul, hbase⟩ := exists_locusQuotientTensor_algEquiv (k := k) x y z
  intro W
  exact endDominance_of_ringEquiv (Subalgebra.inclusion_injective _)
    (Subalgebra.inclusion_injective _) (Subalgebra.inclusion_injective _)
    (Subalgebra.inclusion_injective _) Φ.toRingEquiv
    (locusCoordinateRingEquiv (k := k) y).toRingEquiv
    (locusCoordinateRingEquiv (k := k) (Sum.elim x y)).toRingEquiv
    (locusCoordinateRingEquiv (k := k) (Sum.elim y z)).toRingEquiv
    (locusCoordinateRingEquiv (k := k) x).toRingEquiv
    (locusCoordinateRingEquiv (k := k) z).toRingEquiv
    (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inl)
      (idealOf_eq_comap_rename (a := Sum.elim x y) (b := x) (g := Sum.inl) rfl).le).toRingHom
    (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inr)
      (idealOf_eq_comap_rename (a := Sum.elim y z) (b := z) (g := Sum.inr) rfl).le).toRingHom
    htmul hbase
    (AlgHom.congr_fun (locusCoordinateRingEquiv_comp_quotientMapₐ (k := k) (a := Sum.elim x y)
      (b := x) (g := Sum.inl) rfl))
    (AlgHom.congr_fun (locusCoordinateRingEquiv_comp_quotientMapₐ (k := k) (a := Sum.elim y z)
      (b := z) (g := Sum.inr) rfl)) W

end AclGeom
