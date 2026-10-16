/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.TensorFractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dominating irreducible components of a tensor-product spectrum

The domain-level localization theorem gives actual irreducible closed components
of `Spec (B ⊗[A] C)` whose images in `Spec A` are dense. This is the middle-base
component clause of the C2 geometric bridge. Only genuine domain, fraction-field
and scalar-tower data are used. No component or dominance conclusion is an input.

`LocusPullback` transports this theorem to the actual canonical tuple-locus
scheme fiber product through Mathlib's `pullbackSpecIso`, with the actual
projection checked. `LocusEndDominance` proves the endpoint-density criterion
from the source closure hypotheses. `LocusQuotientComponents` transports the
components and actual projection-density criteria to the literal relative
quotient spectrum using `LocusQuotient`, and to the full incidence quotient
identified by `LocusIncidence`. The chosen joint prime, tuple germs/associativity
and the higher-dimensional family generic-component argument remain obligations.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/

open scoped TensorProduct

namespace AclGeom

/-- The irreducible components of the tensor-product spectrum whose images
are dense in the base spectrum are exactly the closed sets of contracted
minimal primes of the tensor product of the compatible fraction fields. -/
theorem dominatingComponents_tensorProduct_fractionRing
    {A B C K L M : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra A C] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra C M] [IsFractionRing C M]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra A M] [Algebra K M] [IsScalarTower A C M] [IsScalarTower A K M] :
    let φ := (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L M).symm.toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L)
        (IsScalarTower.toAlgHom A C M)).toRingHom
    (fun Q : Ideal (L ⊗[K] M) ↦
      PrimeSpectrum.zeroLocus (Ideal.comap φ Q : Set (B ⊗[A] C))) ''
        minimalPrimes (L ⊗[K] M) =
      {Z | Z ∈ irreducibleComponents (PrimeSpectrum (B ⊗[A] C)) ∧
        closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) '' Z) = Set.univ} := by
  classical
  intro φ
  have hG := minimalPrimes_tensorProduct_fractionRing
    (A := A) (B := B) (C := C) (K := K) (L := L) (M := M)
  have hdom (P : Ideal (B ⊗[A] C)) :
      closure (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) ''
        PrimeSpectrum.zeroLocus (P : Set (B ⊗[A] C))) = Set.univ ↔
      ∀ a : A, a ≠ 0 → algebraMap A (B ⊗[A] C) a ∉ P := by
    rw [PrimeSpectrum.closure_image_comap_zeroLocus,
      PrimeSpectrum.zeroLocus_eq_univ_iff, nilradical_eq_zero]
    change (∀ a : A, algebraMap A (B ⊗[A] C) a ∈ P → a = 0) ↔ _
    constructor
    · intro h a ha hmem
      exact ha (h a hmem)
    · intro h a hmem
      by_contra ha
      exact h a ha hmem
  ext Z
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    have hP : Ideal.comap φ Q ∈ {P : Ideal (B ⊗[A] C) |
        P ∈ minimalPrimes (B ⊗[A] C) ∧
        ∀ a : A, a ≠ 0 → algebraMap A (B ⊗[A] C) a ∉ P} := by
      rw [← hG]
      exact ⟨Q, hQ, rfl⟩
    refine ⟨?_, (hdom _).2 hP.2⟩
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
    exact ⟨Ideal.comap φ Q, hP.1, rfl⟩
  · rintro ⟨hZ, hd⟩
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    change PrimeSpectrum.zeroLocus (P : Set (B ⊗[A] C)) = Z at hZ
    subst Z
    have hmem : P ∈ {P | P ∈ minimalPrimes (B ⊗[A] C) ∧
        ∀ a : A, a ≠ 0 → algebraMap A (B ⊗[A] C) a ∉ P} := ⟨hP, (hdom P).1 hd⟩
    rw [← hG] at hmem
    obtain ⟨Q, hQ, heq⟩ := hmem
    exact ⟨Q, hQ, congrArg (fun P : Ideal (B ⊗[A] C) ↦
      PrimeSpectrum.zeroLocus (P : Set (B ⊗[A] C))) heq⟩

end AclGeom
