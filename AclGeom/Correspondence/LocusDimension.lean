/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Krull dimension of a finite tuple locus

The first paragraph of blueprint §8 identifies the dimension of a tuple locus with
its generated field's transcendence degree. `exists_locusCoordinateRing_dimension`
proves this for the literal coordinate ring `MvPolynomial ι k ⧸ idealOf k a`.
Both dimensions are one internally obtained finite natural number, over arbitrary
base and ambient fields and any finite index type. No algebraic-closedness,
rank-one, rationality or supplied dimension premise is needed.

Two private helpers compare Krull dimensions under integral faithful extensions
and apply Noether normalization to a finite-type domain and its fraction field.
Their consumer is the actual finite-tuple locus theorem below.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex` (#5 C2).

**Status:** proved for finite tuples; tuple composition and the remaining C2
source obligations are separate.
-/
namespace AclGeom

private theorem dimension_eq_of_integral_faithful (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      (fun p q hpq ↦ Ideal.IsIntegral.under_lt_under hpq)
  · apply iSup_le
    intro l
    obtain ⟨P⟩ := (inferInstance : Nonempty (Ideal.primesOver l.head.asIdeal S))
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.val
    change (l.length : WithBot ℕ∞) ≤ _
    rw [← hlen]
    exact le_iSup (fun p : LTSeries (PrimeSpectrum S) ↦ (p.length : WithBot ℕ∞)) L

private theorem exists_dimension_trdeg_eq (k A F : Type*) [Field k] [CommRing A] [IsDomain A]
    [Field F] [Algebra k A] [Algebra A F] [IsFractionRing A F] [Algebra k F]
    [IsScalarTower k A F] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = n ∧ Algebra.trdeg k F = n := by
  obtain ⟨n, g, hg, hgintegral⟩ := exists_integral_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin n) k) A := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) A := .of_algHom g
  have : Algebra.IsIntegral (MvPolynomial (Fin n) k) A := ⟨hgintegral⟩
  have : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have hdim : ringKrullDim A = n := by
    rw [dimension_eq_of_integral_faithful (MvPolynomial (Fin n) k) A]
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, Nat.card_fin, zero_add]
  have hA := (IsTranscendenceBasis.mvPolynomial (Fin n) k).algebraMap_comp (A := A)
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hF := hA.algebraMap_comp (A := F)
  have hcard := hF.lift_cardinalMk_eq_trdeg
  have htr : Algebra.trdeg k F = n := by
    simpa only [Cardinal.lift_mk_fin, Cardinal.lift_eq_nat_iff] using hcard.symm
  exact ⟨n, hdim, htr⟩

open scoped IntermediateField.algebraAdjoinAdjoin

/-- The Krull dimension of the literal coordinate ring `k[ι]/I(a)` and the transcendence degree
of the generated field are the same finite natural number. -/
theorem exists_locusCoordinateRing_dimension {k Ω ι : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [Finite ι] (a : ι → Ω) :
    ∃ n : ℕ, ringKrullDim (MvPolynomial ι k ⧸ idealOf k a) = n ∧
      Algebra.trdeg k (IntermediateField.adjoin k (Set.range a)) = n := by
  let A := Algebra.adjoin k (Set.range a)
  let F := IntermediateField.adjoin k (Set.range a)
  have : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range a)
  obtain ⟨n, hdim, htr⟩ := exists_dimension_trdeg_eq k A F
  exact ⟨n, (ringKrullDim_eq_of_ringEquiv (locusCoordinateRingEquiv a).toRingEquiv).trans hdim,
    htr⟩
end AclGeom
