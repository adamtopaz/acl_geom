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
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IsAlgClosed.Basic

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

Conversely, `exists_idealOf_eq_iff` realizes every prime `P` of a polynomial ring in finitely many
variables as the vanishing ideal of a tuple in an algebraically closed field `Ω` exactly when the
transcendence degree of `Ω` over `k` is at least the Krull dimension of `k[ι] ⧸ P`, an internally
chosen natural number. A private helper embeds the fraction field of `k[ι] ⧸ P` into `Ω`: a finite
transcendence basis goes to an independent family of `Ω`, and the algebraic remainder lifts
because `Ω` is algebraically closed. This is the generic-point existence used by the source's
(8.1) for an arbitrary irreducible curve; the end loci of a joint generic point are its
contractions (`idealOf_eq_comap_rename`). The full generic-extension package of blueprint
`lem:generic-extension` remains separate.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex` (#5 C2).

**Status:** proved for finite tuples, including the realization of primes; tuple composition and
the remaining C2 source obligations are separate.
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

universe u v w

/-- A field of finite transcendence degree `n` over `k` embeds over `k` into every algebraically
closed extension of `k` of transcendence degree at least `n`. -/
private theorem nonempty_algHom_of_trdeg_le {k : Type u} {K : Type v} {Ω : Type w}
    [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] [IsAlgClosed Ω] {n : ℕ} (hK : Algebra.trdeg k K = n)
    (hΩ : (n : Cardinal) ≤ Algebra.trdeg k Ω) : Nonempty (K →ₐ[k] Ω) := by
  have : FinTrdeg k K := FinTrdeg.of_trdeg (hK ▸ Cardinal.natCast_lt_aleph0)
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k K
  have : FaithfulSMul k Ω := (faithfulSMul_iff_algebraMap_injective k Ω).2
    (algebraMap k Ω).injective
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k Ω
  have hsn : Cardinal.mk s = n := hs.cardinalMk_eq_trdeg.trans hK
  obtain ⟨e⟩ : Nonempty (s ↪ B) := by
    refine Cardinal.lift_mk_le'.1 ?_
    calc Cardinal.lift.{w} (Cardinal.mk s) = (n : Cardinal.{max v w}) := by
          rw [hsn, Cardinal.lift_natCast]
      _ = Cardinal.lift.{v} (n : Cardinal.{w}) := (Cardinal.lift_natCast n).symm
      _ ≤ Cardinal.lift.{v} (Cardinal.mk B) := by
          rw [hB.cardinalMk_eq_trdeg]
          exact Cardinal.lift_le.2 hΩ
  let u : s → Ω := fun i ↦ (e i : Ω)
  have hu : AlgebraicIndependent k u := hB.1.comp e e.injective
  let K₀ := IntermediateField.adjoin k (Set.range ((↑) : s → K))
  let ψ : K₀ →ₐ[k] Ω := (IntermediateField.adjoin k (Set.range u)).val.comp
    (hs.1.aevalEquivField.symm.trans hu.aevalEquivField).toAlgHom
  let _ : Algebra K₀ Ω := ψ.toRingHom.toAlgebra
  have : IsScalarTower k K₀ Ω := IsScalarTower.of_algebraMap_eq fun c ↦ (ψ.commutes c).symm
  have : Algebra.IsAlgebraic K₀ K := hs.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift : K →ₐ[K₀] Ω).restrictScalars k⟩

/-- **Realizing a prime as the locus of a tuple.** Let `P` be a prime of the polynomial ring in
finitely many variables over a field `k`, and let `n` be the Krull dimension of `k[ι] ⧸ P`, an
internally chosen natural number. Some tuple in an algebraically closed field `Ω` over `k` has
vanishing ideal exactly `P` if and only if `Ω` has transcendence degree at least `n` over `k`.
Thus every irreducible affine locus over `k` has a generic point in every sufficiently large
algebraically closed ambient field, and the size condition cannot be dropped. -/
theorem exists_idealOf_eq_iff {k Ω ι : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    [Finite ι] (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ n : ℕ, ringKrullDim (MvPolynomial ι k ⧸ P) = n ∧
      ((∃ a : ι → Ω, idealOf k a = P) ↔ (n : Cardinal) ≤ Algebra.trdeg k Ω) := by
  let A := MvPolynomial ι k ⧸ P
  let K := FractionRing A
  have : Algebra.FiniteType k A :=
    .of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨n, hdim, htr⟩ := exists_dimension_trdeg_eq k A K
  refine ⟨n, hdim, ⟨fun h ↦ ?_, fun hΩ ↦ ?_⟩⟩
  · obtain ⟨a, ha⟩ := h
    obtain ⟨m, hm, htm⟩ := exists_locusCoordinateRing_dimension (k := k) a
    rw [ha] at hm
    have hmn : m = n := by exact_mod_cast hm.symm.trans hdim
    let F := IntermediateField.adjoin k (Set.range a)
    have : FaithfulSMul k F := (faithfulSMul_iff_algebraMap_injective k F).2
      (algebraMap k F).injective
    obtain ⟨_, x, hx⟩ := exists_isTranscendenceBasis' k F
    rw [← hmn, ← htm, ← hx.cardinalMk_eq_trdeg]
    exact (hx.1.map' (f := F.val) Subtype.val_injective).cardinalMk_le_trdeg
  · obtain ⟨φ⟩ := nonempty_algHom_of_trdeg_le htr hΩ
    refine ⟨fun i ↦ φ (algebraMap A K (Ideal.Quotient.mk P (MvPolynomial.X i))), ?_⟩
    have hφ : (MvPolynomial.aeval fun i ↦ φ (algebraMap A K (Ideal.Quotient.mk P
        (MvPolynomial.X i))) : MvPolynomial ι k →ₐ[k] Ω) =
        (φ.comp (IsScalarTower.toAlgHom k A K)).comp (Ideal.Quotient.mkₐ k P) :=
      MvPolynomial.algHom_ext fun i ↦ by
        rw [MvPolynomial.aeval_X]
        rfl
    ext p
    rw [mem_idealOf_iff, hφ, AlgHom.comp_apply, AlgHom.comp_apply,
      map_eq_zero_iff φ φ.toRingHom.injective, IsScalarTower.coe_toAlgHom',
      map_eq_zero_iff _ (IsFractionRing.injective A K), Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]

end AclGeom
