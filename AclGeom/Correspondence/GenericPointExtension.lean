/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.LocusIncomparability
import AclGeom.Correspondence.LocusDimension
import AclGeom.Correspondence.GenericExtension
import AclGeom.Correspondence.GeometricPrime
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Generic points of a variety over a coefficient extension

Blueprint Lemma `generic-extension` (a): let `V` be an irreducible affine variety over an
algebraically closed field `k`, given by a prime `P` of `k[ι]` with `ι` finite, and let `E/k` be a
field extension. In §8 a generic point of `V` over `E` is a point of `V` whose field over `E` has
the transcendence degree of `V`. `genericExtension_genericPoint` proves, with the dimension `n`
chosen internally, that `k[ι] ⧸ P` and `E[ι] ⧸ P E[ι]` both have Krull dimension `n`. Every point
`v` of `V` in any field `Ω` over `E` with `trdeg_E E(v) = n` has vanishing ideal over `E` exactly
the extended ideal, has vanishing ideal `P` over `k`, and generates a field linearly disjoint from
`E` over `k`. When `Ω` is algebraically closed, such points exist exactly when
`trdeg_E Ω ≥ n`.

The proof realizes the extended prime by a reference point in the algebraic closure of a
rational function field in countably many variables over `E`. Its ideals and ranks are computed
by `isGeneric_baseChange`, `trdeg_adjoin_of_isGeneric` and `exists_locusCoordinateRing_dimension`.
For a point of `V` of rank `n`, a maximal independent coordinate subfamily has `n` elements. The
same coordinates of the reference point form a transcendence basis, and algebraic incomparability
(`idealOf_eq_of_le_of_comap_eq`) identifies the two ideals. No dimension theory for the extended
quotient is assumed: its dimension is read off the reference point. Parts (b) and (c) are
`exists_ambientAutomorphism_of_idealOf_eq` and `AlgebraicIndependent.aevalEquivField`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved for finite tuples (#5).
-/

open MvPolynomial

namespace AclGeom

universe u v w z

/-- The algebraic closure of the rational function field in countably many variables over `E` has
infinite transcendence degree over `E`. -/
private theorem aleph0_le_trdeg_ref (E : Type v) [Field E] :
    Cardinal.aleph0 ≤
      Algebra.trdeg E (AlgebraicClosure (FractionRing (MvPolynomial ℕ E))) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom E (MvPolynomial ℕ E)
      (AlgebraicClosure (FractionRing (MvPolynomial ℕ E)))) := by
    change Function.Injective (algebraMap (MvPolynomial ℕ E)
      (AlgebraicClosure (FractionRing (MvPolynomial ℕ E))))
    rw [IsScalarTower.algebraMap_eq (MvPolynomial ℕ E) (FractionRing (MvPolynomial ℕ E))
      (AlgebraicClosure (FractionRing (MvPolynomial ℕ E)))]
    exact (algebraMap (FractionRing (MvPolynomial ℕ E)) _).injective.comp
      (IsFractionRing.injective _ _)
  have hX := (MvPolynomial.algebraicIndependent_X ℕ E).map' hinj
  simpa using hX.lift_cardinalMk_le_trdeg

/-- A maximal independent coordinate subfamily of a finite tuple spans it algebraically. -/
private theorem exists_basis_coords {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {ι : Type*}
    [Finite ι] (v : ι → Ω) :
    ∃ S : Set ι, AlgebraicIndepOn E v S ∧ ∀ i, v i ∈ racl E (v '' S) := by
  obtain ⟨S, hS⟩ := (Set.toFinite {S : Set ι | AlgebraicIndepOn E v S}).exists_maximal
    ⟨∅, algebraicIndependent_empty_type_iff.2 (algebraMap E Ω).injective⟩
  refine ⟨S, hS.1, fun i ↦ ?_⟩
  by_cases hi : i ∈ S
  · exact subset_racl E _ ⟨i, hi, rfl⟩
  · rw [mem_racl_iff_isAlgebraic_adjoin]
    by_contra htr
    exact hi (hS.2 ((AlgebraicIndepOn.insert_iff hi).2 ⟨hS.1, htr⟩) (Set.subset_insert _ _)
      (Set.mem_insert _ _))


/-- **A point of a locus with the rank of the locus is generic.** If the vanishing ideal of a
finite tuple `t` is contained in that of `v`, and both generate fields of the same finite
transcendence degree, the two vanishing ideals are equal. -/
private theorem idealOf_eq_of_le_of_trdeg_eq {E K Ω : Type*} [Field E] [Field K] [Field Ω]
    [Algebra E K] [Algebra E Ω] {ι : Type*} [Finite ι] (t : ι → K) (v : ι → Ω) {n : ℕ}
    (hle : idealOf E t ≤ idealOf E v)
    (ht : Algebra.trdeg E (IntermediateField.adjoin E (Set.range t)) = n)
    (hv : Algebra.trdeg E (IntermediateField.adjoin E (Set.range v)) = n) :
    idealOf E v = idealOf E t := by
  obtain ⟨S, hSind, hSspan⟩ := exists_basis_coords (E := E) v
  let g : S → ι := Subtype.val
  have hvS : idealOf E (v ∘ g) = ⊥ := algebraicIndependent_iff_ker_eq_bot.1 hSind
  have hcomapv : (idealOf E v).comap (rename g : MvPolynomial S E →ₐ[E] MvPolynomial ι E) = ⊥ :=
    (idealOf_eq_comap_rename (k := E) (a := v) (b := v ∘ g) (g := g) rfl).symm.trans hvS
  -- The subfamily is a transcendence basis of `E(v)`, so it has `n` elements.
  let F := IntermediateField.adjoin E (Set.range v)
  let w : S → F := fun i ↦ ⟨v i, IntermediateField.subset_adjoin E _ ⟨i, rfl⟩⟩
  have hwind : AlgebraicIndependent E w := AlgebraicIndependent.of_comp F.val hSind
  have hwb : IsTranscendenceBasis E w := by
    refine hwind.isTranscendenceBasis_iff_isAlgebraic.2 ⟨fun z ↦ ?_⟩
    rw [← mem_racl_iff_isAlgebraic_adjoin, ← coe_mem_racl_image_iff, ← Set.range_comp]
    have hz : (z : Ω) ∈ racl E (v '' S) :=
      (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 hSspan) :
        F ≤ racl E (v '' S)) z.2
    rwa [Set.image_eq_range] at hz
  have hS : Cardinal.mk S = n := by
    have h := hwb.lift_cardinalMk_eq_trdeg
    rw [hv, Cardinal.lift_natCast] at h
    exact Cardinal.lift_eq_nat_iff.1 h
  -- The same coordinates of `t` are independent, hence a basis of `E(t)`.
  have htS : idealOf E (t ∘ g) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [idealOf_eq_comap_rename (k := E) (a := t) (b := t ∘ g) (g := g) rfl]
    exact (Ideal.comap_mono hle).trans hcomapv.le
  let G := IntermediateField.adjoin E (Set.range t)
  let w' : S → G := fun i ↦ ⟨t i, IntermediateField.subset_adjoin E _ ⟨i, rfl⟩⟩
  have hw'ind : AlgebraicIndependent E w' :=
    AlgebraicIndependent.of_comp G.val (algebraicIndependent_iff_ker_eq_bot.2 htS)
  have hw'b : IsTranscendenceBasis E w' := by
    refine hw'ind.isTranscendenceBasis_of_lift_trdeg_le_of_finite ?_
    rw [ht, hS, Cardinal.lift_natCast, Cardinal.lift_natCast]
  have halg : ∀ i, t i ∈ racl E (Set.range (t ∘ g)) := fun i ↦ by
    have hx : (⟨t i, IntermediateField.subset_adjoin E _ ⟨i, rfl⟩⟩ : G) ∈
        racl E (Set.range w') :=
      (mem_racl_iff_isAlgebraic_adjoin E).2 (hw'b.isAlgebraic.isAlgebraic _)
    rw [← coe_mem_racl_image_iff, ← Set.range_comp] at hx
    exact hx
  exact idealOf_eq_of_le_of_comap_eq (k := E) t g halg hle (hcomapv.trans htS.symm)

/-- **Generic points after scalar extension** (blueprint `lem:generic-extension` (a)). Let `k` be
algebraically closed, `E/k` a field extension, `Ω` any field over `E`, and `P` a prime of `k[ι]`
with `ι` finite. For an internally chosen `n`, both `k[ι] ⧸ P` and `E[ι] ⧸ P E[ι]` have Krull
dimension `n`. Every point `v` of the locus of `P` with `trdeg_E E(v) = n` has vanishing ideal
`P E[ι]` over `E` and `P` over `k`, and `E` and `k(v)` are linearly disjoint over `k`. If `Ω` is
algebraically closed, a tuple with vanishing ideal `P E[ι]` over `E` exists exactly when
`trdeg_E Ω ≥ n`. -/
theorem genericExtension_genericPoint {k : Type u} {E : Type v} {Ω : Type w} {ι : Type z}
    [Field k] [IsAlgClosed k] [Field E] [Algebra k E] [Field Ω] [Algebra k Ω] [Algebra E Ω]
    [IsScalarTower k E Ω] [Finite ι] (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ n : ℕ, ringKrullDim (MvPolynomial ι k ⧸ P) = n ∧
      ringKrullDim (MvPolynomial ι E ⧸ P.map (MvPolynomial.map (algebraMap k E))) = n ∧
      (∀ v : ι → Ω, P ≤ idealOf k v →
          Algebra.trdeg E (IntermediateField.adjoin E (Set.range v)) = n →
          idealOf E v = P.map (MvPolynomial.map (algebraMap k E)) ∧ idealOf k v = P ∧
            (IsScalarTower.toAlgHom k E Ω).fieldRange.LinearDisjoint
              (IntermediateField.adjoin k (Set.range v))) ∧
      (IsAlgClosed Ω → ((∃ v : ι → Ω, idealOf E v = P.map (MvPolynomial.map (algebraMap k E))) ↔
          (n : Cardinal) ≤ Algebra.trdeg E Ω)) := by
  have hPe : (P.map (MvPolynomial.map (algebraMap k E))).IsPrime :=
    isPrime_map_of_isAlgClosed (E := E) P
  -- A reference generic point over `E` in a field of infinite transcendence degree.
  let R := AlgebraicClosure (FractionRing (MvPolynomial ℕ E))
  obtain ⟨nE, hnE, hiffR⟩ := exists_idealOf_eq_iff (k := E) (Ω := R)
    (P.map (MvPolynomial.map (algebraMap k E)))
  obtain ⟨t, ht⟩ := hiffR.2 (Cardinal.natCast_lt_aleph0.le.trans (aleph0_le_trdeg_ref E))
  have htk : idealOf k t = P := (isGeneric_baseChange (k := k) (E := E) (Ω := R) ht).1
  have htr := trdeg_adjoin_of_isGeneric (k := k) (E := E) (Ω := R) ht
  obtain ⟨n, hn, hntr⟩ := exists_locusCoordinateRing_dimension (k := k) t
  obtain ⟨n', hn', hn'tr⟩ := exists_locusCoordinateRing_dimension (k := E) t
  have hnn : n' = n := by exact_mod_cast hn'tr.symm.trans (htr.trans hntr)
  have hdimE : ringKrullDim (MvPolynomial ι E ⧸ P.map (MvPolynomial.map (algebraMap k E))) = n := by
    rw [← ht, hn', hnn]
  refine ⟨n, by rw [← htk]; exact hn, hdimE, fun v hv hrank ↦ ?_, fun hΩ ↦ ?_⟩
  · -- The extended ideal lies in the locus of `v` over `E`.
    have hle : P.map (MvPolynomial.map (algebraMap k E)) ≤ idealOf E v := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
      exact (mem_idealOf_iff k).1 (hv hp)
    have hEv : idealOf E v = P.map (MvPolynomial.map (algebraMap k E)) :=
      (idealOf_eq_of_le_of_trdeg_eq t v (ht ▸ hle) (hn'tr.trans (congrArg _ hnn)) hrank).trans ht
    have hgenv := isGeneric_baseChange (k := k) (E := E) (Ω := Ω) hEv
    exact ⟨hEv, hgenv.1, hgenv.2⟩
  · have : IsAlgClosed Ω := hΩ
    obtain ⟨m, hm, hiffΩ⟩ := exists_idealOf_eq_iff (k := E) (Ω := Ω)
      (P.map (MvPolynomial.map (algebraMap k E)))
    have hmn : m = n := by exact_mod_cast hm.symm.trans hdimE
    exact hmn ▸ hiffΩ

end AclGeom
