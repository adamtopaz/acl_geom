/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericExtension
import AclGeom.Correspondence.GeometricPrime
import AclGeom.Correspondence.AmbientAutomorphism
import GroupConfig.Rank

/-!
# Loci and generic points

Blueprint `sources/group_configuration/01-universal-domain.tex`, `def:locus`,
`lem:locusprime`, `lem:genexists`, `lem:dim`.

The locus ideal `locusIdeal L a` of a tuple `a` over a subfield `L` is the
extension to `K[X]` of its vanishing ideal `idealOf L a`; it is prime when `L`
is algebraically closed (`AclGeom.isPrime_map_of_isAlgClosed`) and contracts
back to `idealOf L a` (`AclGeom.comap_map_mvPolynomial_eq_self`).  A tuple `a'`
is a *generic point over `M`* of the locus of `a` over the base `k`
(`IsGenericOver M a a'`) if its vanishing ideal over `M` is the extension of
`idealOf k a`; equivalently the two locus ideals in `K[X]` agree
(`isGenericOver_iff_locusIdeal_eq`).

Proved here: generic points over `M` have the same vanishing ideal over `k`
as `a` (`IsGenericOver.idealOf_eq`), the same rank over `M` as over `k`, hence
are independent from `M` (`IsGenericOver.indepOver`, `lem:dim`(1)); generic
points over a larger field are generic over a smaller one
(`IsGenericOver.of_le`); any two generic points over `M` are conjugate by an
automorphism over `M` (`IsGenericOver.exists_algEquiv`, `lem:dim`(3)).
Existence of generic points and the converse of `lem:dim`(2) are in the sequel.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** locus extension/contraction, primality over an algebraically closed
base, and the stated implications from genericity are proved. Conjugacy requires
finite tuples and an algebraically closed ambient field. Existence of generic
points and the converse from independence to unchanged locus remain open.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*}

/-! ### Locus ideals -/

section LocusIdeal

variable (L : Type*) [Field L] [Algebra L K]

/-- `def:locus`: the locus ideal of `a` over the subfield `L`, the extension to `K[X]` of
the vanishing ideal of `a` over `L`. -/
def locusIdeal (a : ι → K) : Ideal (MvPolynomial ι K) :=
  (idealOf L a).map (MvPolynomial.map (algebraMap L K))

theorem locusIdeal_comap (a : ι → K) :
    (locusIdeal L a).comap (MvPolynomial.map (algebraMap L K)) = idealOf L a :=
  comap_map_mvPolynomial_eq_self _

theorem map_mem_locusIdeal {a : ι → K} {f : MvPolynomial ι L} (hf : f ∈ idealOf L a) :
    MvPolynomial.map (algebraMap L K) f ∈ locusIdeal L a :=
  Ideal.mem_map_of_mem _ hf

theorem map_mem_locusIdeal_iff {a : ι → K} {f : MvPolynomial ι L} :
    MvPolynomial.map (algebraMap L K) f ∈ locusIdeal L a ↔ f ∈ idealOf L a := by
  rw [← Ideal.mem_comap, locusIdeal_comap]

/-- `lem:locusprime`: locus ideals over algebraically closed fields are prime. -/
instance locusIdeal_isPrime [IsAlgClosed L] (a : ι → K) : (locusIdeal L a).IsPrime :=
  isPrime_map_of_isAlgClosed (idealOf L a)

/-- Every polynomial of the locus ideal vanishes at the tuple. -/
theorem aeval_eq_zero_of_mem_locusIdeal {a : ι → K} {f : MvPolynomial ι K}
    (hf : f ∈ locusIdeal L a) : MvPolynomial.aeval a f = 0 := by
  have hle : locusIdeal L a ≤ idealOf K a := by
    rw [locusIdeal, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
    exact (mem_idealOf_iff L).1 hg
  exact (mem_idealOf_iff K).1 (hle hf)

end LocusIdeal

/-- The locus ideal over the base `k` is contained in the locus ideal over any subfield. -/
theorem locusIdeal_base_le (M : IntermediateField k K) (a : ι → K) :
    locusIdeal k a ≤ locusIdeal (↥M) a := by
  rw [locusIdeal, Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_eq k (↥M) K, ← MvPolynomial.map_map]
  refine map_mem_locusIdeal (↥M) ?_
  rw [mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
  exact (mem_idealOf_iff k).1 hg

/-- Locus ideals grow with the subfield. -/
theorem locusIdeal_mono {F M : IntermediateField k K} (hFM : F ≤ M) (a : ι → K) :
    locusIdeal (↥F) a ≤ locusIdeal (↥M) a := by
  rw [locusIdeal, Ideal.map_le_iff_le_comap]
  intro g hg
  have hcomp : (algebraMap (↥M) K).comp (IntermediateField.inclusion hFM).toRingHom =
      algebraMap (↥F) K := by
    ext x
    rfl
  rw [Ideal.mem_comap, ← hcomp, ← MvPolynomial.map_map]
  refine map_mem_locusIdeal (↥M) ?_
  rw [mem_idealOf_iff, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hcomp,
    ← MvPolynomial.aeval_def]
  exact (mem_idealOf_iff ↥F).1 hg

/-- The composite of the two scalar extensions `k → M → K` on polynomials. -/
theorem map_comp_map_algebraMap (M : IntermediateField k K) :
    (MvPolynomial.map (algebraMap (↥M) K)).comp (MvPolynomial.map (algebraMap k ↥M)) =
      MvPolynomial.map (algebraMap k K) (σ := ι) := by
  ext p <;> simp

/-! ### Generic points -/

/-- `a'` is a *generic point over `M`* of the locus of `a` over the base `k`: its vanishing
ideal over `M` is the extension of the vanishing ideal of `a` over `k`. -/
def IsGenericOver (M : IntermediateField k K) (a a' : ι → K) : Prop :=
  idealOf (↥M) a' = (idealOf k a).map (MvPolynomial.map (algebraMap k ↥M))

variable {M : IntermediateField k K} {a a' a'' : ι → K}

/-- Genericity in terms of the locus ideals in `K[X]`. -/
theorem isGenericOver_iff_locusIdeal_eq :
    IsGenericOver M a a' ↔ locusIdeal (↥M) a' = locusIdeal k a := by
  constructor
  · intro h
    unfold locusIdeal
    rw [h, Ideal.map_map, map_comp_map_algebraMap]
  · intro h
    unfold IsGenericOver
    rw [← locusIdeal_comap (↥M) a', h, locusIdeal, ← map_comp_map_algebraMap M,
      ← Ideal.map_map, comap_map_mvPolynomial_eq_self]

theorem IsGenericOver.locusIdeal_eq (h : IsGenericOver M a a') :
    locusIdeal (↥M) a' = locusIdeal k a :=
  isGenericOver_iff_locusIdeal_eq.1 h

/-- `lem:dim`(1), first half: a generic point over `M` has the same vanishing ideal over `k`
as the original tuple. -/
theorem IsGenericOver.idealOf_eq (h : IsGenericOver M a a') : idealOf k a' = idealOf k a :=
  (isGeneric_baseChange h).1

/-- `lem:dim`(1): a generic point over `M` has the same rank over `M` as over `k`. -/
theorem IsGenericOver.erk_coe_eq (h : IsGenericOver M a a') :
    erk k (M : Set K) (range a') = erk k ∅ (range a') := by
  rw [erk_coe_eq_toENat_trdeg, erk_empty_eq_toENat_trdeg, trdeg_adjoin_of_isGeneric h]

/-- Tuples with the same vanishing ideal have the same rank. -/
theorem erk_empty_range_eq_of_idealOf_eq {b : ι → K} (h : idealOf k a = idealOf k b) :
    erk k ∅ (range a) = erk k ∅ (range b) := by
  rw [erk_empty_eq_toENat_trdeg, erk_empty_eq_toENat_trdeg,
    (locusFunctionFieldEquivOfIdealEq h).trdeg_eq]

/-- A generic point over `M` has the same rank over `k` as the original tuple. -/
theorem IsGenericOver.erk_empty_eq (h : IsGenericOver M a a') :
    erk k ∅ (range a') = erk k ∅ (range a) :=
  erk_empty_range_eq_of_idealOf_eq h.idealOf_eq

/-- `lem:dim`(1): a generic point over `M` is independent from `M`. -/
theorem IsGenericOver.indepOver [Finite ι] (h : IsGenericOver M a a') :
    IndepOver k ∅ (range a') (M : Set K) := by
  refine indepOver_of_erk_eq (finite_range a') ?_
  rw [empty_union]
  exact h.erk_coe_eq

/-- `lem:genexists`, last clause: a generic point over a larger field is generic over a
smaller one. -/
theorem IsGenericOver.of_le {F : IntermediateField k K} (hFM : F ≤ M)
    (h : IsGenericOver M a a') : IsGenericOver F a a' := by
  have hk : idealOf k a' = idealOf k a := h.idealOf_eq
  rw [isGenericOver_iff_locusIdeal_eq] at h ⊢
  refine le_antisymm ?_ ?_
  · rw [← h]
    exact locusIdeal_mono hFM a'
  · have h1 : locusIdeal k a = locusIdeal k a' := by
      unfold locusIdeal
      rw [hk]
    rw [h1]
    exact locusIdeal_base_le F a'

/-- `lem:dim`(3) / `lem:genexists`: any two generic points over `M` are conjugate by an
automorphism of `K` over `M`. -/
theorem IsGenericOver.exists_algEquiv [IsAlgClosed K] [Finite ι] (h1 : IsGenericOver M a a')
    (h2 : IsGenericOver M a a'') : ∃ σ : K ≃ₐ[↥M] K, ∀ i, σ (a' i) = a'' i := by
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := ↥M) (h1.trans h2.symm)
  exact ⟨σ, hσ⟩

/-- Automorphisms over `M` carry generic points over `M` to generic points over `M`. -/
theorem IsGenericOver.comp (h : IsGenericOver M a a') (σ : K ≃ₐ[↥M] K) :
    IsGenericOver M a (fun i ↦ σ (a' i)) := by
  unfold IsGenericOver at h ⊢
  rw [← h]
  refine idealOf_eq_of_aeval_iff (↥M) fun f ↦ ?_
  have hfun : (fun i ↦ σ (a' i)) = fun i ↦ (σ : K →ₐ[↥M] K) (a' i) := rfl
  rw [hfun, ← MvPolynomial.comp_aeval_apply]
  exact map_eq_zero_iff _ σ.injective

/-- Generic points of the locus of `a` over `M` are exactly the tuples with the same
vanishing ideal over `M` as a given one. -/
theorem IsGenericOver.iff_idealOf_eq (h : IsGenericOver M a a') :
    IsGenericOver M a a'' ↔ idealOf (↥M) a'' = idealOf (↥M) a' := by
  unfold IsGenericOver at h ⊢
  rw [h]

end

end GroupConfig
