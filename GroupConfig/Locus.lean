/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericExtension
import AclGeom.Correspondence.GeometricPrime
import AclGeom.Correspondence.AmbientAutomorphism
import GroupConfig.Rank
import GroupConfig.Dimension
import GroupConfig.Setting

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
Existence of generic points over small subfields of a universal domain
(`exists_isGenericOver`) is obtained by embedding the abstract generic point of
`AclGeom.exists_genericPoint_baseChange` into `K` (relocating a transcendence
basis to fresh elements and extending algebraically with `IsAlgClosed.lift`);
with the dimension drop this gives the converse of `lem:dim`(2)
(`isGenericOver_self_of_indepOver`) and `lem:fresh-conj`
(`exists_algEquiv_indepOver`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** locus extension/contraction, primality over an algebraically closed
base, the stated implications from genericity, and (for finite tuples over small
subfields of a universal domain with algebraically closed base and ambient
fields) existence of generic points, the equivalence between independence from
`M` and unchanged locus over `M`, and the existence of conjugates independent
from a given small set are proved. Conjugacy requires finite tuples and an
algebraically closed ambient field. The arbitrary-prime formulation of
`lem:genexists` is proved in `GroupConfig.PrimeLocus`.
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

/-! ### Existence of generic points -/

/-- A subfield of finite rank in a universal domain is itself the base of a
universal domain. -/
theorem universalDomain_of_isSmall [UniversalDomain k K] (M : IntermediateField k K)
    (hM : IsSmall k (M : Set K)) : UniversalDomain (↥M) K := by
  refine ⟨?_⟩
  have htower := trdeg_add_eq k (↥M) (A := K)
  have hsmall : Algebra.trdeg k ↥M < Cardinal.aleph0 := by
    have h := hM
    unfold IsSmall at h
    rw [erk_empty_eq_toENat_trdeg, Cardinal.toENat_ne_top, adjoin_self] at h
    exact h
  by_contra hlt
  push Not at hlt
  have := Cardinal.add_lt_aleph0 hsmall hlt
  rw [htower] at this
  exact (not_le.2 this) UniversalDomain.aleph0_le_trdeg

/-- `lem:genexists`: over a small subfield `M` of a universal domain, every locus over the
algebraically closed base `k` has a generic point. -/
theorem exists_isGenericOver [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι]
    {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) (a : ι → K) :
    ∃ a' : ι → K, IsGenericOver M a a' := by
  classical
  -- An abstract generic point in some extension `K₀` of `M`.
  obtain ⟨K₀, _, _, _, _, b₀, hb₀, -, -⟩ :=
    exists_genericPoint_baseChange (k := k) (E := ↥M) (F := K) a
  let L₀ : IntermediateField (↥M) K₀ := IntermediateField.adjoin (↥M) (Set.range b₀)
  -- A transcendence basis of `M(b₀)` over `M`; it is finite.
  obtain ⟨ι', t, ht⟩ := exists_isTranscendenceBasis' (↥M) ↥L₀
  have hfin : Algebra.trdeg (↥M) ↥L₀ < Cardinal.aleph0 := by
    rw [← Cardinal.toENat_ne_top,
      ← AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg (↥M) (Set.range b₀)]
    exact (((AlgebraicIndependent.matroid (↥M) K₀).eRk_le_encard _).trans_lt
      (finite_range b₀).encard_lt_top).ne
  have hι' : Finite ι' := by
    rw [← Cardinal.lt_aleph0_iff_finite, ht.cardinalMk_eq_trdeg]
    exact hfin
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι'
  -- A fresh tuple of the same size in `K`, independent over `M`.
  obtain ⟨s₀, hs₀ind, hs₀inj⟩ := exists_fresh_tuple hM n
  have hs₀ : AlgebraicIndependent (↥M) s₀ := by
    have h1 : (AlgebraicIndependent.matroid (↥M) K).Indep (Set.range s₀) := by
      rw [← rkMatroid_coe]
      exact hs₀ind
    exact (algebraicIndependent_subtype_range hs₀inj).1
      (AlgebraicIndependent.matroid_indep_iff.1 h1)
  have hsind : AlgebraicIndependent (↥M) (s₀ ∘ e) := hs₀.comp e e.injective
  -- Relocate the transcendental part, then extend algebraically.
  let φ₀ : ↥(IntermediateField.adjoin (↥M) (Set.range t)) →ₐ[↥M] K :=
    ((IntermediateField.adjoin (↥M) (Set.range (s₀ ∘ e))).val.comp
      hsind.aevalEquivField.toAlgHom).comp ht.1.aevalEquivField.symm.toAlgHom
  have : Algebra.IsAlgebraic (↥(IntermediateField.adjoin (↥M) (Set.range t))) ↥L₀ :=
    ht.isAlgebraic_field
  let _ : Algebra (↥(IntermediateField.adjoin (↥M) (Set.range t))) K := φ₀.toAlgebra
  have : IsScalarTower (↥M) (↥(IntermediateField.adjoin (↥M) (Set.range t))) K :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (φ₀.commutes c).symm
  let ψ : ↥L₀ →ₐ[↥(IntermediateField.adjoin (↥M) (Set.range t))] K := IsAlgClosed.lift
  let ψ' : ↥L₀ →ₐ[↥M] K := ψ.restrictScalars (↥M)
  let b₀' : ι → ↥L₀ := fun i ↦ ⟨b₀ i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  refine ⟨fun i ↦ ψ' (b₀' i), ?_⟩
  unfold IsGenericOver
  rw [← hb₀]
  have h1 : idealOf (↥M) (⇑ψ' ∘ b₀') = idealOf (↥M) b₀' := idealOf_comp_algHom (↥M) ψ' b₀'
  have h2 : idealOf (↥M) (⇑L₀.val ∘ b₀') = idealOf (↥M) b₀' :=
    idealOf_comp_algHom (↥M) L₀.val b₀'
  have h3 : (⇑L₀.val ∘ b₀') = b₀ := funext fun i ↦ rfl
  rw [h3] at h2
  exact h1.trans h2.symm

/-- `lem:dim`(2), converse: a tuple independent from a small subfield `M` is a generic
point over `M` of its own locus over `k`. -/
theorem isGenericOver_self_of_indepOver [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    [Finite ι] {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) {a : ι → K}
    (h : IndepOver k ∅ (Set.range a) (M : Set K)) : IsGenericOver M a a := by
  obtain ⟨b, hb⟩ := exists_isGenericOver hM a
  have hle : idealOf (↥M) b ≤ idealOf (↥M) a := by
    rw [hb, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
    exact (mem_idealOf_iff k).1 hf
  have herk : erk k (M : Set K) (Set.range a) = erk k (M : Set K) (Set.range b) := by
    rw [hb.erk_coe_eq, hb.erk_empty_eq]
    have h' := h (subset_refl _) (finite_range a)
    rwa [empty_union] at h'
  have heq := idealOf_eq_of_le_of_erk_eq M hle herk
  unfold IsGenericOver at hb ⊢
  rw [← heq, hb]

/-- `lem:dim`(2): a tuple is a generic point over a small subfield `M` of its own locus iff
it is independent from `M`. -/
theorem isGenericOver_self_iff [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι]
    {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) {a : ι → K} :
    IsGenericOver M a a ↔ IndepOver k ∅ (Set.range a) (M : Set K) :=
  ⟨fun h ↦ h.indepOver, isGenericOver_self_of_indepOver hM⟩

/-- A set of finite rank over `k` has finite rank over every larger base subfield `M`. -/
theorem isSmall_coe_of_isSmall (M : IntermediateField k K) {C : Set K} (hC : IsSmall k C) :
    IsSmall (↥M) C := by
  unfold IsSmall at hC ⊢
  rw [← erk_coe_union (k := k) M ∅ C, union_empty]
  exact fun htop ↦ hC (top_le_iff.1 (htop ▸ erk_base_mono k (empty_subset _) C))

/-- `lem:fresh-conj`: over a small algebraically closed subfield `M` of a universal domain,
every tuple has a conjugate over `M` independent (over `M`) from any given small set. -/
theorem exists_algEquiv_indepOver [IsAlgClosed K] [UniversalDomain k K] [Finite ι]
    {M : IntermediateField k K} [IsAlgClosed (↥M)] (hM : IsSmall k (M : Set K)) (a : ι → K)
    {w : Set K} (hw : IsSmall k w) :
    ∃ σ : K ≃ₐ[↥M] K, IndepOver k (M : Set K) (Set.range (fun i ↦ σ (a i))) w := by
  have := universalDomain_of_isSmall M hM
  -- Work over the base `M`: a generic point of the locus of `a` over `M` over the small field
  -- `M(w)^{alg}`.
  let M' : IntermediateField (↥M) K := racl (↥M) w
  have hM' : IsSmall (↥M) (M' : Set K) := (isSmall_coe_of_isSmall M hw).racl
  obtain ⟨b, hb⟩ := exists_isGenericOver (k := ↥M) hM' a
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := ↥M) hb.idealOf_eq.symm
  refine ⟨σ, ?_⟩
  have hfun : (fun i ↦ σ (a i)) = b := funext hσ
  rw [hfun]
  have hind : IndepOver (↥M) ∅ (Set.range b) (M' : Set K) := hb.indepOver
  have hind' : IndepOver (↥M) ∅ (Set.range b) w := hind.mono_right (subset_racl _ w)
  have := (indepOver_coe_union_iff M ∅ (Set.range b) w).2 hind'
  rwa [union_empty] at this

end

end GroupConfig
