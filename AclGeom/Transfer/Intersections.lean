/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Combinatorics.Matroid.Rank.ENat
import AclGeom.Closure.Ambient

/-!
# Finite generators for intersections of absolute closures

For finite `A ⊆ K₁` and arbitrary `B ⊆ K₁` there is a finite `C ⊆ K₁` with
`racl(A) ⊓ racl(B) = racl(C)` (blueprint Lemma
finite-intersection-generator, slightly generalized: only one of the two
sets needs to be finite).

Two departures from the blueprint proof, both simplifications:

* the transcendence-basis bookkeeping runs through mathlib's
  algebraic-independence *matroid* (`AlgebraicIndependent.matroid`): a
  matroid basis of the carrier of the intersection is algebraically
  independent, generates it algebraically, and is finite because it is an
  independent subset of the matroid closure of the finite set `A`;
* the automorphism-symmetry step is replaced by minimal-polynomial
  divisibility: an annihilator of `c` over `k(A)` has coefficients in `K₁`,
  so `minpoly K₁ c` divides it and every `K₁`-conjugate of `c` is again a
  root of it — conjugates never leave `racl k A` (`conjugate_mem_racl`).
  No automorphism of `Ω` is ever constructed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5, checklist T2 and T3's strict-inclusion
transfer); the one-quantifier transfer consumes these in
`AclGeom.Transfer.OneQuantifier`.
-/

namespace AclGeom

open IntermediateField Polynomial

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section MatroidBridge

variable (k) in
/-- The closure operator of mathlib's algebraic-independence matroid on `Ω`
is exactly `racl`. -/
theorem mem_matroidClosure_iff {S : Set Ω} {x : Ω}
    [FaithfulSMul k Ω] :
    x ∈ (AlgebraicIndependent.matroid k Ω).closure S ↔ x ∈ racl k S := by
  rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe,
    Subalgebra.mem_algebraicClosure]
  exact (mem_racl_iff_isAlgebraic_adjoin
    (k := k) (S := S) (x := x)).symm

end MatroidBridge

section PolyCharacterization

/-- **Conjugates do not leave a closure defined over a subfield**
(the divisibility replacement for the blueprint's automorphism argument):
if `c ∈ racl k S` with `S ⊆ K₁`, then every root of `minpoly K₁ c` in `Ω`
again lies in `racl k S`. -/
theorem conjugate_mem_racl {K₁ : IntermediateField k Ω} {S : Set Ω}
    (hS : S ⊆ (K₁ : Set Ω)) {c z : Ω} (hc : c ∈ racl k S)
    (hz : ((minpoly K₁ c).map (algebraMap K₁ Ω)).eval z = 0) :
    z ∈ racl k S := by
  obtain ⟨p, hp0, hpc, hpmem⟩ := mem_racl_iff_exists_poly.1 hc
  -- The annihilator has coefficients in `K₁`, so it lifts there.
  have hK : ∀ n, p.coeff n ∈ K₁ := fun n ↦ adjoin_le_iff.2 hS (hpmem n)
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := algebraMap K₁ Ω) p).1 <|
    (Polynomial.lifts_iff_coeff_lifts p).2 fun n ↦ ⟨⟨p.coeff n, hK n⟩, rfl⟩
  have hqc : Polynomial.aeval c q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq]
    exact hpc
  -- `minpoly K₁ c` divides the lift, hence its roots kill `p` too.
  obtain ⟨r, hr⟩ : (minpoly K₁ c).map (algebraMap K₁ Ω) ∣ p := by
    rw [← hq]
    exact Polynomial.map_dvd _ (minpoly.dvd K₁ c hqc)
  refine mem_racl_iff_exists_poly.2 ⟨p, hp0, ?_, hpmem⟩
  rw [hr, Polynomial.eval_mul, hz, zero_mul]

/-- A monic polynomial over `Ω` that splits with all roots in an
intermediate field `E` has all coefficients in `E`. -/
theorem coeff_mem_of_roots_mem {E : IntermediateField k Ω}
    {p : Polynomial Ω} (hmonic : p.Monic) (hsplit : p.Splits)
    (hroots : ∀ z ∈ p.roots, z ∈ E) (n : ℕ) : p.coeff n ∈ E := by
  classical
  have hprod : p = (p.roots.map fun z ↦ X - C z).prod :=
    hsplit.eq_prod_roots_of_monic hmonic
  -- Lift the factorization to `E[X]` along the root memberships.
  set q : Polynomial E :=
    (p.roots.attach.map fun z ↦ X - C (⟨z.1, hroots z.1 z.2⟩ : E)).prod
    with hqdef
  have hq : q.map (algebraMap E Ω) = p := by
    have h1 : q.map (algebraMap E Ω) =
        (Polynomial.mapRingHom (algebraMap E Ω)) q := rfl
    rw [h1, hqdef, map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [hprod, ← Multiset.attach_map_val p.roots,
      Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun z _ ↦ ?_)
    simp [Polynomial.coe_mapRingHom, Polynomial.map_sub]
  rw [← hq, Polynomial.coeff_map]
  exact SetLike.coe_mem _

end PolyCharacterization

section IntersectionGenerator

/-- **Finite generator for an intersection** (blueprint Lemma
finite-intersection-generator, one-sided finiteness): for `A ⊆ K₁` finite
and any `B ⊆ K₁`, the intersection `racl k A ⊓ racl k B` is the closure of
a finite subset `C` of `K₁` — the coefficients of the `K₁`-minimal
polynomials of a matroid basis of the intersection. -/
theorem exists_finite_inter_generator [IsAlgClosed Ω]
    {K₁ : IntermediateField k Ω} {A B : Set Ω} (hAfin : A.Finite)
    (hA : A ⊆ (K₁ : Set Ω)) (hB : B ⊆ (K₁ : Set Ω)) :
    ∃ C : Set Ω, C.Finite ∧ C ⊆ (K₁ : Set Ω) ∧
      racl k A ⊓ racl k B = racl k C := by
  classical
  haveI : FaithfulSMul k Ω :=
    (faithfulSMul_iff_algebraMap_injective k Ω).2
      (algebraMap k Ω).injective
  set E : IntermediateField k Ω := racl k A ⊓ racl k B with hEdef
  -- Absorption: anything generated inside `E` stays below `E`.
  have hIntoE : ∀ {T : Set Ω}, T ⊆ (E : Set Ω) → racl k T ≤ E := by
    intro T hT
    refine le_inf ?_ ?_
    · have h1 : T ⊆ (racl k A : Set Ω) := fun x hx ↦
        (inf_le_left : E ≤ racl k A) (hT hx)
      have h2 := racl_mono (k := k) h1
      rwa [racl_racl k A] at h2
    · have h1 : T ⊆ (racl k B : Set Ω) := fun x hx ↦
        (inf_le_right : E ≤ racl k B) (hT hx)
      have h2 := racl_mono (k := k) h1
      rwa [racl_racl k B] at h2
  -- A matroid basis of the carrier of `E`.
  obtain ⟨s, hs⟩ := (AlgebraicIndependent.matroid k Ω).exists_isBasis
    (E : Set Ω) (by simp)
  obtain ⟨-, hsub, halg⟩ := AlgebraicIndependent.matroid_isBasis_iff.1 hs
  -- The basis generates `E` algebraically.
  have hEs : E ≤ racl k s := fun x hx ↦
    (mem_racl_iff_isAlgebraic_adjoin
      (k := k) (S := s) (x := x)).2 (halg x hx)
  -- The basis is finite: an independent set inside the closure of `A`.
  have hsA : s ⊆ (AlgebraicIndependent.matroid k Ω).closure A := by
    intro x hx
    exact (mem_matroidClosure_iff k).2
      ((inf_le_left : E ≤ racl k A) (hsub hx))
  have hsfin : s.Finite := by
    have hcard := hs.indep.encard_le_eRk_of_subset hsA
    rw [Matroid.eRk_closure_eq] at hcard
    rw [← Set.encard_lt_top_iff]
    exact (hcard.trans ((AlgebraicIndependent.matroid k Ω).eRk_le_encard A)).trans_lt
      hAfin.encard_lt_top
  -- Each basis element is integral over `K₁`.
  have hint : ∀ c ∈ s, IsIntegral K₁ c := by
    intro c hc
    rw [← isAlgebraic_iff_isIntegral]
    refine isAlgebraic_of_le (adjoin_le_iff.2 hA) ?_
    exact (mem_racl_iff k).1 ((inf_le_left : E ≤ racl k A) (hsub hc))
  -- The coefficient set of the minimal polynomials.
  set C : Set Ω := ⋃ c ∈ s,
    (fun n ↦ ((minpoly K₁ c).coeff n : Ω)) '' ↑(minpoly K₁ c).support
    with hCdef
  have hCfin : C.Finite :=
    hsfin.biUnion fun c _ ↦ (minpoly K₁ c).support.finite_toSet.image _
  have hCK : C ⊆ (K₁ : Set Ω) := by
    intro y hy
    obtain ⟨c, -, n, -, rfl⟩ := by
      simpa only [hCdef, Set.mem_iUnion, Set.mem_image, Finset.mem_coe,
        exists_prop] using hy
    exact SetLike.coe_mem _
  -- The mapped minimal polynomial of a basis element and its properties.
  have hkey : ∀ c ∈ s,
      ((minpoly K₁ c).map (algebraMap K₁ Ω)).Monic ∧
      ((minpoly K₁ c).map (algebraMap K₁ Ω)).eval c = 0 := by
    intro c hc
    refine ⟨(minpoly.monic (hint c hc)).map _, ?_⟩
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
  -- Every coefficient of a mapped minimal polynomial lies in `E`.
  have hcoeffE : ∀ c ∈ s, ∀ n,
      ((minpoly K₁ c).map (algebraMap K₁ Ω)).coeff n ∈ E := by
    intro c hc n
    obtain ⟨hmonic, -⟩ := hkey c hc
    refine coeff_mem_of_roots_mem hmonic
      (IsAlgClosed.splits ((minpoly K₁ c).map (algebraMap K₁ Ω)))
      (fun z hz ↦ ?_) n
    have hz0 := Polynomial.isRoot_of_mem_roots hz
    exact ⟨conjugate_mem_racl hA
        ((inf_le_left : E ≤ racl k A) (hsub hc)) hz0,
      conjugate_mem_racl hB
        ((inf_le_right : E ≤ racl k B) (hsub hc)) hz0⟩
  -- Direction 1: `E ≤ racl k C`, since each basis element is a root of a
  -- polynomial with coefficients in `C ∪ {0}`.
  have hsC : s ⊆ (racl k C : Set Ω) := by
    intro c hc
    obtain ⟨hmonic, heval⟩ := hkey c hc
    refine mem_racl_iff_exists_poly.2
      ⟨(minpoly K₁ c).map (algebraMap K₁ Ω), hmonic.ne_zero, heval,
        fun n ↦ ?_⟩
    by_cases h0 : (minpoly K₁ c).coeff n = 0
    · rw [Polynomial.coeff_map, h0, map_zero]
      exact zero_mem _
    · refine subset_adjoin k C ?_
      rw [Polynomial.coeff_map]
      refine Set.mem_biUnion hc ?_
      exact ⟨n, by simpa using Polynomial.mem_support_iff.2 h0, rfl⟩
  have hEC : E ≤ racl k C := fun x hx ↦
    racl_le_of_subset_racl hsC (hEs hx)
  -- Direction 2: `racl k C ≤ E`, since `C` consists of symmetric
  -- expressions in conjugates, all lying in `E`.
  have hCE : C ⊆ (E : Set Ω) := by
    intro y hy
    obtain ⟨c, hc, n, hn, rfl⟩ := by
      simpa only [hCdef, Set.mem_iUnion, Set.mem_image, Finset.mem_coe,
        exists_prop] using hy
    have h1 := hcoeffE c hc n
    rwa [Polynomial.coeff_map] at h1
  exact ⟨C, hCfin, hCK, le_antisymm hEC (hIntoE hCE)⟩

end IntersectionGenerator

section StrictTransfer

/-- The inclusion of closure-intersections is preserved from `K₂` down to
the trace on any subfield: half of blueprint Lemma strict-transfer, needing
only `racl k A ≤ racl k B`. -/
theorem inf_le_inf_of_racl_le {K : IntermediateField k Ω} {A B : Set Ω}
    (hAB : racl k A ≤ racl k B) :
    racl k A ⊓ K ≤ racl k B ⊓ K :=
  inf_le_inf_right K hAB

/-- **Strict-inclusion transfer** (blueprint Lemma strict-transfer): for
`B ⊆ K₁ ≤ K₂` and `racl k A ≤ racl k B`, the trace of the inclusion on
`K₁` is strict iff its trace on `K₂` is strict. The downward direction is
the minimal-polynomial argument: a witness `z ∈ K₂` has its `k(B)`-minimal
polynomial's coefficients in `racl k B ⊓ K₁ = racl k A ⊓ K₁`, making `z`
algebraic over the racl-closed `racl k A` — a contradiction. -/
theorem inf_lt_inf_iff_of_le {K₁ K₂ : IntermediateField k Ω}
    (hK : K₁ ≤ K₂) {A B : Set Ω} (hB : B ⊆ (K₁ : Set Ω))
    (hAB : racl k A ≤ racl k B) :
    racl k A ⊓ K₁ < racl k B ⊓ K₁ ↔ racl k A ⊓ K₂ < racl k B ⊓ K₂ := by
  constructor
  · intro h
    obtain ⟨z, hzB, hzA⟩ := SetLike.exists_of_lt h
    refine lt_of_le_of_ne (inf_le_inf_of_racl_le hAB) fun heq ↦ hzA ?_
    have hz2 : z ∈ racl k B ⊓ K₂ := ⟨hzB.1, hK hzB.2⟩
    rw [← heq] at hz2
    exact ⟨hz2.1, hzB.2⟩
  · intro h
    refine lt_of_le_of_ne (inf_le_inf_of_racl_le hAB) fun heq ↦ ?_
    refine h.ne (le_antisymm (inf_le_inf_of_racl_le hAB) fun z hz ↦ ?_)
    -- `z ∈ racl k B ⊓ K₂`; its `k(B)`-minimal polynomial has coefficients
    -- in `racl k B ⊓ K₁`, hence in `racl k A` by the assumed equality.
    have hzint : IsIntegral (adjoin k B) z :=
      isAlgebraic_iff_isIntegral.1 ((mem_racl_iff k).1 hz.1)
    have hzA : z ∈ racl k A := by
      have hz' : z ∈ racl k ((racl k A : Set Ω)) := by
        rw [mem_racl_iff, adjoin_self]
        refine isAlgebraic_of_coeff_mem
          ((Polynomial.map_ne_zero_iff
            (algebraMap (adjoin k B) Ω).injective).2
            (minpoly.ne_zero hzint)) ?_ fun n ↦ ?_
        · rw [Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
        · rw [Polynomial.coeff_map]
          have hmem : ((minpoly (adjoin k B) z).coeff n : Ω) ∈
              racl k B ⊓ K₁ :=
            ⟨adjoin_le_racl k B (SetLike.coe_mem _),
              adjoin_le_iff.2 hB (SetLike.coe_mem _)⟩
          rw [← heq] at hmem
          exact (inf_le_left : racl k A ⊓ K₁ ≤ racl k A) hmem
      rwa [racl_racl] at hz'
    exact ⟨hzA, hz.2⟩

end StrictTransfer

end

end AclGeom
