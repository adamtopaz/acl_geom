/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Algebra.CharP.Reduced
import GroupConfig.QuasiRational
import GroupConfig.Locus

/-!
# Definable closure

Blueprint `sources/group_configuration/03-codes.tex`, `lem:dcl-galois`, `cor:dcl-props` and
`lem:qr-dcl`.

The definable closure `dcl L` of a subfield `L ⊇ k` of the universal domain `K` is its
perfect closure in `K` (`GroupConfig.dcl`).  It is the fixed field of the automorphisms of
`K` over `L` (`GroupConfig.mem_dcl_iff_forall_fixed`), and `dcl(L, u)` for a tuple `u`
(`GroupConfig.dclAdjoin`) consists exactly of the values at `u` of quasi-rational
expressions over `L` (`GroupConfig.mem_dclAdjoin_iff`,
`GroupConfig.QuasiRational.eval_mem_dclAdjoin`,
`GroupConfig.exists_quasiRational_of_mem_dclAdjoin`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:dcl-galois`, `cor:dcl-props` and `lem:qr-dcl` are proved.
Automorphism transport and equality of algebraic closures are stated both for
intermediate fields and for arbitrary generating sets.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- `dcl`: the definable closure of a subfield `L ⊇ k` of `K` is its perfect closure in
`K`. -/
def dcl (L : IntermediateField k K) : IntermediateField k K :=
  (perfectClosure (↥L) K).restrictScalars k

theorem expChar_intermediateField (L : IntermediateField k K) :
    ExpChar (↥L) (ringExpChar K) :=
  RingHom.expChar (algebraMap (↥L) K) (algebraMap (↥L) K).injective _

theorem mem_dcl_iff {L : IntermediateField k K} {x : K} :
    x ∈ dcl L ↔ ∃ n : ℕ, x ^ ringExpChar K ^ n ∈ L := by
  have := expChar_intermediateField L
  rw [dcl, mem_restrictScalars, mem_perfectClosure_iff_pow_mem (ringExpChar K)]
  simp only [RingHom.mem_range]
  constructor
  · rintro ⟨n, c, hc⟩
    refine ⟨n, ?_⟩
    rw [← hc]
    exact c.2
  · rintro ⟨n, hn⟩
    exact ⟨n, ⟨_, hn⟩, rfl⟩

theorem le_dcl (L : IntermediateField k K) : L ≤ dcl L := fun _ hx ↦
  mem_dcl_iff.2 ⟨0, by rwa [pow_zero, pow_one]⟩

theorem dcl_mono {L L' : IntermediateField k K} (h : L ≤ L') : dcl L ≤ dcl L' := fun _ hx ↦ by
  obtain ⟨n, hn⟩ := mem_dcl_iff.1 hx
  exact mem_dcl_iff.2 ⟨n, h hn⟩

theorem dcl_dcl (L : IntermediateField k K) : dcl (dcl L) = dcl L := by
  refine le_antisymm (fun x hx ↦ ?_) (le_dcl _)
  obtain ⟨n, hn⟩ := mem_dcl_iff.1 hx
  obtain ⟨m, hm⟩ := mem_dcl_iff.1 hn
  refine mem_dcl_iff.2 ⟨n + m, ?_⟩
  rwa [pow_add, pow_mul]

theorem isIntegral_of_mem_dcl {L : IntermediateField k K} {x : K} (hx : x ∈ dcl L) :
    IsIntegral (↥L) x := by
  obtain ⟨n, hn⟩ := mem_dcl_iff.1 hx
  refine IsIntegral.of_pow (expChar_pow_pos K (ringExpChar K) n) ?_
  exact isIntegral_algebraMap (x := (⟨_, hn⟩ : ↥L))

/-- `cor:dcl-props`: `dcl L ⊆ acl L`. -/
theorem dcl_le_racl (L : IntermediateField k K) : dcl L ≤ racl k (L : Set K) := fun _ hx ↦ by
  rw [mem_racl_iff k, adjoin_self]
  exact (isIntegral_of_mem_dcl hx).isAlgebraic

/-- `cor:dcl-props`: automorphisms transport the entire definable closure. -/
theorem dcl_map (σ : K ≃ₐ[k] K) (L : IntermediateField k K) :
    (dcl L).map σ.toAlgHom = dcl (L.map σ.toAlgHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := mem_dcl_iff.1 hy
    exact mem_dcl_iff.2 ⟨n, ⟨_, hn, map_pow σ _ _⟩⟩
  · intro hx
    obtain ⟨n, y, hy, heq⟩ := mem_dcl_iff.1 hx
    refine ⟨σ.symm x, mem_dcl_iff.2 ⟨n, ?_⟩, σ.apply_symm_apply x⟩
    have hpow : (σ.symm x) ^ ringExpChar K ^ n = y := by
      apply σ.injective
      rw [map_pow, σ.apply_symm_apply]
      exact heq.symm
    rwa [hpow]

/-- Taking algebraic closure after definable closure gives the original
algebraic closure. Consumer: the last clause of `cor:dcl-props`. -/
theorem racl_dcl (L : IntermediateField k K) :
    racl k (dcl L : Set K) = racl k (L : Set K) := by
  exact le_antisymm (racl_le_of_subset_racl (dcl_le_racl L))
    (racl_mono (le_dcl L))

/-- `cor:dcl-props`: equal definable closures have equal algebraic closures. -/
theorem racl_eq_of_dcl_eq {L L' : IntermediateField k K} (h : dcl L = dcl L') :
    racl k (L : Set K) = racl k (L' : Set K) := by
  rw [← racl_dcl L, h, racl_dcl L']

/-- The set form of `cor:dcl-props`: automorphisms transport the
perfect closure of a generated field. -/
theorem dcl_adjoin_image (σ : K ≃ₐ[k] K) (A : Set K) :
    (dcl (adjoin k A)).map σ.toAlgHom = dcl (adjoin k (σ '' A)) := by
  rw [dcl_map, adjoin_map, AlgEquiv.coe_toAlgHom]

/-- The set form of the last clause of `cor:dcl-props`, including
`A = C ∪ A₀` and `B = C ∪ A₀'`. -/
theorem racl_eq_of_dcl_adjoin_eq {A B : Set K}
    (h : dcl (adjoin k A) = dcl (adjoin k B)) : racl k A = racl k B := by
  have hA : racl k ((adjoin k A) : Set K) = racl k A :=
    le_antisymm (racl_le_of_subset_racl (adjoin_le_racl k A))
      (racl_mono (subset_adjoin k A))
  have hB : racl k ((adjoin k B) : Set K) = racl k B :=
    le_antisymm (racl_le_of_subset_racl (adjoin_le_racl k B))
      (racl_mono (subset_adjoin k B))
  simpa only [hA, hB] using racl_eq_of_dcl_eq h

/-- Automorphisms over `L` fix the definable closure of `L` pointwise. -/
theorem apply_eq_self_of_mem_dcl {L : IntermediateField k K} {x : K} (hx : x ∈ dcl L)
    (σ : K ≃ₐ[↥L] K) : σ x = x := by
  obtain ⟨n, hn⟩ := mem_dcl_iff.1 hx
  apply iterateFrobenius_inj K (ringExpChar K) n
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow]
  exact σ.commutes ⟨_, hn⟩

/-- Automorphisms over `k` fixing `L` pointwise fix `dcl L` pointwise. -/
theorem apply_eq_self_of_mem_dcl_of_fixes {L : IntermediateField k K} (σ : K ≃ₐ[k] K)
    (hσ : ∀ x ∈ L, σ x = x) {x : K} (hx : x ∈ dcl L) : σ x = x :=
  apply_eq_self_of_mem_dcl hx (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c ↦ hσ c c.2)

/-! ### The Galois characterisation -/

theorem aeval_const_unit {L : Type*} [Field L] [Algebra L K] (x : K) (f : MvPolynomial Unit L) :
    aeval (fun _ : Unit ↦ x) f =
      Polynomial.aeval x (aeval (fun _ : Unit ↦ (Polynomial.X : Polynomial L)) f) := by
  rw [MvPolynomial.comp_aeval_apply]
  simp only [Polynomial.aeval_X]

/-- Two roots in `K` of the same minimal polynomial over `L` have the same vanishing ideal. -/
theorem idealOf_const_unit_eq_of_minpoly_eq {L : IntermediateField k K} {x x' : K}
    (h : minpoly (↥L) x = minpoly (↥L) x') :
    idealOf (↥L) (fun _ : Unit ↦ x) = idealOf (↥L) (fun _ : Unit ↦ x') := by
  refine idealOf_eq_of_aeval_iff (↥L) fun f ↦ ?_
  rw [aeval_const_unit, aeval_const_unit]
  constructor
  · intro h0
    have := minpoly.dvd (↥L) x h0
    rw [h] at this
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero this (minpoly.aeval (↥L) x')
  · intro h0
    have := minpoly.dvd (↥L) x' h0
    rw [← h] at this
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero this (minpoly.aeval (↥L) x)

/-- `lem:dcl-galois`: the definable closure of `L` is the fixed field of the automorphisms of
`K` over `L`. -/
theorem mem_dcl_iff_forall_fixed [IsAlgClosed K] {L : IntermediateField k K} {x : K} :
    x ∈ dcl L ↔ ∀ σ : K ≃ₐ[↥L] K, σ x = x := by
  refine ⟨fun hx σ ↦ apply_eq_self_of_mem_dcl hx σ, fun h ↦ by_contra fun hx ↦ ?_⟩
  suffices hex : ∃ x' : K,
      idealOf (↥L) (fun _ : Unit ↦ x) = idealOf (↥L) (fun _ : Unit ↦ x') ∧ x' ≠ x by
    obtain ⟨x', hx', hne⟩ := hex
    obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := ↥L) hx'
    exact hne ((hσ ()).symm.trans (h σ))
  by_cases halg : IsIntegral (↥L) x
  · classical
    have hsep : (minpoly (↥L) x).natSepDegree ≠ 1 := fun h1 ↦ hx (by
      rw [dcl, mem_restrictScalars, mem_perfectClosure_iff_natSepDegree_eq_one]
      exact h1)
    rw [Polynomial.natSepDegree_eq_of_isAlgClosed K] at hsep
    have hxmem : x ∈ ((minpoly (↥L) x).aroots K).toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
      exact ⟨minpoly.ne_zero halg, minpoly.aeval _ _⟩
    obtain ⟨x', hx'mem, hne⟩ : ∃ x' ∈ ((minpoly (↥L) x).aroots K).toFinset, x' ≠ x := by
      by_contra hall
      refine hsep (Finset.card_eq_one.2 ⟨x, Finset.eq_singleton_iff_unique_mem.2 ⟨hxmem, ?_⟩⟩)
      exact fun x' hx' ↦ by_contra fun hne ↦ hall ⟨x', hx', hne⟩
    have hroot : Polynomial.aeval x' (minpoly (↥L) x) = 0 :=
      (Polynomial.mem_aroots.1 (Multiset.mem_toFinset.1 hx'mem)).2
    refine ⟨x', idealOf_const_unit_eq_of_minpoly_eq ?_, hne⟩
    exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible halg) hroot (minpoly.monic halg)
  · refine ⟨x + 1, ?_, by simp⟩
    have htr : Transcendental (↥L) x := fun h ↦ halg (isAlgebraic_iff_isIntegral.1 h)
    have htr' : Transcendental (↥L) (x + 1) := fun h ↦
      halg (by simpa using (isAlgebraic_iff_isIntegral.1 h).sub isIntegral_one)
    rw [(idealOf_eq_bot_iff (↥L)).2 (algebraicIndependent_unique_type_iff.2 htr),
      (idealOf_eq_bot_iff (↥L)).2 (algebraicIndependent_unique_type_iff.2 htr')]

/-! ### Definable closure of a field and a tuple -/

variable {ι : Type*}

/-- `dcl(L, u)`: the definable closure of the field generated over `L` by a tuple `u`. -/
def dclAdjoin (L : IntermediateField k K) (u : ι → K) : IntermediateField k K :=
  dcl ((adjoin (↥L) (range u)).restrictScalars k)

theorem mem_dclAdjoin_iff {L : IntermediateField k K} {u : ι → K} {x : K} :
    x ∈ dclAdjoin L u ↔ ∃ (n : ℕ) (P Q : MvPolynomial ι (↥L)),
      aeval u Q ≠ 0 ∧ x ^ ringExpChar K ^ n = aeval u P / aeval u Q := by
  rw [dclAdjoin, mem_dcl_iff]
  simp only [mem_restrictScalars]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨r, hr, s, hs, hx⟩ := mem_adjoin_iff_div.1 hn
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range] at hr hs
    obtain ⟨P, rfl⟩ := hr
    obtain ⟨Q, rfl⟩ := hs
    by_cases hQ : aeval u Q = 0
    · refine ⟨n, 0, 1, by simp, ?_⟩
      rw [hx, hQ, div_zero, map_zero, zero_div]
    · exact ⟨n, P, Q, hQ, hx⟩
  · rintro ⟨n, P, Q, -, hx⟩
    refine ⟨n, mem_adjoin_iff_div.2 ⟨aeval u P, ?_, aeval u Q, ?_, hx⟩⟩
    · rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
      exact ⟨P, rfl⟩
    · rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
      exact ⟨Q, rfl⟩

/-- `cor:dcl-props`: monotonicity of `dcl(L, u)` in `L`. -/
theorem dclAdjoin_mono {L L' : IntermediateField k K} (h : L ≤ L') (u : ι → K) :
    dclAdjoin L u ≤ dclAdjoin L' u := fun _ hx ↦ by
  obtain ⟨n, P, Q, hQ, hx⟩ := mem_dclAdjoin_iff.1 hx
  refine mem_dclAdjoin_iff.2 ⟨n, MvPolynomial.map (IntermediateField.inclusion h).toRingHom P,
    MvPolynomial.map (IntermediateField.inclusion h).toRingHom Q, ?_, ?_⟩
  · rwa [aeval_map_inclusion]
  · rwa [aeval_map_inclusion, aeval_map_inclusion]

theorem le_dclAdjoin (L : IntermediateField k K) (u : ι → K) : L ≤ dclAdjoin L u :=
  fun x hx ↦
    le_dcl _ ((mem_restrictScalars k).2 (IntermediateField.algebraMap_mem _ (⟨x, hx⟩ : ↥L)))

theorem range_subset_dclAdjoin (L : IntermediateField k K) (u : ι → K) :
    range u ⊆ dclAdjoin L u :=
  fun _ hx ↦ le_dcl _ ((mem_restrictScalars k).2 (subset_adjoin (↥L) _ hx))

/-- The definable closure of `L(u)` is algebraic over `L` and `u`. -/
theorem dclAdjoin_le_racl (L : IntermediateField k K) (u : ι → K) :
    dclAdjoin L u ≤ racl k ((L : Set K) ∪ range u) := by
  refine (dcl_le_racl _).trans ?_
  rw [restrictScalars_adjoin]
  exact racl_le_of_subset_racl (adjoin_le_racl k _)

/-! ### Quasi-rational expressions -/

section QuasiRational

variable [PerfectField K] {L : IntermediateField k K} {κ : Type*}

/-- `lem:qr-dcl`: the value at `u` of a quasi-rational expression over `L` is definable over
`L, u`. -/
theorem QuasiRational.eval_mem_dclAdjoin (f : QuasiRational (↥L) ι κ) {u : ι → K}
    (hf : f.IsDefinedAt u) (j : κ) : f.eval u j ∈ dclAdjoin L u :=
  mem_dclAdjoin_iff.2 ⟨f.e, f.num j, f.den j, hf j, by rw [QuasiRational.eval_apply, pRoot_pow]⟩

/-- `lem:qr-dcl`: a tuple definable over `L, u` is the value at `u` of a quasi-rational
expression over `L`. -/
theorem exists_quasiRational_of_mem_dclAdjoin [Finite κ] {u : ι → K} {w : κ → K}
    (hw : ∀ j, w j ∈ dclAdjoin L u) :
    ∃ f : QuasiRational (↥L) ι κ, f.IsDefinedAt u ∧ f.eval u = w := by
  choose n P Q hQ hw' using fun j ↦ mem_dclAdjoin_iff.1 (hw j)
  let _ := Fintype.ofFinite κ
  have hle : ∀ j, n j ≤ Finset.univ.sup n := fun j ↦ Finset.le_sup (f := n) (Finset.mem_univ j)
  refine ⟨⟨Finset.univ.sup n, fun j ↦ P j ^ ringExpChar K ^ (Finset.univ.sup n - n j),
    fun j ↦ Q j ^ ringExpChar K ^ (Finset.univ.sup n - n j)⟩, fun j ↦ ?_, funext fun j ↦ ?_⟩
  · change aeval u (Q j ^ ringExpChar K ^ (Finset.univ.sup n - n j)) ≠ 0
    rw [map_pow]
    exact pow_ne_zero _ (hQ j)
  · change pRoot K _ (aeval u (P j ^ _) / aeval u (Q j ^ _)) = w j
    refine pRoot_eq_of_pow_eq ?_
    rw [map_pow, map_pow, ← div_pow, ← hw' j, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (hle j)]

end QuasiRational

end

end GroupConfig
