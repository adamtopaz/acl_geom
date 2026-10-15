/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Codes
import GroupConfig.DefinableClosure

/-!
# Conjugate sets and their codes

Blueprint `sources/group_configuration/01-universal-domain.tex`, `lem:orbit` (finiteness of
conjugates of algebraic tuples), and `sources/group_configuration/03-codes.tex`,
`lem:code`(4), `def:conjset` and `lem:conjcode`.

A tuple `z` algebraic over a subfield `L` has finitely many conjugates under the
automorphisms of `K` over `L` (`GroupConfig.finite_conjugates`); the finite set of
conjugates is `GroupConfig.conjSet` and its code (`def:code`) is `GroupConfig.conjCode`.
The scalar coefficient carrier lies in `dcl L` (`GroupConfig.conjCode_subset_dcl`),
is interalgebraic with the conjugate set (`GroupConfig.racl_conjCode_eq_racl_coords`),
contains `z` in its algebraic closure (`GroupConfig.range_subset_racl_conjCode`),
and a tuple definable over `L₀, z` with coordinates in `L` is definable over `L₀` and the code
(`GroupConfig.mem_dclAdjoin_conjCode`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** algebraic-tuple orbit finiteness and the conjugate-set/definable-code
claims are proved for the scalar coefficient carrier of the coding polynomial.
The distinct finite indexed coefficient-vector presentation in `def:code` remains
an obligation; the polynomial retains its coefficient positions.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {μ : Type*} [Finite μ]

/-- `lem:orbit`: a tuple algebraic over `L` has finitely many conjugates over `L`. -/
theorem finite_conjugates {L : IntermediateField k K} {z : μ → K}
    (hz : ∀ i, IsIntegral (↥L) (z i)) :
    (range fun σ : K ≃ₐ[↥L] K ↦ ⇑σ ∘ z).Finite := by
  classical
  refine (Set.Finite.pi fun i ↦
    ((minpoly (↥L) (z i)).aroots K).toFinset.finite_toSet).subset ?_
  rintro _ ⟨σ, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_aroots]
  refine ⟨minpoly.ne_zero (hz i), ?_⟩
  have := Polynomial.aeval_algHom_apply σ.toAlgHom (z i) (minpoly (↥L) (z i))
  rw [minpoly.aeval, map_zero] at this
  exact this

open Classical in
/-- `def:conjset`: the conjugate set of a tuple algebraic over `L` (the empty set if `z` is
not algebraic over `L`). -/
def conjSet (L : IntermediateField k K) (z : μ → K) : Finset (μ → K) :=
  if h : (range fun σ : K ≃ₐ[↥L] K ↦ ⇑σ ∘ z).Finite then h.toFinset else ∅

variable {L : IntermediateField k K} {z : μ → K} (hz : ∀ i, IsIntegral (↥L) (z i))
include hz

theorem conjSet_eq : conjSet L z = (finite_conjugates hz).toFinset := by
  unfold conjSet
  split_ifs with h
  · rfl
  · exact absurd (finite_conjugates hz) h

theorem mem_conjSet {w : μ → K} : w ∈ conjSet L z ↔ ∃ σ : K ≃ₐ[↥L] K, ⇑σ ∘ z = w := by
  rw [conjSet_eq hz, Set.Finite.mem_toFinset]
  exact Iff.rfl

theorem self_mem_conjSet : z ∈ conjSet L z := (mem_conjSet hz).2 ⟨AlgEquiv.refl, rfl⟩

/-- Automorphisms over `L` permute the conjugate set. -/
theorem conjSet_map (σ : K ≃ₐ[↥L] K) :
    (conjSet L z).map (compEmb (σ.restrictScalars k) (σ.restrictScalars k).injective) =
      conjSet L z := by
  ext w
  rw [Finset.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨τ, rfl⟩ := (mem_conjSet hz).1 hv
    refine (mem_conjSet hz).2 ⟨τ.trans σ, ?_⟩
    rw [compEmb_apply]
    rfl
  · intro hw
    obtain ⟨ρ, rfl⟩ := (mem_conjSet hz).1 hw
    refine ⟨⇑σ.symm ∘ (⇑ρ ∘ z), (mem_conjSet hz).2 ⟨ρ.trans σ.symm, rfl⟩, ?_⟩
    rw [compEmb_apply]
    funext i
    change σ (σ.symm (ρ (z i))) = ρ (z i)
    exact σ.apply_symm_apply _

omit hz in
/-- `def:conjset`: the code of the conjugate set. -/
def conjCode (L : IntermediateField k K) (z : μ → K) : Set K :=
  letI := Fintype.ofFinite μ
  code (conjSet L z)

omit hz in
theorem conjCode_finite : (conjCode L z).Finite :=
  letI := Fintype.ofFinite μ
  code_finite _

omit hz in
instance : Finite ↥(conjCode L z) := (conjCode_finite (L := L) (z := z)).to_subtype

omit [Finite μ] hz in
/-- A finite set of `K` as a tuple indexed by itself. -/
def tupleOf (S : Set K) : ↥S → K := Subtype.val

omit [Field K] [Finite μ] hz in
theorem range_tupleOf (S : Set K) : range (tupleOf S) = S := Subtype.range_coe

omit [Finite μ] hz in
/-- `lem:code`(4): if every automorphism over `L` stabilises `S`, its code lies in `dcl L`. -/
theorem code_subset_dcl [IsAlgClosed K] [Fintype μ] {S : Finset (μ → K)}
    (h : ∀ σ : K ≃ₐ[↥L] K,
      S.map (compEmb (σ.restrictScalars k) (σ.restrictScalars k).injective) = S) :
    code S ⊆ dcl L := fun x hx ↦
  mem_dcl_iff_forall_fixed.2 fun σ ↦
    (fixes_code_iff_algEquiv (σ.restrictScalars k) S).2 (h σ) x hx

/-- `lem:conjcode`: the code of the conjugate set lies in `dcl L`. -/
theorem conjCode_subset_dcl [IsAlgClosed K] : conjCode L z ⊆ dcl L :=
  letI := Fintype.ofFinite μ
  code_subset_dcl fun σ ↦ conjSet_map hz σ

omit hz in
/-- `lem:conjcode`: the code of the conjugate set is interalgebraic with the conjugate set. -/
theorem racl_conjCode_eq_racl_coords :
    racl k (conjCode L z) = racl k (letI := Fintype.ofFinite μ; coords (conjSet L z)) :=
  letI := Fintype.ofFinite μ
  racl_code_eq _

/-- `lem:conjcode`: `z ⊆ acl(c)`. -/
theorem range_subset_racl_conjCode : range z ⊆ racl k (conjCode L z) := by
  let _ := Fintype.ofFinite μ
  rintro _ ⟨j, rfl⟩
  exact mem_racl_code (self_mem_conjSet hz) j

/-- The code of the conjugate set is interalgebraic with `z` as soon as every conjugate is
algebraic over `z`. -/
theorem racl_conjCode_eq (h : ∀ σ : K ≃ₐ[↥L] K, ∀ i, σ (z i) ∈ racl k (range z)) :
    racl k (conjCode L z) = racl k (range z) := by
  let _ := Fintype.ofFinite μ
  refine le_antisymm ?_ (racl_le_of_subset_racl (range_subset_racl_conjCode hz))
  rw [racl_conjCode_eq_racl_coords]
  refine racl_le_of_subset_racl fun x hx ↦ ?_
  obtain ⟨s, hs, j, rfl⟩ := mem_iUnion₂.1 hx
  obtain ⟨σ, rfl⟩ := (mem_conjSet hz).1 hs
  exact h σ j

/-- `lem:conjcode`, last claim: a tuple definable over `L₀, z` with coordinates in `L` is
definable over `L₀` and the code of the conjugate set of `z` over `L`. -/
theorem mem_dclAdjoin_conjCode [IsAlgClosed K] {L₀ : IntermediateField k K} (hL : L₀ ≤ L)
    {ν : Type*} [Finite ν] {w : ν → K} (hw : ∀ j, w j ∈ dclAdjoin L₀ z) (hwL : ∀ j, w j ∈ L)
    (j : ν) : w j ∈ dclAdjoin L₀ (fun x : conjCode L z ↦ (x : K)) := by
  let _ := Fintype.ofFinite μ
  obtain ⟨f, -, hfw⟩ := exists_quasiRational_of_mem_dclAdjoin hw
  unfold dclAdjoin
  refine mem_dcl_iff_forall_fixed.2 fun σ ↦ ?_
  have hfixL₀ : ∀ x ∈ L₀, (σ.restrictScalars k) x = x := fun x hx ↦ by
    change σ x = x
    exact σ.commutes
      ⟨x, (mem_restrictScalars k).2 (IntermediateField.algebraMap_mem _ (⟨x, hx⟩ : ↥L₀))⟩
  have hfixc : ∀ x ∈ conjCode L z, (σ.restrictScalars k) x = x := fun x hx ↦ by
    change σ x = x
    exact σ.commutes ⟨x, (mem_restrictScalars k).2 (subset_adjoin (↥L₀) _ ⟨⟨x, hx⟩, rfl⟩)⟩
  have hS := (fixes_code_iff_algEquiv (σ.restrictScalars k) (conjSet L z)).1 hfixc
  have hz' : ⇑(σ.restrictScalars k) ∘ z ∈ conjSet L z := by
    rw [← hS]
    exact Finset.mem_map_of_mem _ (self_mem_conjSet hz)
  obtain ⟨τ, hτ⟩ := (mem_conjSet hz).1 hz'
  let σ₀ : K ≃ₐ[↥L₀] K :=
    AlgEquiv.ofRingEquiv (f := (σ.restrictScalars k).toRingEquiv) fun c ↦ hfixL₀ c c.2
  let τ₀ : K ≃ₐ[↥L₀] K := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun c ↦ τ.commutes ⟨c, hL c.2⟩
  have e1 : ⇑σ₀ ∘ w = f.eval (⇑σ₀ ∘ z) := by
    rw [← hfw, f.eval_comp σ₀ z]
  have e2 : ⇑σ₀ ∘ z = ⇑τ₀ ∘ z := hτ.symm
  have e3 : f.eval (⇑τ₀ ∘ z) = ⇑τ₀ ∘ w := by
    rw [f.eval_comp τ₀ z, hfw]
  have e4 : ⇑τ₀ ∘ w = w := funext fun j ↦ τ.commutes ⟨w j, hwL j⟩
  change σ (w j) = w j
  exact congrFun (e1.trans ((congrArg f.eval e2).trans (e3.trans e4))) j

end

end GroupConfig
