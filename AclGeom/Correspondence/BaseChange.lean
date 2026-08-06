/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import AclGeom.Correspondence.FunctionField

/-!
# Rational function fields over a relatively closed base

The specialization brick for base-change irreducibility (step 4a of the
fused curve-coset chain): over an infinite field `k` that is algebraically
closed in `K`, a polynomial in `K[t]` satisfying a nontrivial algebraic
relation over `k[t]` has all its coefficients in `k`. Consequently `k(t)` is
relatively algebraically closed in `K(t)`.

The proof is by specialization: evaluating the relation at all but finitely
many points `τ ∈ k` shows the value `x(τ)` is algebraic over `k`, hence lies
in `k`; Lagrange interpolation through `deg x + 1` such nodes then forces
every coefficient of `x` into `k`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C7 support).
-/

namespace AclGeom

open Polynomial

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Specialization brick** (one-variable relative closure of rational
function fields, polynomial form): if `k` is infinite and algebraically
closed in `K`, then a polynomial `x ∈ K[t]` satisfying a nontrivial
polynomial relation with coefficients in `k[t]` is defined over `k`. -/
theorem exists_map_eq_of_eval₂_eq_zero [Infinite k]
    (hk : ∀ y : K, IsAlgebraic k y → y ∈ (algebraMap k K).range)
    {x : Polynomial K} {P : Polynomial (Polynomial k)} (hP : P ≠ 0)
    (hPx : Polynomial.eval₂ (mapRingHom (algebraMap k K)) x P = 0) :
    ∃ y : Polynomial k, x = y.map (algebraMap k K) := by
  classical
  set φ := algebraMap k K with hφ
  -- A nonzero coefficient of the relation, whose roots are the bad nodes.
  obtain ⟨i₀, hi₀⟩ := Polynomial.support_nonempty.2 hP
  have hc₀ : P.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  set bad : Finset k := (P.coeff i₀).roots.toFinset with hbad
  -- Specializing the relation at a good node makes the value algebraic.
  have hval : ∀ τ : k, τ ∉ bad → ∃ c : k, x.eval (φ τ) = φ c := by
    intro τ hτ
    have hPτ : P.map (evalRingHom τ) ≠ 0 := by
      intro h0
      have hcoeff := congrArg (fun q ↦ Polynomial.coeff q i₀) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcoeff
      exact hτ (Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hc₀, hcoeff⟩))
    have hcomp : (evalRingHom (φ τ)).comp (mapRingHom φ) =
        φ.comp (evalRingHom τ) := by
      refine RingHom.ext fun q ↦ ?_
      simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom]
      rw [eval_map, eval₂_at_apply]
    have hrel : Polynomial.eval₂ (φ.comp (evalRingHom τ)) (x.eval (φ τ)) P = 0 := by
      have h := congrArg (evalRingHom (φ τ)) hPx
      rw [map_zero, Polynomial.hom_eval₂, hcomp] at h
      exact h
    have halg : IsAlgebraic k (x.eval (φ τ)) := by
      refine ⟨P.map (evalRingHom τ), hPτ, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact hrel
    obtain ⟨c, hc⟩ := RingHom.mem_range.1 (hk _ halg)
    exact ⟨c, hc.symm⟩
  -- Choose `natDegree x + 1` good nodes.
  obtain ⟨s, hs_sub, hs_card⟩ := Set.Infinite.exists_subset_card_eq
    ((Set.infinite_univ (α := k)).sdiff bad.finite_toSet) (x.natDegree + 1)
  have hs_good : ∀ τ ∈ s, τ ∉ bad := fun τ hτ ↦ (hs_sub hτ).2
  -- The interpolated polynomial over `k`.
  set r : k → k := fun τ ↦ if h : τ ∉ bad then Classical.choose (hval τ h) else 0
    with hr
  have hrspec : ∀ τ ∈ s, x.eval (φ τ) = φ (r τ) := by
    intro τ hτ
    rw [hr]
    simp only [hs_good τ hτ]
    exact Classical.choose_spec (hval τ (hs_good τ hτ))
  set y : Polynomial k := Lagrange.interpolate s id r with hy
  refine ⟨y, ?_⟩
  -- Two polynomials of degree `< s.card` agreeing on the `s`-nodes coincide.
  have hinj : Set.InjOn (fun τ : k ↦ φ τ) s := fun a _ b _ h ↦
    (algebraMap k K).injective h
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := fun τ : k ↦ φ τ)
    s hinj ?_ ?_ ?_
  · calc x.degree ≤ (x.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (s.card : WithBot ℕ) := by
          rw [hs_card]
          exact_mod_cast Nat.lt_succ_self _
  · calc (y.map φ).degree ≤ y.degree := Polynomial.degree_map_le
      _ < (s.card : WithBot ℕ) :=
          Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  · intro τ hτ
    have hnode := Lagrange.eval_interpolate_at_node (v := id) (r := r)
      (Set.injOn_id _) hτ
    simp only [id_eq] at hnode
    rw [eval_map, eval₂_at_apply, hy, hnode]
    exact hrspec τ hτ

/-- The specialization brick in `IsAlgClosed` form: over an algebraically
closed base every element of `K` algebraic over `k` already lies in `k`, and
`k` is infinite. -/
theorem exists_map_eq_of_eval₂_eq_zero_of_isAlgClosed [IsAlgClosed k]
    {x : Polynomial K} {P : Polynomial (Polynomial k)} (hP : P ≠ 0)
    (hPx : Polynomial.eval₂ (mapRingHom (algebraMap k K)) x P = 0) :
    ∃ y : Polynomial k, x = y.map (algebraMap k K) := by
  have hk : ∀ y : K, IsAlgebraic k y → y ∈ (algebraMap k K).range := by
    intro y hy
    have hint : IsIntegral k y := hy.isIntegral
    refine ⟨-(minpoly k y).coeff 0, ?_⟩
    have hq : (minpoly k y).leadingCoeff = 1 := minpoly.monic hint
    have h1 : (minpoly k y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    have h0 : aeval y (minpoly k y) = 0 := minpoly.aeval k y
    rw [eq_X_add_C_of_degree_eq_one h1, hq, C_1, one_mul, aeval_add, aeval_X,
      aeval_C, add_eq_zero_iff_eq_neg] at h0
    exact (map_neg (algebraMap k K) ((minpoly k y).coeff 0)).symm ▸ h0.symm
  exact exists_map_eq_of_eval₂_eq_zero hk hP hPx

section CurveDictionary

open MvPolynomial IntermediateField

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- Partial evaluation of a plane polynomial at a point `u` in the first
coordinate: `g(X, Y) ↦ g(u, Y)`, a one-variable polynomial with coefficients
in `K(u)`. This is the dictionary between the curve ideal in `K[X, Y]` and
minimal polynomials over `K(u)`. -/
def evalFst (u : Ω) :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial ↥(adjoin K ({u} : Set Ω)) :=
  aeval ![Polynomial.C ⟨u, subset_adjoin K _ rfl⟩, Polynomial.X]

/-- Evaluating the second variable recovers the joint evaluation: the
dictionary is compatible with taking points. -/
theorem eval₂_evalFst (u v : Ω) (g : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v
      (evalFst (K := K) u g) = MvPolynomial.aeval ![u, v] g := by
  have hcomp : ((Polynomial.eval₂RingHom
        (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v).comp
      (evalFst (K := K) u).toRingHom) = (MvPolynomial.aeval ![u, v]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [evalFst, IntermediateField.algebraMap_apply]
    · fin_cases i <;> simp [evalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) K →+* Ω) ↦ f g) hcomp

/-- Membership in the vanishing ideal of a plane point, through the
dictionary: `g` vanishes at `(u, v)` iff its partial evaluation at `u`
annihilates `v`. -/
theorem mem_idealOf_iff_evalFst {u v : Ω} {g : MvPolynomial (Fin 2) K} :
    g ∈ idealOf K ![u, v] ↔
      Polynomial.eval₂ (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v
        (evalFst (K := K) u g) = 0 := by
  rw [mem_idealOf_iff, eval₂_evalFst]

/-- `evalFst` factors through the variable-separation equivalence: it is the
coefficientwise evaluation of the `Y`-separated form. -/
theorem evalFst_apply_eq (u : Ω) (g : MvPolynomial (Fin 2) K) :
    evalFst (K := K) u g =
      (finSuccEquiv K 1 (rename (Equiv.swap 0 1) g)).map
        (MvPolynomial.aeval
          ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom := by
  have hcomp : (evalFst (K := K) u (Ω := Ω)).toRingHom =
      ((Polynomial.mapRingHom (MvPolynomial.aeval
          ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom).comp
        ((finSuccEquiv K 1 : MvPolynomial (Fin 2) K ≃ₐ[K] _).toRingEquiv.toRingHom.comp
          (rename (Equiv.swap (0 : Fin 2) 1)).toRingHom)) := by
    have hXone : finSuccEquiv K 1 (X (1 : Fin 2)) = Polynomial.C (X 0) := by
      have h := finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
      simpa using h
    have hC : ∀ c : K, finSuccEquiv K 1 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := fun c ↦ by
      simp [finSuccEquiv_apply, eval₂Hom_C]
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [evalFst, hC]
    · fin_cases i
      · have h1 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        simp [evalFst, h1, hXone]
      · have h1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        simp [evalFst, h1, finSuccEquiv_X_zero]
  exact congrArg (fun (f : MvPolynomial (Fin 2) K →+* _) ↦ f g) hcomp

/-- **Degree preservation**: for `u` transcendental over `K`, the partial
evaluation at `u` preserves the degree in the second variable. This is the
count that transfers divisibility bounds between the plane and `K(u)[Y]`. -/
theorem natDegree_evalFst {u : Ω} (hu : Transcendental K u)
    (g : MvPolynomial (Fin 2) K) :
    (evalFst (K := K) u g).natDegree = g.degreeOf 1 := by
  have htr : Transcendental K
      (⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω))) := by
    intro halg
    exact hu (by
      have := (halg.isIntegral.map
        (adjoin K ({u} : Set Ω)).val).isAlgebraic
      simpa using this)
  have hind : AlgebraicIndependent K
      ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))] :=
    algebraicIndependent_unique_type_iff.2 htr
  have hinj : Function.Injective (MvPolynomial.aeval
      ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom :=
    hind
  rw [evalFst_apply_eq, Polynomial.natDegree_map_eq_of_injective hinj,
    natDegree_finSuccEquiv]
  have hswap := degreeOf_rename_of_injective
    (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) (p := g) 1
  rw [Equiv.swap_apply_right] at hswap
  exact hswap

end CurveDictionary

end

end AclGeom
