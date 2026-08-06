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

section CoordPoly

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']
variable {ι : Type*}

/-- The `j`-th coordinate polynomial of a `K'`-polynomial along a `k`-basis:
apply the coordinate functional coefficientwise. -/
def coordPoly (b : Module.Basis ι k K') (j : ι) (q : Polynomial K') :
    Polynomial k :=
  q.sum fun m a ↦ Polynomial.C (b.repr a j) * Polynomial.X ^ m

theorem coordPoly_coeff (b : Module.Basis ι k K') (j : ι) (q : Polynomial K')
    (m : ℕ) : (coordPoly b j q).coeff m = b.repr (q.coeff m) j := by
  classical
  rw [coordPoly, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl fun i _ ↦
    Polynomial.coeff_C_mul_X_pow (b.repr (q.coeff i) j) i m]
  rw [Finset.sum_ite_eq q.support m fun i ↦ b.repr (q.coeff i) j]
  by_cases hm : m ∈ q.support
  · rw [if_pos hm]
  · rw [if_neg hm, Polynomial.notMem_support_iff.1 hm, map_zero,
      Finsupp.coe_zero, Pi.zero_apply]

/-- Coordinate polynomials commute with evaluation at points of `k`. -/
theorem eval_coordPoly (b : Module.Basis ι k K') (j : ι) (q : Polynomial K')
    (τ : k) :
    (coordPoly b j q).eval τ = b.repr (q.eval (algebraMap k K' τ)) j := by
  classical
  rw [coordPoly, Polynomial.sum_def, Polynomial.eval_finsetSum]
  have hq : q.eval (algebraMap k K' τ) = ∑ m ∈ q.support, τ ^ m • q.coeff m := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [hq, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- Coordinate polynomials are `k[X]`-linear in the `k`-defined factor. -/
theorem coordPoly_mul_map (b : Module.Basis ι k K') (j : ι)
    (r : Polynomial K') (q : Polynomial k) :
    coordPoly b j (r * q.map (algebraMap k K')) = coordPoly b j r * q := by
  classical
  ext m
  rw [coordPoly_coeff, Polynomial.coeff_mul, Polynomial.coeff_mul, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Polynomial.coeff_map, coordPoly_coeff]
  have h1 : r.coeff x.1 * algebraMap k K' (q.coeff x.2) =
      q.coeff x.2 • r.coeff x.1 := by
    rw [Algebra.smul_def, mul_comm]
  rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

end CoordPoly

section Descent

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k K' Ω : Type*} [Field k] [Field K'] [Field Ω]
variable [Algebra k K'] [Algebra K' Ω] [Algebra k Ω] [IsScalarTower k K' Ω]

/-- **The descent brick** (chunk α of the base-change argument): over an
infinite field `k` that is algebraically closed in `K'`, an element of
`K'(u)` that is algebraic over `k(u)` already lies in `k(u)`, for `u`
transcendental over `K'`. The proof homogenizes the algebraic relation into
a polynomial identity, decomposes numerator and denominator along a
`k`-basis of `K'`, and specializes at the points of `k`: the values are
algebraic over `k`, hence in `k`, and cross-multiplied coordinates agree on
a cofinite set, hence everywhere. -/
theorem mem_adjoin_base_of_isAlgebraic [Infinite k]
    (hk : ∀ y : K', IsAlgebraic k y → y ∈ (algebraMap k K').range)
    {u c : Ω} (hu : Transcendental K' u)
    (hcK : c ∈ adjoin K' ({u} : Set Ω))
    (hcalg : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) c) :
    c ∈ adjoin k ({u} : Set Ω) := by
  classical
  set φ' := algebraMap k K' with hφ'
  -- Write `c` as a ratio of `K'`-polynomial values at `u`.
  obtain ⟨r, s, hc⟩ := (mem_adjoin_simple_iff K' c).1 hcK
  rcases eq_or_ne (Polynomial.aeval u s) 0 with hs0 | hs0
  · rw [hc, hs0, div_zero]
    exact zero_mem _
  have hcs : c * Polynomial.aeval u s = Polynomial.aeval u r := by
    rw [hc, div_mul_cancel₀ _ hs0]
  have hs_ne : s ≠ 0 := fun h ↦ hs0 (by rw [h, map_zero])
  -- The algebraic relation, with coefficients polynomial in `u`.
  have hcalg' : IsAlgebraic ↥(Algebra.adjoin k ({u} : Set Ω)) c :=
    (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k ({u} : Set Ω))
      (adjoin k ({u} : Set Ω)) Ω).2 hcalg
  obtain ⟨p, hp0, hpc⟩ := hcalg'
  have hrepr : ∀ m : ℕ, ∃ P : Polynomial k,
      Polynomial.aeval u P = (p.coeff m : Ω) := by
    intro m
    have hle := (Algebra.adjoin_singleton_eq_range_aeval k u).le
    exact (AlgHom.mem_range _).1 (hle (p.coeff m).2)
  choose P hP using hrepr
  set n := p.natDegree with hn
  have hlead : Polynomial.aeval u (P n) ≠ 0 := by
    rw [hP n]
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.2 hp0
  have hPn : P n ≠ 0 := fun h ↦ hlead (by rw [h, map_zero])
  -- Transcendence of `u` over `k` as well.
  have huk : Transcendental k u := fun halg ↦ hu (halg.tower_top K')
  -- Homogenize: a polynomial identity over `K'`.
  set E : Polynomial K' := ∑ m ∈ Finset.range (n + 1),
    (P m).map φ' * r ^ m * s ^ (n - m) with hE
  have hEval : Polynomial.aeval u E = 0 := by
    have hexp : Polynomial.aeval c p =
        ∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m := by
      rw [Polynomial.aeval_eq_sum_range]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Algebra.smul_def]
      rfl
    have hzero : ∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m = 0 := by
      rw [← hexp, hpc]
    have hkey : Polynomial.aeval u E =
        (∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m) *
          (Polynomial.aeval u s) ^ n := by
      rw [hE, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      rw [map_mul, map_mul, map_pow, map_pow,
        Polynomial.aeval_map_algebraMap, hP m, ← hcs]
      have hsplit : (Polynomial.aeval u s : Ω) ^ n =
          (Polynomial.aeval u s) ^ m * (Polynomial.aeval u s) ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hmn]
      rw [hsplit]
      ring
    rw [hkey, hzero, zero_mul]
  have hE0 : E = 0 := by
    by_contra hne
    exact hu ⟨E, hne, hEval⟩
  -- Basis decomposition of numerator and denominator.
  set b := Module.Basis.ofVectorSpace k K' with hb
  -- A coordinate where the denominator is visible.
  obtain ⟨ms, hms⟩ := Polynomial.support_nonempty.2 hs_ne
  have hms0 : s.coeff ms ≠ 0 := Polynomial.mem_support_iff.1 hms
  obtain ⟨j₀, hj₀⟩ : ∃ j, b.repr (s.coeff ms) j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hms0 (b.repr.injective (by ext j; simp [hall j]))
  have hSj₀ : coordPoly b j₀ s ≠ 0 := fun h ↦ by
    have := coordPoly_coeff b j₀ s ms
    rw [h, Polynomial.coeff_zero] at this
    exact hj₀ this.symm
  -- The bad specialization points: roots of `P n` and of the denominator.
  set badP : Finset k := (P n).roots.toFinset with hbadP
  have hsroots : Set.Finite {τ : k | s.eval (φ' τ) = 0} := by
    have hsub : {τ : k | s.eval (φ' τ) = 0} ⊆
        (fun τ ↦ φ' τ) ⁻¹' {y : K' | s.eval y = 0} := fun τ hτ ↦ hτ
    refine Set.Finite.subset (Set.Finite.preimage
      (Set.injOn_of_injective (algebraMap k K').injective)
      (Polynomial.finite_setOf_isRoot hs_ne)) hsub
  -- Pointwise coordinate identities on the good set.
  have hgood : ∀ τ : k, τ ∉ badP → s.eval (φ' τ) ≠ 0 → ∀ j,
      (coordPoly b j r * coordPoly b j₀ s).eval τ =
      (coordPoly b j₀ r * coordPoly b j s).eval τ := by
    intro τ hτP hτs j
    -- The specialized value is algebraic over `k`, hence in `k`.
    have hspec : ∑ m ∈ Finset.range (n + 1),
        φ' ((P m).eval τ) * r.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) = 0 := by
      have h := congrArg (Polynomial.eval (φ' τ)) hE0
      rw [hE, Polynomial.eval_finsetSum, Polynomial.eval_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_pow, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    set w : K' := r.eval (φ' τ) / s.eval (φ' τ) with hw
    have hwalg : IsAlgebraic k w := by
      refine ⟨∑ m ∈ Finset.range (n + 1),
        Polynomial.C ((P m).eval τ) * Polynomial.X ^ m, ?_, ?_⟩
      · intro h0
        have hcoeff := congrArg (fun q ↦ Polynomial.coeff q n) h0
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
        rw [Finset.sum_congr rfl fun m _ ↦
          Polynomial.coeff_C_mul_X_pow ((P m).eval τ) m n] at hcoeff
        rw [Finset.sum_ite_eq (Finset.range (n + 1)) n fun m ↦ (P m).eval τ,
          if_pos (Finset.self_mem_range_succ n)] at hcoeff
        exact hτP (Multiset.mem_toFinset.2
          (Polynomial.mem_roots'.2 ⟨hPn, hcoeff⟩))
      · rw [Polynomial.aeval_def, Polynomial.eval₂_finsetSum]
        have hterm : ∀ m ∈ Finset.range (n + 1),
            Polynomial.eval₂ φ' w (Polynomial.C ((P m).eval τ) *
              Polynomial.X ^ m) =
            φ' ((P m).eval τ) * r.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) /
              s.eval (φ' τ) ^ n := by
          intro m hm
          have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
            Polynomial.eval₂_X, hw, div_pow, ← mul_div_assoc,
            div_eq_div_iff (pow_ne_zero m hτs) (pow_ne_zero n hτs)]
          have hsplit : s.eval (φ' τ) ^ n =
              s.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) := by
            rw [← pow_add, Nat.add_sub_cancel' hmn]
          rw [hsplit]
          ring
        rw [Finset.sum_congr rfl hterm]
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, hspec, zero_mul]
    obtain ⟨cτ, hcτ⟩ := RingHom.mem_range.1 (hk w hwalg)
    -- Numerator = value • denominator, coordinatewise.
    have hrs : r.eval (φ' τ) = cτ • s.eval (φ' τ) := by
      rw [Algebra.smul_def, hcτ, hw, div_mul_cancel₀ _ hτs]
    simp only [Polynomial.eval_mul]
    rw [eval_coordPoly, eval_coordPoly, eval_coordPoly, eval_coordPoly, hrs,
      map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  -- Cross-multiplied coordinates agree everywhere.
  have hD : ∀ j, coordPoly b j r * coordPoly b j₀ s =
      coordPoly b j₀ r * coordPoly b j s := by
    intro j
    have hbadfin : Set.Finite ((badP : Set k) ∪ {τ : k | s.eval (φ' τ) = 0}) :=
      Set.Finite.union badP.finite_toSet hsroots
    have hroots : {τ : k | (coordPoly b j r * coordPoly b j₀ s -
        coordPoly b j₀ r * coordPoly b j s).IsRoot τ}.Infinite := by
      refine Set.Infinite.mono ?_
        (Set.Infinite.sdiff (Set.infinite_univ (α := k)) hbadfin)
      intro τ hτ
      have hτP : τ ∉ badP := fun h ↦ hτ.2 (Or.inl h)
      have hτs : s.eval (φ' τ) ≠ 0 := fun h ↦ hτ.2 (Or.inr h)
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub]
      rw [hgood τ hτP hτs j, sub_self]
    have := Polynomial.eq_zero_of_infinite_isRoot _ hroots
    rw [sub_eq_zero] at this
    exact this
  -- Reconstruct the polynomial identity over `K'` and divide at `u`.
  have hpoly : r * (coordPoly b j₀ s).map φ' = (coordPoly b j₀ r).map φ' * s := by
    ext m
    have hcoord : ∀ j, b.repr ((r * (coordPoly b j₀ s).map φ').coeff m) j =
        b.repr (((coordPoly b j₀ r).map φ' * s).coeff m) j := by
      intro j
      rw [← coordPoly_coeff b j, ← coordPoly_coeff b j, coordPoly_mul_map]
      have hcomm : (coordPoly b j₀ r).map φ' * s =
          s * (coordPoly b j₀ r).map φ' := mul_comm _ _
      rw [hcomm, coordPoly_mul_map, hD j]
      ring_nf
    exact b.repr.injective (Finsupp.ext fun j ↦ hcoord j)
  have hnum : Polynomial.aeval u r * Polynomial.aeval u (coordPoly b j₀ s) =
      Polynomial.aeval u (coordPoly b j₀ r) * Polynomial.aeval u s := by
    have h := congrArg (Polynomial.aeval u) hpoly
    rw [map_mul, map_mul, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_map_algebraMap] at h
    exact h
  have hSu : Polynomial.aeval u (coordPoly b j₀ s) ≠ 0 := fun h ↦
    huk ⟨coordPoly b j₀ s, hSj₀, h⟩
  -- Conclude: `c` is a ratio of `k`-polynomial values at `u`.
  have hcval : c = Polynomial.aeval u (coordPoly b j₀ r) /
      Polynomial.aeval u (coordPoly b j₀ s) := by
    rw [hc, div_eq_div_iff hs0 hSu, hnum]
  rw [hcval]
  have hmemP : ∀ Q : Polynomial k,
      Polynomial.aeval u Q ∈ adjoin k ({u} : Set Ω) := by
    intro Q
    have hmem : Polynomial.aeval u Q ∈ Algebra.adjoin k ({u} : Set Ω) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact (AlgHom.mem_range _).2 ⟨Q, rfl⟩
    exact algebra_adjoin_le_adjoin k _ hmem
  exact div_mem (hmemP _) (hmemP _)

end Descent

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
