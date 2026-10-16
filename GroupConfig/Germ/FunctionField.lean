/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.CanonicalBase
import AclGeom.Closure.Ambient
import AclGeom.Curves.Places
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# The function field of a locus over the universal domain

For a tuple `v` of the universal domain `K` over an algebraically closed field `k`, the locus
ideal `locusIdeal k v ⊆ K[X]` is prime, and its quotient has a fraction field
`LocusFunctionField k v`: the function field over `K` of the locus of `v`. Its elements are
fractions `A / B` of polynomials over `K`. Generic points over small subfields give the
dictionary with the ambient field:

* `LocusFunctionField.map_mem_locusIdeal_iff_aeval`: a polynomial with coefficients in `M` lies in
  the locus ideal iff it vanishes at one generic point over `M`;
* `LocusFunctionField.HasValue`: `h` takes the value `c` at a generic point `y` if
  `h = A / B` with coefficients in `M` and `c = A(y) / B(y)`. Values determine elements and
  conversely (`HasValue.eq`, `HasValue.eq_value`), and every element has values at all generic
  points over some small algebraically closed field (`exists_hasValue`).

For a curve, `LocusFunctionField.isFunctionFieldOneVar` shows that this field is a function
field of one variable over `K`, in the sense of the curve library.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** complete for its consumer, the function-field action of Hrushovski–Weil groups
on curves (`GroupConfig.Germ.IsHW.functionFieldAction`).
-/

namespace GroupConfig

open AclGeom MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] {ι : Type*}

variable (k) in
/-- The function field over `K` of the locus of `v` over `k`: the fraction field of
`K[X] / locusIdeal k v`. -/
abbrev LocusFunctionField (v : ι → K) : Type _ :=
  FractionRing (MvPolynomial ι K ⧸ locusIdeal k v)

namespace LocusFunctionField

variable {v : ι → K}

variable (k v) in
/-- The class of a polynomial over `K` in the function field. -/
def mk : MvPolynomial ι K →ₐ[K] LocusFunctionField k v :=
  (IsScalarTower.toAlgHom K (MvPolynomial ι K ⧸ locusIdeal k v) _).comp
    (Ideal.Quotient.mkₐ K (locusIdeal k v))

variable (k v) in
/-- The coordinate functions. -/
def coord (i : ι) : LocusFunctionField k v := mk k v (X i)

omit [IsAlgClosed k] in
theorem mk_eq_zero_iff {P : MvPolynomial ι K} : mk k v P = 0 ↔ P ∈ locusIdeal k v := by
  change algebraMap (MvPolynomial ι K ⧸ locusIdeal k v) _ (Ideal.Quotient.mk _ P) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

omit [IsAlgClosed k] in
theorem aeval_coord (P : MvPolynomial ι K) : aeval (coord k v) P = mk k v P := by
  have h : aeval (coord k v) = mk k v := MvPolynomial.algHom_ext fun i ↦ by
    rw [aeval_X]
    rfl
  rw [h]

/-- Every element is a fraction of polynomials with denominator outside the locus ideal. -/
theorem exists_fraction (h : LocusFunctionField k v) :
    ∃ A B : MvPolynomial ι K, B ∉ locusIdeal k v ∧ h = mk k v A / mk k v B := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι K ⧸ locusIdeal k v) h
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨A, B, fun hB ↦ ?_, rfl⟩
  exact nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.2 hB)

/-! ### Generic points -/

variable {M : IntermediateField k K} {y : ι → K}

omit [IsAlgClosed k] in
/-- A polynomial with coefficients in `M` lies in the locus ideal iff it vanishes at a generic
point over `M`. -/
theorem map_mem_locusIdeal_iff_aeval (hy : IsGenericOver M v y) (P : MvPolynomial ι M) :
    MvPolynomial.map (algebraMap M K) P ∈ locusIdeal k v ↔ aeval y P = 0 := by
  rw [← hy.locusIdeal_eq, map_mem_locusIdeal_iff, mem_idealOf_iff]

omit [IsAlgClosed k] in
theorem mk_map_ne_zero (hy : IsGenericOver M v y) {P : MvPolynomial ι M} (hP : aeval y P ≠ 0) :
    mk k v (MvPolynomial.map (algebraMap M K) P) ≠ 0 := by
  rw [Ne, mk_eq_zero_iff, map_mem_locusIdeal_iff_aeval hy]
  exact hP

omit [IsAlgClosed k] in
theorem mk_map_eq_zero_iff (hy : IsGenericOver M v y) (P : MvPolynomial ι M) :
    mk k v (MvPolynomial.map (algebraMap M K) P) = 0 ↔ aeval y P = 0 := by
  rw [mk_eq_zero_iff, map_mem_locusIdeal_iff_aeval hy]

variable (M y) in
/-- `h` has value `c` at `y`, through a fraction `A / B` with coefficients in `M`. -/
def HasValue (h : LocusFunctionField k v) (c : K) : Prop :=
  ∃ A B : MvPolynomial ι M, aeval y B ≠ 0 ∧
    h = mk k v (MvPolynomial.map (algebraMap M K) A) /
      mk k v (MvPolynomial.map (algebraMap M K) B) ∧
    c = aeval y A / aeval y B

theorem hasValue_mk (P : MvPolynomial ι M) :
    HasValue M y (mk k v (MvPolynomial.map (algebraMap M K) P)) (aeval y P) :=
  ⟨P, 1, by simp, by simp, by simp⟩

theorem hasValue_coord (i : ι) : HasValue M y (coord k v i) (y i) := by
  have h := hasValue_mk (k := k) (v := v) (M := M) (y := y) (X i)
  rwa [MvPolynomial.map_X, aeval_X] at h

/-- At a generic point, an element has at most one value. -/
theorem HasValue.eq_value (hy : IsGenericOver M v y) {h : LocusFunctionField k v} {c c' : K}
    (h₁ : HasValue M y h c) (h₂ : HasValue M y h c') : c = c' := by
  obtain ⟨A, B, hB, rfl, rfl⟩ := h₁
  obtain ⟨A', B', hB', heq, rfl⟩ := h₂
  rw [div_eq_div_iff (mk_map_ne_zero hy hB) (mk_map_ne_zero hy hB'), ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, ← map_sub, mk_map_eq_zero_iff hy] at heq
  rw [div_eq_div_iff hB hB', ← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]
  exact heq

/-- At a generic point, elements with the same value are equal. -/
theorem HasValue.eq (hy : IsGenericOver M v y) {h h' : LocusFunctionField k v} {c : K}
    (h₁ : HasValue M y h c) (h₂ : HasValue M y h' c) : h = h' := by
  obtain ⟨A, B, hB, rfl, rfl⟩ := h₁
  obtain ⟨A', B', hB', rfl, heq⟩ := h₂
  rw [div_eq_div_iff hB hB', ← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub] at heq
  rw [div_eq_div_iff (mk_map_ne_zero hy hB) (mk_map_ne_zero hy hB'), ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, ← map_sub, mk_map_eq_zero_iff hy]
  exact heq

/-- Values at a generic point are additive. -/
theorem HasValue.add (hy : IsGenericOver M v y) {h h' : LocusFunctionField k v} {c c' : K}
    (h₁ : HasValue M y h c) (h₂ : HasValue M y h' c') : HasValue M y (h + h') (c + c') := by
  obtain ⟨A, B, hB, rfl, rfl⟩ := h₁
  obtain ⟨A', B', hB', rfl, rfl⟩ := h₂
  refine ⟨A * B' + B * A', B * B', by rw [map_mul]; exact mul_ne_zero hB hB', ?_, ?_⟩
  · rw [div_add_div _ _ (mk_map_ne_zero hy hB) (mk_map_ne_zero hy hB')]
    simp only [map_add, map_mul]
  · rw [div_add_div _ _ hB hB']
    simp only [map_add, map_mul]

/-- Values are multiplicative. -/
theorem HasValue.mul {h h' : LocusFunctionField k v} {c c' : K} (h₁ : HasValue M y h c)
    (h₂ : HasValue M y h' c') : HasValue M y (h * h') (c * c') := by
  obtain ⟨A, B, hB, rfl, rfl⟩ := h₁
  obtain ⟨A', B', hB', rfl, rfl⟩ := h₂
  refine ⟨A * A', B * B', by rw [map_mul]; exact mul_ne_zero hB hB', ?_, ?_⟩
  · rw [div_mul_div_comm]
    simp only [map_mul]
  · rw [div_mul_div_comm]
    simp only [map_mul]

/-- A constant from a subfield of `M` has itself as value. -/
theorem hasValue_algebraMap {C : IntermediateField k K} (hCM : C ≤ M) (c : C) :
    HasValue M y (algebraMap C (LocusFunctionField k v) c) (algebraMap C K c) := by
  have h := hasValue_mk (k := k) (v := v) (y := y) (MvPolynomial.C
    (IntermediateField.inclusion hCM c))
  rw [MvPolynomial.map_C, aeval_C] at h
  convert h using 1
  · rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rfl
  · rfl

variable [IsAlgClosed K] [UniversalDomain k K] [Finite ι]

omit [UniversalDomain k K] [Finite ι] in
/-- Every element has a value at every generic point over some small algebraically closed
field containing a prescribed small set. -/
theorem exists_hasValue (h : LocusFunctionField k v) {T : Set K} (hT : IsSmall k T) :
    ∃ N : IntermediateField k K, T ⊆ N ∧ IsAlgClosed ↥N ∧ IsSmall k (N : Set K) ∧
      ∀ y, IsGenericOver N v y → ∃ c, HasValue N y h c := by
  obtain ⟨A, B, hB, rfl⟩ := exists_fraction h
  set N := racl k (T ∪ (↑A.coeffs ∪ ↑B.coeffs))
  have hcoeff : ∀ P : MvPolynomial ι K, ↑P.coeffs ⊆ (N : Set K) →
      ∃ P₀ : MvPolynomial ι N, MvPolynomial.map (algebraMap N K) P₀ = P := fun P hP ↦
    mem_range_map_iff_coeffs_subset.mpr fun c hc ↦ ⟨⟨c, hP hc⟩, rfl⟩
  obtain ⟨A₀, hA₀⟩ := hcoeff A fun c hc ↦ subset_racl k _ (Or.inr (Or.inl hc))
  obtain ⟨B₀, hB₀⟩ := hcoeff B fun c hc ↦ subset_racl k _ (Or.inr (Or.inr hc))
  refine ⟨N, fun c hc ↦ subset_racl k _ (Or.inl hc), isAlgClosed_racl _,
    (hT.union (IsSmall.of_finite (A.coeffs.finite_toSet.union B.coeffs.finite_toSet))).racl,
    fun y hy ↦ ⟨_, A₀, B₀, ?_, by rw [hA₀, hB₀], rfl⟩⟩
  rw [Ne, ← map_mem_locusIdeal_iff_aeval hy, hB₀]
  exact hB

/-! ### Curves -/

/-- For a curve, the function field of the locus is a function field of one variable over the
universal domain. -/
theorem isFunctionFieldOneVar (hv : erk k ∅ (range v) = 1) :
    AclGeom.IsFunctionFieldOneVar K (LocusFunctionField k v) := by
  -- A coordinate transcendental over `k`.
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ racl k (∅ : Set K) := by
    by_contra! hall
    have h0 : erk k ∅ (range v) = 0 := (erk_eq_zero_iff k).2 (by
      rintro _ ⟨i, rfl⟩
      exact hall i)
    rw [hv] at h0
    exact one_ne_zero h0
  have hone : ∀ {C : Set K} {x : K}, x ∉ racl k C → erk k C {x} = 1 := fun hx ↦
    le_antisymm ((erk_le_encard k _ _).trans_eq (encard_singleton _))
      (Order.one_le_iff_ne_zero.2 fun h0 ↦ hx ((erk_singleton_eq_zero_iff k).1 h0))
  set x := coord k v i
  -- `x` is transcendental over `K`.
  have htr : Transcendental K x := by
    rw [transcendental_iff]
    intro q hq
    by_contra hq0
    have hQ : Polynomial.aeval (X i : MvPolynomial ι K) q ∈ locusIdeal k v := by
      rw [← mk_eq_zero_iff, ← Polynomial.aeval_algHom_apply]
      exact hq
    set N := racl k (↑q.coeffs : Set K)
    have hNs : IsSmall k (N : Set K) := (IsSmall.of_finite q.coeffs.finite_toSet).racl
    obtain ⟨y, hy⟩ := exists_isGenericOver hNs v
    obtain ⟨q₀, hq₀⟩ : q ∈ Polynomial.lifts (algebraMap N K) :=
      (Polynomial.lifts_iff_coeff_lifts q).2 fun n ↦ by
        by_cases hn : q.coeff n = 0
        · exact ⟨0, by rw [hn, map_zero]⟩
        · exact ⟨⟨q.coeff n, subset_racl k _ (Polynomial.coeff_mem_coeffs hn)⟩, rfl⟩
    rw [Polynomial.coe_mapRingHom] at hq₀
    have hmap : ∀ p : Polynomial N, Polynomial.aeval (X i : MvPolynomial ι K)
        (p.map (algebraMap N K)) =
          MvPolynomial.map (algebraMap N K) (Polynomial.aeval (X i) p) := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p p' hp hp' => rw [Polynomial.map_add, map_add, hp, hp', map_add, map_add]
      | monomial n c => simp [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    rw [← hq₀, hmap, map_mem_locusIdeal_iff_aeval hy, ← Polynomial.aeval_algHom_apply,
      aeval_X] at hQ
    have hyi : y i ∈ N :=
      mem_racl_iff_exists_poly.2 ⟨q, hq0, by
        rw [← hq₀, Polynomial.eval_map_algebraMap]; exact hQ, fun n ↦ by
          by_cases hn : q.coeff n = 0
          · rw [hn]; exact zero_mem _
          · exact IntermediateField.subset_adjoin _ _ (Polynomial.coeff_mem_coeffs hn)⟩
    have hind := hy.indepOver.erk_eq (a := {y i}) (singleton_subset_iff.2 ⟨i, rfl⟩)
      (finite_singleton _)
    rw [empty_union, (erk_singleton_eq_zero_iff k).2 (subset_racl k _ hyi)] at hind
    have hvi : erk k ∅ ({y i} : Set K) = erk k ∅ {v i} := by
      have hid : idealOf k (fun _ : Unit ↦ y i) = idealOf k (fun _ : Unit ↦ v i) := by
        ext f
        rw [mem_idealOf_iff, mem_idealOf_iff]
        have hy' : aeval (fun _ : Unit ↦ y i) f = aeval y (rename (fun _ ↦ i) f) := by
          rw [aeval_rename]
          rfl
        have hv' : aeval (fun _ : Unit ↦ v i) f = aeval v (rename (fun _ ↦ i) f) := by
          rw [aeval_rename]
          rfl
        rw [hy', hv', ← mem_idealOf_iff k, ← mem_idealOf_iff k, hy.idealOf_eq]
      have h := erk_empty_range_eq_of_idealOf_eq (k := k) hid
      simpa [range_const] using h
    rw [hvi, hone hi] at hind
    exact zero_ne_one hind
  -- Every coordinate is algebraic over `K(x)`.
  have hindx : AlgebraicIndependent K fun _ : Unit ↦ x :=
    algebraicIndependent_unique_type_iff.2 htr
  have halg : ∀ j, IsIntegral (IntermediateField.adjoin K {x}) (coord k v j) := by
    intro j
    have hj : v j ∈ racl k ({v i} : Set K) := by
      by_contra hj
      have h2 := erk_union_eq k ∅ {v i} {v j}
      rw [hone hi, empty_union, hone hj] at h2
      have h3 := (erk_mono k ∅ (show {v i} ∪ {v j} ⊆ range v from
        union_subset (singleton_subset_iff.2 ⟨i, rfl⟩)
          (singleton_subset_iff.2 ⟨j, rfl⟩))).trans_eq hv
      rw [h2] at h3
      norm_num at h3
    -- A polynomial relation between `v j` and `v i` over `k`.
    have hdep : ¬ AlgebraicIndependent k fun o : Option Unit ↦ o.elim (v j) fun _ ↦ v i := by
      rw [AlgebraicIndependent.option_iff, range_const]
      rintro ⟨-, htr'⟩
      rw [← IntermediateField.transcendental_adjoin_iff] at htr'
      exact htr' ((mem_racl_iff k).1 hj)
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨P, hP, hP0⟩ := hdep
    set e : Option Unit → ι := fun o ↦ o.elim j fun _ ↦ i
    have hve : (fun o : Option Unit ↦ o.elim (v j) fun _ ↦ v i) = v ∘ e := by
      funext o
      cases o <;> rfl
    have hmem : MvPolynomial.map (algebraMap k K) (rename e P) ∈ locusIdeal k v := by
      refine map_mem_locusIdeal k ((mem_idealOf_iff k).2 ?_)
      rw [aeval_rename, ← hve]
      exact hP
    have hdepK : ¬ AlgebraicIndependent K fun o : Option Unit ↦ o.elim (coord k v j)
        fun _ ↦ x := by
      rw [algebraicIndependent_iff]
      push Not
      refine ⟨MvPolynomial.map (algebraMap k K) P, ?_, ?_⟩
      · rw [← mk_eq_zero_iff, ← aeval_coord, map_rename, aeval_rename] at hmem
        have hfam : (fun o : Option Unit ↦ o.elim (coord k v j) fun _ ↦ x) = coord k v ∘ e := by
          funext o
          cases o <;> rfl
        rw [hfam]
        exact hmem
      · exact fun h0 ↦ hP0 (MvPolynomial.map_injective _ (algebraMap k K).injective
          (h0.trans (map_zero _).symm))
    rw [AlgebraicIndependent.option_iff, not_and, range_const] at hdepK
    have hnt := hdepK hindx
    rw [← IntermediateField.transcendental_adjoin_iff, Transcendental, not_not] at hnt
    exact hnt.isIntegral
  -- The coordinates generate the function field.
  refine ⟨x, htr, ?_⟩
  have htop : IntermediateField.adjoin (IntermediateField.adjoin K {x}) (range (coord k v)) =
      ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨A, B, -, rfl⟩ := exists_fraction z
    have hmk : ∀ P : MvPolynomial ι K, mk k v P ∈
        IntermediateField.adjoin (IntermediateField.adjoin K {x}) (range (coord k v)) := by
      intro P
      rw [← aeval_coord]
      have hP : aeval (coord k v) P ∈ Algebra.adjoin K (range (coord k v)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact ⟨P, rfl⟩
      have hle : Algebra.adjoin K (range (coord k v)) ≤
          ((IntermediateField.adjoin (IntermediateField.adjoin K {x})
            (range (coord k v))).restrictScalars K).toSubalgebra := by
        rw [IntermediateField.restrictScalars_adjoin]
        exact (Algebra.adjoin_mono subset_union_right).trans
          (IntermediateField.algebra_adjoin_le_adjoin K _)
      exact hle hP
    exact div_mem (hmk A) (hmk B)
  have hfd : FiniteDimensional (IntermediateField.adjoin K {x})
      (IntermediateField.adjoin (IntermediateField.adjoin K {x}) (range (coord k v))) :=
    IntermediateField.finiteDimensional_adjoin fun _ ⟨j, hj⟩ ↦ hj ▸ halg j
  rw [htop] at hfd
  exact (IntermediateField.topEquiv.toLinearEquiv).finiteDimensional

end LocusFunctionField

end

end GroupConfig
