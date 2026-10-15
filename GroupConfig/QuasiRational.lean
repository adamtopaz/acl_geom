/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Variety
import Mathlib.FieldTheory.Perfect

/-!
# Quasi-rational expressions

Blueprint `sources/group_configuration/03-codes.tex`, `def:qr` and the equivariance clause
of `lem:qr-dcl`, and `sources/group_configuration/04-germs.tex`, `lem:qr-agree`.

A quasi-rational expression over a field `L` in the variables `ι` with values in `K^κ` is
a datum `(e, P, Q)` of an exponent and tuples of numerators and denominators in `L[X]`;
it is defined at `u` where no denominator vanishes, and its value there is
`(P_j(u) / Q_j(u))^(1/p^e)`, the unique `p^e`-th root in the perfect field `K`
(`pRoot`, the inverse of the iterated Frobenius; in characteristic `0` the exponential
characteristic is `1` and the root is the identity).  Automorphisms over `L` commute
with evaluation (`QuasiRational.eval_comp`), and two expressions over a subfield `N`
which agree at one generic point over `N` of a locus agree at every point of the locus
where both are defined (`QuasiRational.eval_eq_of_eval_eq`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** expression domains, evaluation in a perfect ambient field,
automorphism equivariance, coefficient-field inclusion, generic-point agreement
on represented loci, and denominator-cleared composition are proved. The
composition is defined on the natural composition domain and agrees there
with the composed values; no equality of maximal expression domains is claimed.
In characteristic zero the root operator is the identity. The definable-closure
characterization is proved in `GroupConfig.DefinableClosure`; group extraction
remains a separate obligation.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

/-! ### Roots in a perfect field -/

section Root

variable (K : Type*) [Field K] [PerfectField K]

/-- The unique `p^e`-th root in a perfect field, `p` the exponential characteristic. -/
def pRoot (e : ℕ) : K ≃+* K := (iterateFrobeniusEquiv K (ringExpChar K) e).symm

variable {K}

theorem pRoot_pow (e : ℕ) (x : K) : pRoot K e x ^ ringExpChar K ^ e = x := by
  rw [← iterateFrobeniusEquiv_def]
  exact RingEquiv.apply_symm_apply _ _

theorem pRoot_eq_of_pow_eq {e : ℕ} {x y : K} (h : y ^ ringExpChar K ^ e = x) :
    pRoot K e x = y := by
  rw [← h, ← iterateFrobeniusEquiv_def]
  exact RingEquiv.symm_apply_apply _ _

theorem pRoot_pow_add (e e' : ℕ) (x : K) :
    pRoot K e x ^ ringExpChar K ^ (e + e') = x ^ ringExpChar K ^ e' := by
  rw [pow_add, pow_mul, pRoot_pow]

/-- Two roots agree iff the radicands agree after cross-raising to the other's power. -/
theorem pRoot_eq_pRoot_iff {e e' : ℕ} {x x' : K} :
    pRoot K e x = pRoot K e' x' ↔ x ^ ringExpChar K ^ e' = x' ^ ringExpChar K ^ e := by
  constructor
  · intro h
    rw [← pRoot_pow_add e e' x, h, add_comm, pRoot_pow_add]
  · intro h
    apply (iterateFrobeniusEquiv K (ringExpChar K) (e + e')).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, pRoot_pow_add, add_comm,
      pRoot_pow_add, h]

/-- Ring homomorphisms commute with roots. -/
theorem map_pRoot {F : Type*} [FunLike F K K] [RingHomClass F K K] (σ : F) (e : ℕ) (x : K) :
    σ (pRoot K e x) = pRoot K e (σ x) :=
  (pRoot_eq_of_pow_eq (by rw [← map_pow, pRoot_pow])).symm

end Root

/-! ### Quasi-rational expressions -/

/-- `def:qr`: a quasi-rational expression over `L` in the variables `ι` with values in `K^κ`:
an exponent `e` and numerators and denominators in `L[X]`; its value is
`(P_j(u) / Q_j(u))^(1/p^e)`. -/
structure QuasiRational (L : Type*) [Field L] (ι κ : Type*) where
  /-- The exponent of the root. -/
  e : ℕ
  /-- The numerators. -/
  num : κ → MvPolynomial ι L
  /-- The denominators. -/
  den : κ → MvPolynomial ι L

namespace QuasiRational

variable {L : Type*} [Field L] {ι κ : Type*} {K : Type*} [Field K] [PerfectField K]
  [Algebra L K]

/-- The expression is *defined at* `u` if no denominator vanishes there. -/
def IsDefinedAt (f : QuasiRational L ι κ) (u : ι → K) : Prop := ∀ j, aeval u (f.den j) ≠ 0

/-- The value `(P_j(u) / Q_j(u))^(1/p^e)` of the expression at `u`. -/
def eval (f : QuasiRational L ι κ) (u : ι → K) : κ → K :=
  fun j ↦ pRoot K f.e (aeval u (f.num j) / aeval u (f.den j))

theorem eval_apply (f : QuasiRational L ι κ) (u : ι → K) (j : κ) :
    f.eval u j = pRoot K f.e (aeval u (f.num j) / aeval u (f.den j)) := rfl

omit [PerfectField K] in
/-- Evaluating a polynomial over `L` commutes with automorphisms over `L`. -/
theorem aeval_comp_algEquiv (σ : K ≃ₐ[L] K) (u : ι → K) (P : MvPolynomial ι L) :
    aeval (⇑σ ∘ u) P = σ (aeval u P) := by
  change aeval (fun i ↦ σ.toAlgHom (u i)) P = σ.toAlgHom (aeval u P)
  rw [← comp_aeval_apply]

omit [PerfectField K] in
theorem isDefinedAt_comp_iff (f : QuasiRational L ι κ) (σ : K ≃ₐ[L] K) (u : ι → K) :
    f.IsDefinedAt (⇑σ ∘ u) ↔ f.IsDefinedAt u := by
  unfold IsDefinedAt
  simp only [aeval_comp_algEquiv, ne_eq, map_eq_zero_iff _ σ.injective]

/-- `lem:qr-dcl`, equivariance: automorphisms over `L` commute with evaluation. -/
theorem eval_comp (f : QuasiRational L ι κ) (σ : K ≃ₐ[L] K) (u : ι → K) :
    f.eval (⇑σ ∘ u) = ⇑σ ∘ f.eval u := by
  funext j
  simp only [eval, Function.comp_apply, aeval_comp_algEquiv, ← map_div₀, map_pRoot]

end QuasiRational

/-! ### Change of coefficient field -/

section Map

variable {L : Type*} [Field L] {ι κ : Type*} {K : Type*} [Field K] [PerfectField K]
  [Algebra L K]

/-- Transport an expression along a ring homomorphism of coefficient fields. -/
def QuasiRational.map {L' : Type*} [Field L'] (φ : L →+* L') (f : QuasiRational L ι κ) :
    QuasiRational L' ι κ :=
  ⟨f.e, fun j ↦ MvPolynomial.map φ (f.num j), fun j ↦ MvPolynomial.map φ (f.den j)⟩

variable {k : Type*} [Field k] [Algebra k K]

omit [PerfectField K] in
theorem aeval_map_inclusion {M M₁ : IntermediateField k K} (h : M ≤ M₁) (u : ι → K)
    (P : MvPolynomial ι (↥M)) :
    aeval u (MvPolynomial.map (IntermediateField.inclusion h).toRingHom P) = aeval u P := by
  rw [aeval_def, aeval_def, eval₂_map]
  congr 1

omit [PerfectField K] in
theorem QuasiRational.isDefinedAt_map_iff {M M₁ : IntermediateField k K} (h : M ≤ M₁)
    (f : QuasiRational (↥M) ι κ) (u : ι → K) :
    (f.map (IntermediateField.inclusion h).toRingHom).IsDefinedAt u ↔ f.IsDefinedAt u := by
  unfold QuasiRational.IsDefinedAt
  simp only [QuasiRational.map]
  exact forall_congr' fun j ↦ by rw [aeval_map_inclusion]

theorem QuasiRational.eval_map {M M₁ : IntermediateField k K} (h : M ≤ M₁)
    (f : QuasiRational (↥M) ι κ) (u : ι → K) :
    (f.map (IntermediateField.inclusion h).toRingHom).eval u = f.eval u := by
  funext j
  simp only [QuasiRational.eval, QuasiRational.map, aeval_map_inclusion]

end Map

/-! ### Agreement at a generic point -/

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField K] {ι κ : Type*}

omit [PerfectField K] in
/-- Polynomials over a subfield of `N`, viewed in `K[X]`, are polynomials over `N`. -/
theorem map_algebraMap_mem_range {M N : IntermediateField k K} (h : M ≤ N)
    (P : MvPolynomial ι (↥M)) :
    MvPolynomial.map (algebraMap (↥M) K) P ∈ (MvPolynomial.map (algebraMap (↥N) K)).range := by
  refine RingHom.mem_range.2 ⟨MvPolynomial.map (IntermediateField.inclusion h).toRingHom P, ?_⟩
  rw [MvPolynomial.map_map]
  congr 1

/-- `lem:qr-agree`: two quasi-rational expressions over subfields of `N` which agree at a
generic point over `N` of the locus of `a` agree at every point of the locus where both are
defined. -/
theorem QuasiRational.eval_eq_of_eval_eq {M M' N : IntermediateField k K} (hMN : M ≤ N)
    (hM'N : M' ≤ N) {a y' y : ι → K} (hy' : IsGenericOver N a y') (hy : InLocus (k := k) a y)
    {f : QuasiRational (↥M) ι κ} {f' : QuasiRational (↥M') ι κ}
    (hfy' : f.IsDefinedAt y') (hf'y' : f'.IsDefinedAt y') (hfy : f.IsDefinedAt y)
    (hf'y : f'.IsDefinedAt y) (heq : f.eval y' = f'.eval y') : f.eval y = f'.eval y := by
  funext j
  have hj := congrFun heq j
  simp only [QuasiRational.eval_apply, pRoot_eq_pRoot_iff, div_pow] at hj ⊢
  rw [div_eq_div_iff (pow_ne_zero _ (hfy' j)) (pow_ne_zero _ (hf'y' j))] at hj
  rw [div_eq_div_iff (pow_ne_zero _ (hfy j)) (pow_ne_zero _ (hf'y j))]
  -- The cross-multiplied difference is a polynomial over `N` vanishing at `y'`, hence in the
  -- locus ideal, hence vanishing at `y`.
  set A : MvPolynomial ι K :=
    MvPolynomial.map (algebraMap (↥M) K) (f.num j) ^ ringExpChar K ^ f'.e *
        MvPolynomial.map (algebraMap (↥M') K) (f'.den j) ^ ringExpChar K ^ f.e -
      MvPolynomial.map (algebraMap (↥M') K) (f'.num j) ^ ringExpChar K ^ f.e *
        MvPolynomial.map (algebraMap (↥M) K) (f.den j) ^ ringExpChar K ^ f'.e with hA
  have hAmem : A ∈ (MvPolynomial.map (algebraMap (↥N) K)).range :=
    sub_mem (mul_mem (pow_mem (map_algebraMap_mem_range hMN _) _)
        (pow_mem (map_algebraMap_mem_range hM'N _) _))
      (mul_mem (pow_mem (map_algebraMap_mem_range hM'N _) _)
        (pow_mem (map_algebraMap_mem_range hMN _) _))
  obtain ⟨A₀, hA₀⟩ := RingHom.mem_range.1 hAmem
  have hAy' : aeval y' A = 0 := by
    simp only [hA, map_sub, map_mul, map_pow, aeval_map_algebraMap]
    rw [hj, sub_self]
  have hA₀I : MvPolynomial.map (algebraMap (↥N) K) A₀ ∈ locusIdeal k a := by
    rw [← hy'.locusIdeal_eq]
    refine map_mem_locusIdeal (↥N) ((mem_idealOf_iff (↥N)).2 ?_)
    rw [← aeval_map_algebraMap (A := K), hA₀]
    exact hAy'
  have hAy := (mem_idealOf_iff K).1 (hy hA₀I)
  rw [hA₀] at hAy
  simp only [hA, map_sub, map_mul, map_pow, aeval_map_algebraMap] at hAy
  exact sub_eq_zero.1 hAy

/-! ### Composition -/

section Comp

variable {L : Type*} [Field L] {ι κ μ : Type*} {K : Type*} [Field K] [PerfectField K]
  [Algebra L K]

/-- The exponential characteristic of a subfield is that of the ambient field. -/
theorem expChar_of_algebra (L K : Type*) [Field L] [Field K] [Algebra L K] :
    ExpChar L (ringExpChar K) :=
  RingHom.expChar (algebraMap L K) (algebraMap L K).injective _

/-- Roots compose. -/
theorem pRoot_add (e e' : ℕ) (x : K) : pRoot K (e + e') x = pRoot K e (pRoot K e' x) :=
  pRoot_eq_of_pow_eq (by rw [pow_add, pow_mul, pRoot_pow, pRoot_pow])

/-- Taking a root of the value of a Frobenius-twisted polynomial is evaluating the polynomial
at the roots. -/
theorem pRoot_aeval_twist [ExpChar L (ringExpChar K)] (e : ℕ) (R : κ → K)
    (N : MvPolynomial κ L) :
    pRoot K e (aeval R (MvPolynomial.map (iterateFrobenius L (ringExpChar K) e) N)) =
      aeval (fun j ↦ pRoot K e (R j)) N := by
  rw [aeval_def, aeval_def, eval₂_map]
  change (pRoot K e).toRingHom (eval₂ _ R N) = _
  rw [eval₂_comp_left]
  congr 1
  ext c
  change pRoot K e (algebraMap L K (iterateFrobenius L (ringExpChar K) e c)) = algebraMap L K c
  rw [RingHom.map_iterateFrobenius]
  exact pRoot_eq_of_pow_eq (iterateFrobenius_def _ _ _).symm

variable [Fintype κ]

omit [PerfectField K] [Algebra L K] in
/-- Substituting the fractions `P j / Q j` into `N` and clearing denominators by `(∏ Q j)^d`. -/
def substFrac (N : MvPolynomial κ L) (P Q : κ → MvPolynomial ι L) (d : ℕ) : MvPolynomial ι L :=
  ∑ m ∈ N.support, C (N.coeff m) * ∏ j, (P j ^ m j * Q j ^ (d - m j))

omit [PerfectField K] in
theorem aeval_substFrac {N : MvPolynomial κ L} {d : ℕ} (hd : N.totalDegree ≤ d)
    (P Q : κ → MvPolynomial ι L) {u : ι → K} (hQ : ∀ j, aeval u (Q j) ≠ 0) :
    aeval u (substFrac N P Q d) =
      aeval (fun j ↦ aeval u (P j) / aeval u (Q j)) N * ∏ j, aeval u (Q j) ^ d := by
  classical
  have hm : ∀ m ∈ N.support, ∀ j, m j ≤ d := by
    intro m hmN j
    refine le_trans ?_ ((le_totalDegree hmN).trans hd)
    by_cases hj : j ∈ m.support
    · exact Finset.single_le_sum (f := fun i ↦ m i) (fun _ _ ↦ Nat.zero_le _) hj
    · simp [Finsupp.notMem_support_iff.1 hj]
  rw [aeval_def (fun j ↦ aeval u (P j) / aeval u (Q j)), eval₂_eq, Finset.sum_mul]
  unfold substFrac
  simp only [map_sum, map_mul, map_prod, map_pow, aeval_C]
  refine Finset.sum_congr rfl fun m hmN ↦ ?_
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support)
    (fun j _ hj ↦ by simp [Finsupp.notMem_support_iff.1 hj]), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hdm : d = m j + (d - m j) := (Nat.add_sub_cancel' (hm m hmN j)).symm
  rw [hdm, Nat.add_sub_cancel_left, pow_add, div_pow]
  field_simp
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ (hQ j))]

variable (p : ℕ) [ExpChar L p]

/-- `lem:qr-dcl`: the composite of quasi-rational expressions, `g ∘ f`, with exponent
`e_g + e_f`: the coefficients of `g` are twisted by the `p^(e_f)`-th power Frobenius and the
fractions of `f` are substituted with denominators cleared. -/
def QuasiRational.comp (g : QuasiRational L κ μ) (f : QuasiRational L ι κ) :
    QuasiRational L ι μ where
  e := g.e + f.e
  num m := substFrac (MvPolynomial.map (iterateFrobenius L p f.e) (g.num m)) f.num f.den
    (max (MvPolynomial.map (iterateFrobenius L p f.e) (g.num m)).totalDegree
      (MvPolynomial.map (iterateFrobenius L p f.e) (g.den m)).totalDegree)
  den m := substFrac (MvPolynomial.map (iterateFrobenius L p f.e) (g.den m)) f.num f.den
    (max (MvPolynomial.map (iterateFrobenius L p f.e) (g.num m)).totalDegree
      (MvPolynomial.map (iterateFrobenius L p f.e) (g.den m)).totalDegree)

end Comp

section CompEval

variable {L : Type*} [Field L] {ι κ μ : Type*} {K : Type*} [Field K] [PerfectField K]
  [Algebra L K] [Fintype κ] [ExpChar L (ringExpChar K)]

/-- The composite is defined where the inner expression is defined and the outer expression
is defined at its value. -/
theorem QuasiRational.isDefinedAt_comp (g : QuasiRational L κ μ) (f : QuasiRational L ι κ)
    {u : ι → K}
    (hf : f.IsDefinedAt u) (hg : g.IsDefinedAt (f.eval u)) :
    (g.comp (ringExpChar K) f).IsDefinedAt u := by
  intro m
  simp only [QuasiRational.comp]
  rw [aeval_substFrac (le_max_right _ _) _ _ hf]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun j _ ↦ pow_ne_zero _ (hf j))
  intro h0
  apply hg m
  have hval := pRoot_aeval_twist (K := K) f.e (fun j ↦ aeval u (f.num j) / aeval u (f.den j))
    (g.den m)
  rw [h0, map_zero] at hval
  exact hval.symm

/-- `lem:qr-dcl`: the composite evaluates to the composite of the values. -/
theorem QuasiRational.comp_eval (g : QuasiRational L κ μ) (f : QuasiRational L ι κ) {u : ι → K}
    (hf : f.IsDefinedAt u) : (g.comp (ringExpChar K) f).eval u = g.eval (f.eval u) := by
  funext m
  simp only [QuasiRational.eval_apply, QuasiRational.comp]
  rw [aeval_substFrac (le_max_left _ _) _ _ hf, aeval_substFrac (le_max_right _ _) _ _ hf,
    mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ pow_ne_zero _ (hf j)), pRoot_add,
    map_div₀, pRoot_aeval_twist, pRoot_aeval_twist]
  rfl

end CompEval

end

end GroupConfig
