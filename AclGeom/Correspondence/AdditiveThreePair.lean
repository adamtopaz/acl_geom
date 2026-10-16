/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.Algebra.MvPolynomial.Nilpotent
import AclGeom.Correspondence.Additive
import AclGeom.Closure.Ambient
import AclGeom.Closure.FreshExtension
import AclGeom.Geometry.Points
import AclGeom.Geometry.Representatives
import AclGeom.Transfer.Transcendence

/-!
# The additive correspondence theorem for three pairs

Blueprint Theorem `addcorr`: for algebraically independent `x₁, x₂, x₃` over an algebraically
closed `k ⊆ Ω` with `[xᵢ] = [yᵢ]`, `[x₁ + x₂] = [y₁ + y₂]` and `[x₁ + x₃] = [y₁ + y₃]`, there are
nonzero additive polynomials `P, Q` and constants `dᵢ ∈ k` with `Q(yᵢ) = P(xᵢ) + dᵢ` for all
three pairs, and `d₁ + d₂`, `d₁ + d₃` are the translation constants of the two sums (`addcorr`).

The two-pair core `AddCorrSetup.exists_delta_gen_data` gives, for each of the pairs `(1, 2)` and
`(1, 3)`, a prime generator `G = P(X₀) + Q(X₁)` taking constant values at both of its pairs.  The
two generators are compared on the first curve: its vanishing ideal is principal
(`exists_prime_span_idealOf`), and `G - e₁` is a translate of the prime `G`
(`prime_sub_C_of_split`), hence an associate of the curve's generator.  The two translated
generators therefore differ by a nonzero constant, so the first generator is constant on the
third pair too.  Additivity in every algebra (`IsAdditive.aeval_add`) gives the translation
constants of the sums.

The two-pair core needs elements fresh over the pairs; the blueprint has no such hypothesis.  The
theorem passes to the algebraically closed extension `FreshAmbient Ω` (`Closure.FreshExtension`)
and pulls the `k`-polynomial equations back along the injective embedding.  The independence of
`(y₁, y₂, y₃)` assumed by the blueprint follows from `[xᵢ] = [yᵢ]` and is not used.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5).
-/

namespace AclGeom

open ClosedIF MvPolynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Over an infinite field, a pointwise additive polynomial is additive in every commutative
algebra. -/
theorem IsAdditive.aeval_add [Infinite k] {P : Polynomial k} (hP : IsAdditive P)
    {A : Type*} [CommRing A] [Algebra k A] (x y : A) :
    Polynomial.aeval (x + y) P = Polynomial.aeval x P + Polynomial.aeval y P := by
  have h : (Polynomial.aeval (X 0 + X 1) P : MvPolynomial (Fin 2) k) =
      Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) P := by
    refine MvPolynomial.funext fun v ↦ ?_
    change MvPolynomial.aeval v _ = MvPolynomial.aeval v _
    simp only [map_add, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    exact hP (v 0) (v 1)
  have h' := congrArg (MvPolynomial.aeval ![x, y]) h
  simpa only [map_add, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h'

/-- A prime split generator `G = P(X₀) + Q(X₁)` stays prime after subtracting a constant: over an
algebraically closed base, `G - e` is the translate of `G` by a root of `P - e`. -/
private theorem prime_sub_C_of_split [IsAlgClosed k] {G : MvPolynomial (Fin 2) k}
    {P Q : Polynomial k} (hGp : Prime G)
    (hG : G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q)
    (hP0 : P.coeff 0 = 0) (hP : P ≠ 0) (hPa : IsAdditive P) (e : k) :
    Prime (G - C e) := by
  have hdeg : 0 < P.degree := by
    by_contra h
    exact hP ((Polynomial.eq_C_of_degree_le_zero (not_lt.1 h)).trans (by rw [hP0, map_zero]))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (P - Polynomial.C e)
    (by rw [Polynomial.degree_sub_C hdeg]; exact hdeg.ne')
  have hPa' : P.eval a = e := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] at ha
  have hneg : P.eval (-a) = -e := by
    have h := hPa a (-a)
    rw [add_neg_cancel, hPa.eval_zero, hPa'] at h
    linear_combination -h
  have htrans : translate ![-a, 0] G = G - C e := by
    rw [hG, map_add, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
      translate_X, translate_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, add_zero]
    rw [hPa.aeval_add, ← MvPolynomial.algebraMap_eq,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hneg, map_neg,
      MvPolynomial.algebraMap_eq]
    ring
  let T : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
    AlgEquiv.ofAlgHom (translate ![-a, 0]) (translate (-![-a, 0]))
      (AlgHom.ext fun g ↦ by
        rw [AlgHom.comp_apply, AlgHom.id_apply]
        exact translate_translate_neg ![-a, 0] g)
      (AlgHom.ext fun g ↦ by
        rw [AlgHom.comp_apply, AlgHom.id_apply]
        exact translate_neg_translate ![-a, 0] g)
  rw [← htrans]
  exact (MulEquiv.prime_iff T).2 hGp

/-- The three-pair conclusion in sum form, in an ambient field with fresh elements. -/
private theorem addcorr_of_four_le_trdeg [IsAlgClosed k] [IsAlgClosed Ω]
    (htr : (4 : Cardinal) ≤ Algebra.trdeg k Ω) {x₁ x₂ x₃ y₁ y₂ y₃ : Ω}
    (hx : AlgebraicIndependent k ![x₁, x₂, x₃])
    (h₁ : racl k {x₁} = racl k {y₁}) (h₂ : racl k {x₂} = racl k {y₂})
    (h₃ : racl k {x₃} = racl k {y₃})
    (h₁₂ : racl k {x₁ + x₂} = racl k {y₁ + y₂}) (h₁₃ : racl k {x₁ + x₃} = racl k {y₁ + y₃}) :
    ∃ P Q : Polynomial k, IsAdditive P ∧ IsAdditive Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      ∃ e₁ e₂ e₃ : k,
        Polynomial.aeval x₁ P + Polynomial.aeval y₁ Q = algebraMap k Ω e₁ ∧
        Polynomial.aeval x₂ P + Polynomial.aeval y₂ Q = algebraMap k Ω e₂ ∧
        Polynomial.aeval x₃ P + Polynomial.aeval y₃ Q = algebraMap k Ω e₃ := by
  classical
  have mem : ∀ {u v : Ω}, racl k {u} = racl k {v} → v ∈ racl k {u} := fun h ↦ by
    rw [h]
    exact subset_racl k _ (Set.mem_singleton _)
  have fresh : ∀ S : Finset Ω, S.card ≤ 3 → ∃ z : Ω, z ∉ racl k (S : Set Ω) :=
    exists_notMem_racl_of_card_lt_trdeg (n := 3) (lt_of_lt_of_le (by norm_num) htr)
  -- The two pair setups `(1, 2)` and `(1, 3)`.
  let S₂ : AddCorrSetup k Ω :=
    { x₁ := x₁, y₁ := y₁, x₂ := x₂, y₂ := y₂
      indep := AlgebraicIndependent.pair_of_triple hx (i := 0) (j := 1) (by decide)
      y₁_mem := mem h₁, x₁_mem := mem h₁.symm, y₂_mem := mem h₂, x₂_mem := mem h₂.symm
      sum_mem := mem h₁₂, sum_mem' := mem h₁₂.symm }
  let S₃ : AddCorrSetup k Ω :=
    { x₁ := x₁, y₁ := y₁, x₂ := x₃, y₂ := y₃
      indep := AlgebraicIndependent.pair_zero_two hx
      y₁_mem := mem h₁, x₁_mem := mem h₁.symm, y₂_mem := mem h₃, x₂_mem := mem h₃.symm
      sum_mem := mem h₁₃, sum_mem' := mem h₁₃.symm }
  obtain ⟨s₂, hs₂⟩ := fresh {x₁, x₂} (Finset.card_le_two.trans (by norm_num))
  obtain ⟨t₂, ht₂⟩ := fresh {x₁, x₂, s₂} Finset.card_le_three
  obtain ⟨s₃, hs₃⟩ := fresh {x₁, x₃} (Finset.card_le_two.trans (by norm_num))
  obtain ⟨t₃, ht₃⟩ := fresh {x₁, x₃, s₃} Finset.card_le_three
  have hs₂' : s₂ ∉ racl k ({x₁, x₂} : Set Ω) := by simpa using hs₂
  have ht₂' : t₂ ∉ racl k ({x₁, x₂, s₂} : Set Ω) := by simpa using ht₂
  have hs₃' : s₃ ∉ racl k ({x₁, x₃} : Set Ω) := by simpa using hs₃
  have ht₃' : t₃ ∉ racl k ({x₁, x₃, s₃} : Set Ω) := by simpa using ht₃
  obtain ⟨G, P, Q, hGp, hG, hP0, -, hP, hQ, hPa, hQa, e₁, e₂, he₁, he₂⟩ :=
    S₂.exists_delta_gen_data (s := s₂) (s' := t₂) hs₂' ht₂'
  obtain ⟨G', P', Q', hGp', hG', hP0', -, hP', -, hPa', -, e₁', e₃, he₁', he₃⟩ :=
    S₃.exists_delta_gen_data (s := s₃) (s' := t₃) hs₃' ht₃'
  -- The vanishing ideal of the first curve is principal and prime.
  have hx₁ : Transcendental k x₁ := hx.transcendental 0
  obtain ⟨F, hFp, hF⟩ := exists_prime_span_idealOf k hx₁ (mem h₁)
  have assoc : ∀ (H : MvPolynomial (Fin 2) k) (R S : Polynomial k) (e : k), Prime H →
      H = Polynomial.aeval (X 0) R + Polynomial.aeval (X 1) S → R.coeff 0 = 0 → R ≠ 0 →
      IsAdditive R → aeval ![x₁, y₁] H = algebraMap k Ω e → Associated F (H - C e) :=
    fun H R S e hHp hH hR0 hR hRa he ↦ by
      refine Prime.associated_of_dvd hFp (prime_sub_C_of_split hHp hH hR0 hR hRa e) ?_
      have hmem : H - C e ∈ idealOf k ![x₁, y₁] := by
        rw [mem_idealOf_iff, map_sub, he, aeval_C, sub_self]
      rw [hF, Ideal.mem_span_singleton] at hmem
      exact hmem
  obtain ⟨u, hu⟩ := (assoc G P Q e₁ hGp hG hP0 hP hPa he₁).symm.trans
    (assoc G' P' Q' e₁' hGp' hG' hP0' hP' hPa' he₁')
  obtain ⟨r, hr, hur⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  -- Evaluate the comparison at the third pair.
  have h3 := congrArg (aeval ![x₃, y₃]) hu
  rw [hur, map_mul, map_sub, map_sub, aeval_C, aeval_C, aeval_C,
    show aeval ![x₃, y₃] G' = algebraMap k Ω e₃ from he₃] at h3
  have hr0 : algebraMap k Ω r ≠ 0 := (map_ne_zero _).2 hr.ne_zero
  have he₃' : aeval ![x₃, y₃] G = algebraMap k Ω (e₁ + (e₃ - e₁') / r) := by
    rw [map_add, map_div₀, map_sub]
    field_simp
    linear_combination h3
  have split : ∀ {v w : Ω} {e : k}, aeval ![v, w] G = algebraMap k Ω e →
      Polynomial.aeval v P + Polynomial.aeval w Q = algebraMap k Ω e := fun h ↦ by
    rw [hG, map_add, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
      aeval_X, aeval_X] at h
    simpa using h
  exact ⟨P, Q, hPa, hQa, hP, hQ, e₁, e₂, _, split he₁, split he₂, split he₃'⟩

/-- **The additive correspondence theorem** (blueprint Theorem `addcorr`): for algebraically
independent `x₁, x₂, x₃` over an algebraically closed `k ⊆ Ω`, with `[xᵢ] = [yᵢ]`,
`[x₁ + x₂] = [y₁ + y₂]` and `[x₁ + x₃] = [y₁ + y₃]`, there are nonzero additive polynomials
`P, Q` and constants `dᵢ ∈ k` with `Q(yᵢ) = P(xᵢ) + dᵢ` for `i = 1, 2, 3`.  Moreover `d₁ + d₂`
and `d₁ + d₃` are the translation constants of the two sum correspondences. -/
theorem addcorr [IsAlgClosed k] [IsAlgClosed Ω] {x₁ x₂ x₃ y₁ y₂ y₃ : Ω}
    (hx : AlgebraicIndependent k ![x₁, x₂, x₃])
    (h₁ : point k x₁ = point k y₁) (h₂ : point k x₂ = point k y₂)
    (h₃ : point k x₃ = point k y₃)
    (h₁₂ : point k (x₁ + x₂) = point k (y₁ + y₂))
    (h₁₃ : point k (x₁ + x₃) = point k (y₁ + y₃)) :
    ∃ P Q : Polynomial k, IsAdditive P ∧ IsAdditive Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      ∃ d₁ d₂ d₃ : k,
        Polynomial.aeval y₁ Q = Polynomial.aeval x₁ P + algebraMap k Ω d₁ ∧
        Polynomial.aeval y₂ Q = Polynomial.aeval x₂ P + algebraMap k Ω d₂ ∧
        Polynomial.aeval y₃ Q = Polynomial.aeval x₃ P + algebraMap k Ω d₃ ∧
        Polynomial.aeval (y₁ + y₂) Q =
          Polynomial.aeval (x₁ + x₂) P + algebraMap k Ω (d₁ + d₂) ∧
        Polynomial.aeval (y₁ + y₃) Q =
          Polynomial.aeval (x₁ + x₃) P + algebraMap k Ω (d₁ + d₃) := by
  classical
  -- Pass to an algebraically closed extension with four fresh elements.
  let ι : Ω →ₐ[k] FreshAmbient Ω := IsScalarTower.toAlgHom k Ω (FreshAmbient Ω)
  have hι : Function.Injective ι := ι.toRingHom.injective
  have htr := four_le_trdeg_freshAmbient k Ω
  -- Transport of the hypotheses.
  have hpt : ∀ {u v : Ω}, point k u = point k v → racl k {ι u} = racl k {ι v} :=
    fun {u v} h ↦ by
      simpa [Set.image_singleton] using
        algHom_racl_image_eq_of_racl_eq ι (congrArg Subtype.val h : racl k {u} = racl k {v})
  have hsum : ∀ {u v w z : Ω}, point k (u + v) = point k (w + z) →
      racl k {ι u + ι v} = racl k {ι w + ι z} := fun {u v w z} h ↦ by
    simpa only [map_add] using hpt h
  obtain ⟨P, Q, hPa, hQa, hP, hQ, e₁, e₂, e₃, he₁, he₂, he₃⟩ :=
    addcorr_of_four_le_trdeg htr (x₁ := ι x₁) (x₂ := ι x₂) (x₃ := ι x₃)
      (by
        convert hx.map' hι using 1
        funext i
        fin_cases i <;> rfl)
      (hpt h₁) (hpt h₂) (hpt h₃) (hsum h₁₂) (hsum h₁₃)
  -- Pull the polynomial equations back to `Ω`.
  have pull : ∀ {u v : Ω} {e : k},
      Polynomial.aeval (ι u) P + Polynomial.aeval (ι v) Q = algebraMap k (FreshAmbient Ω) e →
      Polynomial.aeval u P + Polynomial.aeval v Q = algebraMap k Ω e := fun h ↦ hι (by
    rw [map_add, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
      AlgHom.commutes]
    exact h)
  have he₁' := pull he₁
  have he₂' := pull he₂
  have he₃' := pull he₃
  refine ⟨-P, Q, fun a b ↦ ?_, hQa, neg_ne_zero.2 hP, hQ, e₁, e₂, e₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.eval_neg, Polynomial.eval_neg, Polynomial.eval_neg, hPa a b, neg_add]
  · rw [map_neg]
    linear_combination he₁'
  · rw [map_neg]
    linear_combination he₂'
  · rw [map_neg]
    linear_combination he₃'
  · rw [hQa.aeval_add, map_neg, hPa.aeval_add, map_add]
    linear_combination he₁' + he₂'
  · rw [hQa.aeval_add, map_neg, hPa.aeval_add, map_add]
    linear_combination he₁' + he₃'

end AclGeom
