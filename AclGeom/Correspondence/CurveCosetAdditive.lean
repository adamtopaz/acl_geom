/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AdditiveThreePair
import AclGeom.Correspondence.AdditiveSubgroup

/-!
# Generic sums of plane finite correspondences are cosets

Blueprint Lemma `curve-coset` in the additive plane `Gₐ² = (k², +)`, the group in which the
source applies it (the proof of Theorem `addcorr`), restricted to finite correspondences: curves
whose two coordinate projections are nonconstant.

Let `(x₁, y₁)` and `(x₂, y₂)` be generic points of two such curves over an algebraically closed
field `k`, with `x₁, x₂` independent, and suppose their sum `(x₁ + x₂, y₁ + y₂)` is again the
generic point of a finite correspondence. Then the three curves are cosets of one closed,
connected, one-dimensional additive subgroup `H ⊆ k²`
(`curveCoset_additive_of_finiteCorrespondence`). The conclusion gives `H` in the input form of the
subgroup classification `addSubgroup_classification_of_connected`, together with the coset
equalities of the three curve ideals and of their point sets.

The two-pair additive core (`AddCorrSetup.exists_delta_gen_data`) supplies a prime generator
`G = P(X₀) + Q(X₁)` with additive `P, Q`, constant on both correspondences. Its fresh-element
hypotheses are met in the auxiliary ambient `FreshAmbient Ω`, and the polynomial data over `k`
pull back. Each curve ideal is principal and prime (`exists_prime_span_idealOf`); it contains the
translate of `G` through a root of `P` at the constant, so the two generators are associates.
`H` is the zero set of `G`: the Nullstellensatz identifies its ideal and primality gives
connectedness. A translate of `G` is a nonzerodivisor in a maximal ideal of height two, which gives
dimension one.

Curves with a constant coordinate (vertical and horizontal lines) are not covered, nor is the
general statement for an arbitrary connected algebraic group.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** Lemma `curve-coset` is proved for finite-correspondence curves in `Gₐ²` over
algebraically closed fields; the statement for arbitrary connected groups remains open (#5).
-/

namespace AclGeom

open ClosedIF MvPolynomial Pointwise

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **Generic sums of plane finite correspondences are cosets** (blueprint Lemma `curve-coset`
for `Gₐ²`, restricted to curves with nonconstant projections). If the generic points `(x₁, y₁)`
and `(x₂, y₂)` of two finite correspondences over an algebraically closed field have
independent first coordinates and their sum is again the generic point of a finite
correspondence, then the three curves are cosets `g₁ + H`, `g₂ + H` and `g₁ + g₂ + H` of one
closed, connected, one-dimensional additive subgroup `H ⊆ k²` with nonconstant projections, as
ideals and as point sets. -/
theorem curveCoset_additive_of_finiteCorrespondence [IsAlgClosed k] [IsAlgClosed Ω]
    {x₁ x₂ y₁ y₂ : Ω} (hx : AlgebraicIndependent k ![x₁, x₂])
    (h₁ : point k x₁ = point k y₁) (h₂ : point k x₂ = point k y₂)
    (h₁₂ : point k (x₁ + x₂) = point k (y₁ + y₂)) :
    ∃ (H : AddSubgroup (Fin 2 → k)) (F : MvPolynomial (Fin 2) k) (g₁ g₂ : Fin 2 → k),
      Prime F ∧ vanishingIdeal k (H : Set (Fin 2 → k)) = Ideal.span {F} ∧
      zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H ∧
      ConnectedSpace
        (PrimeSpectrum (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k)))) ∧
      ringKrullDim (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))) = 1 ∧
      (∃ u ∈ H, ∃ v ∈ H, u 0 ≠ v 0) ∧ (∃ u ∈ H, ∃ v ∈ H, u 1 ≠ v 1) ∧
      idealOf k ![x₁, y₁] = Ideal.span {translate (-g₁) F} ∧
      idealOf k ![x₂, y₂] = Ideal.span {translate (-g₂) F} ∧
      idealOf k ![x₁ + x₂, y₁ + y₂] = Ideal.span {translate (-(g₁ + g₂)) F} ∧
      zeroLocus k (idealOf k ![x₁, y₁]) = g₁ +ᵥ (H : Set (Fin 2 → k)) ∧
      zeroLocus k (idealOf k ![x₂, y₂]) = g₂ +ᵥ (H : Set (Fin 2 → k)) ∧
      zeroLocus k (idealOf k ![x₁ + x₂, y₁ + y₂]) = (g₁ + g₂) +ᵥ (H : Set (Fin 2 → k)) := by
  classical
  -- The prime split generator, through an ambient field with fresh elements.
  obtain ⟨G, P, Q, hG, hGPQ, hP0, hQ0, hP, hQ, hPa, hQa, d₁, d₂, hd₁, hd₂⟩ :
      ∃ (G : MvPolynomial (Fin 2) k) (P Q : Polynomial k), Prime G ∧
        G = Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) Q ∧
        P.coeff 0 = 0 ∧ Q.coeff 0 = 0 ∧ P ≠ 0 ∧ Q ≠ 0 ∧ IsAdditive P ∧ IsAdditive Q ∧
        ∃ d₁ d₂ : k, aeval ![x₁, y₁] G = algebraMap k Ω d₁ ∧
          aeval ![x₂, y₂] G = algebraMap k Ω d₂ := by
    let ι : Ω →ₐ[k] FreshAmbient Ω := IsScalarTower.toAlgHom k Ω (FreshAmbient Ω)
    have hι : Function.Injective ι := ι.toRingHom.injective
    have htr := four_le_trdeg_freshAmbient k Ω
    have hpt : ∀ {u v : Ω}, point k u = point k v → racl k {ι u} = racl k {ι v} :=
      fun {u v} h ↦ by
        simpa [Set.image_singleton] using
          algHom_racl_image_eq_of_racl_eq ι (congrArg Subtype.val h : racl k {u} = racl k {v})
    have mem : ∀ {u v : FreshAmbient Ω}, racl k {u} = racl k {v} → v ∈ racl k {u} :=
      fun h ↦ by
        rw [h]
        exact subset_racl k _ (Set.mem_singleton _)
    have h₁' := hpt h₁
    have h₂' := hpt h₂
    have h₁₂' : racl k {ι x₁ + ι x₂} = racl k {ι y₁ + ι y₂} := by
      simpa only [map_add] using hpt h₁₂
    let S : AddCorrSetup k (FreshAmbient Ω) :=
      { x₁ := ι x₁, y₁ := ι y₁, x₂ := ι x₂, y₂ := ι y₂
        indep := by
          convert hx.map' hι using 1
          funext i
          fin_cases i <;> rfl
        y₁_mem := mem h₁', x₁_mem := mem h₁'.symm, y₂_mem := mem h₂', x₂_mem := mem h₂'.symm
        sum_mem := mem h₁₂', sum_mem' := mem h₁₂'.symm }
    have fresh : ∀ T : Finset (FreshAmbient Ω), T.card ≤ 3 →
        ∃ z : FreshAmbient Ω, z ∉ racl k (T : Set (FreshAmbient Ω)) :=
      exists_notMem_racl_of_card_lt_trdeg (n := 3) (lt_of_lt_of_le (by norm_num) htr)
    obtain ⟨s, hs⟩ := fresh {ι x₁, ι x₂} (Finset.card_le_two.trans (by decide))
    obtain ⟨s', hs'⟩ := fresh {ι x₁, ι x₂, s} Finset.card_le_three
    have hs₀ : s ∉ racl k ({ι x₁, ι x₂} : Set (FreshAmbient Ω)) := by simpa using hs
    have hs₁ : s' ∉ racl k ({ι x₁, ι x₂, s} : Set (FreshAmbient Ω)) := by simpa using hs'
    obtain ⟨G, P, Q, hG, hGPQ, hP0, hQ0, hP, hQ, hPa, hQa, d₁, d₂, hd₁, hd₂⟩ :=
      S.exists_delta_gen_data (s := s) (s' := s') hs₀ hs₁
    have pull : ∀ {u v : Ω} {d : k},
        aeval ![ι u, ι v] G = algebraMap k (FreshAmbient Ω) d →
        aeval ![u, v] G = algebraMap k Ω d := fun {u v d} h ↦ hι (by
      have e : (fun i ↦ ι (![u, v] i)) = ![ι u, ι v] := by
        funext i
        fin_cases i <;> rfl
      rw [AlgHom.commutes, MvPolynomial.comp_aeval_apply, e]
      exact h)
    exact ⟨G, P, Q, hG, hGPQ, hP0, hQ0, hP, hQ, hPa, hQa, d₁, d₂,
      pull (u := x₁) (v := y₁) hd₁, pull (u := x₂) (v := y₂) hd₂⟩
  -- Evaluation of the split generator.
  have evalΩ : ∀ p : Fin 2 → Ω,
      aeval p G = Polynomial.aeval (p 0) P + Polynomial.aeval (p 1) Q := fun p ↦ by
    rw [hGPQ, map_add, ← Polynomial.aeval_algHom_apply (aeval p) (X 0) P,
      ← Polynomial.aeval_algHom_apply (aeval p) (X 1) Q, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X]
  have evalk : ∀ p : Fin 2 → k, aeval p G = P.eval (p 0) + Q.eval (p 1) := fun p ↦ by
    rw [hGPQ, map_add, ← Polynomial.aeval_algHom_apply (aeval p) (X 0) P,
      ← Polynomial.aeval_algHom_apply (aeval p) (X 1) Q, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval]
  have hneg : ∀ {R : Polynomial k}, IsAdditive R → ∀ a : k, R.eval (-a) = -R.eval a :=
    fun {R} hR a ↦ by
      have h := hR a (-a)
      rw [add_neg_cancel, hR.eval_zero] at h
      linear_combination -h
  -- Roots of the nonconstant additive parts.
  have root : ∀ {R : Polynomial k}, R ≠ 0 → R.coeff 0 = 0 → ∀ d : k, ∃ a : k, R.eval a = d :=
    fun {R} hR hR0 d ↦ by
      have hdeg : 0 < R.degree := by
        by_contra h
        exact hR ((Polynomial.eq_C_of_degree_le_zero (not_lt.1 h)).trans (by rw [hR0, map_zero]))
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (R - Polynomial.C d)
        (by rw [Polynomial.degree_sub_C hdeg]; exact hdeg.ne')
      refine ⟨a, ?_⟩
      have h0 := ha.eq_zero
      rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] at h0
      exact h0
  -- A shifted generator lies in the ideal of a curve on which `G` is constant.
  have memShift : ∀ {u v : Ω} {d a : k}, aeval ![u, v] G = algebraMap k Ω d → P.eval a = d →
      translate (-![a, 0]) G ∈ idealOf k ![u, v] := by
    intro u v d a hd ha
    rw [mem_idealOf_iff, aeval_translate, evalΩ]
    change Polynomial.aeval (u + algebraMap k Ω (-a)) P +
      Polynomial.aeval (v + algebraMap k Ω (-0)) Q = 0
    rw [neg_zero, map_zero, add_zero, hPa.aeval_add,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hneg hPa, ha]
    have hd' := hd
    rw [evalΩ] at hd'
    change Polynomial.aeval u P + Polynomial.aeval v Q = algebraMap k Ω d at hd'
    rw [map_neg]
    linear_combination hd'
  -- Each curve ideal is generated by the shifted generator.
  have idealEq : ∀ {u v : Ω} {d a : k}, Transcendental k u → v ∈ racl k {u} →
      aeval ![u, v] G = algebraMap k Ω d → P.eval a = d →
      idealOf k ![u, v] = Ideal.span {translate (-![a, 0]) G} := by
    intro u v d a hu hv hd ha
    obtain ⟨f, hf, hfI⟩ := exists_prime_span_idealOf k hu hv
    have hmem := memShift hd ha
    rw [hfI, Ideal.mem_span_singleton] at hmem
    rw [hfI]
    exact Ideal.span_singleton_eq_span_singleton.2
      (Prime.associated_of_dvd hf ((prime_translate_iff _).2 hG) hmem)
  -- The correspondence data in `Ω`.
  have memΩ : ∀ {u v : Ω}, point k u = point k v → v ∈ racl k {u} := fun {u v} h ↦ by
    have hr : racl k {u} = racl k {v} := congrArg Subtype.val h
    rw [hr]
    exact subset_racl k _ (Set.mem_singleton _)
  let S₀ : AddCorrSetup k Ω :=
    { x₁ := x₁, y₁ := y₁, x₂ := x₂, y₂ := y₂, indep := hx
      y₁_mem := memΩ h₁, x₁_mem := memΩ h₁.symm, y₂_mem := memΩ h₂, x₂_mem := memΩ h₂.symm
      sum_mem := memΩ h₁₂, sum_mem' := memΩ h₁₂.symm }
  have hx₁t : Transcendental k x₁ := hx.transcendental 0
  have hx₂t : Transcendental k x₂ := hx.transcendental 1
  have hx₁₂t : Transcendental k (x₁ + x₂) := S₀.sum_fst_transcendental
  obtain ⟨a₁, ha₁⟩ := root hP hP0 d₁
  obtain ⟨a₂, ha₂⟩ := root hP hP0 d₂
  have ha₁₂ : P.eval (a₁ + a₂) = d₁ + d₂ := by rw [hPa, ha₁, ha₂]
  have hd₁₂ : aeval ![x₁ + x₂, y₁ + y₂] G = algebraMap k Ω (d₁ + d₂) := by
    have e₁ := hd₁
    have e₂ := hd₂
    rw [evalΩ] at e₁ e₂ ⊢
    change Polynomial.aeval x₁ P + Polynomial.aeval y₁ Q = algebraMap k Ω d₁ at e₁
    change Polynomial.aeval x₂ P + Polynomial.aeval y₂ Q = algebraMap k Ω d₂ at e₂
    change Polynomial.aeval (x₁ + x₂) P + Polynomial.aeval (y₁ + y₂) Q = _
    rw [hPa.aeval_add, hQa.aeval_add, map_add]
    linear_combination e₁ + e₂
  have hI₁ := idealEq hx₁t (memΩ h₁) hd₁ ha₁
  have hI₂ := idealEq hx₂t (memΩ h₂) hd₂ ha₂
  have hI₁₂ := idealEq hx₁₂t (memΩ h₁₂) hd₁₂ ha₁₂
  have hg : (![a₁, 0] : Fin 2 → k) + ![a₂, 0] = ![a₁ + a₂, 0] := by
    funext i
    fin_cases i <;> simp
  -- The subgroup: the zero set of `G`.
  let H : AddSubgroup (Fin 2 → k) :=
    { carrier := {u | aeval u G = 0}
      add_mem' := fun {u v} hu hv ↦ by
        change aeval u G = 0 at hu
        change aeval v G = 0 at hv
        change aeval (u + v) G = 0
        rw [evalk] at hu hv ⊢
        rw [Pi.add_apply, Pi.add_apply, hPa, hQa]
        linear_combination hu + hv
      zero_mem' := by
        change aeval 0 G = 0
        rw [evalk, Pi.zero_apply, Pi.zero_apply, hPa.eval_zero, hQa.eval_zero, add_zero]
      neg_mem' := fun {u} hu ↦ by
        change aeval u G = 0 at hu
        change aeval (-u) G = 0
        rw [evalk] at hu ⊢
        rw [Pi.neg_apply, Pi.neg_apply, hneg hPa, hneg hQa]
        linear_combination -hu }
  have hHset : (H : Set (Fin 2 → k)) = zeroLocus k (Ideal.span {G}) := by
    rw [zeroLocus_span]
    ext u
    change aeval u G = 0 ↔ ∀ f ∈ ({G} : Set (MvPolynomial (Fin 2) k)), aeval u f = 0
    exact ⟨fun h f hf ↦ by rw [Set.mem_singleton_iff.1 hf]; exact h,
      fun h ↦ h G (Set.mem_singleton G)⟩
  have hGspan : (Ideal.span {G}).IsPrime := (Ideal.span_singleton_prime hG.ne_zero).2 hG
  have hvan : vanishingIdeal k (H : Set (Fin 2 → k)) = Ideal.span {G} := by
    rw [hHset, vanishingIdeal_zeroLocus_eq_radical, hGspan.radical]
  have hclosed : zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H := by
    rw [hvan, ← hHset]
  -- Dimension one: a translate of `G` is a nonzerodivisor in a maximal ideal of height two.
  have hdim1 : ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {G}) = 1 := by
    have hdim : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal (idealOf k ![x₁, y₁])
      (idealOf_isPrime k ![x₁, y₁]).ne_top
    have : M.IsPrime := hMmax.isPrime
    have hlt : idealOf k ![x₁, y₁] < M :=
      lt_of_le_of_ne hIM fun h ↦ not_isMaximal_idealOf k hx₁t (h ▸ hMmax)
    have hne : (idealOf k ![x₁, y₁]).height ≠ 0 := fun h ↦
      idealOf_ne_bot_of_mem_racl k (memΩ h₁) (Ideal.height_eq_zero_iff_eq_bot.1 h)
    have hM2 : (2 : ℕ∞) ≤ M.height :=
      calc (2 : ℕ∞) = 1 + 1 := one_add_one_eq_two.symm
        _ ≤ (idealOf k ![x₁, y₁]).height + 1 := by
          gcongr
          exact Order.one_le_iff_ne_zero.2 hne
        _ ≤ M.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hMh : (M.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin 2) k) := by
      refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hMmax.ne_top) ?_
      rw [hdim]
      exact WithBot.coe_le_coe.2 hM2
    have hT := (prime_translate_iff (-![a₁, 0])).2 hG
    have hrM : translate (-![a₁, 0]) G ∈ M := hIM (by
      rw [hI₁]
      exact Ideal.subset_span (Set.mem_singleton _))
    have key : ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {translate (-![a₁, 0]) G}) + 1 =
        ringKrullDim (MvPolynomial (Fin 2) k) := by
      refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_of_ne_zero hT.ne_zero)) ?_
      rw [← hMh]
      exact Ideal.height_le_ringKrullDim_quotient_add_one hrM
    let T : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
      AlgEquiv.ofAlgHom (translate (-![a₁, 0])) (translate ![a₁, 0])
        (AlgHom.ext fun g ↦ by
          rw [AlgHom.comp_apply, AlgHom.id_apply]
          exact translate_neg_translate _ g)
        (AlgHom.ext fun g ↦ by
          rw [AlgHom.comp_apply, AlgHom.id_apply]
          exact translate_translate_neg _ g)
    have hmap : Ideal.span {translate (-![a₁, 0]) G} = (Ideal.span {G}).map
        (T.toRingEquiv : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ T.toRingEquiv hmap), hdim,
      ← one_add_one_eq_two (R := WithBot ℕ∞), ENat.WithBot.add_one_cancel] at key
    exact key
  -- Coset point sets.
  have cosetSet : ∀ g : Fin 2 → k,
      zeroLocus k (Ideal.span {translate (-g) G}) = g +ᵥ (H : Set (Fin 2 → k)) := by
    intro g
    ext u
    rw [zeroLocus_span, Set.mem_vadd_set_iff_neg_vadd_mem]
    change (∀ f ∈ ({translate (-g) G} : Set (MvPolynomial (Fin 2) k)), aeval u f = 0) ↔
      aeval (-g + u) G = 0
    have hfun : (fun j ↦ u j + algebraMap k k ((-g) j)) = -g + u := by
      funext j
      simp [add_comm]
    have hu : aeval u (translate (-g) G) = aeval (-g + u) G := by
      rw [aeval_translate, hfun]
    exact ⟨fun h ↦ hu.symm.trans (h _ (Set.mem_singleton _)),
      fun h f hf ↦ by rw [Set.mem_singleton_iff.1 hf, hu]; exact h⟩
  -- Nonconstant projections.
  obtain ⟨b, hb⟩ := root hQ hQ0 (-P.eval 1)
  obtain ⟨c, hc⟩ := root hP hP0 (-Q.eval 1)
  have hproj₀ : ∃ u ∈ H, ∃ v ∈ H, u 0 ≠ v 0 := by
    refine ⟨0, H.zero_mem, ![1, b], ?_, by simp⟩
    change aeval ![1, b] G = 0
    rw [evalk]
    change P.eval 1 + Q.eval b = 0
    rw [hb, add_neg_cancel]
  have hproj₁ : ∃ u ∈ H, ∃ v ∈ H, u 1 ≠ v 1 := by
    refine ⟨0, H.zero_mem, ![c, 1], ?_, by simp⟩
    change aeval ![c, 1] G = 0
    rw [evalk]
    change P.eval c + Q.eval 1 = 0
    rw [hc, neg_add_cancel]
  refine ⟨H, G, ![a₁, 0], ![a₂, 0], hG, hvan, hclosed, ?_, ?_, hproj₀, hproj₁, hI₁, hI₂, ?_,
    ?_, ?_, ?_⟩
  · rw [hvan]
    infer_instance
  · rw [hvan]
    exact hdim1
  · rw [hg]
    exact hI₁₂
  · rw [hI₁]
    exact cosetSet _
  · rw [hI₂]
    exact cosetSet _
  · rw [hI₁₂, hg]
    exact cosetSet _

end AclGeom
