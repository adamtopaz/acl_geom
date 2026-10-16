/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AdditiveSubgroup

/-!
# Connected one-dimensional subgroups of the additive plane

Blueprint Lemma `subgroup-classification` (a) in its source form: over an algebraically closed
field `k`, a Zariski-closed, connected, one-dimensional subgroup `H ⊆ k²` whose two projections
are nonconstant is `{(u, v) : P(u) = Q(v)}` for nonzero additive polynomials `P, Q`
(`addSubgroup_classification_of_connected`).  The coordinate ring of `H` is
`k[X₀, X₁] ⧸ I(H)` with `I(H)` the vanishing ideal.  Connectedness is connectedness of its prime
spectrum, and dimension one is its Krull dimension.

The bridge to the prime-ideal form `addSubgroup_classification` shows that `I(H)` is prime.  Its
minimal primes are finitely many.  If two of their zero loci `C, C'` meet at `c`, the vanishing
ideal of `C + C' - c` is prime (the irreducible components `C, C'` are irreducible), contains
`I(H)` because `H` is a subgroup, and lies in both primes; minimality makes them equal
(`eq_of_mem_minimalPrimes`).  Distinct components are therefore disjoint, hence comaximal by the
Nullstellensatz, and the Chinese remainder theorem produces a nontrivial idempotent of the
coordinate ring unless there is only one component.  The idempotents of a ring with connected
spectrum are `0` and `1`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C4).
-/

namespace AclGeom

open MvPolynomial

variable {k : Type*} [Field k]

/-- Evaluation of a translate at a point of `k²`. -/
private theorem aeval_translate_eq (u c : Fin 2 → k) (g : MvPolynomial (Fin 2) k) :
    aeval u (translate c g) = aeval (u + c) g := by
  rw [aeval_translate]
  have hfun : (fun j ↦ u j + algebraMap k k (c j)) = u + c := by
    funext j
    simp
  rw [hfun]

variable [IsAlgClosed k]

/-- A prime ideal is the vanishing ideal of its zero locus. -/
private theorem vanishingIdeal_zeroLocus_of_isPrime {P : Ideal (MvPolynomial (Fin 2) k)}
    (hP : P.IsPrime) : vanishingIdeal k (zeroLocus k P) = P := by
  rw [vanishingIdeal_zeroLocus_eq_radical, hP.radical]

/-- **Irreducibility of a translated sum of components**: if `g * h` vanishes on
`C + C' - c` for zero loci `C, C'` of primes, then `g` or `h` vanishes there. -/
private theorem forall_add_sub_or {P P' : Ideal (MvPolynomial (Fin 2) k)} (hP : P.IsPrime)
    (hP' : P'.IsPrime) (c : Fin 2 → k) {g h : MvPolynomial (Fin 2) k}
    (hgh : ∀ u ∈ zeroLocus k P, ∀ v ∈ zeroLocus k P', aeval (u + v - c) (g * h) = 0) :
    (∀ u ∈ zeroLocus k P, ∀ v ∈ zeroLocus k P', aeval (u + v - c) g = 0) ∨
      (∀ u ∈ zeroLocus k P, ∀ v ∈ zeroLocus k P', aeval (u + v - c) h = 0) := by
  classical
  -- The ideal of translates `f(· + v - c)`, `v ∈ C'`.
  let T : MvPolynomial (Fin 2) k → Ideal (MvPolynomial (Fin 2) k) := fun f ↦
    Ideal.span ((fun v ↦ translate (v - c) f) '' zeroLocus k P')
  have hT : ∀ (f : MvPolynomial (Fin 2) k) (u : Fin 2 → k),
      (∀ v ∈ zeroLocus k P', aeval (u + v - c) f = 0) →
      T f ≤ RingHom.ker (aeval u : MvPolynomial (Fin 2) k →ₐ[k] k) := by
    intro f u hf
    refine Ideal.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, aeval_translate_eq, ← add_sub_assoc]
    exact hf v hv
  -- For each `u ∈ C`, one of the two translates lies in `P'`.
  have hsplit : ∀ u ∈ zeroLocus k P, (∀ v ∈ zeroLocus k P', aeval (u + v - c) g = 0) ∨
      (∀ v ∈ zeroLocus k P', aeval (u + v - c) h = 0) := by
    intro u hu
    have hmem : translate (u - c) g * translate (u - c) h ∈ P' := by
      rw [← map_mul, ← vanishingIdeal_zeroLocus_of_isPrime hP', mem_vanishingIdeal_iff]
      intro v hv
      rw [aeval_translate_eq, show v + (u - c) = u + v - c by abel]
      exact hgh u hu v hv
    rcases hP'.mem_or_mem hmem with hg | hh
    · left
      intro v hv
      have := (mem_vanishingIdeal_iff.1
        ((vanishingIdeal_zeroLocus_of_isPrime hP').symm ▸ hg)) v hv
      rwa [aeval_translate_eq, show v + (u - c) = u + v - c by abel] at this
    · right
      intro v hv
      have := (mem_vanishingIdeal_iff.1
        ((vanishingIdeal_zeroLocus_of_isPrime hP').symm ▸ hh)) v hv
      rwa [aeval_translate_eq, show v + (u - c) = u + v - c by abel] at this
  -- So `T g ⊓ T h` vanishes on `C`, hence lies in the prime `P`.
  have hinf : T g ⊓ T h ≤ P := by
    intro f hf
    rw [← vanishingIdeal_zeroLocus_of_isPrime hP, mem_vanishingIdeal_iff]
    intro u hu
    rcases hsplit u hu with hg | hh
    · exact (RingHom.mem_ker).1 (hT g u hg hf.1)
    · exact (RingHom.mem_ker).1 (hT h u hh hf.2)
  have hfin : ∀ f, T f ≤ P → ∀ u ∈ zeroLocus k P, ∀ v ∈ zeroLocus k P',
      aeval (u + v - c) f = 0 := by
    intro f hf u hu v hv
    have hmem : translate (v - c) f ∈ P := hf (Ideal.subset_span ⟨v, hv, rfl⟩)
    have := hu _ hmem
    rwa [aeval_translate_eq, ← add_sub_assoc] at this
  rcases hP.inf_le.1 hinf with hg | hh
  · exact Or.inl (hfin g hg)
  · exact Or.inr (hfin h hh)

/-- **Meeting components coincide**: two minimal primes of the vanishing ideal of a closed
subgroup whose zero loci share a point are equal. -/
private theorem eq_of_mem_minimalPrimes {H : AddSubgroup (Fin 2 → k)}
    (hclosed : zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H)
    {P P' : Ideal (MvPolynomial (Fin 2) k)}
    (hP : P ∈ (vanishingIdeal k (H : Set (Fin 2 → k))).minimalPrimes)
    (hP' : P' ∈ (vanishingIdeal k (H : Set (Fin 2 → k))).minimalPrimes)
    {c : Fin 2 → k} (hc : c ∈ zeroLocus k P) (hc' : c ∈ zeroLocus k P') : P = P' := by
  have hPp : P.IsPrime := hP.1.1
  have hP'p : P'.IsPrime := hP'.1.1
  have hsub : ∀ {Q : Ideal (MvPolynomial (Fin 2) k)},
      vanishingIdeal k (H : Set (Fin 2 → k)) ≤ Q → ∀ x ∈ zeroLocus k Q, x ∈ H := by
    intro Q hQ x hx
    have hx' : x ∈ zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) :=
      zeroLocus_anti_mono hQ hx
    rw [hclosed] at hx'
    exact hx'
  let Q := vanishingIdeal k
    {w : Fin 2 → k | ∃ u ∈ zeroLocus k P, ∃ v ∈ zeroLocus k P', w = u + v - c}
  have hmemQ : ∀ g, g ∈ Q ↔
      ∀ u ∈ zeroLocus k P, ∀ v ∈ zeroLocus k P', aeval (u + v - c) g = 0 := by
    intro g
    rw [mem_vanishingIdeal_iff]
    constructor
    · intro hg u hu v hv
      exact hg _ ⟨u, hu, v, hv, rfl⟩
    · rintro hg _ ⟨u, hu, v, hv, rfl⟩
      exact hg u hu v hv
  have hQP : Q ≤ P := fun g hg ↦ by
    rw [← vanishingIdeal_zeroLocus_of_isPrime hPp, mem_vanishingIdeal_iff]
    intro u hu
    have := (hmemQ g).1 hg u hu c hc'
    rwa [add_sub_cancel_right] at this
  have hQP' : Q ≤ P' := fun g hg ↦ by
    rw [← vanishingIdeal_zeroLocus_of_isPrime hP'p, mem_vanishingIdeal_iff]
    intro v hv
    have := (hmemQ g).1 hg c hc v hv
    rwa [add_sub_cancel_left] at this
  have hJQ : vanishingIdeal k (H : Set (Fin 2 → k)) ≤ Q := fun g hg ↦ (hmemQ g).2 fun u hu v hv ↦
    mem_vanishingIdeal_iff.1 hg _
      (H.sub_mem (H.add_mem (hsub hP.1.2 u hu) (hsub hP'.1.2 v hv)) (hsub hP.1.2 c hc))
  have hQprime : Q.IsPrime := by
    refine ⟨fun htop ↦ hPp.ne_top (top_le_iff.1 (htop ▸ hQP)), fun {g h} hgh ↦ ?_⟩
    rcases forall_add_sub_or hPp hP'p c ((hmemQ (g * h)).1 hgh) with hg | hh
    · exact Or.inl ((hmemQ g).2 hg)
    · exact Or.inr ((hmemQ h).2 hh)
  obtain ⟨P'', hP'', hP''Q⟩ := Ideal.exists_minimalPrimes_le hJQ
  have h1 : P = P'' := le_antisymm (hP.2 hP''.1 (hP''Q.trans hQP)) (hP''Q.trans hQP)
  have h2 : P' = P'' := le_antisymm (hP'.2 hP''.1 (hP''Q.trans hQP')) (hP''Q.trans hQP')
  exact h1.trans h2.symm

/-- In a ring with connected prime spectrum, the only idempotents are `0` and `1`. -/
private theorem eq_zero_or_one_of_isIdempotentElem {A : Type*} [CommRing A]
    [ConnectedSpace (PrimeSpectrum A)] {y : A} (hy : IsIdempotentElem y) : y = 0 ∨ y = 1 := by
  have hzero : ∀ z : A, IsIdempotentElem z →
      ((PrimeSpectrum.basicOpen z : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)) = ∅ → z = 0 := by
    intro z hz h
    have hbot : PrimeSpectrum.basicOpen z = ⊥ := by
      ext1
      simpa using h
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff z).1 hbot
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn
      exact (subsingleton_of_zero_eq_one hn.symm).elim _ _
    · rwa [hz.pow_eq hpos.ne'] at hn
  have hcl : IsClopen ((PrimeSpectrum.basicOpen y : TopologicalSpace.Opens (PrimeSpectrum A)) :
      Set (PrimeSpectrum A)) := PrimeSpectrum.isClopen_iff.2 ⟨y, hy, rfl⟩
  rcases isClopen_iff.1 hcl with h | h
  · exact Or.inl (hzero y hy h)
  · right
    have h1 : ((PrimeSpectrum.basicOpen (1 - y) :
        TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) = ∅ := by
      have hmul : PrimeSpectrum.basicOpen ((1 - y) * y) = ⊥ := by
        rw [show (1 - y) * y = 0 by rw [sub_mul, one_mul, hy.eq, sub_self],
          PrimeSpectrum.basicOpen_zero]
      have h2 := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum A) ↦
        (U : Set (PrimeSpectrum A))) hmul
      simp only [PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
        TopologicalSpace.Opens.coe_bot, h, Set.inter_univ] at h2
      exact h2
    have := hzero (1 - y) hy.one_sub h1
    exact (sub_eq_zero.1 this).symm

/-- **The vanishing ideal of a closed connected subgroup is prime.** -/
private theorem isPrime_vanishingIdeal_of_connected (H : AddSubgroup (Fin 2 → k))
    (hclosed : zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H)
    [hconn : ConnectedSpace
      (PrimeSpectrum (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))))] :
    (vanishingIdeal k (H : Set (Fin 2 → k))).IsPrime := by
  classical
  set J := vanishingIdeal k (H : Set (Fin 2 → k)) with hJdef
  have hJrad : J.radical = J := by
    have h := vanishingIdeal_zeroLocus_eq_radical (K := k) J
    rw [hclosed] at h
    exact h.symm
  have hJtop : J ≠ ⊤ := fun h ↦ by
    have h1 : (1 : MvPolynomial (Fin 2) k) ∈ J := h ▸ Submodule.mem_top
    have h2 := mem_vanishingIdeal_iff.1 h1 0 H.zero_mem
    simp at h2
  -- Distinct minimal primes are comaximal.
  have hcop : ∀ P ∈ J.minimalPrimes, ∀ P' ∈ J.minimalPrimes, P ≠ P' → IsCoprime P P' := by
    intro P hP P' hP' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    have hempty : zeroLocus k (P ⊔ P') = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      exact hne (eq_of_mem_minimalPrimes hclosed hP hP' (zeroLocus_anti_mono le_sup_left hc)
        (zeroLocus_anti_mono le_sup_right hc))
    have h := vanishingIdeal_zeroLocus_eq_radical (K := k) (P ⊔ P')
    have htop : vanishingIdeal k (∅ : Set (Fin 2 → k)) = ⊤ :=
      eq_top_iff.2 fun g _ ↦ mem_vanishingIdeal_iff.2 fun x hx ↦ absurd hx (Set.notMem_empty x)
    rw [hempty, htop] at h
    exact Ideal.radical_eq_top.1 h.symm
  -- At most one minimal prime, by the Chinese remainder theorem and connectedness.
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin 2) k) J
  have hsing : J.minimalPrimes.Subsingleton := by
    intro P hP P' hP'
    by_contra hne
    have := hfin.to_subtype
    let f : J.minimalPrimes → Ideal (MvPolynomial (Fin 2) k) := Subtype.val
    have hpair : Pairwise (Function.onFun IsCoprime f) := fun i j hij ↦
      hcop i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h)
    have hinf : ⨅ i, f i = J :=
      (sInf_eq_iInf' J.minimalPrimes).symm.trans (Ideal.sInf_minimalPrimes.trans hJrad)
    let e := (Ideal.quotEquivOfEq hinf.symm).trans (Ideal.quotientInfRingEquivPiQuotient f hpair)
    let i₀ : J.minimalPrimes := ⟨P, hP⟩
    let i₁ : J.minimalPrimes := ⟨P', hP'⟩
    have hi : i₁ ≠ i₀ := fun h ↦ hne (congrArg Subtype.val h).symm
    have hnt : ∀ i : J.minimalPrimes, Nontrivial (MvPolynomial (Fin 2) k ⧸ f i) := fun i ↦ by
      have : (f i).IsPrime := i.2.1.1
      infer_instance
    let s : ∀ i : J.minimalPrimes, MvPolynomial (Fin 2) k ⧸ f i := Pi.single i₀ 1
    have hs : IsIdempotentElem s := by
      funext i
      by_cases hii : i = i₀
      · subst hii
        simp [s]
      · simp [s, hii]
    rcases eq_zero_or_one_of_isIdempotentElem (hs.map e.symm) with h0 | h1
    · have h := congrFun (e.symm.injective (h0.trans (map_zero e.symm).symm)) i₀
      simp [s] at h
    · have h := congrFun (e.symm.injective (h1.trans (map_one e.symm).symm)) i₁
      simp [s, hi] at h
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hJtop
  have hJP : J = P := by
    have hset : J.minimalPrimes = {P} := (hsing.eq_singleton_of_mem hP)
    rw [← hJrad, ← Ideal.sInf_minimalPrimes, hset, sInf_singleton]
  rw [hJP]
  exact hP.1.1

/-- **Connected one-dimensional subgroups of `Gₐ²`** (blueprint Lemma
`subgroup-classification` (a)).  Over an algebraically closed field, let `H ⊆ k²` be a
Zariski-closed additive subgroup whose coordinate ring `k[X₀, X₁] ⧸ I(H)` has connected prime
spectrum and Krull dimension one, and whose two projections are nonconstant.  Then
`I(H) = (P(X₀) - Q(X₁))` for nonzero additive polynomials `P, Q`, and
`H = {(u, v) : P(u) = Q(v)}`. -/
theorem addSubgroup_classification_of_connected (H : AddSubgroup (Fin 2 → k))
    (hclosed : zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H)
    [ConnectedSpace
      (PrimeSpectrum (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))))]
    (hdim : ringKrullDim (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))) = 1)
    (hproj₀ : ∃ u ∈ H, ∃ v ∈ H, u 0 ≠ v 0) (hproj₁ : ∃ u ∈ H, ∃ v ∈ H, u 1 ≠ v 1) :
    ∃ P Q : Polynomial k, IsAdditive P ∧ IsAdditive Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      vanishingIdeal k (H : Set (Fin 2 → k)) =
        Ideal.span {Polynomial.aeval (X 0) P - Polynomial.aeval (X 1) Q} ∧
      (H : Set (Fin 2 → k)) = {u | P.eval (u 0) = Q.eval (u 1)} := by
  have := isPrime_vanishingIdeal_of_connected H hclosed
  exact addSubgroup_classification H _ hclosed.symm hdim hproj₀ hproj₁

end AclGeom
