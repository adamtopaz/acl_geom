/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.JCoordinates
import AclGeom.Geometry.FrobeniusPowers
import AclGeom.Transfer.Descent

/-!
# The Frobenius kernel theorem

A field automorphism acting trivially on the point geometry is an integral
Frobenius power (blueprint Thm `kernel`, checklist U1): if `σ : K ≃+* K`
satisfies `[σ x] = [x]` for every `x` transcendental over `k`, `K` is perfect
of exponential characteristic `q`, and `trdeg_k K ≥ 5`, then
`σ = Frob^n` for some `n : ℤ`.  The exponent is unique in positive
characteristic, and in characteristic zero `σ = 1`.

The rank-five hypothesis is explicit: the displayed blueprint statement omits it, although its
proof and the main theorem use it. The original wording and the rank-one counterexample are
recorded on #9.

Two simplifications relative to the blueprint:

* `σ` is not assumed to carry `k` onto itself, and `k` is not assumed to be
  relatively algebraically closed in `K`: the elements algebraic over `k` are
  handled by writing `c = (t + c) - t` with `t` transcendental.
* j-rigidity, proved over algebraically closed fields, is transported to an
  arbitrary field `K` once and for all (`j_rigidity_field`), through the
  algebraic closure of `K` and the algebraic closure of `k` inside it.

**Status:** complete (M7, checklist U1).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section RigidityField

/-- **j-rigidity over an arbitrary field** (blueprint Thm `jrigidity`, with
the algebraically closed hypotheses removed): the elementwise statement of
`j_rigidity` holds for elements of any field `K ⊇ k`.  The proof embeds `K` in
its algebraic closure `Ω`, enlarges the base to the algebraic closure of `k`
in `Ω`, applies `j_rigidity` there, and pulls the conclusion back. -/
theorem j_rigidity_field (q : ℕ) [ExpChar k q]
    {x a y b : K} (hind : AlgebraicIndependent k ![x, a])
    (hy : y ∈ racl k {x}) (hx : x ∈ racl k {y})
    (hb : b ∈ racl k {a}) (ha : a ∈ racl k {b})
    (hadd : y + b ∈ racl k {x + a}) (hadd' : x + a ∈ racl k {y + b})
    (hmul : y * b ∈ racl k {x * a}) (hmul' : x * a ∈ racl k {y * b})
    (hjj : y * (1 + b) ∈ racl k {x * (1 + a)})
    (hjj' : x * (1 + a) ∈ racl k {y * (1 + b)})
    {s s' : K} (hs : s ∉ racl k {x, a}) (hss' : s' ∉ racl k {x, a, s}) :
    ∃ u v : ℕ, y ^ q ^ v = x ^ q ^ u ∧ b ^ q ^ v = a ^ q ^ u := by
  classical
  set Ω := AlgebraicClosure K
  set ι : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω with hιdef
  have hιinj : Function.Injective ι := ι.toRingHom.injective
  have : IsAlgClosed (↥(algebraicClosure k Ω)) :=
    (algebraicClosure.isAlgClosure k Ω).isAlgClosed
  have : ExpChar (↥(algebraicClosure k Ω)) q :=
    expChar_of_injective_ringHom
      (algebraMap k (↥(algebraicClosure k Ω))).injective q
  have halg : ∀ z ∈ algebraicClosure k Ω, IsAlgebraic k z := fun z hz ↦
    (mem_algebraicClosure_iff (F := k)).1 hz
  have hbase : ∀ {S : Set Ω} {z : Ω},
      z ∈ racl k S ↔ z ∈ racl (↥(algebraicClosure k Ω)) S :=
    fun {S z} ↦ (mem_racl_base_iff_of_algebraic halg).symm
  have tr : ∀ {w z : K}, z ∈ racl k ({w} : Set K) →
      ι z ∈ racl (↥(algebraicClosure k Ω)) ({ι w} : Set Ω) := fun h ↦
    hbase.1 ((algHom_mem_racl_singleton_iff ι).2 h)
  have hpair : (⇑ι '' ({x, a} : Set K)) = ({ι x, ι a} : Set Ω) := by
    simp [Set.image_insert_eq, Set.image_singleton]
  have htriple : (⇑ι '' ({x, a, s} : Set K)) = ({ι x, ι a, ι s} : Set Ω) := by
    simp [Set.image_insert_eq, Set.image_singleton]
  have hindΩ : AlgebraicIndependent k ![ι x, ι a] := by
    refine algebraicIndependent_pair ?_ ?_
    · intro h
      exact AlgebraicIndependent.notMem_racl_pair' hind
        ((algHom_mem_racl_singleton_iff ι).1 h)
    · intro h
      exact AlgebraicIndependent.notMem_racl_pair hind
        ((algHom_mem_racl_singleton_iff ι).1 h)
  have hindb : AlgebraicIndependent (↥(algebraicClosure k Ω)) ![ι x, ι a] :=
    algebraicIndependent_pair_base_of_algebraic halg hindΩ
  have hsΩ : ι s ∉ racl (↥(algebraicClosure k Ω)) ({ι x, ι a} : Set Ω) := by
    intro h
    apply hs
    rw [← algHom_mem_racl_image_iff ι, hpair]
    exact hbase.2 h
  have hss'Ω :
      ι s' ∉ racl (↥(algebraicClosure k Ω)) ({ι x, ι a, ι s} : Set Ω) := by
    intro h
    apply hss'
    rw [← algHom_mem_racl_image_iff ι, htriple]
    exact hbase.2 h
  obtain ⟨u, v, h1, h2⟩ := j_rigidity (k := ↥(algebraicClosure k Ω)) q
    (x := ι x) (a := ι a) (y := ι y) (b := ι b) hindb
    (tr hy) (tr hx) (tr hb) (tr ha)
    (by simpa only [map_add] using tr hadd)
    (by simpa only [map_add] using tr hadd')
    (by simpa only [map_mul] using tr hmul)
    (by simpa only [map_mul] using tr hmul')
    (by simpa only [map_add, map_mul, map_one] using tr hjj)
    (by simpa only [map_add, map_mul, map_one] using tr hjj')
    hsΩ hss'Ω
  refine ⟨u, v, hιinj ?_, hιinj ?_⟩
  · rw [map_pow, map_pow]
    exact h1
  · rw [map_pow, map_pow]
    exact h2

end RigidityField

section FrobeniusPowers

variable (q : ℕ) [ExpChar K q] [PerfectRing K q]

/-- **Separation of Frobenius exponents** on a transcendental element: in
positive characteristic, `Frob^m x = Frob^n x` with `x` transcendental over
`k` forces `m = n`. -/
theorem eq_of_frobeniusZPow_apply_eq (hq : 2 ≤ q) {m n : ℤ} {x : K}
    (hx : x ∉ racl k (∅ : Set K))
    (h : frobeniusZPow K q m x = frobeniusZPow K q n x) : m = n := by
  have hd : frobeniusZPow K q (m - n) x = x := by
    rw [frobeniusZPow_sub, RingAut.mul_apply, h]
    exact (frobeniusZPow K q n).symm_apply_apply x
  have hsep : ∀ d : ℕ, frobeniusZPow K q d x = x → d = 0 := fun d hfix ↦ by
    rw [frobeniusZPow_natCast_apply] at hfix
    have h0 : x ^ q ^ d = x ^ q ^ 0 := by rw [hfix, pow_zero, pow_one]
    exact pow_pow_sep_of_notMem_racl_empty hx hq h0
  rcases Int.eq_nat_or_neg (m - n) with ⟨d, hd' | hd'⟩
  · rw [hd'] at hd
    have := hsep d hd
    omega
  · have hd2 : frobeniusZPow K q d x = x := by
      have h3 : frobeniusZPow K q d (frobeniusZPow K q (m - n) x) =
          frobeniusZPow K q d x := by rw [hd]
      rw [← RingAut.mul_apply, frobeniusZPow, frobeniusZPow, ← zpow_add,
        hd', add_neg_cancel, zpow_zero] at h3
      exact h3.symm
    have := hsep d hd2
    omega

/-- On an element transcendental over `k`, two Frobenius powers agree only
if they are equal as automorphisms: in positive characteristic their
exponents agree, and in characteristic zero every power is the identity. -/
theorem frobeniusZPow_eq_of_apply_eq {m n : ℤ} {x : K}
    (hx : x ∉ racl k (∅ : Set K))
    (h : frobeniusZPow K q m x = frobeniusZPow K q n x) :
    frobeniusZPow K q m = frobeniusZPow K q n := by
  rcases expChar_is_prime_or_one K q with hq | hq
  · rw [eq_of_frobeniusZPow_apply_eq q hq.two_le hx h]
  · rw [frobeniusZPow_eq_one_of_eq_one q hq m, frobeniusZPow_eq_one_of_eq_one q hq n]

end FrobeniusPowers

section Kernel

/-- Exchange for singletons: if a transcendental `x` is algebraic over `k(y)`,
then `y` is algebraic over `k(x)`. -/
theorem racl_exchange_singleton {x y : K} (hx : x ∉ racl k (∅ : Set K))
    (h : x ∈ racl k ({y} : Set K)) : y ∈ racl k ({x} : Set K) := by
  have h' : x ∈ racl k (insert y (∅ : Set K)) := by simpa using h
  simpa using racl_exchange h' hx

variable (q : ℕ) [ExpChar K q]

/-- An element transcendental over `k` stays transcendental after adding an
element algebraic over `k`. -/
theorem add_notMem_racl_empty {t c : K} (ht : t ∉ racl k (∅ : Set K))
    (hc : c ∈ racl k (∅ : Set K)) : t + c ∉ racl k (∅ : Set K) := by
  intro h
  apply ht
  have := sub_mem h hc
  rwa [add_sub_cancel_right] at this

variable [PerfectRing K q]

/-- On an independent pair, an automorphism fixing every transcendental
point acts by one integral Frobenius power (blueprint Thm `kernel`, first
step, via `j_rigidity_field`). -/
theorem exists_frobeniusZPow_pair (σ : K ≃+* K)
    (hσ : ∀ z : K, z ∉ racl k (∅ : Set K) →
      ClosedIF.point k (σ z) = ClosedIF.point k z)
    (hfresh : ∀ S : Finset K, S.card ≤ 3 → ∃ z, z ∉ racl k (S : Set K))
    {x a : K} (hind : AlgebraicIndependent k ![x, a]) :
    ∃ n : ℤ, σ x = frobeniusZPow K q n x ∧ σ a = frobeniusZPow K q n a := by
  classical
  have : ExpChar k q := (algebraMap k K).expChar (algebraMap k K).injective q
  obtain ⟨hx, hxa, hmul, hjj, ha⟩ := jCoordinates_notMem_bot hind
  have htrans : ∀ z : K, z ∉ (⊥ : ClosedIF k K) → z ∉ racl k (∅ : Set K) :=
    fun z hz h ↦ hz (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))
  have hx0 := htrans x hx
  have hxa0 := htrans (x + a) hxa
  have hmul0 := htrans (x * a) hmul
  have hjj0 : x * (1 + a) ∉ racl k (∅ : Set K) := by
    rw [show x * (1 + a) = x + x * a by ring]
    exact htrans _ hjj
  have ha0 := htrans a ha
  obtain ⟨r₁, r₁'⟩ := ClosedIF.point_eq_point_iff.1 (hσ x hx0)
  obtain ⟨r₂, r₂'⟩ := ClosedIF.point_eq_point_iff.1 (hσ _ hxa0)
  obtain ⟨r₃, r₃'⟩ := ClosedIF.point_eq_point_iff.1 (hσ _ hmul0)
  obtain ⟨r₄, r₄'⟩ := ClosedIF.point_eq_point_iff.1 (hσ _ hjj0)
  obtain ⟨r₅, r₅'⟩ := ClosedIF.point_eq_point_iff.1 (hσ a ha0)
  rw [map_add] at r₂ r₂'
  rw [map_mul] at r₃ r₃'
  rw [map_mul, map_add, map_one] at r₄ r₄'
  obtain ⟨s, hs⟩ := hfresh {x, a} ((Finset.card_insert_le _ _).trans (by simp))
  obtain ⟨s', hs'⟩ := hfresh {x, a, s}
    ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))))
  have hs₂ : s ∉ racl k ({x, a} : Set K) := by simpa using hs
  have hs₂' : s' ∉ racl k ({x, a, s} : Set K) := by simpa using hs'
  obtain ⟨u, v, h1, h2⟩ := j_rigidity_field q hind r₁ r₁' r₅ r₅' r₂ r₂' r₃ r₃'
    r₄ r₄' hs₂ hs₂'
  exact ⟨(u : ℤ) - v, (frobeniusZPow_sub_apply_of_pow_eq q h1).symm,
    (frobeniusZPow_sub_apply_of_pow_eq q h2).symm⟩

/-- **The Frobenius kernel theorem** (blueprint Thm `kernel`): over a perfect
field `K` of exponential characteristic `q` with `trdeg_k K ≥ 5`, a field
automorphism fixing every point `[z]` with `z` transcendental over `k` is an
integral power of Frobenius. -/
theorem exists_eq_frobeniusZPow_of_point_fixed
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (σ : K ≃+* K)
    (hσ : ∀ z : K, z ∉ racl k (∅ : Set K) →
      ClosedIF.point k (σ z) = ClosedIF.point k z) :
    ∃ n : ℤ, σ = frobeniusZPow K q n := by
  classical
  have : ExpChar k q := (algebraMap k K).expChar (algebraMap k K).injective q
  have hfresh := fresh_three_of_five_le_trdeg htr
  have hfresh4 := fresh_four_of_five_le_trdeg htr
  -- A reference independent pair and its exponent.
  obtain ⟨x₀, hx₀⟩ := hfresh ∅ (by simp)
  obtain ⟨a₀, ha₀⟩ := hfresh {x₀} (by simp)
  have hx₀' : x₀ ∉ racl k (∅ : Set K) := by simpa using hx₀
  have ha₀' : a₀ ∉ racl k ({x₀} : Set K) := by simpa using ha₀
  have hind₀ : AlgebraicIndependent k ![x₀, a₀] := by
    refine algebraicIndependent_pair ?_ ha₀'
    intro h
    -- exchange: `x₀ ∈ racl {a₀}` with `x₀` transcendental puts `a₀` in
    -- `racl {x₀}`.
    exact ha₀' (racl_exchange_singleton hx₀' h)
  obtain ⟨n, hxn, -⟩ := exists_frobeniusZPow_pair q σ hσ hfresh hind₀
  -- Every transcendental element moves by the same power.
  have htrans : ∀ z : K, z ∉ racl k (∅ : Set K) →
      σ z = frobeniusZPow K q n z := by
    intro z hz
    obtain ⟨t, ht⟩ := hfresh4 {x₀, a₀, z}
      ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))))
    have ht' : t ∉ racl k ({x₀, a₀, z} : Set K) := by simpa using ht
    have hind₁ : AlgebraicIndependent k ![x₀, t] := by
      refine algebraicIndependent_pair ?_ ?_
      · intro h
        exact ht' (racl_exchange_singleton hx₀'
          h |> fun h' ↦ racl_mono (by simp) h')
      · intro h
        exact ht' (racl_mono (by simp) h)
    have hind₂ : AlgebraicIndependent k ![z, t] := by
      refine algebraicIndependent_pair ?_ ?_
      · intro h
        exact ht' (racl_exchange_singleton hz h |> fun h' ↦ racl_mono (by simp) h')
      · intro h
        exact ht' (racl_mono (by simp) h)
    obtain ⟨n₁, hx₁, ht₁⟩ := exists_frobeniusZPow_pair q σ hσ hfresh hind₁
    obtain ⟨n₂, hz₂, ht₂⟩ := exists_frobeniusZPow_pair q σ hσ hfresh hind₂
    have ht0 : t ∉ racl k (∅ : Set K) := fun h ↦ ht' (racl_mono (by simp) h)
    have e₁ : frobeniusZPow K q n = frobeniusZPow K q n₁ :=
      frobeniusZPow_eq_of_apply_eq q hx₀' (hxn.symm.trans hx₁)
    have e₂ : frobeniusZPow K q n₁ = frobeniusZPow K q n₂ :=
      frobeniusZPow_eq_of_apply_eq q ht0 (ht₁.symm.trans ht₂)
    rw [hz₂, e₁, e₂]
  refine ⟨n, RingEquiv.ext fun c ↦ ?_⟩
  by_cases hc : c ∈ racl k (∅ : Set K)
  · -- Algebraic elements: `c = (x₀ + c) - x₀`.
    have h1 := htrans (x₀ + c) (add_notMem_racl_empty hx₀' hc)
    have h2 := htrans x₀ hx₀'
    rw [map_add, map_add, h2] at h1
    exact add_left_cancel h1
  · exact htrans c hc

/-- **Uniqueness of the Frobenius exponent** (blueprint Thm `kernel`, last
clause): in positive characteristic, as soon as some element is
transcendental over `k`, distinct integral Frobenius powers are distinct. -/
theorem frobeniusZPow_injective (hq : q ≠ 1) {x : K}
    (hx : x ∉ racl k (∅ : Set K)) {m n : ℤ}
    (h : frobeniusZPow K q m = frobeniusZPow K q n) : m = n := by
  rcases expChar_is_prime_or_one K q with hp | hq1
  · exact eq_of_frobeniusZPow_apply_eq q hp.two_le hx (by rw [h])
  · exact absurd hq1 hq

/-- **The kernel theorem in characteristic zero**: an automorphism fixing
every transcendental point is the identity. -/
theorem eq_refl_of_point_fixed [ExpChar K 1]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (σ : K ≃+* K)
    (hσ : ∀ z : K, z ∉ racl k (∅ : Set K) →
      ClosedIF.point k (σ z) = ClosedIF.point k z) :
    σ = RingEquiv.refl K := by
  obtain ⟨n, hn⟩ := exists_eq_frobeniusZPow_of_point_fixed 1 htr σ hσ
  rw [hn, frobeniusZPow_eq_one_of_eq_one 1 rfl n]
  rfl

end Kernel

end

end AclGeom
