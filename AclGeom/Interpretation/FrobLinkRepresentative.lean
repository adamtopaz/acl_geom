/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobLinkSemantic

/-!
# A common representative of the Frobenius-link multiplier

The original proof of blueprint Lemma `frobeq-correct` (remark `frob-link-audit`, claim (10.1))
used one representative `c` of the multiplier point of a direct Frobenius link from
`j(x, a)` to `j(x', a')` in all three product clauses, asserting
`[cx'] = [x]`, `[cx'a'] = [xa]` and `[cx'(1 + a')] = [x(1 + a)]`.  Each product clause supplies
its own representatives, so that inference is unjustified as written.  The claim itself holds
over perfect fields (`DirectFrobLink.exists_common_representative`).

The proof uses the incidence-rigidity theorem rather than the original calculation.  The link
twists the parameter by Frobenius (`DirectFrobLink.frobenius_of_witnesses`): `a' = a^Q` or
`a = a'^Q` for a power `Q` of the characteristic exponent.  In the first case `c = x^Q / x'`, and
in the second `c = x^{1/Q} / x'`, which uses perfection, satisfy the three equalities.  Every
point `C` satisfying the first two product clauses lies on the lines `[x'] ⊔ [x]` and
`[x'a'] ⊔ [xa]` (`MulPoint.le_sup`), and so does `[c]`.  The two lines are distinct, because `x, x',
a` are independent, so `C = [c]`.

This proves the statement (10.1) by a different route; it does not validate the original
separate-representative inference, which is retained as provenance.  The original proof's next
step, that (10.1) forces the Frobenius twist, is covered at the level of statements by
`DirectFrobLink.frobenius_of_witnesses`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.

**Status:** claim (10.1) is proved over perfect fields by incidence rigidity and the uniqueness of
the concurrency point (#23).
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **A common representative of the multiplier** (blueprint remark `frob-link-audit`,
claim (10.1)).  For a direct Frobenius link from `j(x, a)` to `j(y, a')` and every point `C`
with `MulPoint C [y] [x]` and `MulPoint C [ya'] [xa]`, some `c` generates `C` and satisfies
`[cy] = [x]`, `[cya'] = [xa]` and `[cy(1 + a')] = [x(1 + a)]`.  The ambient field is perfect; the
base field is arbitrary. -/
theorem DirectFrobLink.exists_common_representative [PerfectField K] (q : ℕ) [ExpChar k q]
    {u v : Fin 5 → Point k K} (h : DirectFrobLink u v) {x a y a' : K}
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a')
    {C : Point k K} (hC₀ : MulPoint C (v 0) (u 0)) (hC₂ : MulPoint C (v 2) (u 2)) :
    ∃ c : K, point k c = C.1 ∧ point k (c * y) = point k x ∧
      point k (c * y * a') = point k (x * a) ∧
      point k (c * y * (1 + a')) = point k (x * (1 + a)) := by
  obtain ⟨s, hs⟩ := h.frobenius_of_witnesses q hu hv
  obtain ⟨hu0, -, hu2, -, hu4⟩ := hu
  obtain ⟨hv0, -, hv2, -, hv4⟩ := hv
  -- The link's rank clause: `x, y, a` are independent.
  have hind : AlgebraicIndependent k ![x, y, a] := by
    have hr := h.independent
    unfold PointTripleIndependent at hr
    rw [hu0, hv0, hu4] at hr
    exact algebraicIndependent_of_rankEq_three_points hr
  have : ExpChar K q := expChar_of_injective_algebraMap (algebraMap k K).injective q
  have hQ : q ^ s ≠ 0 := pow_ne_zero s (expChar_pos (R := K) q).ne'
  have hy0 : y ≠ 0 := AlgebraicIndependent.ne_zero hind 1
  have ha'0 : a' ≠ 0 := fun h0 ↦ (v 4).2.1 (by
    rw [hv4, h0, point_eq_bot_iff]
    exact mem_bot_iff.2 isAlgebraic_zero)
  -- A common representative, from the Frobenius twist.
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c : K, point k (c * y) = point k x ∧
      point k (c * y * a') = point k (x * a) ∧
      point k (c * y * (1 + a')) = point k (x * (1 + a)) := by
    rcases hs with hs | hs
    · have e : x ^ q ^ s * (1 + a ^ q ^ s) = (x * (1 + a)) ^ q ^ s := by
        rw [mul_pow, add_pow_expChar_pow, one_pow]
      refine ⟨x ^ q ^ s / y, ?_, ?_, ?_⟩
      · rw [div_mul_cancel₀ _ hy0, point_pow x hQ]
      · rw [div_mul_cancel₀ _ hy0, hs, ← mul_pow, point_pow _ hQ]
      · rw [div_mul_cancel₀ _ hy0, hs, e, point_pow _ hQ]
    · obtain ⟨r, hr⟩ : ∃ r : K, r ^ q ^ s = x :=
        ⟨(iterateFrobeniusEquiv K q s).symm x, (iterateFrobeniusEquiv K q s).apply_symm_apply x⟩
      refine ⟨r / y, ?_, ?_, ?_⟩
      · rw [div_mul_cancel₀ _ hy0, ← point_pow r hQ, hr]
      · rw [div_mul_cancel₀ _ hy0, ← point_pow (r * a') hQ, mul_pow, hr, ← hs]
      · rw [div_mul_cancel₀ _ hy0, ← point_pow (r * (1 + a')) hQ, mul_pow, hr,
          add_pow_expChar_pow, one_pow, ← hs]
  -- `c` lies on both lines `[y] ⊔ [x]` and `[ya'] ⊔ [xa]`.
  have hcL₁ : c ∈ racl k ({y, x} : Set K) := by
    have h1 : c * y ∈ point k x := by
      rw [← hc₁]
      exact mem_point_self (c * y)
    have hcy : c * y ∈ racl k ({y, x} : Set K) :=
      racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ (Set.mem_singleton x)))
        (mem_point.1 h1)
    have h' := div_mem hcy (subset_racl k ({y, x} : Set K) (Set.mem_insert _ _))
    rwa [mul_div_cancel_right₀ c hy0] at h'
  have hcL₂ : c ∈ racl k ({y * a', x * a} : Set K) := by
    have h2 : c * y * a' ∈ point k (x * a) := by
      rw [← hc₂]
      exact mem_point_self (c * y * a')
    have hcya : c * y * a' ∈ racl k ({y * a', x * a} : Set K) :=
      racl_mono (Set.singleton_subset_iff.2
          (Set.mem_insert_of_mem _ (Set.mem_singleton (x * a)))) (mem_point.1 h2)
    have h' := div_mem hcya (subset_racl k ({y * a', x * a} : Set K) (Set.mem_insert _ _))
    rwa [mul_assoc, mul_div_cancel_right₀ c (mul_ne_zero hy0 ha'0)] at h'
  -- `c` generates a point: otherwise `x` would be algebraic over `y`.
  have hxy : x ∉ racl k ({y} : Set K) :=
    AlgebraicIndependent.notMem_racl_pair'
      (AlgebraicIndependent.pair_of_triple hind (i := 0) (j := 1) (by decide))
  have hcbot : c ∉ (⊥ : ClosedIF k K) := fun hc ↦ hxy (by
    have hcy : c * y ∈ racl k ({y} : Set K) :=
      mul_mem (racl_mono (Set.empty_subset _) (mem_racl_empty_of_isAlgebraic (mem_bot_iff.1 hc)))
        (subset_racl k _ rfl)
    have hx : x ∈ point k (c * y) := by
      rw [hc₁]
      exact mem_point_self x
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hcy) (mem_point.1 hx))
  refine ⟨c, ?_, hc₁, hc₂, hc₃⟩
  -- Two distinct lines through `C` and `[c]` force `C = [c]`.
  by_contra hne
  have hne' : C ≠ Point.mk' k c hcbot := fun h' ↦ hne (congrArg Subtype.val h').symm
  have hcle₁ : point k c ≤ (v 0).1 ⊔ (u 0).1 := by
    rw [hv0, hu0]
    refine point_le_iff.2 ?_
    change c ∈ ((point k y ⊔ point k x).1 : IntermediateField k K)
    rw [coe_sup_point₂]
    exact hcL₁
  have hcle₂ : point k c ≤ (v 2).1 ⊔ (u 2).1 := by
    rw [hv2, hu2]
    refine point_le_iff.2 ?_
    change c ∈ ((point k (y * a') ⊔ point k (x * a)).1 : IntermediateField k K)
    rw [coe_sup_point₂]
    exact hcL₂
  have hCc := rankEq_two_sup_of_ne hne'
  have hL₁ : C.1 ⊔ point k c = (v 0).1 ⊔ (u 0).1 :=
    RankEq.eq_of_le (sup_le hC₀.le_sup hcle₁) hCc (rankEq_two_sup_of_ne hC₀.ne)
  have hL₂ : C.1 ⊔ point k c = (v 2).1 ⊔ (u 2).1 :=
    RankEq.eq_of_le (sup_le hC₂.le_sup hcle₂) hCc (rankEq_two_sup_of_ne hC₂.ne)
  -- Then `[xa]` lies on `[y] ⊔ [x]`, so `a` would be algebraic over `x, y`.
  have hxa : (u 2).1 ≤ (v 0).1 ⊔ (u 0).1 := le_sup_right.trans (hL₂.symm.trans hL₁).le
  rw [hu2, hv0, hu0] at hxa
  have hxa' : x * a ∈ racl k ({y, x} : Set K) := by
    have h' := point_le_iff.1 hxa
    change x * a ∈ ((point k y ⊔ point k x).1 : IntermediateField k K) at h'
    rwa [coe_sup_point₂] at h'
  have ha : a ∈ racl k ({y, x} : Set K) := by
    have h' := div_mem hxa' (subset_racl k ({y, x} : Set K)
      (Set.mem_insert_of_mem _ (Set.mem_singleton x)))
    have hx0 : x ≠ 0 := AlgebraicIndependent.ne_zero hind 0
    rwa [mul_div_cancel_left₀ a hx0] at h'
  have hna := AlgebraicIndependent.notMem_racl_image hind (S := {0, 1}) (i := 2) (by decide)
  rw [Set.image_insert_eq, Set.image_singleton] at hna
  exact hna (by rw [Set.pair_comm]; exact ha)

end AclGeom
