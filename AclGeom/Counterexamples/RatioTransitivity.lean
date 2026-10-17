/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.GenericArithmetic

/-!
# The blueprint's literal ratio relation is not transitive

Validation for issue #23, continuing `AclGeom.Counterexamples.GenericArithmetic`.  After Lemma
`ratio-semantics`, the blueprint ratio section asserts that reflexivity, symmetry and transitivity
of `RatioEq` follow from equality in `K`.  For the literal relation `BlueprintRatioEq` on pairs of
members of the Frobenius class `J₁ = [j(x, a)]`, transitivity fails
(`blueprintRatioEq_not_transitive`).

The literal graph `BlueprintJMul u v w` reads its second input `v` only through the points `v 0`
and `v 4`.  Since `[c²] = [c]`, a generic product `x · c² = d` gives `JMul(j(x, a), j(c, a),
j(d, a))` as well as `JMul(j(x, a), j(c², a), j(d, a))`.  For algebraically independent
`x, y, z, a` and `m = (j(y, a), j(z, a))`, this supplies monomial witnesses for

* `RatioEq((j(x, a), j(x, a)), m)`, with `c₁ = z/y`, `c₂ = xz/y²`, `d₁ = x(z/y)`,
  `d₂ = x(z/y)²`;
* `RatioEq(m, (j(x, a), j(x², a)))`, with `c₁ = z/y²`, `c₂ = z/(xy)`, `d₁ = x(z/(xy))`,
  `d₂ = x²(z/(xy))²`.

No witnesses relate `(j(x, a), j(x, a))` to `(j(x, a), j(x², a))`, for any base tuple.  This part
is purely geometric.  By the multiplication diagram, the output point of a derived product lies on
the line through its inputs, and its second input lies on the line through its first input and
its output.  The two products against the shared first input `j(x, a)` and the shared output `d₁`
force `c₁` and `c₂` to have the same `X` point.  The shared output `d₂` then lies on the two lines
joining that point to `[xa]` and to `[x²a]`, which contradicts the rank-three clause of the first
product.

The base field is arbitrary and `K` has transcendence degree at least five over it.
Reflexivity of the literal relation is proved separately over perfect ambient fields
in `Counterexamples.RatioReflexivity`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (refutation for issue #23).
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Geometry

/-- The incidences of a derived product: its inputs are distinct, its second input differs from
its output, the output lies on the line through the inputs, and the second input lies on the line
through the first input and the output. -/
private theorem MulPoint.incidence {U V W : Point k K} (h : MulPoint U V W) :
    U ≠ V ∧ V ≠ W ∧ W.1 ≤ U.1 ⊔ V.1 ∧ V.1 ≤ U.1 ⊔ W.1 := by
  obtain ⟨_, R, _, _, _, _, -, hd⟩ := h
  have hUV : U ≠ V := by simpa using hd.distinct.ne (show (0 : Fin 8) ≠ 1 by decide)
  have hUW : U ≠ W := by simpa using hd.distinct.ne (show (0 : Fin 8) ≠ 3 by decide)
  have hVW : V ≠ W := by simpa using hd.distinct.ne (show (1 : Fin 8) ≠ 3 by decide)
  have hV : V.1 ≤ U.1 ⊔ (V.1 ⊔ (W.1 ⊔ R.1)) := le_sup_of_le_right le_sup_left
  have hW : W.1 ≤ U.1 ⊔ (V.1 ⊔ (W.1 ⊔ R.1)) :=
    le_sup_of_le_right (le_sup_of_le_right le_sup_left)
  have hUV' : U.1 ⊔ V.1 = U.1 ⊔ (V.1 ⊔ (W.1 ⊔ R.1)) :=
    RankEq.eq_of_le (sup_le le_sup_left hV) (rankEq_two_sup_of_ne hUV) hd.line_XYEV
  have hUW' : U.1 ⊔ W.1 = U.1 ⊔ (V.1 ⊔ (W.1 ⊔ R.1)) :=
    RankEq.eq_of_le (sup_le le_sup_left hW) (rankEq_two_sup_of_ne hUW) hd.line_XYEV
  exact ⟨hUV, hVW, hW.trans hUV'.ge, hV.trans hUW'.ge⟩

/-- A point `D ≠ C` cannot lie on two lines `PC` and `P'C` whose join contains a rank-three
closed subfield: both lines would equal `CD`. -/
private theorem not_two_lines {P P' C D : Point k K} {E : ClosedIF k K} (hE : RankEq 3 E)
    (hEle : E ≤ P.1 ⊔ (P'.1 ⊔ C.1)) (hPC : P ≠ C) (hP'C : P' ≠ C) (hDC : D ≠ C)
    (hD : D.1 ≤ P.1 ⊔ C.1) (hD' : D.1 ≤ P'.1 ⊔ C.1) : False := by
  have hCD : RankEq 2 (C.1 ⊔ D.1) := rankEq_two_sup_of_ne hDC.symm
  have hL : C.1 ⊔ D.1 = P.1 ⊔ C.1 :=
    RankEq.eq_of_le (sup_le le_sup_right hD) hCD (rankEq_two_sup_of_ne hPC)
  have hL' : C.1 ⊔ D.1 = P'.1 ⊔ C.1 :=
    RankEq.eq_of_le (sup_le le_sup_right hD') hCD (rankEq_two_sup_of_ne hP'C)
  have hle : E ≤ P.1 ⊔ C.1 :=
    hEle.trans (sup_le le_sup_left (sup_le ((le_sup_left.trans hL'.ge).trans hL.le) le_sup_right))
  have hmono := (AlgebraicIndependent.matroid k K).eRk_mono
    (show (E : Set K) ⊆ ((P.1 ⊔ C.1 : ClosedIF k K) : Set K) from
      fun _ hz ↦ ClosedIF.le_iff.1 hle hz)
  rw [rankEq_iff_eRk.1 hE, rankEq_iff_eRk.1 (rankEq_two_sup_of_ne hPC)] at hmono
  exact absurd (Nat.cast_le.1 hmono) (by decide)

/-- **No literal ratio witnesses relate `(j(x, a), j(x, a))` to `(j(x, a), j(x², a))`**, for any
base tuple.  The argument uses only the incidences of derived products and the rank-three clause
of the first product. -/
private theorem not_blueprintRatioEq_sq (b : Fin 5 → Point k K) {x a : K}
    (h₁ : AlgebraicIndependent k ![x, a]) (h₂ : AlgebraicIndependent k ![x ^ 2, a]) :
    ¬ BlueprintRatioEq b (jTupleOf x a h₁, jTupleOf x a h₁)
      (jTupleOf x a h₁, jTupleOf (x ^ 2) a h₂) := by
  rintro ⟨c₁, c₂, _, d₂, -, -, -, -, ⟨-, -, hind, hX₁, -, hQ₁, -⟩, ⟨-, -, -, -, -, hQ₂, -⟩,
    ⟨-, -, -, hX₃, -, hQ₃, -⟩, ⟨-, -, -, -, -, hQ₄, -⟩⟩
  have hx0 : x ≠ 0 := fun h0 ↦ h₁.transcendental 0 (by
    change IsAlgebraic k x
    rw [h0]
    exact isAlgebraic_zero)
  have ha0 : a ≠ 0 := fun h0 ↦ h₁.transcendental 1 (by
    change IsAlgebraic k a
    rw [h0]
    exact isAlgebraic_zero)
  -- The coordinates `[a] ≤ [x] ∨ [xa]` and `[x], [a] ≤ [xa] ∨ [x²a]`.
  have hA : (jTupleOf x a h₁ 4).1 ≤ (jTupleOf x a h₁ 0).1 ⊔ (jTupleOf x a h₁ 2).1 := by
    change point k a ≤ point k x ⊔ point k (x * a)
    refine ClosedIF.point_le_iff.2 ?_
    change a ∈ ((point k x ⊔ point k (x * a)).1 : IntermediateField k K)
    rw [coe_sup_point₂]
    have h := div_mem (subset_racl k ({x, x * a} : Set K)
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (subset_racl k _ (Set.mem_insert _ _))
    rwa [mul_div_cancel_left₀ a hx0] at h
  have hX : (jTupleOf x a h₁ 0).1 ≤ (jTupleOf x a h₁ 2).1 ⊔ (jTupleOf (x ^ 2) a h₂ 2).1 := by
    change point k x ≤ point k (x * a) ⊔ point k (x ^ 2 * a)
    refine ClosedIF.point_le_iff.2 ?_
    change x ∈ ((point k (x * a) ⊔ point k (x ^ 2 * a)).1 : IntermediateField k K)
    rw [coe_sup_point₂]
    have h := div_mem (subset_racl k ({x * a, x ^ 2 * a} : Set K)
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (subset_racl k _ (Set.mem_insert _ _))
    rwa [(div_eq_iff (mul_ne_zero hx0 ha0)).2 (by ring : x ^ 2 * a = x * (x * a))] at h
  have hA' : (jTupleOf x a h₁ 4).1 ≤ (jTupleOf x a h₁ 2).1 ⊔ (jTupleOf (x ^ 2) a h₂ 2).1 := by
    change point k a ≤ point k (x * a) ⊔ point k (x ^ 2 * a)
    refine ClosedIF.point_le_iff.2 ?_
    change a ∈ ((point k (x * a) ⊔ point k (x ^ 2 * a)).1 : IntermediateField k K)
    rw [coe_sup_point₂]
    have h := div_mem (pow_mem (subset_racl k ({x * a, x ^ 2 * a} : Set K)
      (Set.mem_insert _ _)) 2) (subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rwa [(div_eq_iff (mul_ne_zero (pow_ne_zero 2 hx0) ha0)).2
      (by ring : (x * a) ^ 2 = a * (x ^ 2 * a))] at h
  -- The products against the shared input `j(x, a)` and output `d₁` force `c₂ 0 = c₁ 0`.
  have hC : c₂ 0 = c₁ 0 := by
    by_contra hne
    obtain ⟨hXC, -, hD₁, -⟩ := hX₁.incidence
    obtain ⟨-, -, -, hC₂X⟩ := hX₃.incidence
    obtain ⟨hQC, -, hE₁, -⟩ := hQ₁.incidence
    obtain ⟨-, -, -, hC₂Q⟩ := hQ₃.incidence
    exact not_two_lines (P := jTupleOf x a h₁ 0) (P' := jTupleOf x a h₁ 2) (C := c₁ 0)
      (D := c₂ 0) hind (sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_right)
        (hA.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_left)))))
      hXC hQC hne (hC₂X.trans (sup_le le_sup_left hD₁)) (hC₂Q.trans (sup_le le_sup_left hE₁))
  -- The shared output `d₂` then lies on the lines `[xa] c₁` and `[x²a] c₁`.
  rw [hC] at hQ₄
  obtain ⟨hQC, hCE, hE, -⟩ := hQ₂.incidence
  obtain ⟨hQ'C, -, hE', -⟩ := hQ₄.incidence
  exact not_two_lines (P := jTupleOf x a h₁ 2) (P' := jTupleOf (x ^ 2) a h₂ 2) (C := c₁ 0)
    (D := d₂ 2) hind (sup_le (hX.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_left)))
      (sup_le (le_sup_of_le_right le_sup_right)
        (hA'.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_left)))))
    hQC hQ'C hCE.symm hE hE'

end Geometry

section Witnesses

/-- The literal product graph reads its second input only through the points `v 0` and `v 4`. -/
private theorem BlueprintJMul.of_right {u v v' w : Fin 5 → Point k K} (h : BlueprintJMul u v w)
    (h₀ : v' 0 = v 0) (h₄ : v' 4 = v 4) : BlueprintJMul u v' w := by
  obtain ⟨e₁, e₂, hi, hm₀, hs, hm₂, hm₃⟩ := h
  rw [← h₀] at hi hm₀ hm₂ hm₃
  rw [← h₄] at e₁ e₂
  exact ⟨e₁, e₂, hi, hm₀, hs, hm₂, hm₃⟩

/-- The product of the first two entries of an independent triple is independent of the third. -/
private theorem pair_mul_of_triple {p q a : K} (h : AlgebraicIndependent k ![p, q, a]) :
    AlgebraicIndependent k ![p * q, a] := by
  have hq0 : q ≠ 0 := fun h0 ↦ h.transcendental 1 (by
    change IsAlgebraic k q
    rw [h0]
    exact isAlgebraic_zero)
  have h' : AlgebraicIndependent k ![p * q, q, a] := by
    refine AlgebraicIndependent.triple_of_mem h (fun i ↦ ?_) (fun i ↦ ?_)
    · fin_cases i
      · exact mul_mem (subset_racl k _ ⟨0, rfl⟩) (subset_racl k _ ⟨1, rfl⟩)
      · exact subset_racl k _ ⟨1, rfl⟩
      · exact subset_racl k _ ⟨2, rfl⟩
    · fin_cases i
      · have hpq : p * q ∈ racl k (Set.range ![p * q, q, a]) := subset_racl k _ ⟨0, rfl⟩
        have hq : q ∈ racl k (Set.range ![p * q, q, a]) := subset_racl k _ ⟨1, rfl⟩
        have hp := div_mem hpq hq
        rwa [mul_div_cancel_right₀ p hq0] at hp
      · exact subset_racl k _ ⟨1, rfl⟩
      · exact subset_racl k _ ⟨2, rfl⟩
  exact AlgebraicIndependent.pair_zero_two h'

variable (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)

include htr

/-- A generic product `p · q = d` satisfies the literal product graph. -/
private theorem blueprintJMul_of_mul {p q d a : K} (hpq : AlgebraicIndependent k ![p, q, a])
    (hd : AlgebraicIndependent k ![d, a]) (h : p * q = d) :
    BlueprintJMul (jTupleOf p a (AlgebraicIndependent.pair_zero_two hpq))
      (jTupleOf q a (AlgebraicIndependent.pair_one_two hpq)) (jTupleOf d a hd) := by
  have key : ∀ (u v : Fin 5 → Point k K) (t : K) (ht : AlgebraicIndependent k ![t, a]),
      t = d → BlueprintJMul u v (jTupleOf t a ht) → BlueprintJMul u v (jTupleOf d a hd) := by
    rintro _ _ _ _ rfl hj
    exact hj
  exact key _ _ _ _ (by rw [map_one, one_mul, h])
    (blueprintJMul_kappa hpq htr (one_ne_zero : (1 : k) ≠ 0))

/-- **The literal ratio relation is not transitive** (blueprint ratio section, after Lemma
`ratio-semantics`: "Reflexivity, symmetry, and transitivity of `RatioEq` now follow from equality
in `K`").  There is a Frobenius class `J₁ = [j(x, a)]` on whose pairs of members the literal
relation `BlueprintRatioEq` is not transitive (`IsTrans` fails). -/
theorem blueprintRatioEq_not_transitive :
    ∃ (x₀ a : K) (h₀ : AlgebraicIndependent k ![x₀, a]),
      ¬ IsTrans ({u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ×
          {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u}) fun r s ↦
        BlueprintRatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1) (s.1.1, s.2.1) := by
  classical
  obtain ⟨x, y, a, hind⟩ := exists_algebraicIndependent_triple htr
  obtain ⟨z, hz⟩ := fresh_four_of_five_le_trdeg htr {x, y, a}
    (Finset.card_le_three.trans (by norm_num))
  have hz' : z ∉ racl k ({x, y, a} : Set K) := by simpa using hz
  have hx0 : x ≠ 0 := fun h0 ↦ hind.transcendental 0 (by
    change IsAlgebraic k x
    rw [h0]
    exact isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h0 ↦ hind.transcendental 1 (by
    change IsAlgebraic k y
    rw [h0]
    exact isAlgebraic_zero)
  have hz0 : z ≠ 0 := fun h0 ↦ hz' (by rw [h0]; exact zero_mem _)
  have hxw : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyw : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
  -- Membership in `F = racl {x, y, a}`, and absorption of pairs over `F`.
  have hxF : x ∈ racl k ({x, y, a} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hyF : y ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have haF : a ∈ racl k ({x, y, a} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hsub : ∀ p ∈ racl k ({x, y, a} : Set K),
      racl k ({p, a} : Set K) ≤ racl k ({x, y, a} : Set K) := fun p hp ↦
    racl_le_of_subset_racl (Set.insert_subset hp (Set.singleton_subset_iff.2 haF))
  have hxa : AlgebraicIndependent k ![x, a] := AlgebraicIndependent.pair_zero_two hind
  have hya : AlgebraicIndependent k ![y, a] := AlgebraicIndependent.pair_one_two hind
  have hza : AlgebraicIndependent k ![z, a] :=
    AlgebraicIndependent.pair_zero_two (AlgebraicIndependent.insert_left hya fun h ↦
      hz' (racl_mono (Set.subset_insert _ _) h))
  have hx2a : AlgebraicIndependent k ![x ^ 2, a] :=
    (algebraicIndependent_congr_racl (v := ![x, a]) (w := ![x ^ 2, a])
      (Fin.forall_fin_two.2 ⟨(racl_pow x two_ne_zero).symm, rfl⟩)).1 hxa
  have hxya : x ∉ racl k ({y, a} : Set K) := by
    have h := AlgebraicIndependent.notMem_racl_image hind (S := {1, 2}) (i := 0) (by decide)
    rwa [Set.image_insert_eq, Set.image_singleton] at h
  -- The eight independent triples behind the generic products.
  have T₁ : AlgebraicIndependent k ![x, z / y, a] :=
    AlgebraicIndependent.insert_middle hxa fun h ↦ hz' (by
      have h' := mul_mem (hsub x hxF h) hyF
      rwa [div_mul_cancel₀ z hy0] at h')
  have T₂ : AlgebraicIndependent k ![x, (z / y) ^ 2, a] :=
    AlgebraicIndependent.insert_middle hxa fun h ↦ hz' (by
      have h' := mul_mem ((isRAC_racl _).mem_of_pow_mem two_ne_zero (hsub x hxF h)) hyF
      rwa [div_mul_cancel₀ z hy0] at h')
  have T₃ : AlgebraicIndependent k ![y, x * z / y ^ 2, a] :=
    AlgebraicIndependent.insert_middle hya fun h ↦ hz' (by
      have h' := div_mem (mul_mem (hsub y hyF h) (pow_mem hyF 2)) hxF
      rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hy0), mul_div_cancel_left₀ z hx0] at h')
  have T₄ : AlgebraicIndependent k ![z, x * z / y ^ 2, a] :=
    AlgebraicIndependent.insert_middle hza fun h ↦ hz' (by
      have hG : racl k ({z, a} : Set K) ≤ racl k (insert z ({y, a} : Set K)) :=
        racl_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2
          (Set.mem_insert_of_mem _ (Set.mem_singleton a))))
      have hyG : y ∈ racl k (insert z ({y, a} : Set K)) :=
        subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hzG : z ∈ racl k (insert z ({y, a} : Set K)) := subset_racl k _ (Set.mem_insert _ _)
      have hx := div_mem (mul_mem (hG h) (pow_mem hyG 2)) hzG
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hy0), mul_div_cancel_right₀ x hz0] at hx
      exact racl_exchange hx hxya)
  have T₅ : AlgebraicIndependent k ![x, z / (x * y), a] :=
    AlgebraicIndependent.insert_middle hxa fun h ↦ hz' (by
      have h' := mul_mem (hsub x hxF h) (mul_mem hxF hyF)
      rwa [div_mul_cancel₀ z (mul_ne_zero hx0 hy0)] at h')
  have T₆ : AlgebraicIndependent k ![x ^ 2, (z / (x * y)) ^ 2, a] :=
    AlgebraicIndependent.insert_middle hx2a fun h ↦ hz' (by
      have h' := mul_mem ((isRAC_racl _).mem_of_pow_mem two_ne_zero
        (hsub (x ^ 2) (pow_mem hxF 2) h)) (mul_mem hxF hyF)
      rwa [div_mul_cancel₀ z (mul_ne_zero hx0 hy0)] at h')
  have T₇ : AlgebraicIndependent k ![y, z / y ^ 2, a] :=
    AlgebraicIndependent.insert_middle hya fun h ↦ hz' (by
      have h' := mul_mem (hsub y hyF h) (pow_mem hyF 2)
      rwa [div_mul_cancel₀ z (pow_ne_zero 2 hy0)] at h')
  have T₈ : AlgebraicIndependent k ![z, z / y ^ 2, a] :=
    AlgebraicIndependent.insert_middle hza fun h ↦ hz' (by
      have hy2 := div_mem (subset_racl k ({z, a} : Set K) (Set.mem_insert _ _)) h
      rw [div_div_cancel₀ hz0] at hy2
      have hy := racl_exchange ((isRAC_racl _).mem_of_pow_mem two_ne_zero hy2)
        (AlgebraicIndependent.notMem_racl_pair' hya)
      exact racl_mono (Set.subset_insert _ _) hy)
  -- Every `j(p, a)` lies in the Frobenius class of `j(x, a)`.
  have hJ : ∀ (p : K) (hp : AlgebraicIndependent k ![p, a]),
      FrobEq (jTupleOf x a hxa) (jTupleOf p a hp) := fun _ hp ↦
    frobEq_jTupleOf_of_common htr hxa hp
  -- `RatioEq((j(x, a), j(x, a)), (j(y, a), j(z, a)))`.
  have hrm : BlueprintRatioEq (jTupleOf x a hxa) (jTupleOf x a hxa, jTupleOf x a hxa)
      (jTupleOf y a hya, jTupleOf z a hza) :=
    ⟨_, _, _, _, hJ _ (AlgebraicIndependent.pair_one_two T₁),
      hJ _ (AlgebraicIndependent.pair_one_two T₃),
      hJ _ (pair_mul_of_triple T₁), hJ _ (pair_mul_of_triple T₂),
      blueprintJMul_of_mul htr T₁ (pair_mul_of_triple T₁) rfl,
      (blueprintJMul_of_mul htr T₂ (pair_mul_of_triple T₂) rfl).of_right
        (Subtype.ext (point_pow (z / y) two_ne_zero).symm) (jTupleOf_four_eq _ _),
      blueprintJMul_of_mul htr T₃ (pair_mul_of_triple T₁) (by linear_combination (x * z / y) * hyw),
      blueprintJMul_of_mul htr T₄ (pair_mul_of_triple T₂) (by ring)⟩
  -- `RatioEq((j(y, a), j(z, a)), (j(x, a), j(x², a)))`.
  have hmt : BlueprintRatioEq (jTupleOf x a hxa) (jTupleOf y a hya, jTupleOf z a hza)
      (jTupleOf x a hxa, jTupleOf (x ^ 2) a hx2a) :=
    ⟨_, _, _, _, hJ _ (AlgebraicIndependent.pair_one_two T₇),
      hJ _ (AlgebraicIndependent.pair_one_two T₅),
      hJ _ (pair_mul_of_triple T₅), hJ _ (pair_mul_of_triple T₆),
      blueprintJMul_of_mul htr T₇ (pair_mul_of_triple T₅)
        (by linear_combination (z / y) * hyw - (z / y) * hxw),
      blueprintJMul_of_mul htr T₈ (pair_mul_of_triple T₆)
        (by linear_combination (-(z ^ 2 / y ^ 2) * (x * x⁻¹ + 1)) * hxw),
      blueprintJMul_of_mul htr T₅ (pair_mul_of_triple T₅) rfl,
      (blueprintJMul_of_mul htr T₆ (pair_mul_of_triple T₆) rfl).of_right
        (Subtype.ext (point_pow (z / (x * y)) two_ne_zero).symm) (jTupleOf_four_eq _ _)⟩
  refine ⟨x, a, hxa, fun htrans ↦ not_blueprintRatioEq_sq (jTupleOf x a hxa) hxa hx2a ?_⟩
  exact @IsTrans.trans _ _ htrans (⟨_, hJ x hxa⟩, ⟨_, hJ x hxa⟩) (⟨_, hJ y hya⟩, ⟨_, hJ z hza⟩)
    (⟨_, hJ x hxa⟩, ⟨_, hJ _ hx2a⟩) hrm hmt

end Witnesses

end AclGeom
