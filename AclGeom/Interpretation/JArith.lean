/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.FiniteRank

/-!
# Generic arithmetic on `j`-tuples by meets of joins (EH95, Lemma 2.11)

Evans and Hrushovski obtain the arithmetic of the fixed class of `j`-tuples from explicit
incidence configurations (EH95, Figures 4 and 5): every coordinate of `j(x - y, a)` and of
`j(x / y, a)` is the meet of two lines spanned by coordinates of `j(x, a)`, `j(y, a)` and
previously constructed points.  This file defines these two operations on five-tuples of closed
subfields, `jSub` and `jDiv`, and proves that they compute `j(x - y, a)` and `j(x / y, a)` when
`x, y, a` are independent.  The derived operations `jNeg`, `jInv`, `jAdd` and `jMul` follow
EH95: negation and inversion of `j(y, a)` use `j(x, a)` as auxiliary tuple, and
`x + y = x - (-y)`, `x y = x / y⁻¹`; they compute `j(-y, a)`, `j(y⁻¹, a)`, `j(x + y, a)` and
`j(x y, a)` under the same independence hypothesis (`jNeg_jC`, `jInv_jC`, `jAdd_jC`, `jMul_jC`).

The only geometric input is that two distinct lines meet in at most a point
(`inf_line_eq_point`): no correctness or completeness of `Q`/`Q′` is used.  The coordinate order
is `(X, P, Q, R, A)`, so `j(x, a) = ([x], [x + a], [x a], [x + x a], [a])`.

**Status:** the generic coordinate computations are proved (#23). `ClassArithmetic` proves
corrected fixed-class correctness, `Ratio` proves corrected ratio semantics, and `Field` proves
corrected total graphs, a named transported field structure and the actual decoding ring
equivalence under explicit perfection, rank-five and ACF J-completeness inputs. Unconditional
completeness, naturality and reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Close goals `e ∈ racl k S` in which `e` is a field expression in elements of `S`. -/
macro "racl_field" : tactic => `(tactic|
  repeat' (first
    | (refine subset_racl _ _ ?_; simp; done)
    | exact one_mem _
    | apply add_mem
    | apply sub_mem
    | apply mul_mem
    | apply div_mem
    | apply inv_mem
    | apply neg_mem))

section Lines

/-- Membership in a relative closure along an equation. -/
theorem mem_racl_of_eq {S : Set K} {e e' : K} (heq : e = e') (h : e' ∈ racl k S) :
    e ∈ racl k S :=
  heq ▸ h


/-- Two distinct lines meet in at most a point: if `t` lies on the line through `p, q` and on the
line through `r, s`, both pairs are independent and `r` is off the first line, then the meet of
the two lines is exactly the point `[t]`. -/
theorem inf_line_eq_point {p q r s t : K}
    (hpq : AlgebraicIndependent k ![p, q]) (hrs : AlgebraicIndependent k ![r, s])
    (hr : r ∉ racl k ({p, q} : Set K)) (ht : t ∉ (⊥ : ClosedIF k K))
    (htpq : t ∈ racl k ({p, q} : Set K)) (htrs : t ∈ racl k ({r, s} : Set K)) :
    (point k p ⊔ point k q) ⊓ (point k r ⊔ point k s) = point k t := by
  have hrank : ∀ {u v : K}, AlgebraicIndependent k ![u, v] →
      RankEq 2 (point k u ⊔ point k v) := by
    intro u v huv
    have h := rankEq_iSup_point huv
    refine h.congr ?_
    rw [sup_eq_iSup_two]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hmem : ∀ {u v z : K}, z ∈ racl k ({u, v} : Set K) →
      point k z ≤ point k u ⊔ point k v := by
    intro u v z hz
    rw [point_le_iff, ← SetLike.mem_coe]
    change z ∈ ((point k u ⊔ point k v).1 : Set K)
    rw [coe_sup_point₂]
    exact hz
  have hle : point k t ≤ (point k p ⊔ point k q) ⊓ (point k r ⊔ point k s) :=
    le_inf (hmem htpq) (hmem htrs)
  have htne : point k t ≠ ⊥ := fun h ↦ ht ((point_eq_bot_iff).1 h)
  by_cases hP : ∃ P : Point k K, P.1 ≤ point k p ⊔ point k q ∧
      (point k p ⊔ point k q) ⊓ (point k r ⊔ point k s) ≤ P.1
  · obtain ⟨P, -, hEP⟩ := hP
    have htP : point k t = P.1 :=
      ((P.2.le_iff.1 (hle.trans hEP)).resolve_left htne)
    exact le_antisymm (htP ▸ hEP) hle
  · simp only [not_exists, not_and] at hP
    exfalso
    have hE := RankEq.eq_of_le_of_not_le_point inf_le_left (hrank hpq)
      (fun P hP1 hP2 ↦ hP P hP1 hP2)
    have h12 : point k p ⊔ point k q ≤ point k r ⊔ point k s := inf_eq_left.1 hE
    have heq := RankEq.eq_of_le h12 (hrank hpq) (hrank hrs)
    apply hr
    have hr2 : r ∈ ((point k r ⊔ point k s).1 : Set K) := by
      rw [coe_sup_point₂]
      exact subset_racl k _ (by simp)
    rw [← heq, coe_sup_point₂] at hr2
    exact hr2

/-- A field element is transcendental once some element off a closure becomes algebraic after
adjoining it. -/
theorem notMem_bot_of_mem_racl_insert {t v : K} {S : Set K} (hv : v ∉ racl k S)
    (h : v ∈ racl k (insert t S)) : t ∉ (⊥ : ClosedIF k K) := by
  intro ht
  apply hv
  refine racl_le_of_subset_racl ?_ h
  rintro w (rfl | hw)
  · exact racl_mono (Set.empty_subset _)
      (mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 ht))
  · exact subset_racl k _ hw

/-- The first two entries of an independent triple are independent, and the third is off their
closure. -/
theorem AlgebraicIndependent.pair_and_notMem {p q r : K}
    (h : AlgebraicIndependent k ![p, q, r]) :
    AlgebraicIndependent k ![p, q] ∧ r ∉ racl k ({p, q} : Set K) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := h.comp ![0, 1] hinj
    convert this using 1
    funext i
    fin_cases i <;> rfl
  · have h2 := (algebraicIndependent_iff_forall_notMem_racl.1 h) 2
    have himage : (![p, q, r] '' {(2 : Fin 3)}ᶜ) = ({p, q} : Set K) := by
      ext z
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hi
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [himage] at h2
    exact h2

/-- Two independent triples sharing their spans make the line meet exact. -/
theorem inf_line_eq_point_of_triples {p q r s t : K}
    (h₁ : AlgebraicIndependent k ![p, q, r]) (h₂ : AlgebraicIndependent k ![r, s, p])
    (ht : t ∉ (⊥ : ClosedIF k K))
    (htpq : t ∈ racl k ({p, q} : Set K)) (htrs : t ∈ racl k ({r, s} : Set K)) :
    (point k p ⊔ point k q) ⊓ (point k r ⊔ point k s) = point k t :=
  inf_line_eq_point (AlgebraicIndependent.pair_and_notMem h₁).1
    (AlgebraicIndependent.pair_and_notMem h₂).1 (AlgebraicIndependent.pair_and_notMem h₁).2 ht
    htpq htrs

end Lines

section Operations

/-- The closed-lattice `j`-tuple `([x], [x + a], [x a], [x + x a], [a])`. -/
def jC (x a : K) : Fin 5 → ClosedIF k K :=
  ![point k x, point k (x + a), point k (x * a), point k (x + x * a), point k a]

/-- EH95, Fig. 4: the coordinates of the difference of two `j`-tuples with a common parameter,
as meets of joins. -/
def jSub (u v : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  let X := (u 0 ⊔ v 0) ⊓ (u 1 ⊔ v 1)
  ![X, (u 1 ⊔ v 0) ⊓ (u 4 ⊔ X), (u 2 ⊔ v 2) ⊓ (u 4 ⊔ X), (u 3 ⊔ v 3) ⊓ (u 4 ⊔ X), u 4]

/-- EH95, Fig. 5: the coordinates of the quotient of two `j`-tuples with a common parameter, as
meets of joins (using the auxiliary points `[x - y]` and `[x + y a]`). -/
def jDiv (u v : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  let D := (u 0 ⊔ v 0) ⊓ (u 1 ⊔ v 1)
  let X := (u 0 ⊔ v 0) ⊓ (u 2 ⊔ v 2)
  let T := (u 0 ⊔ v 2) ⊓ (D ⊔ v 3)
  ![X, (v 0 ⊔ T) ⊓ (u 4 ⊔ X), (v 0 ⊔ u 2) ⊓ (u 4 ⊔ X), (v 0 ⊔ u 3) ⊓ (u 4 ⊔ X), u 4]

end Operations

section Correctness

variable {x y a : K} (h : AlgebraicIndependent k ![x, y, a])
include h

namespace JArith

/-- Independence of a triple from mutual algebraicity with `x, y, a`. -/
theorem triple_of_span {u v w : K}
    (h₁ : u ∈ racl k ({x, y, a} : Set K)) (h₂ : v ∈ racl k ({x, y, a} : Set K))
    (h₃ : w ∈ racl k ({x, y, a} : Set K))
    (h₄ : x ∈ racl k ({u, v, w} : Set K)) (h₅ : y ∈ racl k ({u, v, w} : Set K))
    (h₆ : a ∈ racl k ({u, v, w} : Set K)) :
    AlgebraicIndependent k ![u, v, w] := by
  have hspan : racl k (Set.range ![x, y, a]) = racl k (Set.range ![u, v, w]) := by
    have e1 : Set.range ![x, y, a] = ({x, y, a} : Set K) := by
      ext z; simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    have e2 : Set.range ![u, v, w] = ({u, v, w} : Set K) := by
      ext z; simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [e1, e2]
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro z (rfl | rfl | rfl) <;> assumption
    · rintro z (rfl | rfl | rfl) <;> assumption
  refine algebraicIndependent_of_rankEq_iSup_point ?_
  exact (rankEq_iSup_point h).congr (iSup_point_congr hspan)

/-- The generic entries are nonzero. -/
theorem x_ne_zero : x ≠ 0 := fun h0 ↦ h.transcendental 0 (by simp [h0, isAlgebraic_zero])
/-- The generic entries are nonzero. -/
theorem y_ne_zero : y ≠ 0 := fun h0 ↦ h.transcendental 1 (by simp [h0, isAlgebraic_zero])
/-- The generic entries are nonzero. -/
theorem a_ne_zero : a ≠ 0 := fun h0 ↦ h.transcendental 2 (by simp [h0, isAlgebraic_zero])
/-- The parameter is not `-1`. -/
theorem one_add_a_ne_zero : 1 + a ≠ 0 := fun h0 ↦ h.transcendental 2 (by
  have ha : a = algebraMap k K (-1) := by rw [map_neg, map_one]; linear_combination h0
  change IsAlgebraic k a
  rw [ha]
  exact isAlgebraic_algebraMap _)

private theorem yx : x ∉ racl k ({y, a} : Set K) := by
  have h0 := (algebraicIndependent_iff_forall_notMem_racl.1 h) 0
  have himage : (![x, y, a] '' {(0 : Fin 3)}ᶜ) = ({y, a} : Set K) := by
    ext z
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i
      · exact absurd rfl hi
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  rw [himage] at h0
  exact h0

/-- A field expression `t` with `x` algebraic over `{t, y, a}` is transcendental. -/
private theorem tr {t : K} (ht : x ∈ racl k ({t, y, a} : Set K)) : t ∉ (⊥ : ClosedIF k K) :=
  notMem_bot_of_mem_racl_insert (yx h) ht

/-- Fig. 4: `[x - y] = ([x] ⊔ [y]) ⊓ ([x + a] ⊔ [y + a])`. -/
theorem jSub_X : (point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a)) =
    point k (x - y) := by
  refine inf_line_eq_point_of_triples (r := x + a) (s := y + a)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (by racl_field) (mem_racl_of_eq (show a = (x + a) - x by ring) (by racl_field)))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show y = (y + a) - ((x + a) - x) by ring) (by racl_field))
      (mem_racl_of_eq (show a = (x + a) - x by ring) (by racl_field)))
    (tr h (mem_racl_of_eq (show x = (x - y) + y by ring) (by racl_field))) (by racl_field)
    (mem_racl_of_eq (show x - y = (x + a) - (y + a) by ring) (by racl_field))

/-- Fig. 4: `[x - y + a] = ([x + a] ⊔ [y]) ⊓ ([a] ⊔ [x - y])`. -/
theorem jSub_P : (point k (x + a) ⊔ point k y) ⊓ (point k a ⊔ point k (x - y)) =
    point k (x - y + a) := by
  refine inf_line_eq_point_of_triples (r := a) (s := x - y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + a) - a by ring) (by racl_field))
        (by racl_field) (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + a) - a by ring) (by racl_field))
      (mem_racl_of_eq (show y = ((x + a) - a) - (x - y) by ring) (by racl_field)) (by racl_field))
    (tr h (mem_racl_of_eq (show x = (x - y + a) + y - a by ring) (by racl_field)))
    (mem_racl_of_eq (show x - y + a = (x + a) - y by ring) (by racl_field))
    (by racl_field)

/-- Fig. 4: `[(x - y) a] = ([x a] ⊔ [y a]) ⊓ ([a] ⊔ [x - y])`. -/
theorem jSub_Q : (point k (x * a) ⊔ point k (y * a)) ⊓ (point k a ⊔ point k (x - y)) =
    point k ((x - y) * a) := by
  have ha := a_ne_zero h
  refine inf_line_eq_point_of_triples (r := a) (s := x - y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x * a) / a by field_simp) (by racl_field))
      (mem_racl_of_eq (show y = (y * a) / a by field_simp) (by racl_field)) (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x * a) / a by field_simp) (by racl_field))
      (mem_racl_of_eq (show y = (x * a) / a - (x - y) by field_simp; ring) (by racl_field))
      (by racl_field))
    (tr h (mem_racl_of_eq (show x = (x - y) * a / a + y by field_simp; ring) (by racl_field)))
    (mem_racl_of_eq (show (x - y) * a = x * a - y * a by ring) (by racl_field))
    (by racl_field)

/-- Fig. 4: `[(x - y) + (x - y) a] = ([x + x a] ⊔ [y + y a]) ⊓ ([a] ⊔ [x - y])`. -/
theorem jSub_R : (point k (x + x * a) ⊔ point k (y + y * a)) ⊓ (point k a ⊔ point k (x - y)) =
    point k (x - y + (x - y) * a) := by
  have ha := one_add_a_ne_zero h
  refine inf_line_eq_point_of_triples (r := a) (s := x - y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + x * a) / (1 + a) by field_simp) (by racl_field))
      (mem_racl_of_eq (show y = (y + y * a) / (1 + a) by field_simp)
        (by racl_field)) (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + x * a) / (1 + a) by field_simp) (by racl_field))
      (mem_racl_of_eq (show y = (x + x * a) / (1 + a) - (x - y) by field_simp; ring)
        (by racl_field))
      (by racl_field))
    (tr h
      (mem_racl_of_eq (show x = (x - y + (x - y) * a) / (1 + a) + y by field_simp; ring)
        (by racl_field)))
    (mem_racl_of_eq (show x - y + (x - y) * a = (x + x * a) - (y + y * a) by ring) (by racl_field))
    (by racl_field)

/-- Fig. 5: `[x / y] = ([x] ⊔ [y]) ⊓ ([x a] ⊔ [y a])`. -/
theorem jDiv_X : (point k x ⊔ point k y) ⊓ (point k (x * a) ⊔ point k (y * a)) =
    point k (x / y) := by
  have hx := x_ne_zero h
  have hy := y_ne_zero h
  have ha := a_ne_zero h
  refine inf_line_eq_point_of_triples (r := x * a) (s := y * a)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (by racl_field) (mem_racl_of_eq (show a = (x * a) / x by field_simp) (by racl_field)))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show y = (y * a) / ((x * a) / x) by field_simp) (by racl_field))
      (mem_racl_of_eq (show a = (x * a) / x by field_simp) (by racl_field)))
    (tr h (mem_racl_of_eq (show x = (x / y) * y by field_simp) (by racl_field)))
    (by racl_field)
    (mem_racl_of_eq (show x / y = (x * a) / (y * a) by field_simp) (by racl_field))

/-- Fig. 5 (auxiliary): `[x + y a] = ([x] ⊔ [y a]) ⊓ ([x - y] ⊔ [y + y a])`. -/
theorem jDiv_T : (point k x ⊔ point k (y * a)) ⊓ (point k (x - y) ⊔ point k (y + y * a)) =
    point k (x + y * a) := by
  have hy := y_ne_zero h
  refine inf_line_eq_point_of_triples (r := x - y) (s := y + y * a)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show y = x - (x - y) by ring) (by racl_field))
      (mem_racl_of_eq (show a = (y * a) / (x - (x - y)) by rw [sub_sub_cancel]; field_simp)
        (by racl_field)))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show y = x - (x - y) by ring) (by racl_field))
      (mem_racl_of_eq
        (show a = (y + y * a) / (x - (x - y)) - 1 by rw [sub_sub_cancel]; field_simp; ring)
        (by racl_field)))
    (tr h (mem_racl_of_eq (show x = (x + y * a) - y * a by ring) (by racl_field)))
    (by racl_field)
    (mem_racl_of_eq (show x + y * a = (x - y) + (y + y * a) by ring) (by racl_field))

/-- Fig. 5: `[x / y + a] = ([y] ⊔ [x + y a]) ⊓ ([a] ⊔ [x / y])`. -/
theorem jDiv_P : (point k y ⊔ point k (x + y * a)) ⊓ (point k a ⊔ point k (x / y)) =
    point k (x / y + a) := by
  have hy := y_ne_zero h
  refine inf_line_eq_point_of_triples (r := a) (s := x / y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + y * a) - y * a by ring) (by racl_field))
        (by racl_field) (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x / y) * y by field_simp) (by racl_field))
        (by racl_field) (by racl_field))
    (tr h (mem_racl_of_eq (show x = (x / y + a - a) * y by field_simp; ring) (by racl_field)))
    (mem_racl_of_eq (show x / y + a = (x + y * a) / y by field_simp) (by racl_field))
    (by racl_field)

/-- Fig. 5: `[(x / y) a] = ([y] ⊔ [x a]) ⊓ ([a] ⊔ [x / y])`. -/
theorem jDiv_Q : (point k y ⊔ point k (x * a)) ⊓ (point k a ⊔ point k (x / y)) =
    point k (x / y * a) := by
  have hy := y_ne_zero h
  have ha := a_ne_zero h
  refine inf_line_eq_point_of_triples (r := a) (s := x / y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x * a) / a by field_simp) (by racl_field))
        (by racl_field) (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x / y) * y by field_simp) (by racl_field))
        (by racl_field) (by racl_field))
    (tr h (mem_racl_of_eq (show x = (x / y * a) / a * y by field_simp) (by racl_field)))
    (mem_racl_of_eq (show x / y * a = (x * a) / y by field_simp) (by racl_field))
    (by racl_field)

/-- Fig. 5: `[x / y + (x / y) a] = ([y] ⊔ [x + x a]) ⊓ ([a] ⊔ [x / y])`. -/
theorem jDiv_R : (point k y ⊔ point k (x + x * a)) ⊓ (point k a ⊔ point k (x / y)) =
    point k (x / y + x / y * a) := by
  have hy := y_ne_zero h
  have ha := one_add_a_ne_zero h
  refine inf_line_eq_point_of_triples (r := a) (s := x / y)
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x + x * a) / (1 + a) by field_simp)
        (by racl_field)) (by racl_field)
      (by racl_field))
    (triple_of_span h (by racl_field) (by racl_field) (by racl_field)
      (mem_racl_of_eq (show x = (x / y) * y by field_simp) (by racl_field))
        (by racl_field) (by racl_field))
    (tr h (mem_racl_of_eq (show x = (x / y + x / y * a) / (1 + a) * y by field_simp)
      (by racl_field)))
    (mem_racl_of_eq (show x / y + x / y * a = (x + x * a) / y by field_simp) (by racl_field))
    (by racl_field)

end JArith

open JArith

/-- **EH95, Lemma 2.11, Fig. 4.** For independent `x, y, a`, the meet/join construction
`jSub` computes `j(x - y, a)` from `j(x, a)` and `j(y, a)`. -/
theorem jSub_jC : jSub (jC (k := k) x a) (jC y a) = jC (x - y) a := by
  have hX := jSub_X h
  funext i
  fin_cases i
  · exact hX
  · change (point k (x + a) ⊔ point k y) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a))) =
      point k (x - y + a)
    rw [hX]
    exact jSub_P h
  · change (point k (x * a) ⊔ point k (y * a)) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a))) =
      point k ((x - y) * a)
    rw [hX]
    exact jSub_Q h
  · change (point k (x + x * a) ⊔ point k (y + y * a)) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a))) =
      point k (x - y + (x - y) * a)
    rw [hX]
    exact jSub_R h
  · rfl

/-- **EH95, Lemma 2.11, Fig. 5.** For independent `x, y, a`, the meet/join construction
`jDiv` computes `j(x / y, a)` from `j(x, a)` and `j(y, a)`. -/
theorem jDiv_jC : jDiv (jC (k := k) x a) (jC y a) = jC (x / y) a := by
  have hX := jDiv_X h
  have hD := jSub_X h
  have hT : (point k x ⊔ point k (y * a)) ⊓
      ((point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a)) ⊔ point k (y + y * a)) =
      point k (x + y * a) := by
    rw [hD]
    exact jDiv_T h
  funext i
  fin_cases i
  · exact hX
  · change (point k y ⊔ (point k x ⊔ point k (y * a)) ⊓
        ((point k x ⊔ point k y) ⊓ (point k (x + a) ⊔ point k (y + a)) ⊔
          point k (y + y * a))) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x * a) ⊔ point k (y * a))) =
      point k (x / y + a)
    rw [hT, hX]
    exact jDiv_P h
  · change (point k y ⊔ point k (x * a)) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x * a) ⊔ point k (y * a))) =
      point k (x / y * a)
    rw [hX]
    exact jDiv_Q h
  · change (point k y ⊔ point k (x + x * a)) ⊓
        (point k a ⊔ (point k x ⊔ point k y) ⊓ (point k (x * a) ⊔ point k (y * a))) =
      point k (x / y + x / y * a)
    rw [hX]
    exact jDiv_R h
  · rfl

end Correctness

section Derived

/-- Negation of `v` through an auxiliary tuple `z` (EH95, after Lemma 2.11):
`-y = (z - y) - z`. -/
def jNeg (v z : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  jSub (jSub z v) z

/-- Inversion of `v` through an auxiliary tuple `z`: `y⁻¹ = (z / y) / z`. -/
def jInv (v z : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  jDiv (jDiv z v) z

/-- Addition, using `u` as the auxiliary tuple for the negation of `v`: `x + y = x - (-y)`. -/
def jAdd (u v : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  jSub u (jNeg v u)

/-- Multiplication, using `u` as the auxiliary tuple for the inversion of `v`:
`x y = x / y⁻¹`. -/
def jMul (u v : Fin 5 → ClosedIF k K) : Fin 5 → ClosedIF k K :=
  jDiv u (jInv v u)

variable {x y a : K} (h : AlgebraicIndependent k ![x, y, a])
include h

namespace JArith

/-- `(x - y, x, a)` is independent. -/
theorem triple_sub_x : AlgebraicIndependent k ![x - y, x, a] :=
  triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
    (mem_racl_of_eq (show y = x - (x - y) by ring) (by racl_field)) (by racl_field)

/-- `(x / y, x, a)` is independent. -/
theorem triple_div_x : AlgebraicIndependent k ![x / y, x, a] := by
  have hx := x_ne_zero h
  have hy := y_ne_zero h
  exact triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
    (mem_racl_of_eq (show y = x / (x / y) by field_simp) (by racl_field)) (by racl_field)

/-- `(x, -y, a)` is independent. -/
theorem triple_x_neg : AlgebraicIndependent k ![x, -y, a] :=
  triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
    (mem_racl_of_eq (show y = -(-y) by ring) (by racl_field)) (by racl_field)

/-- `(x, y⁻¹, a)` is independent. -/
theorem triple_x_inv : AlgebraicIndependent k ![x, y⁻¹, a] :=
  triple_of_span h (by racl_field) (by racl_field) (by racl_field) (by racl_field)
    (mem_racl_of_eq (show y = (y⁻¹)⁻¹ by rw [inv_inv]) (by racl_field)) (by racl_field)

end JArith

open JArith

/-- Negation of `j(y, a)` through `j(x, a)`, for independent `x, y, a`. -/
theorem jNeg_jC : jNeg (jC (k := k) y a) (jC x a) = jC (-y) a := by
  rw [jNeg, jSub_jC h, jSub_jC (triple_sub_x h)]
  exact congrArg (jC · a) (by ring)

/-- Inversion of `j(y, a)` through `j(x, a)`, for independent `x, y, a`. -/
theorem jInv_jC : jInv (jC (k := k) y a) (jC x a) = jC y⁻¹ a := by
  have hx := x_ne_zero h
  have hy := y_ne_zero h
  rw [jInv, jDiv_jC h, jDiv_jC (triple_div_x h)]
  exact congrArg (jC · a) (by field_simp)

/-- **Generic addition** (EH95 Lemma 2.11 consequence): for independent `x, y, a`,
`jAdd (j(x, a)) (j(y, a)) = j(x + y, a)`. -/
theorem jAdd_jC : jAdd (jC (k := k) x a) (jC y a) = jC (x + y) a := by
  rw [jAdd, jNeg_jC h, jSub_jC (triple_x_neg h)]
  exact congrArg (jC · a) (by ring)

/-- **Generic multiplication** (EH95 Lemma 2.11 consequence): for independent `x, y, a`,
`jMul (j(x, a)) (j(y, a)) = j(x y, a)`. -/
theorem jMul_jC : jMul (jC (k := k) x a) (jC y a) = jC (x * y) a := by
  rw [jMul, jInv_jC h, jDiv_jC (triple_x_inv h)]
  exact congrArg (jC · a) (by rw [div_inv_eq_mul])

end Derived

end AclGeom
