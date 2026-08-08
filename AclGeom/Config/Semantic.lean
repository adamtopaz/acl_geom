/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Equivalence

/-!
# The semantic relations Q, Q′, and J

The semantic configurations of blueprint Def semantic-configs: for points of
the geometry `𝒢(K/k)`, writing `[x]` for the principal closure
`ClosedIF.point k x`,

* `QSem X Y Z W`: some independent pair `x, y` has
  `(X, Y, Z, W) = ([x], [y], [x+y], [x/y])`;
* `Q'Sem X Y Z W`: likewise with `[xy]` in place of `[x/y]`;
* `JSem X`: the five-tuple `X` is `([x], [x+a], [xa], [x+xa], [a])` for some
  independent `x, a` (the image of the `j`-map).

The normalization identities (`[cx] = [x]`, `[x+c] = [x]`, invariance under
nonzero powers, inverses, and negation) are recorded at the level of
principal closures; the blueprint notes they need no extra theory beyond
the singleton-closure calculus of `AclGeom.Closure.Basic`.

By the blueprint's architecture rule, this file imports only closure/point
foundations — no geometric predicates.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

namespace ClosedIF

/-- Normalization: scaling by a nonzero constant of the base field does not
move a principal closure (blueprint §semantic relations). -/
theorem point_algebraMap_mul {c : k} (hc : c ≠ 0) (x : K) :
    point k (algebraMap k K c * x) = point k x :=
  Subtype.ext (racl_algebraMap_mul hc x)

/-- Normalization: translating by a constant of the base field does not
move a principal closure (blueprint §semantic relations). -/
theorem point_add_algebraMap (x : K) (c : k) :
    point k (x + algebraMap k K c) = point k x :=
  Subtype.ext (racl_add_algebraMap x c)

/-- Normalization: nonzero powers — in particular positive Frobenius
powers — do not move a principal closure (blueprint §semantic relations). -/
theorem point_pow (x : K) {n : ℕ} (hn : n ≠ 0) :
    point k (x ^ n) = point k x :=
  Subtype.ext (racl_pow x hn)

/-- Normalization: inversion does not move a principal closure. -/
theorem point_inv (x : K) : point k x⁻¹ = point k x :=
  Subtype.ext (racl_inv x)

/-- Normalization: negation does not move a principal closure. -/
theorem point_neg (x : K) : point k (-x) = point k x :=
  Subtype.ext (racl_neg x)

/-- A ratio and its reciprocal generate the same principal closure. -/
theorem point_div_symm (x y : K) : point k (x / y) = point k (y / x) := by
  rw [← point_inv (x / y), inv_div]

end ClosedIF

open ClosedIF

/-- The semantic relation `Q` (blueprint Def semantic-configs): the four
points are `([x], [y], [x+y], [x/y])` for some pair `x, y` algebraically
independent over `k`. -/
def QSem (X Y Z W : Point k K) : Prop :=
  ∃ x y : K, AlgebraicIndependent k ![x, y] ∧
    X.1 = point k x ∧ Y.1 = point k y ∧
    Z.1 = point k (x + y) ∧ W.1 = point k (x / y)

/-- The semantic relation `Q′` (blueprint Def semantic-configs): the four
points are `([x], [y], [x+y], [xy])` for some pair `x, y` algebraically
independent over `k`. -/
def Q'Sem (X Y Z W : Point k K) : Prop :=
  ∃ x y : K, AlgebraicIndependent k ![x, y] ∧
    X.1 = point k x ∧ Y.1 = point k y ∧
    Z.1 = point k (x + y) ∧ W.1 = point k (x * y)

/-- The semantic relation `J` (blueprint Def semantic-configs): the
five-tuple is the value `j(x, a) = ([x], [x+a], [xa], [x+xa], [a])` of the
`j`-map at some pair `x, a` algebraically independent over `k`. -/
def JSem (X : Fin 5 → Point k K) : Prop :=
  ∃ x a : K, AlgebraicIndependent k ![x, a] ∧
    (X 0).1 = point k x ∧ (X 1).1 = point k (x + a) ∧
    (X 2).1 = point k (x * a) ∧ (X 3).1 = point k (x + x * a) ∧
    (X 4).1 = point k a

/-- `QSem` is invariant under swapping the pair through the reciprocal
ratio: the witnesses `(x, y)` and `(y, x)` produce the same third
coordinate and reciprocal fourth coordinates, which generate the same
point. -/
theorem QSem.swap {X Y Z W : Point k K} (h : QSem X Y Z W) :
    QSem Y X Z W := by
  obtain ⟨x, y, hind, hX, hY, hZ, hW⟩ := h
  have hind' : AlgebraicIndependent k ![y, x] :=
    algebraicIndependent_pair (AlgebraicIndependent.notMem_racl_pair hind)
      (AlgebraicIndependent.notMem_racl_pair' hind)
  refine ⟨y, x, hind', hY, hX, ?_, ?_⟩
  · rwa [add_comm]
  · rw [hW, point_div_symm]

/-- `Q'Sem` is symmetric in its first two arguments. -/
theorem Q'Sem.swap {X Y Z W : Point k K} (h : Q'Sem X Y Z W) :
    Q'Sem Y X Z W := by
  obtain ⟨x, y, hind, hX, hY, hZ, hW⟩ := h
  have hind' : AlgebraicIndependent k ![y, x] :=
    algebraicIndependent_pair (AlgebraicIndependent.notMem_racl_pair hind)
      (AlgebraicIndependent.notMem_racl_pair' hind)
  refine ⟨y, x, hind', hY, hX, ?_, ?_⟩
  · rwa [add_comm]
  · rwa [mul_comm]

/-- **The projection identity** (blueprint end of §geometric definition
of J, semantic form): the semantic `Q` is the `P`-projection of the
semantic `J`. -/
theorem qSem_iff_exists_jSem {X Q R A : Point k K} :
    QSem X Q R A ↔ ∃ P : Point k K, JSem ![X, P, Q, R, A] := by
  constructor
  · rintro ⟨u, v, hpair, hX, hQ, hR, hA⟩
    have hu0 : u ∉ racl k (∅ : Set K) := fun h ↦
      AlgebraicIndependent.notMem_racl_pair' hpair
        (racl_mono (Set.empty_subset _) h)
    have hv0 : v ∉ racl k (∅ : Set K) := fun h ↦
      AlgebraicIndependent.notMem_racl_pair hpair
        (racl_mono (Set.empty_subset _) h)
    have hune : u ≠ 0 := by
      intro h0
      rw [h0] at hu0
      exact hu0 (zero_mem _)
    have hvu : v ∉ racl k ({u} : Set K) :=
      AlgebraicIndependent.notMem_racl_pair hpair
    -- The `a`-coordinate is the ratio `v/u`.
    have hratio_u : v / u ∉ racl k ({u} : Set K) := by
      intro h
      have hu : u ∈ racl k ({u} : Set K) := subset_racl k _ rfl
      have h2 := MulMemClass.mul_mem hu h
      rw [mul_div_cancel₀ v hune] at h2
      exact hvu h2
    have hu_ratio : u ∉ racl k ({v / u} : Set K) := by
      intro h
      have h' : u ∈ racl k (insert (v / u) (∅ : Set K)) := by simpa using h
      have h2 := racl_exchange h' hu0
      have h3 : v / u ∈ racl k ({u} : Set K) := by simpa using h2
      exact hratio_u h3
    have hpair' : AlgebraicIndependent k ![u, v / u] :=
      algebraicIndependent_pair hu_ratio hratio_u
    have hP0 : u + v / u ∉ (⊥ : ClosedIF k K) := by
      intro hbot
      refine hratio_u ?_
      have h0 : u + v / u ∈ racl k (∅ : Set K) :=
        mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 hbot)
      have hsum : u + v / u ∈ racl k ({u} : Set K) :=
        racl_mono (Set.empty_subset _) h0
      have hu : u ∈ racl k ({u} : Set K) := subset_racl k _ rfl
      have h2 := sub_mem hsum hu
      rwa [add_sub_cancel_left] at h2
    refine ⟨Point.mk' k (u + v / u) hP0, u, v / u, hpair', hX, rfl, ?_, ?_, ?_⟩
    · show Q.1 = point k (u * (v / u))
      rw [hQ]
      have harith : u * (v / u) = v := mul_div_cancel₀ v hune
      rw [harith]
    · show R.1 = point k (u + u * (v / u))
      rw [hR]
      have harith : u + u * (v / u) = u + v := by
        rw [mul_div_cancel₀ v hune]
      rw [harith]
    · show A.1 = point k (v / u)
      rw [hA]
      exact point_div_symm u v
  · rintro ⟨P, x, a, hpair, h0, h1, h2, h3, h4⟩
    have h0' : X.1 = point k x := h0
    have h2' : Q.1 = point k (x * a) := h2
    have h3' : R.1 = point k (x + x * a) := h3
    have h4' : A.1 = point k a := h4
    have hx0 : x ∉ racl k (∅ : Set K) := fun h ↦
      AlgebraicIndependent.notMem_racl_pair' hpair
        (racl_mono (Set.empty_subset _) h)
    have hxne : x ≠ 0 := by
      intro he
      rw [he] at hx0
      exact hx0 (zero_mem _)
    have hane : a ≠ 0 := by
      intro he
      have ha0 : a ∉ racl k (∅ : Set K) := fun h ↦
        AlgebraicIndependent.notMem_racl_pair hpair
          (racl_mono (Set.empty_subset _) h)
      rw [he] at ha0
      exact ha0 (zero_mem _)
    have hax : a ∉ racl k ({x} : Set K) :=
      AlgebraicIndependent.notMem_racl_pair hpair
    -- The pair `(x, xa)` is independent.
    have hprod_x : x * a ∉ racl k ({x} : Set K) := by
      intro hm
      have hxx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
      have h5 := MulMemClass.mul_mem (inv_mem hxx) hm
      rw [inv_mul_cancel_left₀ hxne] at h5
      exact hax h5
    have hx_prod : x ∉ racl k ({x * a} : Set K) := by
      intro hm
      have hm' : x ∈ racl k (insert (x * a) (∅ : Set K)) := by
        simpa using hm
      have h5 := racl_exchange hm' hx0
      have h6 : x * a ∈ racl k ({x} : Set K) := by simpa using h5
      exact hprod_x h6
    refine ⟨x, x * a, algebraicIndependent_pair hx_prod hprod_x,
      h0', h2', h3', ?_⟩
    rw [h4']
    have harith : x / (x * a) = a⁻¹ := by
      field_simp
    rw [harith, point_inv]

end

end AclGeom
