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

end

end AclGeom
