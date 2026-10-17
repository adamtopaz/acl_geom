/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.ReducedSubscheme

/-!
# The generic-point hypothesis of the curve-coset lemma

Blueprint Lemma `curve-coset` assumes that the product of independent generic points of two curves
`A` and `B` in a group scheme `G` is generic in a curve `D`. In scheme language, the generic point
of the fibre product `A ×ₖ B` of the reduced induced subschemes is sent into `D` by
`(x, y) ↦ x * y`. This module derives from that hypothesis the closed-point form used by the
stabilizer argument: `a * b` is a point of `D` for all `k`-points `a` of `A` and `b` of `B`
(`mul_mem_of_genericPoint_mem`).

The preimage of `D` is closed and contains the generic point, so it is everything. Each `k`-point
of `G` lying in a closed set lifts to the reduced induced subscheme, because the spectrum of `k`
is reduced. A pair of `k`-points of `A` and `B` then gives a `k`-point of the product, which
`(x, y) ↦ x * y` sends to `a * b`.

The irreducibility of `A ×ₖ B` is a separate input of this auxiliary lemma. Over an algebraically
closed field, `CurveCosetSource` derives it internally from `IntegralProduct`. The final consumer
`curveCoset_of_genericProduct` also constructs the actual closed algebraic subgroup.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the closed-point consequence of the generic-point hypothesis is proved, for an
irreducible product.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

namespace GroupScheme

variable {k : Type u} [Field k] (G : Over (Spec (.of k)))

/-- The reduced induced closed subscheme on a closed subset of a `k`-scheme, as a `k`-scheme.
Named consumer: the generic-point hypothesis of the curve-coset lemma. -/
def reducedOver (Z : Closeds G.left) : Over (Spec (.of k)) :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ G.hom)

/-- The inclusion of the reduced induced closed subscheme, over `Spec k`. -/
def reducedOverι (Z : Closeds G.left) : reducedOver G Z ⟶ G :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

variable {G}

/-- A `k`-point of `G` whose closed point lies in `Z` has image in `Z`. -/
theorem range_left_subset_of_mem (Z : Closeds G.left) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ Z) :
    Set.range (p.left : Spec (.of k) ⟶ G.left) ⊆ Z := by
  rintro _ ⟨x, rfl⟩
  rwa [Subsingleton.elim (α := ↥(Spec (.of k))) x (IsLocalRing.closedPoint k)]

/-- A `k`-point of `G` whose closed point lies in `Z` lifts to the reduced induced subscheme. -/
def liftPoint (Z : Closeds G.left) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ Z) : 𝟙_ (Over (Spec (.of k))) ⟶ reducedOver G Z :=
  Over.homMk
    (liftToReducedSubscheme (Y := Spec (.of k)) Z p.left (range_left_subset_of_mem Z p hp))
    (by
      change liftToReducedSubscheme (Y := Spec (.of k)) Z p.left
          (range_left_subset_of_mem Z p hp) ≫
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ G.hom = 𝟙 _
      rw [← Category.assoc, liftToReducedSubscheme_subschemeι]
      exact Over.w p)

theorem liftPoint_comp_reducedOverι (Z : Closeds G.left) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ Z) : liftPoint Z p hp ≫ reducedOverι G Z = p :=
  Over.OverMorphism.ext (liftToReducedSubscheme_subschemeι (Y := Spec (.of k)) Z p.left
    (range_left_subset_of_mem Z p hp))

variable [GrpObj G]

/-- **The generic-point hypothesis of the curve-coset lemma gives its closed-point form.** If the
generic point of the product of the reduced induced subschemes on closed sets `A` and `B` is sent
into a closed set `D` by `(x, y) ↦ x * y`, then `a * b` lies in `D` for all `k`-points `a` of
`A` and `b` of `B`. The product is assumed irreducible. -/
theorem mul_mem_of_genericPoint_mem {A B : Closeds G.left} {D : Set G.left} (hD : IsClosed D)
    [IrreducibleSpace (reducedOver G A ⊗ reducedOver G B).left]
    (hgen : ((reducedOverι G A ⊗ₘ reducedOverι G B) ≫ μ[G]).left
      (genericPoint (reducedOver G A ⊗ reducedOver G B).left) ∈ D)
    (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (ha : a.left (IsLocalRing.closedPoint k) ∈ A)
    (hb : b.left (IsLocalRing.closedPoint k) ∈ B) :
    (a * b).left (IsLocalRing.closedPoint k) ∈ D := by
  -- The preimage of `D` is everything.
  have hall : ∀ x, ((reducedOverι G A ⊗ₘ reducedOverι G B) ≫ μ[G]).left x ∈ D := by
    intro x
    have hcl := hD.preimage ((reducedOverι G A ⊗ₘ reducedOverι G B) ≫ μ[G]).left.continuous
    have hmem : genericPoint (reducedOver G A ⊗ reducedOver G B).left ∈
        ((reducedOverι G A ⊗ₘ reducedOverι G B) ≫ μ[G]).left ⁻¹' D := hgen
    have hsub := closure_minimal (Set.singleton_subset_iff.2 hmem) hcl
    rw [genericPoint_closure] at hsub
    exact hsub (Set.mem_univ x)
  -- The pair `(a, b)` as a point of the product.
  have hpair : lift (liftPoint A a ha) (liftPoint B b hb) ≫
      (reducedOverι G A ⊗ₘ reducedOverι G B) ≫ μ[G] = a * b := by
    rw [lift_map_assoc, liftPoint_comp_reducedOverι, liftPoint_comp_reducedOverι, Hom.mul_def]
  rw [← hpair]
  exact hall ((lift (liftPoint A a ha) (liftPoint B b hb)).left (IsLocalRing.closedPoint k))

end GroupScheme

end

end AclGeom
