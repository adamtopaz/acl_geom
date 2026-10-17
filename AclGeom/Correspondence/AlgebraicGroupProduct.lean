/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.MultiplicativeGroupScheme

/-!
# Products of algebraic groups and the two-dimensional torus

The product of two algebraic groups over a field `k` is their product as group objects over
`Spec k` (`AlgebraicGroup.prod`), and its `k`-points are pairs of points
(`AlgebraicGroup.prodPointsMulEquiv`). In particular the two-dimensional torus `Gₘ²`
(`multiplicativeGroupSq`) is commutative with points `kˣ × kˣ`, and over an algebraically closed
field its closed points are the pairs of units (`multiplicativeGroupSq.closedPointsEquiv`).

The named consumer is the curve-coset invocation in the proof of blueprint Theorem `mulcorr`, which
applies the curve-coset lemma in `Gₘ²`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** products, the torus `Gₘ²` and their point coordinates are constructed.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

/-- Morphisms into a product of monoid objects are pairs of morphisms, as monoids. -/
def homTensorMulEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {T M N : C} [MonObj M] [MonObj N] : (T ⟶ M ⊗ N) ≃* (T ⟶ M) × (T ⟶ N) where
  toFun p := (p ≫ fst M N, p ≫ snd M N)
  invFun q := lift q.1 q.2
  left_inv p := lift_comp_fst_snd p
  right_inv q := Prod.ext (lift_fst q.1 q.2) (lift_snd q.1 q.2)
  map_mul' p q := Prod.ext (MonObj.mul_comp p q (fst M N)) (MonObj.mul_comp p q (snd M N))

namespace AlgebraicGroup

variable {k : Type u} [Field k]

/-- The product of two algebraic groups over `k`. -/
def prod (G H : AlgebraicGroup k) : AlgebraicGroup k :=
  @ofGroupScheme k _ (G.toGroupScheme ⊗ H.toGroupScheme)
    (inferInstance : LocallyOfFiniteType
      (pullback.fst G.toGroupScheme.X.hom H.toGroupScheme.X.hom ≫ G.toGroupScheme.X.hom))
    (inferInstance : QuasiCompact
      (pullback.fst G.toGroupScheme.X.hom H.toGroupScheme.X.hom ≫ G.toGroupScheme.X.hom))

/-- A product of commutative algebraic groups is commutative. -/
instance (G H : AlgebraicGroup k) [IsCommMonObj G.toGroupScheme.X]
    [IsCommMonObj H.toGroupScheme.X] : IsCommMonObj (G.prod H).toGroupScheme.X :=
  (inferInstance : IsCommMonObj (G.toGroupScheme.X ⊗ H.toGroupScheme.X))

/-- The `k`-points of a product of algebraic groups are pairs of points. -/
def prodPointsMulEquiv (G H : AlgebraicGroup k) :
    (𝟙_ (Over (Spec (.of k))) ⟶ (G.prod H).toGroupScheme.X) ≃*
      (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) ×
        (𝟙_ (Over (Spec (.of k))) ⟶ H.toGroupScheme.X) :=
  homTensorMulEquiv

end AlgebraicGroup

variable (k : Type u) [Field k]

/-- The two-dimensional torus `Gₘ²` over `k`. -/
def multiplicativeGroupSq : AlgebraicGroup k :=
  (multiplicativeGroup k).prod (multiplicativeGroup k)

instance : IsCommMonObj (multiplicativeGroupSq k).toGroupScheme.X :=
  (inferInstance :
    IsCommMonObj ((multiplicativeGroup k).prod (multiplicativeGroup k)).toGroupScheme.X)

/-- The `k`-points of `Gₘ²` are the pairs of units of `k`. -/
def multiplicativeGroupSq.pointsMulEquiv :
    (𝟙_ (Over (Spec (.of k))) ⟶ (multiplicativeGroupSq k).toGroupScheme.X) ≃* kˣ × kˣ :=
  (AlgebraicGroup.prodPointsMulEquiv _ _).trans
    (MulEquiv.prodCongr (multiplicativeGroup.pointsMulEquiv k)
      (multiplicativeGroup.pointsMulEquiv k))

/-- Over an algebraically closed field, the closed points of `Gₘ²` are the pairs of units. -/
def multiplicativeGroupSq.closedPointsEquiv [IsAlgClosed k] :
    closedPoints (multiplicativeGroupSq k).carrier ≃ kˣ × kˣ :=
  GroupScheme.pointsEquivClosedPoints.symm.trans
    (multiplicativeGroupSq.pointsMulEquiv k).toEquiv

end

end AclGeom
