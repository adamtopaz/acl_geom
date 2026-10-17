/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AlgebraicGroup
import AclGeom.Correspondence.HopfSpecPoints
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The multiplicative group as an algebraic group

The multiplicative group `Gₘ` over a field `k` is `Spec k[ℤ]`, the spectrum of the group algebra
`k[ℤ] = k[T, T⁻¹]` with its Hopf algebra structure (`multiplicativeGroup`). It is commutative, and
its `k`-points form the group `kˣ` (`multiplicativeGroup.pointsMulEquiv`): a point is the
evaluation `T ↦ u` at a unit `u`, and the group law of points is multiplication of units, because
`T` is group-like.

The named consumers are the curve-coset invocation in the proof of blueprint Theorem `mulcorr`
and the multiplicative factor of the affine group in blueprint Lemma `affine-action` (8.4a).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** `Gₘ` and its point group are constructed.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k]

/-- The group `ℤ` is finitely generated as an additive monoid. -/
instance addMonoid_fg_int : AddMonoid.FG ℤ :=
  AddGroup.fg_iff_addMonoid_fg.mp (Module.Finite.iff_addGroup_fg.mp inferInstance)

/-- The multiplicative group `Gₘ = Spec k[ℤ]` over a field, as an algebraic group. -/
def multiplicativeGroup : AlgebraicGroup k :=
  @AlgebraicGroup.ofGroupScheme k _
    (Grp.mk ((Spec (.of (AddMonoidAlgebra k ℤ))).asOver (Spec (.of k))))
    (locallyOfFiniteType_specOverSpec :
      LocallyOfFiniteType (Spec (.of (AddMonoidAlgebra k ℤ)) ↘ Spec (.of k)))
    (inferInstance : QuasiCompact (Spec (.of (AddMonoidAlgebra k ℤ)) ↘ Spec (.of k)))

/-- `Gₘ` is commutative. -/
instance : IsCommMonObj (multiplicativeGroup k).toGroupScheme.X :=
  (inferInstance : IsCommMonObj ((Spec (.of (AddMonoidAlgebra k ℤ))).asOver (Spec (.of k))))

/-- `k`-algebra maps `k[ℤ] → C` into a commutative `k`-algebra, under convolution, are the units of
`C`, through the value at the generator `T`. -/
def unitsMulEquivConv (C : Type*) [CommRing C] [Algebra k C] :
    WithConv (AddMonoidAlgebra k ℤ →ₐ[k] C) ≃* Cˣ :=
  MulEquiv.mk'
    ((WithConv.equiv _).trans <| (AddMonoidAlgebra.lift (R := k) (M := ℤ) (A := C)).symm.trans <|
      (⟨fun φ ↦ φ.toHomUnits, fun ψ ↦ (Units.coeHom C).comp ψ,
        fun φ ↦ MonoidHom.ext fun _ ↦ rfl, fun ψ ↦ MonoidHom.ext fun _ ↦ Units.ext rfl⟩ :
        (Multiplicative ℤ →* C) ≃ (Multiplicative ℤ →* Cˣ)).trans (zpowersHom Cˣ).symm)
    (fun f g ↦ Units.ext (by
      change (f * g) (AddMonoidAlgebra.single 1 1) =
        f (AddMonoidAlgebra.single 1 1) * g (AddMonoidAlgebra.single 1 1)
      rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply]
      simp))

/-- The unit attached to a `k`-algebra map `k[ℤ] → C` is its value at the generator `T`. -/
theorem unitsMulEquivConv_apply_val (C : Type*) [CommRing C] [Algebra k C]
    (f : WithConv (AddMonoidAlgebra k ℤ →ₐ[k] C)) :
    ((unitsMulEquivConv k C f : Cˣ) : C) = f (AddMonoidAlgebra.single 1 1) :=
  rfl

/-- The `k`-algebra map attached to a unit `u` sends the generator `T` to `u`. -/
theorem unitsMulEquivConv_symm_apply_single (C : Type*) [CommRing C] [Algebra k C] (u : Cˣ) :
    (unitsMulEquivConv k C).symm u (AddMonoidAlgebra.single 1 1) = u := by
  rw [← unitsMulEquivConv_apply_val, MulEquiv.apply_symm_apply]

/-- The `k`-points of `Gₘ` are the units of `k`. -/
def multiplicativeGroup.pointsMulEquiv :
    (𝟙_ (Over (Spec (.of k))) ⟶ (multiplicativeGroup k).toGroupScheme.X) ≃* kˣ :=
  (hopfPointsMulEquiv k (AddMonoidAlgebra k ℤ)).trans (unitsMulEquivConv k k)

end

end AclGeom
