/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteExtensionChart
import AclGeom.Correspondence.PrincipalLocalization

/-!
# Principal-open maps between finite-extension charts

A field equivalence between the selected fraction fields of two
`FiniteExtensionChart`s restricts contravariantly to an embedding of the
target coordinate ring into the source fraction field.  Clearing the finitely
many target-generator denominators produces a dominant partial map from one
explicit dense principal open of the source chart to the target chart.

Applying this construction to an equivalence and its inverse is the algebraic
input for extracting a dense-open transition isomorphism.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry

universe u v w

namespace FiniteExtensionTransition

variable {k K₁ K₂ L₁ L₂ : Type u} {ι₁ : Type v} {ι₂ : Type w}
  [Field k] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra k K₁] [Algebra K₁ L₁] [Algebra k L₁]
  [IsScalarTower k K₁ L₁] [FiniteDimensional K₁ L₁]
  [Algebra k K₂] [Algebra K₂ L₂] [Algebra k L₂]
  [IsScalarTower k K₂ L₂] [FiniteDimensional K₂ L₂]

/-- The target coordinate ring embedded in the source fraction field by the
inverse of a field equivalence. -/
def transitionAlgHom (a₂ : ι₂ → K₂) (e : L₁ ≃ₐ[k] L₂) :
    FiniteExtensionChart.coordinateRing
        (k := k) (K := K₂) (L := L₂) a₂ →ₐ[k] L₁ :=
  e.symm.toAlgHom.comp (Subalgebra.val _)

omit [Algebra k K₂] [IsScalarTower k K₂ L₂] in
/-- The coordinate-ring homomorphism induced by a field equivalence is
injective. -/
theorem transitionAlgHom_injective (a₂ : ι₂ → K₂) (e : L₁ ≃ₐ[k] L₂) :
    Function.Injective (transitionAlgHom (k := k) a₂ e) :=
  e.symm.injective.comp Subtype.val_injective

/-- A field equivalence between finite-extension charts spreads to a
dominant partial map on one dense principal open of the source chart. -/
noncomputable def partialMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₁) (L := L₁) a₁).PartialMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  exact PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (transitionAlgHom (k := k) a₂ e)
    (transitionAlgHom_injective (k := k) a₂ e)

/-- The principal-open map induced by a finite-extension field equivalence is
dominant. -/
instance partialMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (e : L₁ ≃ₐ[k] L₂) :
    IsDominant (partialMap (k := k) a₁ a₂ ha₁ e).hom := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  change IsDominant (PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (transitionAlgHom (k := k) a₂ e)
    (transitionAlgHom_injective (k := k) a₂ e)).hom
  infer_instance

end FiniteExtensionTransition

end

end AclGeom
