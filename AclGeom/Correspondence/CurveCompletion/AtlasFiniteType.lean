/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedAtlas
import AclGeom.Curves.DegreeBound

/-!
# Atlas Finite Type

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- The inverse of a separating parameter is again transcendental and gives the SAME finite
separable function-field extension. Named consumer: chartBaseHom_locallyOfFiniteType. -/
theorem separating_inverse (t : F) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    Transcendental k t⁻¹ ∧
      FiniteDimensional (IntermediateField.adjoin k ({t⁻¹} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
  have he := adjoin_inv_eq (k := k) t
  exact ⟨(fun h ↦ htr (IsAlgebraic.inv_iff.mp h)),
    (congrArg (fun E : IntermediateField k F ↦ FiniteDimensional E F) he).mpr inferInstance,
    (congrArg (fun E : IntermediateField k F ↦ Algebra.IsSeparable E F) he).mpr inferInstance⟩

/-- Both actual normalized chart morphisms are locally of finite type over the original base. Named
consumer: modelHom_locallyOfFiniteType. -/
theorem chartBaseHom_locallyOfFiniteType (t : F) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] (b : Bool) :
    LocallyOfFiniteType (chartBaseHom (k := k) t b) := by
  have hinv := separating_inverse t htr
  have := hinv.2.1
  have := hinv.2.2
  cases b
  · let := normalizedBaseAlgebra (k := k) t
    have : Algebra.FiniteType k (normalizedRing (k := k) t) :=
      (normalizedRing_properties t htr).2.2.2
    change LocallyOfFiniteType (Spec.map
      (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · let := normalizedBaseAlgebra (k := k) t⁻¹
    have : Algebra.FiniteType k (normalizedRing (k := k) t⁻¹) :=
      (normalizedRing_properties t⁻¹ hinv.1).2.2.2
    change LocallyOfFiniteType (Spec.map
      (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t⁻¹))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The actual model is locally of finite type, with every chart finiteness input proved internally.
Named consumer: modelHom_isProper. -/
theorem modelHom_locallyOfFiniteType (t : F) (ht : t ≠ 0) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    LocallyOfFiniteType (modelHom (k := k) t ht) := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  let : ∀ i : ULift.{u} Bool, LocallyOfFiniteType (chartBaseHom (k := k) t i.down) :=
    fun i ↦ chartBaseHom_locallyOfFiniteType t htr i.down
  exact WeilGluing.commonOverlapToBase_locallyOfFiniteType
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    (fun i ↦ chartBaseHom (k := k) t i.down) (overlapBaseHom (k := k) t)
    (fun i ↦ overlap_chart_base_comm (k := k) t i.down)

end
end AclGeom.CurveCompletion
