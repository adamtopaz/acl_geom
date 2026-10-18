/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ModelStalks
import AclGeom.Correspondence.CurveCompletion.CommonOverlapGeometry
import AclGeom.Correspondence.CurveCompletion.ChartValuativeLift
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Atlas Geometry

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

/-- Every map from the spectrum of a local ring into the actual model factors through an actual
normalization chart. Named consumer: modelHom_valuative_uniqueness. -/
theorem exists_chart_factor (t : F) (ht : t ≠ 0)
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ model (k := k) t ht) :
    ∃ (i : ULift.{u} Bool) (g : Spec (.of R) ⟶ chart (k := k) t i.down),
      g ≫ (atlas (k := k) t ht).ι i = f := by
  let D := atlas (k := k) t ht
  change ∃ (i : D.J) (g : Spec (.of R) ⟶ D.U i), g ≫ D.ι i = f
  obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective (f (IsLocalRing.closedPoint R))
  have : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  have hr : Set.range f ⊆ Set.range (D.ι i) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open
      (IsOpenImmersion.isOpen_range (D.ι i)) ⟨y, hy⟩
  refine ⟨i, IsOpenImmersion.lift (D.ι i) f hr, ?_⟩
  exact IsOpenImmersion.lift_fac (D.ι i) f hr

/-- The two actual normalized overlap maps agree after their actual chart inclusions. Named
consumer: overlap_glue_condition_bool. -/
theorem overlap_glue_condition (t : F) (ht : t ≠ 0) :
    overlapToChart (k := k) t false ≫ (atlas (k := k) t ht).ι ⟨false⟩ =
      overlapToChart (k := k) t true ≫ (atlas (k := k) t ht).ι ⟨true⟩ := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  exact WeilGluing.commonOverlap_glue_condition
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    ⟨false⟩ ⟨true⟩ (by decide)

/-- Either actual overlap/chart inclusion equals its opposite-chart composite. Named consumer:
modelHom_valuative_existence. -/
theorem overlap_glue_condition_bool (t : F) (ht : t ≠ 0) (b : Bool) :
    overlapToChart (k := k) t b ≫ (atlas (k := k) t ht).ι ⟨b⟩ =
      overlapToChart (k := k) t (!b) ≫ (atlas (k := k) t ht).ι ⟨!b⟩ := by
  cases b
  · exact overlap_glue_condition t ht
  · exact (overlap_glue_condition t ht).symm

/-- The SAME normalized overlap is the actual pullback of the two chart inclusions. Named consumer:
chart_model_maps_eq_of_fraction_field. -/
theorem overlap_isPullback (t : F) (ht : t ≠ 0) (b : Bool) :
    IsPullback (overlapToChart (k := k) t b) (overlapToChart (k := k) t (!b))
      ((atlas (k := k) t ht).ι ⟨b⟩) ((atlas (k := k) t ht).ι ⟨!b⟩) := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  exact WeilGluing.commonOverlap_isPullback
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    ⟨b⟩ ⟨!b⟩ (by cases b <;> decide)

end
end AclGeom.CurveCompletion
