/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.InverseNormalizedLocalization
import AclGeom.Correspondence.WeilGluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Normalized Atlas

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
attribute [local instance] normalizedOverlapAlgebra inverseNormalizedOverlapAlgebra

/-- One of the two actual affine normalization schemes, indexed by a Boolean. Named consumer:
atlas. -/
abbrev chart (t : F) (b : Bool) : Scheme.{u} :=
  Spec (.of (normalizedRing (k := k) (if b then t⁻¹ else t)))

/-- The actual spectrum map from the SAME normalized overlap to either affine chart. Named consumer:
atlas. -/
def overlapToChart (t : F) (b : Bool) :
    Spec (.of (normalizedOverlap (k := k) t)) ⟶ chart (k := k) t b := by
  cases b
  · exact Spec.map (CommRingCat.ofHom (normalizedToOverlap t))
  · exact Spec.map (CommRingCat.ofHom (inverseNormalizedToOverlap t))

/-- Both actual overlap maps are open immersions, proved from their literal principal localizations.
Named consumer: atlas. -/
theorem overlapToChart_isOpenImmersion (t : F) (ht : t ≠ 0) (b : Bool) :
    IsOpenImmersion (overlapToChart (k := k) t b) := by
  cases b
  · have := normalizedOverlap_isLocalization (k := k) t ht
    exact IsOpenImmersion.of_isLocalization
      (algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t) (parameter t))
  · have := inverseNormalizedOverlap_isLocalization (k := k) t ht
    exact IsOpenImmersion.of_isLocalization
      (algebraMap (parameterRing (k := k) t⁻¹) (normalizedRing (k := k) t⁻¹) (parameter t⁻¹))

/-- The actual two-normalization-chart atlas. Its maps are the literal localization
maps, not supplied gluing certificates. Named consumer: the actual proper curve model. -/
def atlas (t : F) (ht : t ≠ 0) : Scheme.GlueData.{u} := by
  letI : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  exact WeilGluing.commonOverlapGlueData (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)

/-- The actual scheme obtained by gluing the two normalization charts. Named consumer:
exists_proper_normal_completion. -/
def model (t : F) (ht : t ≠ 0) : Scheme.{u} := (atlas (k := k) t ht).glued

/-- The actual glued normalization model is integral. Named consumer:
exists_proper_normal_completion. -/
instance model_integral (t : F) (ht : t ≠ 0) : IsIntegral (model (k := k) t ht) := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  let : ∀ i : ULift.{u} Bool, IsIntegral (chart (k := k) t i.down) := by
    rintro ⟨b⟩
    cases b <;> simp only [chart] <;> infer_instance
  exact WeilGluing.commonOverlap_isIntegral
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)

/-- The actual chart structure morphism to the original base field. Named consumer: modelHom. -/
def chartBaseHom (t : F) (b : Bool) : chart (k := k) t b ⟶ Spec (.of k) := by
  cases b
  · letI := normalizedBaseAlgebra (k := k) t
    exact Spec.map (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t)))
  · letI := normalizedBaseAlgebra (k := k) t⁻¹
    exact Spec.map (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t⁻¹)))

/-- Each actual chart structure morphism is affine. Named consumer: modelHom_quasiCompact. -/
theorem chartBaseHom_isAffine (t : F) (b : Bool) : IsAffineHom (chartBaseHom (k := k) t b) := by
  cases b
  · let := normalizedBaseAlgebra (k := k) t
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t))))
    exact isAffineHom_of_isAffine _
  · let := normalizedBaseAlgebra (k := k) t⁻¹
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t⁻¹))))
    exact isAffineHom_of_isAffine _

/-- The normalized overlap's actual structure morphism to the original base field. Named consumer:
modelHom. -/
def overlapBaseHom (t : F) : Spec (.of (normalizedOverlap (k := k) t)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (normalizedOverlap (k := k) t)))

/-- Both actual overlap/chart structure diagrams commute. Named consumer: modelHom. -/
theorem overlap_chart_base_comm (t : F) (b : Bool) :
    overlapToChart (k := k) t b ≫ chartBaseHom (k := k) t b = overlapBaseHom (k := k) t := by
  cases b
  · change Spec.map (CommRingCat.ofHom (normalizedToOverlap t)) ≫
      Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  · change Spec.map (CommRingCat.ofHom (inverseNormalizedToOverlap t)) ≫
      Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1

/-- The actual structure morphism of the glued model, constructed by compatible chart descent. Named
consumer: modelHom_isProper. -/
def modelHom (t : F) (ht : t ≠ 0) : model (k := k) t ht ⟶ Spec (.of k) := by
  letI : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  exact WeilGluing.commonOverlapToBase
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    (fun i ↦ chartBaseHom (k := k) t i.down) (overlapBaseHom (k := k) t)
    (fun i ↦ overlap_chart_base_comm (k := k) t i.down)

/-- The actual glued model as a scheme over the original base field. Named consumer:
exists_proper_normal_completion. -/
def curve (t : F) (ht : t ≠ 0) : Over (Spec (.of k)) := Over.mk (modelHom (k := k) t ht)

/-- Each actual chart inclusion commutes with the descended structure morphism. Named consumer:
modelHom_locallyOfFiniteType. -/
theorem chart_modelHom (t : F) (ht : t ≠ 0) (i : ULift.{u} Bool) :
    (atlas (k := k) t ht).ι i ≫ modelHom (k := k) t ht = chartBaseHom (k := k) t i.down := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  exact WeilGluing.commonOverlap_ι_toBase
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    (fun i ↦ chartBaseHom (k := k) t i.down) (overlapBaseHom (k := k) t)
    (fun i ↦ overlap_chart_base_comm (k := k) t i.down) i

/-- The actual two-chart model is quasi-compact over the original base field. Named consumer:
modelHom_isProper. -/
instance modelHom_quasiCompact (t : F) (ht : t ≠ 0) : QuasiCompact (modelHom (k := k) t ht) := by
  let : ∀ i : ULift.{u} Bool, IsOpenImmersion (overlapToChart (k := k) t i.down) :=
    fun i ↦ overlapToChart_isOpenImmersion t ht i.down
  let : ∀ i : ULift.{u} Bool, QuasiCompact (chartBaseHom (k := k) t i.down) := by
    intro i
    have := chartBaseHom_isAffine (k := k) t i.down
    infer_instance
  exact WeilGluing.commonOverlapToBase_quasiCompact
    (fun i : ULift.{u} Bool ↦ chart (k := k) t i.down)
    (Spec (.of (normalizedOverlap (k := k) t))) (fun i ↦ overlapToChart (k := k) t i.down)
    (fun i ↦ chartBaseHom (k := k) t i.down) (overlapBaseHom (k := k) t)
    (fun i ↦ overlap_chart_base_comm (k := k) t i.down)

end
end AclGeom.CurveCompletion
