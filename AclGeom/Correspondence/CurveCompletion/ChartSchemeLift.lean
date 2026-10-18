/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedAtlas
import AclGeom.Correspondence.CurveCompletion.ChartValuativeLift
/-!
# Chart Scheme Lift

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
attribute [local instance] normalizedBaseAlgebra

/-- An actual normalized-chart scheme map extends over an integrally closed fraction ring when its
parameter lies there, with BOTH actual scheme diagrams. Named consumer:
exists_model_lift_from_chart. -/
theorem exists_chart_scheme_lift (t : F) (htr : Transcendental k t)
    {O K : Type u} [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] [IsIntegrallyClosed O]
    (q : Spec (.of K) ⟶ Spec (.of (normalizedRing (k := k) t)))
    (s : Spec (.of O) ⟶ Spec (.of k))
    (hq : q ≫ Spec.algebraMap k (normalizedRing (k := k) t) =
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s)
    (hmem : (Spec.preimage q).hom
      (algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t) (parameter t)) ∈
        (algebraMap O K).range) :
    ∃ g : Spec (.of O) ⟶ Spec (.of (normalizedRing (k := k) t)),
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g = q ∧
        g ≫ Spec.algebraMap k (normalizedRing (k := k) t) = s := by
  let : Algebra k O := (Spec.preimage s).hom.toAlgebra
  let : Algebra k K := ((algebraMap O K).comp (Spec.preimage s).hom).toAlgebra
  have : IsScalarTower k O K := IsScalarTower.of_algebraMap_eq' rfl
  have hbase : q ≫ Spec.algebraMap k (normalizedRing (k := k) t) =
      Spec.algebraMap k K := by
    rw [hq, ← Spec.map_preimage s, ← Spec.map_comp]
    rfl
  let φ := Spec.homEquivAlgHom (R := k) ⟨q, hbase⟩
  have hm : φ
      (algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t) (parameter t)) ∈
        (algebraMap O K).range := hmem
  obtain ⟨ψ, hψ, _⟩ := existsUnique_chart_lift t htr (O := O) (K := K) φ hm
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp]
    have hring : (algebraMap O K).comp ψ.toRingHom = φ.toRingHom := by
      exact congrArg AlgHom.toRingHom hψ
    rw [show CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (algebraMap O K) =
      CommRingCat.ofHom φ.toRingHom from CommRingCat.hom_ext hring]
    exact Spec.map_preimage q
  · rw [← Spec.map_comp]
    have hr : CommRingCat.ofHom (algebraMap k (normalizedRing (k := k) t)) ≫
        CommRingCat.ofHom ψ.toRingHom = Spec.preimage s := by
      ext c
      exact ψ.commutes c
    rw [hr, Spec.map_preimage]

end
end AclGeom.CurveCompletion
