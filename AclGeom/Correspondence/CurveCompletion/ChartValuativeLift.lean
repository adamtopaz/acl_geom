/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.NormalizedChart
import AclGeom.Correspondence.CurveCompletion.IntegralLift
/-!
# Chart Valuative Lift

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
universe u v w z
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
attribute [local instance] normalizedBaseAlgebra

/-- An actual normalized-chart map lifts uniquely to an integrally closed ring inside its
fraction field whenever the literal parameter lies in that ring. No algebra over that ring
on the chart is assumed. Named consumer: exists_chart_scheme_lift. -/
theorem existsUnique_chart_lift (t : F) (htr : Transcendental k t)
    {O : Type w} {K : Type z}
    [CommRing O] [IsDomain O] [Field K]
    [Algebra k O] [Algebra k K] [Algebra O K]
    [IsScalarTower k O K] [IsFractionRing O K] [IsIntegrallyClosed O]
    (φ : normalizedRing (k := k) t →ₐ[k] K)
    (hmem : φ (algebraMap (parameterRing (k := k) t) (normalizedRing (k := k) t)
      (parameter t)) ∈ (algebraMap O K).range) :
    ∃! ψ : normalizedRing (k := k) t →ₐ[k] O,
      (IsScalarTower.toAlgHom k O K).comp ψ = φ := by
  let P := parameterRing (k := k) t
  let A := normalizedRing (k := k) t
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' rfl
  let e : Polynomial k ≃ₐ[k] P := Polynomial.algEquivOfTranscendental k t htr
  obtain ⟨β, hβ⟩ := hmem
  let g : P →ₐ[k] O := (Polynomial.aeval β).comp e.symm.toAlgHom
  have hg : (IsScalarTower.toAlgHom k O K).comp g =
      φ.comp (IsScalarTower.toAlgHom k P A) := by
    have hp : ((IsScalarTower.toAlgHom k O K).comp g).comp e.toAlgHom =
        (φ.comp (IsScalarTower.toAlgHom k P A)).comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      change algebraMap O K (Polynomial.aeval β (e.symm (e Polynomial.X))) =
        φ (algebraMap P A (e Polynomial.X))
      rw [e.symm_apply_apply, Polynomial.aeval_X]
      have heX : e Polynomial.X = parameter t :=
        Polynomial.algEquivOfTranscendental_apply_X k t htr
      rw [heX]
      exact hβ
    ext p
    obtain ⟨q, rfl⟩ := e.surjective p
    exact AlgHom.congr_fun hp q
  let : Algebra P O := g.toRingHom.toAlgebra
  let : Algebra P K := (φ.comp (IsScalarTower.toAlgHom k P A)).toRingHom.toAlgebra
  have : IsScalarTower P O K := IsScalarTower.of_algebraMap_eq fun p ↦
    (AlgHom.congr_fun hg p).symm
  let φP : A →ₐ[P] K :=
    { φ.toRingHom with commutes' := fun p ↦ rfl }
  obtain ⟨ψP, hψP, _⟩ := existsUnique_integral_lift (O := O) (K := K) φP
  have : IsScalarTower k P O := IsScalarTower.of_algebraMap_eq fun c ↦
    (g.commutes c).symm
  let ψ : A →ₐ[k] O := ψP.restrictScalars k
  have hψ : (IsScalarTower.toAlgHom k O K).comp ψ = φ := by
    ext a
    exact AlgHom.congr_fun hψP a
  refine ⟨ψ, hψ, ?_⟩
  intro θ hθ
  ext a
  apply IsFractionRing.injective O K
  exact AlgHom.congr_fun (hθ.trans hψ.symm) a

end
end AclGeom.CurveCompletion
