/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Main

/-!
# Reconstruction from the point geometry

The point-geometry formulation of blueprint Thm `target`: a bijection preserving the full
point closure is induced by an isomorphism of arbitrary chosen perfections. The exact
Frobenius fibre, characteristic-zero uniqueness and positive-characteristic uniqueness of
the exponent hold for its action on points. Conversely, a compatible isomorphism of
perfections preserves point closure.

**Status:** proved under the original RAC and source rank-five hypotheses.
-/

namespace AclGeom

universe u v

variable {k : Type*} {K : Type u} {l : Type*} {L : Type v}
  [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- **Point-geometry reconstruction** (blueprint Thm `target`, point presentation).
The closure-preserving point equivalence determines a reconstruction with exactly the
integral Frobenius twists as its possible inducing maps. -/
theorem point_reconstruction_target (π : Perfection K) (ρ : Perfection L)
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S) :
    Cardinal.lift.{v} (Algebra.trdeg k K) = Cardinal.lift.{u} (Algebra.trdeg l L) ∧
      ∃ (Φ : π.carrier ≃+* ρ.carrier)
        (hΦ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ),
        Point.map (π.inducedIso ρ hΦ) = e ∧
        (∀ (Ψ : π.carrier ≃+* ρ.carrier)
          (hΨ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Ψ),
          Point.map (π.inducedIso ρ hΨ) = e ↔ ∃ n : ℤ, Ψ = Φ.trans (ρ.frobZPow n)) ∧
        (ρ.p = 1 → ∀ (Ψ : π.carrier ≃+* ρ.carrier)
          (hΨ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Ψ),
          Point.map (π.inducedIso ρ hΨ) = e → Ψ = Φ) ∧
        (ρ.p ≠ 1 → Function.Injective fun n : ℤ ↦ Φ.trans (ρ.frobZPow n)) ∧
        ∀ (Ψ : π.carrier ≃+* ρ.carrier)
          (hΨ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Ψ)
          (S : Set (Point k K)) (P : Point k K),
          Point.map (π.inducedIso ρ hΨ) P ∈
            pointCl (Point.map (π.inducedIso ρ hΨ) '' S) ↔ P ∈ pointCl S := by
  let φ := latticeIsoOfPointEquiv e hcl
  have hpoint (Ψ : π.carrier ≃+* ρ.carrier)
      (hΨ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Ψ) :
      Point.map (π.inducedIso ρ hΨ) = e ↔ Reconstructs π ρ φ Ψ := by
    rw [Reconstructs, Perfection.induces_iff_eq_inducedIso hΨ]
    constructor
    · intro h
      exact (latticeIsoOfPointEquiv_unique e hcl _ h).symm
    · intro h
      rw [← h]
      exact point_map_latticeIsoOfPointEquiv e hcl
  obtain ⟨hrank, Φ, hΦ, h, -, hfibre, hzero, hpos, -⟩ :=
    reconstruction_target π ρ hk hl htr φ
  exact ⟨hrank, Φ, hΦ, (hpoint Φ hΦ).2 h,
    fun Ψ hΨ ↦ (hpoint Ψ hΨ).trans (hfibre Ψ),
    fun hp Ψ hΨ he ↦ hzero hp Ψ ((hpoint Ψ hΨ).1 he),
    hpos, fun Ψ hΨ _ _ ↦ pointCl_map_iff (π.inducedIso ρ hΨ)⟩

end AclGeom
