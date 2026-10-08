/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.MultiplierCurve
import AclGeom.Correspondence.FamilyCover
import AclGeom.Correspondence.CurveIdeal
import AclGeom.Geometry.Representatives

/-!
# A shared prime multiplier equation over the fixed parameter field

A literal fixed-five relocation has the same multiplier-pair ideal over the actual field k(f).
The original independence of a,b,x,c gives independence of a,b,ac,x, so the multiplier projection
is generic over k(f) and the dependent pair has one prime equation shared by both presentations.

The named consumer is the finite-component selection in the corrected blueprint
`affine-grid-extraction` argument (#27, L2). No geometric primality after extending coefficients,
stabilizer, action, linearity, fresh-input existence or guarded completeness is assumed or proved.

**Status:** shared prime multiplier equation over k(f) proved (#27, L2b).
Larger-base genericity, component/stabilizer linearity and guarded completeness remain open.
-/

namespace AclGeom

noncomputable section

open MvPolynomial IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The independence provided by L1b gives the actual multiplier-curve coordinates. -/
private theorem multiplier_tuple_independent {a b x c : K}
    (hind : AlgebraicIndependent k ![a, b, x, c]) :
    AlgebraicIndependent k ![a, b, a * c, x] := by
  have ha0 : a ≠ 0 := hind.ne_zero 0
  refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
  · have ha : a ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨0, rfl⟩
    have hb : b ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨1, rfl⟩
    have hx : x ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨2, rfl⟩
    have hc : c ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨3, rfl⟩
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact mul_mem ha hc
    · exact hx
  · have ha : a ∈ racl k (Set.range ![a, b, a * c, x]) := subset_racl k _ ⟨0, rfl⟩
    have hb : b ∈ racl k (Set.range ![a, b, a * c, x]) := subset_racl k _ ⟨1, rfl⟩
    have hac : a * c ∈ racl k (Set.range ![a, b, a * c, x]) := subset_racl k _ ⟨2, rfl⟩
    have hx : x ∈ racl k (Set.range ![a, b, a * c, x]) := subset_racl k _ ⟨3, rfl⟩
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hx
    · have h := mul_mem hac (inv_mem ha)
      have heq : (a * c) * a⁻¹ = c := by
        rw [mul_comm a c, mul_inv_cancel_right₀ ha0]
      rw [heq] at h
      exact h

/-- A literal fixed-five affine relocation has the same prime multiplier equation over k(f),
starting from the original independence of a,b,x,c and the explicit meet conditions. -/
theorem exists_prime_multiplier_curve_of_joint_ideal {a b x c p δ f a' b' x' : K}
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hJ : idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a', b', x']) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]))
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K)) :
    ∃ F : MvPolynomial (Fin 2) ↥(adjoin k ({f} : Set K)), Prime F ∧
      idealOf ↥(adjoin k ({f} : Set K)) ![a * c, x] = Ideal.span {F} ∧
      idealOf ↥(adjoin k ({f} : Set K)) ![a' * c, x'] = Ideal.span {F} := by
  obtain ⟨hI, _, _, _⟩ := affine_multiplier_curve_of_joint_ideal hJ hfm hfu
  obtain ⟨hX, hM, _⟩ := multiplier_projection_genericity (multiplier_tuple_independent hind) hfm hfu
  have hm : Transcendental ↥(adjoin k ({f} : Set K)) (a * c) := by
    intro halg
    exact hM (racl_mono (by simp) ((mem_racl_iff k).2 halg))
  have hx : x ∈ racl ↥(adjoin k ({f} : Set K)) ({a * c} : Set K) := by
    apply mem_racl_adjoin_base_iff.2
    simpa [Set.pair_comm] using hX
  obtain ⟨F, hF, hspan⟩ := exists_prime_span_idealOf ↥(adjoin k ({f} : Set K)) hm hx
  have hs (u v : K) :
      (Fin.snoc (Fin.snoc (![f] : Fin 1 → K) u) v : Fin 3 → K) = ![f, u, v] := by
    funext i
    fin_cases i <;> rfl
  have he := pairIdeal_eq_over_commonParameter_of_familyIdeal_eq (k := k)
    (p := (![f] : Fin 1 → K)) (x := a' * c) (y := x') (x' := a * c) (y' := x)
    (by rw [hs, hs]; exact hI)
  rw [Matrix.range_cons_empty] at he
  exact ⟨F, hF, hspan, he.trans hspan⟩

end

end AclGeom
