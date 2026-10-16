/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AdditiveSubgroup
import AclGeom.Correspondence.SubgroupConnectedPrime

/-!
# Connected one-dimensional subgroups of the additive plane

Blueprint Lemma `subgroup-classification` (a) in its source form: over an algebraically closed
field `k`, a Zariski-closed, connected, one-dimensional subgroup `H ⊆ k²` whose two projections
are nonconstant is `{(u, v) : P(u) = Q(v)}` for nonzero additive polynomials `P, Q`
(`addSubgroup_classification_of_connected`).  The coordinate ring of `H` is
`k[X₀, X₁] ⧸ I(H)` with `I(H)` the vanishing ideal.  Connectedness is connectedness of its prime
spectrum, and dimension one is its Krull dimension.

The bridge to the prime-ideal form `addSubgroup_classification` shows that `I(H)` is prime.  This
is `isPrime_vanishingIdeal_of_connected` for the operation `(c, u, v) ↦ u + v - c`, realized in
each variable by translations of polynomials.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C4).
-/

namespace AclGeom

open MvPolynomial

variable {k : Type*} [Field k]

/-- Evaluation of a translate at a point of `k²`. -/
private theorem aeval_translate_eq (u c : Fin 2 → k) (g : MvPolynomial (Fin 2) k) :
    aeval u (translate c g) = aeval (u + c) g := by
  rw [aeval_translate]
  have hfun : (fun j ↦ u j + algebraMap k k (c j)) = u + c := by
    funext j
    simp
  rw [hfun]

variable [IsAlgClosed k]

/-- **Connected one-dimensional subgroups of `Gₐ²`** (blueprint Lemma
`subgroup-classification` (a)).  Over an algebraically closed field, let `H ⊆ k²` be a
Zariski-closed additive subgroup whose coordinate ring `k[X₀, X₁] ⧸ I(H)` has connected prime
spectrum and Krull dimension one, and whose two projections are nonconstant.  Then
`I(H) = (P(X₀) - Q(X₁))` for nonzero additive polynomials `P, Q`, and
`H = {(u, v) : P(u) = Q(v)}`. -/
theorem addSubgroup_classification_of_connected (H : AddSubgroup (Fin 2 → k))
    (hclosed : zeroLocus k (vanishingIdeal k (H : Set (Fin 2 → k))) = H)
    [ConnectedSpace
      (PrimeSpectrum (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))))]
    (hdim : ringKrullDim (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k (H : Set (Fin 2 → k))) = 1)
    (hproj₀ : ∃ u ∈ H, ∃ v ∈ H, u 0 ≠ v 0) (hproj₁ : ∃ u ∈ H, ∃ v ∈ H, u 1 ≠ v 1) :
    ∃ P Q : Polynomial k, IsAdditive P ∧ IsAdditive Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      vanishingIdeal k (H : Set (Fin 2 → k)) =
        Ideal.span {Polynomial.aeval (X 0) P - Polynomial.aeval (X 1) Q} ∧
      (H : Set (Fin 2 → k)) = {u | P.eval (u 0) = Q.eval (u 1)} := by
  have := isPrime_vanishingIdeal_of_connected (H : Set (Fin 2 → k)) hclosed ⟨0, H.zero_mem⟩
    (fun c u v ↦ u + v - c) (fun c hc u hu v hv ↦ H.sub_mem (H.add_mem hu hv) hc)
    (fun c _ u ↦ add_sub_cancel_right u c) (fun c _ v ↦ add_sub_cancel_left c v)
    (fun c v ↦ translate (v - c))
    (fun c v u g ↦ by rw [aeval_translate_eq, ← add_sub_assoc])
    (fun c u ↦ translate (u - c))
    (fun c u v g ↦ by rw [aeval_translate_eq, add_sub_left_comm, ← add_sub_assoc])
  exact addSubgroup_classification H _ hclosed.symm hdim hproj₀ hproj₁

end AclGeom
