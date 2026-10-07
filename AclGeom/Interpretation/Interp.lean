/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Decode
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# The interpreted carrier and its decoding onto `K`

Blueprint §"The ratio quotient and the interpreted field": the ratio quotient of the fixed class
`J₁ = [j(x₀, a)]_FrobEq` represents the nonzero elements of `K`, and a new zero is adjoined
(`RatioInterp`, the blueprint's `Interp(J₁)` with `WithZero`).  Decoding
`0 ↦ 0`, `[u₁, u₂] ↦ μ(u₁)/μ(u₂)` is a bijection onto `K` (`ratioInterpDecode`; blueprint
Lemma `decode-equiv`), with evaluation laws `ratioInterpDecode_zero` and
`ratioInterpDecode_coe`.  It is assembled from the nonzero decoding `ratioDecodeEquiv` and
Mathlib's `WithZero.withZeroUnitsEquiv : WithZero Kˣ ≃* K`.

`K` is perfect of rank at least five, and completeness over `k̄ ⊆ K̄` (`hcomp`) stays explicit.

**Status:** the corrected ratio quotient with an adjoined zero decodes bijectively to the field,
under explicit perfection, rank-five and ACF J-completeness inputs (#23). `Field` proves
corrected total geometric graphs, a named transported field structure and the actual decoding
ring equivalence under the same inputs. Graph naturality and reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The interpreted carrier** of the class of `j(x₀, a)`: the ratio quotient with a new zero
adjoined (blueprint `Interp(J₁)`). -/
abbrev RatioInterp [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :=
  WithZero (Quotient (ratioSetoid q htr hcomp h₀))

/-- **Decoding** (blueprint Lemma `decode-equiv`): the interpreted carrier is in bijection with `K`,
by `0 ↦ 0` and `[u₁, u₂] ↦ μ(u₁)/μ(u₂)`. -/
def ratioInterpDecode [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    RatioInterp q htr hcomp h₀ ≃ K := by
  classical
  exact (Equiv.optionCongr (ratioDecodeEquiv q htr hcomp h₀)).trans
    WithZero.withZeroUnitsEquiv.toEquiv

/-- The adjoined zero decodes to `0`. -/
theorem ratioInterpDecode_zero [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a]) :
    ratioInterpDecode q htr hcomp h₀ 0 = 0 :=
  rfl

/-- The class of a pair `(r₁, r₂)` of class members decodes to `μ(r₁)/μ(r₂)`. -/
theorem ratioInterpDecode_coe [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    (r₁ r₂ : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w}) :
    ratioInterpDecode q htr hcomp h₀
        ((Quotient.mk (ratioSetoid q htr hcomp h₀) (r₁, r₂) : Quotient _) :
          RatioInterp q htr hcomp h₀) =
      (jClassEquiv q htr hcomp h₀ r₁ : K) / (jClassEquiv q htr hcomp h₀ r₂ : K) :=
  rfl

end

end AclGeom
