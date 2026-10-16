/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobEqCorrect
import AclGeom.Transfer.JCorrectness

/-!
# The Frobenius link is an equivalence relation

Blueprint Lemma `frobeq-correct` asserts the semantic characterization
`FrobEq(j(x, a), j(x', a')) ⇔ ∃ n ∈ ℤ, a' = a^{p^n}`, "and hence that `FrobEq` is an
equivalence relation on `J`".  The characterization is `frobEq_iff_exists_frobeniusZPow`, whose
algebraically closed completeness input stays explicit.  This module proves the second half
over a perfect field of transcendence degree at least five, with no further hypothesis:
`FrobEq` is an equivalence relation on the geometric `J`-tuples (`frobEq_equivalence`), and
`frobEqSetoid` is the global Frobenius setoid.

Every geometric `J`-tuple is semantic over such a field (`jGeom_iff_jSem_of_perfectField`), and
`jCompletenessACF` supplies the completeness input over `k̄ ⊆ K̄`.  Reflexivity is the exponent
`0`, symmetry is `FrobEq.symm`, and transitivity adds the two Frobenius exponents.  No relatively
algebraically closed base and no infinite base field is needed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#8, #23).
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **`FrobEq` is an equivalence relation on the geometric `J`-tuples** (blueprint Lemma
`frobeq-correct`, second half), over a perfect field of transcendence degree at least five. -/
theorem frobEq_equivalence [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    Equivalence fun u v : {w : Fin 5 → Point k K // IsJTuple w} ↦ FrobEq u.1 v.1 := by
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have hcomp := jCompletenessACF (five_le_trdeg_algebraicClosure htr)
  have hsem (u : {w : Fin 5 → Point k K // IsJTuple w}) : JSem u.1 :=
    (jGeom_iff_jSem_of_perfectField htr).1 u.2
  refine ⟨fun u ↦ ?_, fun h ↦ FrobEq.symm h, fun {u v w} h₁ h₂ ↦ ?_⟩
  · obtain ⟨x, a, hxa, hu⟩ := hsem u
    exact (frobEq_iff_exists_frobeniusZPow (ringExpChar K) htr hcomp hxa hxa hu hu).2
      ⟨0, by rw [frobeniusZPow, zpow_zero]; rfl⟩
  · obtain ⟨x, a, hxa, hu⟩ := hsem u
    obtain ⟨y, b, hyb, hv⟩ := hsem v
    obtain ⟨z, c, hzc, hw⟩ := hsem w
    obtain ⟨n, rfl⟩ :=
      (frobEq_iff_exists_frobeniusZPow (ringExpChar K) htr hcomp hxa hyb hu hv).1 h₁
    obtain ⟨m, rfl⟩ :=
      (frobEq_iff_exists_frobeniusZPow (ringExpChar K) htr hcomp hyb hzc hv hw).1 h₂
    exact (frobEq_iff_exists_frobeniusZPow (ringExpChar K) htr hcomp hxa hzc hu hw).2
      ⟨m + n, by simp only [frobeniusZPow, zpow_add, RingAut.mul_apply]⟩

/-- **The global Frobenius setoid** on the geometric `J`-tuples of a perfect field of
transcendence degree at least five: its classes are the Frobenius classes `[j(x₀, a)]_FrobEq`. -/
def frobEqSetoid [PerfectField K] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    Setoid {w : Fin 5 → Point k K // IsJTuple w} :=
  ⟨_, frobEq_equivalence htr⟩

end AclGeom
