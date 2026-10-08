/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.RationalFunctions
import AclGeom.Counterexamples.QDescent
import AclGeom.Counterexamples.QSemantic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric Q and Q′ without semantic representatives

Over `k(X₀, …, X₄)` for any characteristic-zero field `k`, both arbitrary-field geometric
correctness assertions fail (`not_forall_qGeom_imp_qSem` and
`not_forall_q'Geom_imp_q'Sem`). The Q tuple is
`([X₀], [X₀X₁²], [X₀(1+X₁)²], [X₁])`; the Q′ tuple has last point `[X₀X₁]`.

Counterexamples/QDescent reflects the explicit table and quadrangle witnesses over an algebraic
closure. Counterexamples/QSemantic proves that semantic representatives would make `X₀/x²`
algebraic. Closure/RationalFunctions shows that this would give a square equal to a nonzero
constant times `X₀`, which is impossible. The corollaries apply the actual geometric and
semantic predicates, with no completeness hypothesis.

**Status:** both concrete characteristic-zero refutations and their generic sufficient
conditions are proved (#25). Its unguarded `Q` conclusion is superseded by the any-field
degenerate refutation in Counterexamples.QDegenerate (#27); the independent `Q′` refutation
remains relevant. General descent, guarded ACF `Q` completeness and ACF `Q′` completeness
remain open. The original withdrawn blueprint consequence retains its provenance.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

noncomputable section

section Refutation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Geometric

variable {s t e₁ e₂ e₃ : K} (hind : AlgebraicIndependent k ![s, t, e₁, e₂, e₃])

include hind

/-- **Geometric `Q` for the #25 tuple**, with no ambient data: `qGeom_rat` over `Ω = K̄`, at a
square root of `s` there. -/
theorem qGeom_of_indep {P D Y I : Point k K} (hP : P.1 = point k s)
    (hD : D.1 = point k (s * t ^ 2)) (hY : Y.1 = point k (s * (1 + t) ^ 2))
    (hI : I.1 = point k t) : QGeom P D Y I := by
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_pow_nat_eq (IsScalarTower.toAlgHom k K (AlgebraicClosure K) s) two_pos
  exact qGeom_rat (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) hind hr hP hD hY hI

/-- **Geometric `Q′` for the #25 tuple**, with no ambient data: `qPrimeGeom_rat` over `Ω = K̄`,
at a square root of `s` there. -/
theorem q'Geom_of_indep {X Y S E : Point k K} (hX : X.1 = point k s)
    (hY : Y.1 = point k (s * t ^ 2)) (hS : S.1 = point k (s * (1 + t) ^ 2))
    (hE : E.1 = point k (s * t)) : Q'Geom X Y S E := by
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_pow_nat_eq (IsScalarTower.toAlgHom k K (AlgebraicClosure K) s) two_pos
  exact qPrimeGeom_rat (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) hind hr hX hY hS hE

end Geometric

variable [CharZero k] {v : Fin 5 → K} (hv : AlgebraicIndependent k v)
  (hsq : ∀ x : K, x ≠ 0 → ¬ IsAlgebraic k (v 0 / x ^ 2))

include hv hsq

/-- **Correctness of `Q` fails** over `K/k` whenever `K` has five independent elements, the first
of which is not a constant times a square. -/
theorem not_forall_qGeom_imp_qSem_of_indep :
    ¬ ∀ P D Y I : Point k K, QGeom P D Y I → QSem P D Y I := by
  have hind : AlgebraicIndependent k ![v 0, v 1, v 2, v 3, v 4] := by
    convert hv using 1
    funext i
    fin_cases i <;> rfl
  have hst : AlgebraicIndependent k ![v 0, v 1] := by
    have h := hv.comp ![0, 1] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hte : v 1 ∉ racl k (∅ : Set K) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hst (racl_mono (Set.empty_subset _) h)
  have htt : v 1 ∈ racl k ({v 1} : Set K) := subset_racl k _ rfl
  have ht0 : v 1 ≠ 0 := ne_zero_of_notMem_racl_empty hte
  have h1t : 1 + v 1 ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hte)
  intro h
  exact not_qSem_of_indep hst hsq
    (P := Point.mk' k (v 0) (by simpa using mul_notMem_bot hst (one_mem _) one_ne_zero))
    (D := Point.mk' k (v 0 * v 1 ^ 2) (mul_notMem_bot hst (pow_mem htt 2) (pow_ne_zero 2 ht0)))
    (Y := Point.mk' k (v 0 * (1 + v 1) ^ 2)
      (mul_notMem_bot hst (pow_mem (add_mem (one_mem _) htt) 2) (pow_ne_zero 2 h1t)))
    (I := Point.mk' k (v 1) fun hb ↦ hte (mem_racl_empty_of_isAlgebraic (mem_bot_iff.1 hb)))
    rfl rfl rfl rfl (h _ _ _ _ (qGeom_of_indep hind rfl rfl rfl rfl))

/-- **Correctness of `Q′` fails** over `K/k` whenever `K` has five independent elements, the first
of which is not a constant times a square. -/
theorem not_forall_q'Geom_imp_q'Sem_of_indep :
    ¬ ∀ X Y S E : Point k K, Q'Geom X Y S E → Q'Sem X Y S E := by
  have hind : AlgebraicIndependent k ![v 0, v 1, v 2, v 3, v 4] := by
    convert hv using 1
    funext i
    fin_cases i <;> rfl
  have hste : AlgebraicIndependent k ![v 0, v 1, v 2] := by
    have h := hv.comp ![0, 1, 2] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hst : AlgebraicIndependent k ![v 0, v 1] := by
    have h := hv.comp ![0, 1] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hte : v 1 ∉ racl k (∅ : Set K) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hst (racl_mono (Set.empty_subset _) h)
  have htt : v 1 ∈ racl k ({v 1} : Set K) := subset_racl k _ rfl
  have ht0 : v 1 ≠ 0 := ne_zero_of_notMem_racl_empty hte
  have h1t : 1 + v 1 ≠ 0 := ne_zero_of_notMem_racl_empty (one_add_notMem_racl_empty hte)
  intro h
  exact not_q'Sem_of_indep hste hsq
    (X := Point.mk' k (v 0) (by simpa using mul_notMem_bot hst (one_mem _) one_ne_zero))
    (Y := Point.mk' k (v 0 * v 1 ^ 2) (mul_notMem_bot hst (pow_mem htt 2) (pow_ne_zero 2 ht0)))
    (S := Point.mk' k (v 0 * (1 + v 1) ^ 2)
      (mul_notMem_bot hst (pow_mem (add_mem (one_mem _) htt) 2) (pow_ne_zero 2 h1t)))
    (E := Point.mk' k (v 0 * v 1) (mul_notMem_bot hst htt ht0))
    rfl rfl rfl rfl (h _ _ _ _ (q'Geom_of_indep hind rfl rfl rfl rfl))

end Refutation

section RationalFunctionField

variable (k : Type*) [Field k]

variable [CharZero k]

/-- **#25, `Q`: correctness of `Q` fails over `k(X₀, …, X₄)/k`.**  The tuple
`([X₀], [X₀ X₁²], [X₀ (1 + X₁)²], [X₁])` is geometric but not semantic. -/
theorem not_forall_qGeom_imp_qSem :
    ¬ ∀ P D Y I : Point k (FractionRing (MvPolynomial (Fin 5) k)),
      QGeom P D Y I → QSem P D Y I :=
  not_forall_qGeom_imp_qSem_of_indep (algebraicIndependent_algebraMap_X k (Fin 5))
    (not_isAlgebraic_X_div_sq k (0 : Fin 5))

/-- **#25, `Q′`: correctness of `Q′` fails over `k(X₀, …, X₄)/k`.**  The tuple
`([X₀], [X₀ X₁²], [X₀ (1 + X₁)²], [X₀ X₁])` is geometric but not semantic. -/
theorem not_forall_q'Geom_imp_q'Sem :
    ¬ ∀ X Y S E : Point k (FractionRing (MvPolynomial (Fin 5) k)),
      Q'Geom X Y S E → Q'Sem X Y S E :=
  not_forall_q'Geom_imp_q'Sem_of_indep (algebraicIndependent_algebraMap_X k (Fin 5))
    (not_isAlgebraic_X_div_sq k (0 : Fin 5))

end RationalFunctionField

end

end AclGeom
