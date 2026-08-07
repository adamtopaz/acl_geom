/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Equivalence
import AclGeom.Geometry.FiniteRank

/-!
# A small geometry language for finite configurations

The finite collection of geometric relations used by the configuration layer
(blueprint §small geometry language):

* `MemCl P Q`: `P ∈ cl(Q₀, …, Qₙ₋₁)`, i.e. `P` lies below the join of the
  tuple `Q`;
* `line P Q = P ∨ Q` and `Col P Q R ↔ R ≤ P ∨ Q`;
* `IsPartialQuadrangle f`: six distinct points whose four named triples
  (`quadTriples`) are dependent, all other triples independent, and whose
  total join has rank three (blueprint Def partialquad), with the "every
  other" clause quantified over three-element finsets of `Fin 6`;
* the simplification lemmas naming the four dependent triples, and the
  permutation lemma `IsPartialQuadrangle.comp_perm` transporting the
  predicate along any permutation preserving `quadTriples`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G1).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section Incidence

/-- `P ∈ cl(Q₀, …, Qₙ₋₁)`: the point `P` lies below the join of the finite
point tuple `Q` (blueprint §small geometry language). -/
def MemCl {n : ℕ} (P : Point k K) (Q : Fin n → Point k K) : Prop :=
  P.1 ≤ ⨆ i, (Q i).1

/-- The line through two points: their join in the closed lattice
(blueprint §small geometry language). When collinearity is intended to
describe a genuine line, distinctness hypotheses must be added at the use
site. -/
def line (P Q : Point k K) : ClosedIF k K :=
  P.1 ⊔ Q.1

/-- `Col P Q R`: the point `R` lies on the line through `P` and `Q`
(blueprint §small geometry language). -/
def Col (P Q R : Point k K) : Prop :=
  R.1 ≤ line P Q

theorem line_comm (P Q : Point k K) : line P Q = line Q P :=
  sup_comm _ _

theorem col_comm {P Q R : Point k K} (h : Col P Q R) : Col Q P R := by
  rwa [Col, line_comm]

/-- The join of a two-entry tuple of points is the corresponding line. -/
theorem iSup_pair (P Q : Point k K) :
    ⨆ i, ((![P, Q] : Fin 2 → Point k K) i).1 = line P Q := by
  refine le_antisymm (iSup_le fun i ↦ ?_) (sup_le ?_ ?_)
  · fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup_of_le 0 (by simp)
  · exact le_iSup_of_le 1 (by simp)

/-- Collinearity is membership in the closure of the pair. -/
theorem col_iff_memCl {P Q R : Point k K} :
    Col P Q R ↔ MemCl R ![P, Q] := by
  rw [Col, MemCl, iSup_pair]

/-- Membership in the closure of a tuple is membership in the point closure
of its range, linking the configuration language to the pregeometry API. -/
theorem memCl_iff_mem_pointCl {n : ℕ} {P : Point k K}
    {Q : Fin n → Point k K} :
    MemCl P Q ↔ P ∈ pointCl (Set.range Q) := by
  rw [MemCl, mem_pointCl_iff]
  have h : (⨆ i, (Q i).1) = sSup (Subtype.val '' Set.range Q) := by
    refine le_antisymm (iSup_le fun i ↦ le_sSup ⟨Q i, ⟨i, rfl⟩, rfl⟩)
      (sSup_le ?_)
    rintro E ⟨R, ⟨i, rfl⟩, rfl⟩
    exact le_iSup (fun j ↦ (Q j).1) i
  rw [h]
  exact Iff.rfl


end Incidence

section PartialQuadrangle

/-- The four dependent triples of the partial quadrangle in the canonical
ordering `(S, T, U, S', T', U') = (0, 1, 2, 3, 4, 5)`: `(S, T, U)`,
`(S, T', U')`, `(S', T, U')`, `(S', T', U)` (blueprint Def partialquad). -/
def quadTriples : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 4, 5}, {1, 3, 5}, {2, 3, 4}}

/-- Every named triple has three elements. -/
theorem card_of_mem_quadTriples {s : Finset (Fin 6)}
    (hs : s ∈ quadTriples) : s.card = 3 := by
  fin_cases hs <;> decide

/-- Six distinct points form a *partial quadrangle* when the four named
triples are dependent (rank two), every other three-element subtuple is
independent (rank three), and the join of all six has rank three
(blueprint Def partialquad). -/
structure IsPartialQuadrangle (f : Fin 6 → Point k K) : Prop where
  /-- The six points are distinct. -/
  injective : Function.Injective f
  /-- Each named triple is dependent: its join has rank two. -/
  rank_dep : ∀ s ∈ quadTriples, RankEq 2 (s.sup fun i ↦ (f i).1)
  /-- Every other three-element subtuple is independent: rank three. -/
  rank_free : ∀ s : Finset (Fin 6), s.card = 3 → s ∉ quadTriples →
    RankEq 3 (s.sup fun i ↦ (f i).1)
  /-- The join of all six points has rank three. -/
  rank_total : RankEq 3 (Finset.univ.sup fun i ↦ (f i).1)

namespace IsPartialQuadrangle

variable {f : Fin 6 → Point k K}

/-- Simplification: the triple `(S, T, U)` is dependent. -/
theorem rank_STU (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 0).1 ⊔ ((f 1).1 ⊔ (f 2).1)) := by
  have := h.rank_dep {0, 1, 2} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S, T', U')` is dependent. -/
theorem rank_STU' (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 0).1 ⊔ ((f 4).1 ⊔ (f 5).1)) := by
  have := h.rank_dep {0, 4, 5} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S', T, U')` is dependent. -/
theorem rank_S'TU' (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 1).1 ⊔ ((f 3).1 ⊔ (f 5).1)) := by
  have := h.rank_dep {1, 3, 5} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S', T', U)` is dependent. -/
theorem rank_S'T'U (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 2).1 ⊔ ((f 3).1 ⊔ (f 4).1)) := by
  have := h.rank_dep {2, 3, 4} (by decide)
  simpa [Finset.sup_insert] using this

/-- The permutation lemma: a partial quadrangle stays a partial quadrangle
under any reordering that preserves the four named triples (blueprint
§small geometry language). At concrete permutations the hypothesis is
checked by `decide`. -/
theorem comp_perm (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s : Finset (Fin 6), s ∈ quadTriples ↔ s.image σ ∈ quadTriples)
    (h : IsPartialQuadrangle f) : IsPartialQuadrangle (f ∘ σ) := by
  have hsup : ∀ s : Finset (Fin 6),
      (s.sup fun i ↦ ((f ∘ σ) i).1) = (s.image σ).sup fun i ↦ (f i).1 := by
    intro s
    rw [Finset.sup_image]
    rfl
  refine ⟨h.injective.comp σ.injective, fun s hs ↦ ?_, fun s hs3 hs ↦ ?_, ?_⟩
  · rw [hsup]
    exact h.rank_dep _ ((hσ s).1 hs)
  · rw [hsup]
    refine h.rank_free _ ?_ fun hmem ↦ hs ((hσ s).2 hmem)
    rw [Finset.card_image_of_injective _ σ.injective]
    exact hs3
  · rw [hsup]
    have huniv : (Finset.univ.image σ : Finset (Fin 6)) = Finset.univ := by
      ext i
      simp
    rw [huniv]
    exact h.rank_total

end IsPartialQuadrangle

end PartialQuadrangle

end

end AclGeom
