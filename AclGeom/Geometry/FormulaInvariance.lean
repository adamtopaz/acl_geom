/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Geometry.Transport
import AclGeom.Config.Language

/-!
# Invariance of the finite geometry language

The blueprint's small geometry language uses point variables, finite joins and meets,
equality and incidence, Boolean operations and point quantifiers. `GeometryTerm` and
`GeometryFormula` make that recursion precise, including the finite-rank atoms used by
the configurations. Terms commute with lattice isomorphisms, and satisfaction is
invariant. The presentation bridge gives the same result for closure-preserving point
equivalences. Tuple incidence and collinearity are named consumers of this theorem.

No field semantics, algebraic closedness, rank bound or completeness input is required.
Existing concrete configuration transport is unchanged; configuration extraction and
the group/action engine remain open (#6/#27). The frozen M4a chain is not used.

**Status:** generic formula invariance and its incidence consumers proved (G1c, #6).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

/-- Finite lattice terms in `n` point variables (blueprint §small geometry language).
The finite point join includes the empty join; nested binary joins and meets allow
arbitrary finite expressions. The consumer is `GeometryFormula` and its invariance. -/
inductive GeometryTerm (n : ℕ) where
  /-- A point variable, viewed in the closed lattice. -/
  | point (i : Fin n)
  /-- The bottom closed element. -/
  | bot
  /-- The top closed element. -/
  | top
  /-- The join of a finite tuple of point variables. -/
  | join {m : ℕ} (f : Fin m → Fin n)
  /-- The binary join of two terms. -/
  | sup (s t : GeometryTerm n)
  /-- The binary meet of two terms. -/
  | inf (s t : GeometryTerm n)

/-- Formulas in `n` point variables, with equality/order and finite-rank atoms,
Boolean operations and point quantifiers. A quantifier binds the variable at index
zero and shifts the other variables by one. The blueprint consumer is the generic
recursion theorem `GeometryFormula.holds_map_iff`. -/
inductive GeometryFormula : ℕ → Type where
  /-- Equality of lattice terms; this also expresses equality of points. -/
  | equal {n : ℕ} (s t : GeometryTerm n) : GeometryFormula n
  /-- Order of lattice terms, including point-below-join incidence. -/
  | le {n : ℕ} (s t : GeometryTerm n) : GeometryFormula n
  /-- Exact finite rank of a lattice term. -/
  | rankEq {n : ℕ} (r : ℕ) (t : GeometryTerm n) : GeometryFormula n
  /-- A finite upper bound on the rank of a lattice term. -/
  | rankLE {n : ℕ} (r : ℕ) (t : GeometryTerm n) : GeometryFormula n
  /-- Negation. -/
  | neg {n : ℕ} (φ : GeometryFormula n) : GeometryFormula n
  /-- Conjunction. -/
  | conj {n : ℕ} (φ ψ : GeometryFormula n) : GeometryFormula n
  /-- Disjunction. -/
  | disj {n : ℕ} (φ ψ : GeometryFormula n) : GeometryFormula n
  /-- Implication. -/
  | impl {n : ℕ} (φ ψ : GeometryFormula n) : GeometryFormula n
  /-- Existential quantification over points. -/
  | existsPoint {n : ℕ} (φ : GeometryFormula (n + 1)) : GeometryFormula n
  /-- Universal quantification over points. -/
  | forallPoint {n : ℕ} (φ : GeometryFormula (n + 1)) : GeometryFormula n

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- Interpret a finite lattice term at a tuple of points. Its named consumer is
formula satisfaction and term transport. -/
def GeometryTerm.eval {n : ℕ} (ρ : Fin n → Point k K) : GeometryTerm n → ClosedIF k K
  | .point i => (ρ i).1
  | .bot => ⊥
  | .top => ⊤
  | .join f => ⨆ i, (ρ (f i)).1
  | .sup s t => s.eval ρ ⊔ t.eval ρ
  | .inf s t => s.eval ρ ⊓ t.eval ρ

/-- Satisfaction of a geometry formula. Point quantifiers extend the assignment
using `Fin.cons`, so the bound point is at index zero. Its consumer is the blueprint's
generic invariance theorem and the named incidence predicates below. -/
def GeometryFormula.Holds {n : ℕ} (ρ : Fin n → Point k K) : GeometryFormula n → Prop
  | .equal s t => s.eval ρ = t.eval ρ
  | .le s t => s.eval ρ ≤ t.eval ρ
  | .rankEq r t => RankEq r (t.eval ρ)
  | .rankLE r t => RankLE r (t.eval ρ)
  | .neg φ => ¬ φ.Holds ρ
  | .conj φ ψ => φ.Holds ρ ∧ ψ.Holds ρ
  | .disj φ ψ => φ.Holds ρ ∨ ψ.Holds ρ
  | .impl φ ψ => φ.Holds ρ → ψ.Holds ρ
  | .existsPoint φ => ∃ P : Point k K, φ.Holds (Fin.cons P ρ)
  | .forallPoint φ => ∀ P : Point k K, φ.Holds (Fin.cons P ρ)

/-- Lattice terms commute with an order isomorphism, by structural recursion.
This is the term step of the blueprint's generic formula invariance theorem. -/
theorem GeometryTerm.eval_map (e : ClosedIF k K ≃o ClosedIF l L) {n : ℕ}
    (t : GeometryTerm n) (ρ : Fin n → Point k K) :
    t.eval (Point.map e ∘ ρ) = e (t.eval ρ) := by
  induction t with
  | point i => rfl
  | bot => exact e.map_bot.symm
  | top => exact e.map_top.symm
  | join f => exact point_map_iSup e (ρ ∘ f)
  | sup s t hs ht => simp only [eval, hs, ht, map_sup]
  | inf s t hs ht => simp only [eval, hs, ht, map_inf]

/-- **Generic formula invariance** (blueprint §small geometry language): equality,
order, finite rank, Boolean operations and point quantifiers are preserved by a
lattice isomorphism. Surjectivity of its point map handles both quantifiers. The
actual consumers are point-geometry invariance, tuple incidence and collinearity. -/
theorem GeometryFormula.holds_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {n : ℕ}
    (φ : GeometryFormula n) (ρ : Fin n → Point k K) :
    φ.Holds (Point.map e ∘ ρ) ↔ φ.Holds ρ := by
  induction φ with
  | equal s t => simp only [Holds, GeometryTerm.eval_map, e.injective.eq_iff]
  | le s t => simp only [Holds, GeometryTerm.eval_map, e.le_iff_le]
  | rankEq r t => simp only [Holds, GeometryTerm.eval_map, rankEq_map_iff]
  | rankLE r t => simp only [Holds, GeometryTerm.eval_map, rankLE_map_iff]
  | neg φ ih => exact not_congr (ih ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ ρ) (ihψ ρ)
  | impl φ ψ ihφ ihψ => exact imp_congr (ihφ ρ) (ihψ ρ)
  | existsPoint φ ih =>
    have hcons (P : Point k K) :
        Fin.cons (Point.map e P) (Point.map e ∘ ρ) = Point.map e ∘ Fin.cons P ρ := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    constructor
    · rintro ⟨Q, hQ⟩
      obtain ⟨P, rfl⟩ := (Point.map e).surjective Q
      exact ⟨P, (ih (Fin.cons P ρ)).1 (hcons P ▸ hQ)⟩
    · rintro ⟨P, hP⟩
      exact ⟨Point.map e P, (hcons P).symm ▸ (ih (Fin.cons P ρ)).2 hP⟩
  | forallPoint φ ih =>
    have hcons (P : Point k K) :
        Fin.cons (Point.map e P) (Point.map e ∘ ρ) = Point.map e ∘ Fin.cons P ρ := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    constructor
    · intro h P
      exact (ih (Fin.cons P ρ)).1 (hcons P ▸ h (Point.map e P))
    · intro h Q
      obtain ⟨P, rfl⟩ := (Point.map e).surjective Q
      exact (hcons P).symm ▸ (ih (Fin.cons P ρ)).2 (h P)

/-- The blueprint's generic recursion theorem for a closure-preserving equivalence
of point geometries. The proved point/lattice presentation bridge supplies the
lattice map; no configuration completeness hypothesis is used. -/
theorem GeometryFormula.holds_pointEquiv_iff (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S)
    {n : ℕ} (φ : GeometryFormula n) (ρ : Fin n → Point k K) :
    φ.Holds (e ∘ ρ) ↔ φ.Holds ρ := by
  simpa only [point_map_latticeIsoOfPointEquiv] using
    φ.holds_map_iff (latticeIsoOfPointEquiv e hcl) ρ

/-- Tuple incidence is invariant under a lattice isomorphism, as a concrete
point-below-finite-join instance of generic formula invariance (blueprint G1c). -/
theorem memCl_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {n : ℕ}
    {P : Point k K} {Q : Fin n → Point k K} :
    MemCl (Point.map e P) (Point.map e ∘ Q) ↔ MemCl P Q := by
  simpa only [GeometryFormula.Holds, GeometryTerm.eval, Function.comp_apply,
    Fin.cons_zero, Fin.cons_succ, MemCl] using
    (GeometryFormula.le (.point 0) (.join Fin.succ)).holds_map_iff e (Fin.cons P Q)

/-- Collinearity is invariant under a lattice isomorphism, as a concrete
point-below-binary-join instance of generic formula invariance (blueprint G1c). -/
theorem col_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {P Q R : Point k K} :
    Col (Point.map e P) (Point.map e Q) (Point.map e R) ↔ Col P Q R := by
  simpa only [GeometryFormula.Holds, GeometryTerm.eval, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Matrix.cons_val_succ, Col, line] using
    (GeometryFormula.le (.point 2) (.sup (.point 0) (.point 1))).holds_map_iff e ![P, Q, R]

end

end AclGeom
