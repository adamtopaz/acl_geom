/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Counterexamples.BlueprintTransport

/-!
# The literal operation graphs and their geometric invariance

The blueprint section `Geometric graphs of addition and multiplication`, before Thm
`total-field-graphs`, defines the operation graphs on nonzero ratio classes by recipes:

* multiplication replaces both inputs by `RatioEq`-related representatives in generic position,
  applies `JMul` to the numerators and to the denominators, and compares the output by
  `RatioEq`;
* nonzero addition replaces both inputs by `RatioEq`-related representatives with a common
  denominator, applies `JAddTotalNZ` to the numerators and compares the resulting ratio by
  `RatioEq`; the zero sum is detected by `JNeg` on the two numerators.

This module states these recipes literally, as `BlueprintRatioAddGraph` and
`BlueprintRatioMulGraph`, on pairs of members of the Frobenius class of an arbitrary base tuple
with an adjoined zero.  Every replacement and comparison is an explicit `BlueprintRatioEq`
witness, input representative first, and every representative and witness is a class member.
The generic position of the multiplication recipe is the independence clause of `BlueprintJMul`;
no further independence is imposed.  The named-zero clauses are the completion supplied by the
proof of Thm `total-field-graphs` ("the named zero clauses are literal field identities").

The proof of Prop `interpreted-reconstruction` asserts that these graphs use only the closure
relation, equality, finite rank and point quantifiers, so that a geometry isomorphism and its
inverse preserve them.  This invariance is proved here (`blueprintRatioAddGraph_map_iff`,
`blueprintRatioMulGraph_map_iff`) from the literal predicate transport of
`AclGeom.Counterexamples.BlueprintTransport`, through the pointwise class map `frobEqClassMap`.

This is invariance only.  The literal ratio relation is not transitive
(`blueprintRatioEq_not_transitive`), so the graphs are stated on representatives and no descent
to a quotient is asserted.  No functionality, totality, decoding or field structure is asserted
either.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the literal representative-level recipes are transcribed and their geometric
invariance is proved (#8, #23).  The definitions are not a functionality or totality theorem;
Thm `total-field-graphs` for these literal graphs is not addressed here.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

section Defs

/-- **The literal addition graph** of the blueprint, on pairs of members of the Frobenius class
of `b` with an adjoined zero `none`.  Zero is neutral; this completion is supplied by the proof
of Thm `total-field-graphs`.  Two nonzero inputs `r₀, s₀` are replaced by `RatioEq`-related
representatives `(u, e)`, `(v, e)` with a common denominator `e`.  Either `JNeg(u, v)` and the
sum is zero, or `JAddTotalNZ(u, v, w)` and the output is `RatioEq`-related to `(w, e)`.  This
is a literal transcription only; it is not asserted to be functional or total. -/
def BlueprintRatioAddGraph (b : Fin 5 → Point k K)
    (r s t : Option ({u : Fin 5 → Point k K // FrobEq b u} ×
      {u : Fin 5 → Point k K // FrobEq b u})) : Prop :=
  (r = none ∧ t = s) ∨ (s = none ∧ t = r) ∨
    ∃ r₀ s₀, r = some r₀ ∧ s = some s₀ ∧
      ∃ u v e : {u : Fin 5 → Point k K // FrobEq b u},
        BlueprintRatioEq b (r₀.1.1, r₀.2.1) (u.1, e.1) ∧
        BlueprintRatioEq b (s₀.1.1, s₀.2.1) (v.1, e.1) ∧
        ((BlueprintJNeg b u.1 v.1 ∧ t = none) ∨
          ∃ (w : {u : Fin 5 → Point k K // FrobEq b u}) (t₀ : _), t = some t₀ ∧
            BlueprintJAddTotalNZ b u.1 v.1 w.1 ∧ BlueprintRatioEq b (w.1, e.1) (t₀.1.1, t₀.2.1))

/-- **The literal multiplication graph** of the blueprint, on pairs of members of the Frobenius
class of `b` with an adjoined zero `none`.  A product with a zero factor is zero; this completion
is supplied by the proof of Thm `total-field-graphs`.  Two nonzero inputs `r₀, s₀` are replaced
by `RatioEq`-related representatives `(u₁, u₂)`, `(v₁, v₂)`, the numerators and the denominators
are multiplied by `JMul`, and the output is `RatioEq`-related to `(w₁, w₂)`.  This is a literal
transcription only; it is not asserted to be functional or total. -/
def BlueprintRatioMulGraph (b : Fin 5 → Point k K)
    (r s t : Option ({u : Fin 5 → Point k K // FrobEq b u} ×
      {u : Fin 5 → Point k K // FrobEq b u})) : Prop :=
  ((r = none ∨ s = none) ∧ t = none) ∨
    ∃ r₀ s₀ t₀, r = some r₀ ∧ s = some s₀ ∧ t = some t₀ ∧
      ∃ u₁ u₂ v₁ v₂ w₁ w₂ : {u : Fin 5 → Point k K // FrobEq b u},
        BlueprintRatioEq b (r₀.1.1, r₀.2.1) (u₁.1, u₂.1) ∧
        BlueprintRatioEq b (s₀.1.1, s₀.2.1) (v₁.1, v₂.1) ∧
        BlueprintJMul u₁.1 v₁.1 w₁.1 ∧ BlueprintJMul u₂.1 v₂.1 w₂.1 ∧
        BlueprintRatioEq b (w₁.1, w₂.1) (t₀.1.1, t₀.2.1)

end Defs

/-- **The map of Frobenius classes** induced by an order isomorphism of closed lattices, for an
arbitrary base tuple `b`: class members are mapped pointwise by `Point.map e` onto the class of
the image `Point.map e ∘ b`. -/
def frobEqClassMap (e : ClosedIF k K ≃o ClosedIF l L) (b : Fin 5 → Point k K) :
    {u : Fin 5 → Point k K // FrobEq b u} ≃
      {u : Fin 5 → Point l L // FrobEq (Point.map e ∘ b) u} :=
  (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).subtypeEquiv fun _ ↦ (frobEq_map_iff e).symm

/-- **The literal multiplication graph is invariant** under order isomorphisms of closed
lattices: class members, representatives and witnesses are mapped pointwise, and every
`RatioEq` replacement and `JMul` product transfers.  This is invariance only. -/
theorem blueprintRatioMulGraph_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (b : Fin 5 → Point k K)
    (r s t : Option ({u : Fin 5 → Point k K // FrobEq b u} ×
      {u : Fin 5 → Point k K // FrobEq b u})) :
    BlueprintRatioMulGraph (Point.map e ∘ b)
        (r.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b)))
        (s.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b)))
        (t.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b))) ↔
      BlueprintRatioMulGraph b r s t := by
  have hc : ∀ u, (frobEqClassMap e b u).1 = Point.map e ∘ u.1 := fun _ ↦ rfl
  have hR : ∀ p₁ p₂ q₁ q₂ : {u : Fin 5 → Point k K // FrobEq b u},
      BlueprintRatioEq (Point.map e ∘ b) ((frobEqClassMap e b p₁).1, (frobEqClassMap e b p₂).1)
          ((frobEqClassMap e b q₁).1, (frobEqClassMap e b q₂).1) ↔
        BlueprintRatioEq b (p₁.1, p₂.1) (q₁.1, q₂.1) := fun _ _ _ _ ↦ by
    rw [hc, hc, hc, hc]
    exact blueprintRatioEq_map_iff e
  have hM : ∀ u v w : {u : Fin 5 → Point k K // FrobEq b u},
      BlueprintJMul (frobEqClassMap e b u).1 (frobEqClassMap e b v).1 (frobEqClassMap e b w).1 ↔
        BlueprintJMul u.1 v.1 w.1 := fun _ _ _ ↦ by
    rw [hc, hc, hc]
    exact blueprintJMul_map_iff e
  have hS := (frobEqClassMap e b).surjective
  constructor
  · rintro (⟨hrs, ht⟩ | ⟨r₀, s₀, t₀, hr, hs, ht, u₁, u₂, v₁, v₂, w₁, w₂, h₁, h₂, m₁, m₂, h₃⟩)
    · exact Or.inl ⟨hrs.imp Option.map_eq_none_iff.1 Option.map_eq_none_iff.1,
        Option.map_eq_none_iff.1 ht⟩
    · obtain ⟨r₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨s₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 hs
      obtain ⟨t₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨u₁, rfl⟩ := hS u₁
      obtain ⟨u₂, rfl⟩ := hS u₂
      obtain ⟨v₁, rfl⟩ := hS v₁
      obtain ⟨v₂, rfl⟩ := hS v₂
      obtain ⟨w₁, rfl⟩ := hS w₁
      obtain ⟨w₂, rfl⟩ := hS w₂
      exact Or.inr ⟨r₀, s₀, t₀, rfl, rfl, rfl, u₁, u₂, v₁, v₂, w₁, w₂, (hR _ _ _ _).1 h₁,
        (hR _ _ _ _).1 h₂, (hM _ _ _).1 m₁, (hM _ _ _).1 m₂, (hR _ _ _ _).1 h₃⟩
  · rintro (⟨hrs, rfl⟩ | ⟨r₀, s₀, t₀, rfl, rfl, rfl, u₁, u₂, v₁, v₂, w₁, w₂, h₁, h₂, m₁, m₂, h₃⟩)
    · exact Or.inl ⟨hrs.imp Option.map_eq_none_iff.2 Option.map_eq_none_iff.2, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl, rfl, rfl, frobEqClassMap e b u₁, frobEqClassMap e b u₂,
        frobEqClassMap e b v₁, frobEqClassMap e b v₂, frobEqClassMap e b w₁,
        frobEqClassMap e b w₂, (hR _ _ _ _).2 h₁, (hR _ _ _ _).2 h₂, (hM _ _ _).2 m₁,
        (hM _ _ _).2 m₂, (hR _ _ _ _).2 h₃⟩

/-- **The literal addition graph is invariant** under order isomorphisms of closed lattices:
class members, representatives and witnesses are mapped pointwise, and every `RatioEq`
replacement, the `JNeg` zero test and the `JAddTotalNZ` sum transfer.  This is invariance
only. -/
theorem blueprintRatioAddGraph_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (b : Fin 5 → Point k K)
    (r s t : Option ({u : Fin 5 → Point k K // FrobEq b u} ×
      {u : Fin 5 → Point k K // FrobEq b u})) :
    BlueprintRatioAddGraph (Point.map e ∘ b)
        (r.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b)))
        (s.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b)))
        (t.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b))) ↔
      BlueprintRatioAddGraph b r s t := by
  have hc : ∀ u, (frobEqClassMap e b u).1 = Point.map e ∘ u.1 := fun _ ↦ rfl
  have hR : ∀ p₁ p₂ q₁ q₂ : {u : Fin 5 → Point k K // FrobEq b u},
      BlueprintRatioEq (Point.map e ∘ b) ((frobEqClassMap e b p₁).1, (frobEqClassMap e b p₂).1)
          ((frobEqClassMap e b q₁).1, (frobEqClassMap e b q₂).1) ↔
        BlueprintRatioEq b (p₁.1, p₂.1) (q₁.1, q₂.1) := fun _ _ _ _ ↦ by
    rw [hc, hc, hc, hc]
    exact blueprintRatioEq_map_iff e
  have hN : ∀ u v : {u : Fin 5 → Point k K // FrobEq b u},
      BlueprintJNeg (Point.map e ∘ b) (frobEqClassMap e b u).1 (frobEqClassMap e b v).1 ↔
        BlueprintJNeg b u.1 v.1 := fun _ _ ↦ by
    rw [hc, hc]
    exact blueprintJNeg_map_iff e
  have hA : ∀ u v w : {u : Fin 5 → Point k K // FrobEq b u},
      BlueprintJAddTotalNZ (Point.map e ∘ b) (frobEqClassMap e b u).1 (frobEqClassMap e b v).1
          (frobEqClassMap e b w).1 ↔ BlueprintJAddTotalNZ b u.1 v.1 w.1 := fun _ _ _ ↦ by
    rw [hc, hc, hc]
    exact blueprintJAddTotalNZ_map_iff e
  have hS := (frobEqClassMap e b).surjective
  have hinj : Function.Injective
      (Option.map (Prod.map (frobEqClassMap e b) (frobEqClassMap e b))) :=
    Option.map_injective ((frobEqClassMap e b).prodCongr (frobEqClassMap e b)).injective
  constructor
  · rintro (⟨hr, hts⟩ | ⟨hs, htr⟩ | ⟨r₀, s₀, hr, hs, u, v, e', h₁, h₂, hbr⟩)
    · exact Or.inl ⟨Option.map_eq_none_iff.1 hr, hinj hts⟩
    · exact Or.inr (Or.inl ⟨Option.map_eq_none_iff.1 hs, hinj htr⟩)
    · obtain ⟨r₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨s₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 hs
      obtain ⟨u, rfl⟩ := hS u
      obtain ⟨v, rfl⟩ := hS v
      obtain ⟨e', rfl⟩ := hS e'
      refine Or.inr (Or.inr ⟨r₀, s₀, rfl, rfl, u, v, e', (hR _ _ _ _).1 h₁, (hR _ _ _ _).1 h₂, ?_⟩)
      rcases hbr with ⟨hneg, ht⟩ | ⟨w, t₀, ht, hsum, h₃⟩
      · exact Or.inl ⟨(hN _ _).1 hneg, Option.map_eq_none_iff.1 ht⟩
      · obtain ⟨t₀, rfl, rfl⟩ := Option.map_eq_some_iff.1 ht
        obtain ⟨w, rfl⟩ := hS w
        exact Or.inr ⟨w, t₀, rfl, (hA _ _ _).1 hsum, (hR _ _ _ _).1 h₃⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r₀, s₀, rfl, rfl, u, v, e', h₁, h₂, hbr⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · refine Or.inr (Or.inr ⟨_, _, rfl, rfl, frobEqClassMap e b u, frobEqClassMap e b v,
        frobEqClassMap e b e', (hR _ _ _ _).2 h₁, (hR _ _ _ _).2 h₂, ?_⟩)
      rcases hbr with ⟨hneg, rfl⟩ | ⟨w, t₀, rfl, hsum, h₃⟩
      · exact Or.inl ⟨(hN _ _).2 hneg, rfl⟩
      · exact Or.inr ⟨frobEqClassMap e b w, _, rfl, (hA _ _ _).2 hsum, (hR _ _ _ _).2 h₃⟩

end

end AclGeom
