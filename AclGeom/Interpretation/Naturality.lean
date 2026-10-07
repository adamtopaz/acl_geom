/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Field
import AclGeom.Interpretation.TotalTransport

/-!
# Naturality of the interpreted carrier and of the total field graphs

Let `e : ClosedIF k K ≃o ClosedIF l L` be an order isomorphism of closed-subfield lattices that
carries the base tuple `j(x₀, a)` of `K` to the base tuple `j(x₀', a')` of `L`
(`hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀'`).

* `ratioClassMap`: tuples are mapped pointwise by `Point.map e` (`Equiv.piCongrRight`).  This
  restricts to a bijection between the two fixed Frobenius classes (`frobEq_map_iff`).
* `ratioInterpMap`: pairs of class members are mapped componentwise.  The corrected ratio relation
  is preserved and reflected (`ratioEq_map_iff`), so the map descends to the ratio quotients
  (`Quotient.congr`) and extends over the adjoined zeros (`Equiv.optionCongr`).
* `ratioAddGraph_map_iff`, `ratioMulGraph_map_iff`: the carrier map preserves and reflects the
  corrected total addition and multiplication graphs, branch by branch.  These are the zero
  clauses, the common-denominator clause with its opposite and nonzero branches, and the generic
  product clause, with every witness and genericity clause.

Both maps are the geometric ones and are not defined through the decodings.  Witnesses on the target
side are pulled back by the surjectivity of the class map, and equalities in the target carrier
are reflected by the injectivity of the carrier map.  The adjoined zero and the class of a pair of
representatives are mapped definitionally.

The map of classes needs only the image-base equality.  The carriers themselves are the
interpreted carriers of `K` and `L`, so their perfection, rank-five and ACF J-completeness inputs
are explicit on both sides; the bases, the ambient fields and the exponents `q`, `q'` are
independent.

**Status:** geometric class/carrier maps and graph transport are complete (#23/#8, I6b3),
under the explicit image-base equality and carrier inputs above. The induced ring isomorphism,
corrected interpreted reconstruction and existence of the image base remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The map of fixed Frobenius classes** induced by an order isomorphism of closed lattices that
carries the base tuple `j(x₀, a)` to the base tuple `j(x₀', a')`: tuples are mapped pointwise by
`Point.map e`. -/
def ratioClassMap (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K}
    (h₀ : AlgebraicIndependent k ![x₀, a]) {x₀' a' : L}
    (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀') :
    {u : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) u} ≃
      {u : Fin 5 → Point l L // FrobEq (jTupleOf x₀' a' h₀') u} :=
  (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).subtypeEquiv fun u ↦ by
    rw [← hφ]
    exact (frobEq_map_iff e).symm

/-- **The map of interpreted carriers** induced by an order isomorphism of closed lattices that
carries the base tuple `j(x₀, a)` to the base tuple `j(x₀', a')`.  Pairs of class members are
mapped componentwise by `ratioClassMap`, which respects the corrected ratio relation in both
directions, and the adjoined zero goes to the adjoined zero. -/
def ratioInterpMap [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀') :
    RatioInterp q htr hcomp h₀ ≃ RatioInterp q' htr' hcomp' h₀' :=
  Equiv.optionCongr (Quotient.congr
    ((ratioClassMap e h₀ h₀' hφ).prodCongr (ratioClassMap e h₀ h₀' hφ)) fun r s ↦ by
      change RatioEq (jTupleOf x₀ a h₀) (r.1.1, r.2.1) (s.1.1, s.2.1) ↔
        RatioEq (jTupleOf x₀' a' h₀') (Point.map e ∘ r.1.1, Point.map e ∘ r.2.1)
          (Point.map e ∘ s.1.1, Point.map e ∘ s.2.1)
      rw [← hφ]
      exact (ratioEq_map_iff e).symm)

/-- **Naturality of the corrected addition graph**: the map of interpreted carriers induced by a
closed-lattice isomorphism preserves and reflects `RatioAddGraph`.  The zero clauses, the
common-denominator clause and both of its branches (opposite numerators, total nonzero sum)
transfer with all their witnesses. -/
theorem ratioAddGraph_map_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    {r s t : RatioInterp q htr hcomp h₀} :
    RatioAddGraph q' htr' hcomp' h₀'
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ r)
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ s)
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ t) ↔
      RatioAddGraph q htr hcomp h₀ r s t := by
  -- The carrier map sends the adjoined zero to the adjoined zero, and the class of a pair of
  -- representatives to the class of the mapped pair; it is injective.
  have hΦ0 : ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ 0 = 0 := rfl
  have hΦmk : ∀ u v : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
      ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
          ((Quotient.mk (ratioSetoid q htr hcomp h₀) (u, v) : Quotient _) :
            RatioInterp q htr hcomp h₀) =
        ((Quotient.mk (ratioSetoid q' htr' hcomp' h₀')
            (ratioClassMap e h₀ h₀' hφ u, ratioClassMap e h₀ h₀' hφ v) : Quotient _) :
          RatioInterp q' htr' hcomp' h₀') := fun _ _ ↦ rfl
  have hinj := (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ).injective
  unfold RatioAddGraph
  constructor
  · rintro (⟨hr, ht⟩ | ⟨hs, ht⟩ | ⟨u, v, d, hr, hs, hb⟩)
    · exact Or.inl ⟨hinj (hr.trans hΦ0.symm), hinj ht⟩
    · exact Or.inr (Or.inl ⟨hinj (hs.trans hΦ0.symm), hinj ht⟩)
    · -- Pull the target witnesses back along the class map.
      obtain ⟨u₀, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective u
      obtain ⟨v₀, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective v
      obtain ⟨d₀, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective d
      refine Or.inr (Or.inr ⟨u₀, v₀, d₀, hinj (hr.trans (hΦmk u₀ d₀).symm),
        hinj (hs.trans (hΦmk v₀ d₀).symm), ?_⟩)
      rcases hb with ⟨hneg, ht⟩ | ⟨w, hadd, ht⟩
      · refine Or.inl ⟨?_, hinj (ht.trans hΦ0.symm)⟩
        -- Restate without the class map, whose type mentions the target base, then rewrite it.
        have hneg' : JNegTotalRel (jTupleOf x₀' a' h₀') (Point.map e ∘ u₀.1)
            (Point.map e ∘ v₀.1) := hneg
        rw [← hφ] at hneg'
        exact (jNegTotalRel_map_iff e).1 hneg'
      · obtain ⟨w₀, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective w
        refine Or.inr ⟨w₀, ?_, hinj (ht.trans (hΦmk w₀ d₀).symm)⟩
        have hadd' : JAddTotalNZRel (jTupleOf x₀' a' h₀') (Point.map e ∘ u₀.1)
            (Point.map e ∘ v₀.1) (Point.map e ∘ w₀.1) := hadd
        rw [← hφ] at hadd'
        exact (jAddTotalNZRel_map_iff e).1 hadd'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨u, v, d, rfl, rfl, hb⟩)
    · exact Or.inl ⟨hΦ0, rfl⟩
    · exact Or.inr (Or.inl ⟨hΦ0, rfl⟩)
    · refine Or.inr (Or.inr ⟨ratioClassMap e h₀ h₀' hφ u, ratioClassMap e h₀ h₀' hφ v,
        ratioClassMap e h₀ h₀' hφ d, hΦmk u d, hΦmk v d, ?_⟩)
      rcases hb with ⟨hneg, rfl⟩ | ⟨w, hadd, rfl⟩
      · refine Or.inl ⟨?_, hΦ0⟩
        -- Restate without the class map, whose type mentions the target base, then rewrite it.
        change JNegTotalRel (jTupleOf x₀' a' h₀') (Point.map e ∘ u.1) (Point.map e ∘ v.1)
        rw [← hφ]
        exact (jNegTotalRel_map_iff e).2 hneg
      · refine Or.inr ⟨ratioClassMap e h₀ h₀' hφ w, ?_, hΦmk w d⟩
        change JAddTotalNZRel (jTupleOf x₀' a' h₀') (Point.map e ∘ u.1) (Point.map e ∘ v.1)
          (Point.map e ∘ w.1)
        rw [← hφ]
        exact (jAddTotalNZRel_map_iff e).2 hadd

/-- **Naturality of the corrected multiplication graph**: the map of interpreted carriers induced
by a closed-lattice isomorphism preserves and reflects `RatioMulGraph`.  The zero-factor clause
and the generic product clause transfer with all their witnesses and genericity clauses. -/
theorem ratioMulGraph_map_iff [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    {r s t : RatioInterp q htr hcomp h₀} :
    RatioMulGraph q' htr' hcomp' h₀'
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ r)
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ s)
        (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ t) ↔
      RatioMulGraph q htr hcomp h₀ r s t := by
  -- The carrier map sends the adjoined zero to the adjoined zero, and the class of a pair of
  -- representatives to the class of the mapped pair; it is injective.
  have hΦ0 : ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ 0 = 0 := rfl
  have hΦmk : ∀ u v : {w : Fin 5 → Point k K // FrobEq (jTupleOf x₀ a h₀) w},
      ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
          ((Quotient.mk (ratioSetoid q htr hcomp h₀) (u, v) : Quotient _) :
            RatioInterp q htr hcomp h₀) =
        ((Quotient.mk (ratioSetoid q' htr' hcomp' h₀')
            (ratioClassMap e h₀ h₀' hφ u, ratioClassMap e h₀ h₀' hφ v) : Quotient _) :
          RatioInterp q' htr' hcomp' h₀') := fun _ _ ↦ rfl
  have hinj := (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ).injective
  unfold RatioMulGraph
  constructor
  · rintro (⟨hrs, ht⟩ | ⟨u₁, u₂, v₁, v₂, w₁, w₂, hr, hs, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, ht⟩)
    · exact Or.inl ⟨hrs.imp (fun h ↦ hinj (h.trans hΦ0.symm)) fun h ↦ hinj (h.trans hΦ0.symm),
        hinj (ht.trans hΦ0.symm)⟩
    · -- Pull the target witnesses back along the class map.
      obtain ⟨u₁, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective u₁
      obtain ⟨u₂, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective u₂
      obtain ⟨v₁, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective v₁
      obtain ⟨v₂, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective v₂
      obtain ⟨w₁, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective w₁
      obtain ⟨w₂, rfl⟩ := (ratioClassMap e h₀ h₀' hφ).surjective w₂
      exact Or.inr ⟨u₁, u₂, v₁, v₂, w₁, w₂, hinj (hr.trans (hΦmk u₁ u₂).symm),
        hinj (hs.trans (hΦmk v₁ v₂).symm),
        ⟨(jMulRel_map_iff e (u := u₁.1) (v := v₁.1) (w := w₁.1)).1 m₁,
          (pointTripleIndependent_map_iff e (X := u₁.1 0) (Y := v₁.1 0) (A := u₁.1 4)).1 g₁⟩,
        ⟨(jMulRel_map_iff e (u := u₂.1) (v := v₂.1) (w := w₂.1)).1 m₂,
          (pointTripleIndependent_map_iff e (X := u₂.1 0) (Y := v₂.1 0) (A := u₂.1 4)).1 g₂⟩,
        hinj (ht.trans (hΦmk w₁ w₂).symm)⟩
  · rintro (⟨rfl | rfl, rfl⟩ | ⟨u₁, u₂, v₁, v₂, w₁, w₂, rfl, rfl, ⟨m₁, g₁⟩, ⟨m₂, g₂⟩, rfl⟩)
    · exact Or.inl ⟨Or.inl hΦ0, hΦ0⟩
    · exact Or.inl ⟨Or.inr hΦ0, hΦ0⟩
    · exact Or.inr ⟨ratioClassMap e h₀ h₀' hφ u₁, ratioClassMap e h₀ h₀' hφ u₂,
        ratioClassMap e h₀ h₀' hφ v₁, ratioClassMap e h₀ h₀' hφ v₂,
        ratioClassMap e h₀ h₀' hφ w₁, ratioClassMap e h₀ h₀' hφ w₂, hΦmk u₁ u₂, hΦmk v₁ v₂,
        ⟨(jMulRel_map_iff e).2 m₁, (pointTripleIndependent_map_iff e).2 g₁⟩,
        ⟨(jMulRel_map_iff e).2 m₂, (pointTripleIndependent_map_iff e).2 g₂⟩, hΦmk w₁ w₂⟩

end

end AclGeom
