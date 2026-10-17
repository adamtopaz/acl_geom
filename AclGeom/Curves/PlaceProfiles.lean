/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.PlaceAction

/-!
# Finite normalized-order profiles distinguish places

A finite family of places of a one-variable function field can be distinguished by the
orders of finitely many nonzero elements of any domain with that fraction field. Distinct
valuation rings give an element with different order signs. Writing it as a fraction shows
that a numerator or denominator distinguishes their orders.

Named consumer: locally closed orbit fibers for the actual scheme boundary in
`SchemePlaceFixed`. That consumer uses the genuine global-section domain and derives the
finite family from the affine curve, with no caller-supplied separation certificate.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom.Place

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- Finitely many nonzero section values distinguish any finite family of places.
Named consumer: the actual affine-curve boundary's orbit fibers in `SchemePlaceFixed`. -/
theorem exists_finset_ord_separating (R : Type*) [CommRing R] [IsDomain R] [Algebra R F]
    [IsFractionRing R F] {B : Set (Place k F)} (hB : B.Finite) :
    ∃ s : Finset R, (∀ a ∈ s, algebraMap R F a ≠ 0) ∧
      ∀ P ∈ B, ∀ Q ∈ B, (∀ a ∈ s,
        P.ord (algebraMap R F a) = Q.ord (algebraMap R F a)) → P = Q := by
  classical
  have hpair : ∀ P Q : Place k F, P ≠ Q →
      ∃ a : R, algebraMap R F a ≠ 0 ∧
        P.ord (algebraMap R F a) ≠ Q.ord (algebraMap R F a) := by
    intro P Q hPQ
    by_contra hn
    push Not at hn
    apply hPQ
    apply ext_val
    apply SetLike.ext
    intro f
    by_cases hf : f = 0
    · subst f
      simp only [zero_mem]
    have ho : P.ord f = Q.ord f := by
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R f
      have hbF : algebraMap R F b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have haF : algebraMap R F a ≠ 0 := by
        intro ha
        apply hf
        rw [← hab, ha, zero_div]
      rw [← hab, div_eq_mul_inv, P.ord_mul haF (inv_ne_zero hbF),
        Q.ord_mul haF (inv_ne_zero hbF), P.ord_inv hbF, Q.ord_inv hbF,
        hn a haF, hn b hbF]
    rw [← P.val.valuation_le_one_iff f, ← Q.val.valuation_le_one_iff f,
      ← P.ord_nonneg_iff hf, ← Q.ord_nonneg_iff hf, ho]
  let T := (hB.toFinset ×ˢ hB.toFinset).filter fun pq ↦ pq.1 ≠ pq.2
  have ht : ∀ pq : T, ∃ a : R, algebraMap R F a ≠ 0 ∧
      pq.1.1.ord (algebraMap R F a) ≠ pq.1.2.ord (algebraMap R F a) := by
    intro pq
    exact hpair pq.1.1 pq.1.2 (Finset.mem_filter.1 pq.2).2
  choose a ha using ht
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · intro r hr
    obtain ⟨pq, _, rfl⟩ := Finset.mem_image.1 hr
    exact (ha pq).1
  · intro P hP Q hQ ho
    by_contra hPQ
    have hmem : (P, Q) ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset]
      exact ⟨⟨hP, hQ⟩, hPQ⟩
    let pq : T := ⟨(P, Q), hmem⟩
    exact (ha pq).2 (ho (a pq) (Finset.mem_image.2 ⟨pq, Finset.mem_univ _, rfl⟩))

end

end AclGeom.Place
