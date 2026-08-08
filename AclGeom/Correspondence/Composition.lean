/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints

/-!
# Composition of correspondence germs at generic points

The opening of the correspondence calculus (blueprint §8.1, checklist C2)
in the elementwise presentation of the rational-curve route (design issue
on the project tracker): an irreducible finite correspondence germ between
two point-curves is presented by an interalgebraic pair of transcendental
elements, and composition happens at a *shared middle representative*:

* `mem_racl_trans` / `comp_pair_of_shared_middle`: with a literally shared
  middle, the composite pair is automatically interalgebraic — all content
  lives in the matching step;
* `exists_pair_relocation_fixing`: the matching step — a germ presentation
  `(w', u)` relocates onto any prescribed interalgebraic representative
  `w` of its source point, preserving the vanishing ideal and hence the
  germ. This is blueprint Lemma 8.1(b) with the transcendence basis pinned
  to a prescribed image.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4a, issue #12 pipeline step 1).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section SharedMiddle

/-- Interalgebraicity is transitive through a shared middle element. -/
theorem mem_racl_trans {z w u : Ω} (hzw : z ∈ racl k ({w} : Set Ω))
    (hwu : w ∈ racl k ({u} : Set Ω)) : z ∈ racl k ({u} : Set Ω) :=
  racl_le_of_subset_racl (Set.singleton_subset_iff.2 hwu) hzw

/-- Composition of correspondence germs at a shared middle
representative: the composite pair is interalgebraic. -/
theorem comp_pair_of_shared_middle {z w u : Ω}
    (hzw : z ∈ racl k ({w} : Set Ω)) (hwz : w ∈ racl k ({z} : Set Ω))
    (hwu : u ∈ racl k ({w} : Set Ω)) (huw : w ∈ racl k ({u} : Set Ω)) :
    u ∈ racl k ({z} : Set Ω) ∧ z ∈ racl k ({u} : Set Ω) :=
  ⟨mem_racl_trans hwu hwz, mem_racl_trans hzw huw⟩

end SharedMiddle

section Matching

/-- **The matching step of germ composition** (blueprint Lemma 8.1(b),
pinned form): a correspondence-germ presentation `(w', u)` relocates onto
any prescribed interalgebraic representative `w` of its source point —
there is `u'` with the pair `(w, u')` carrying the same vanishing ideal
as `(w', u)`. -/
theorem exists_pair_relocation_fixing [IsAlgClosed Ω] {w' u w : Ω}
    (hw'0 : w' ∉ racl k (∅ : Set Ω))
    (hu : u ∈ racl k ({w'} : Set Ω))
    (hw0 : w ∉ racl k (∅ : Set Ω)) :
    ∃ u' : Ω, idealOf k ![w, u'] = idealOf k ![w', u] := by
  classical
  -- The transcendence data for the relocation.
  have hw'tr : Transcendental k w' := fun halg ↦
    hw'0 (mem_racl_empty_of_isAlgebraic halg)
  have hwtr : Transcendental k w := fun halg ↦
    hw0 (mem_racl_empty_of_isAlgebraic halg)
  have ht : AlgebraicIndependent k ![w'] :=
    algebraicIndependent_unique_type_iff.2 hw'tr
  have hs : AlgebraicIndependent k ![w] :=
    algebraicIndependent_unique_type_iff.2 hwtr
  have hrt : Set.range (![w'] : Fin 1 → Ω) = ({w'} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
  have hrs : Set.range (![w] : Fin 1 → Ω) = ({w} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
  have hra : Set.range (![w', u] : Fin 2 → Ω) = ({w', u} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  have hle : adjoin k (Set.range (![w'] : Fin 1 → Ω)) ≤
      adjoin k (Set.range (![w', u] : Fin 2 → Ω)) := by
    rw [hrt, hra]
    exact adjoin.mono _ _ _ (by simp)
  have halg : Algebra.IsAlgebraic
      ↥(adjoin k (Set.range (![w'] : Fin 1 → Ω)))
      ↥(extendScalars hle) := by
    refine isAlgebraic_extendScalars_adjoin hle ?_
    intro x hx
    rw [hra] at hx
    rw [hrt]
    rcases hx with rfl | hx
    · have hmem : x ∈ adjoin k ({x} : Set Ω) := subset_adjoin k _ rfl
      have h := isAlgebraic_algebraMap
        (R := ↥(adjoin k ({x} : Set Ω))) (A := Ω) ⟨x, hmem⟩
      simpa using h
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (mem_racl_iff k).1 hu
  -- The relocation embedding, with the basis pinned to `w`.
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic (halg := halg) hle
    (adjoinTranscendentalAlgHom ht hs)
  set ta : Fin 2 → ↥(adjoin k (Set.range (![w', u] : Fin 2 → Ω))) :=
    fun j ↦ ⟨(![w', u] : Fin 2 → Ω) j, subset_adjoin k _ ⟨j, rfl⟩⟩
    with hta
  refine ⟨ψ (ta 1), ?_⟩
  -- The relocated tuple starts at `w`.
  have hb0 : ψ (ta 0) = w := by
    have hmem : w' ∈ adjoin k (Set.range (![w'] : Fin 1 → Ω)) := by
      rw [hrt]
      exact subset_adjoin k _ rfl
    have h1 : ta 0 = ⟨w', hle hmem⟩ := Subtype.ext rfl
    rw [h1, hψ ⟨w', hmem⟩]
    have h2 : (⟨w', hmem⟩ :
        ↥(adjoin k (Set.range (![w'] : Fin 1 → Ω)))) =
        ⟨(![w'] : Fin 1 → Ω) 0, subset_adjoin k _ ⟨0, rfl⟩⟩ := rfl
    rw [h2, adjoinTranscendentalAlgHom_apply]
    exact rfl
  have hbfun : (![w, ψ (ta 1)] : Fin 2 → Ω) = fun j ↦ ψ (ta j) := by
    funext j
    fin_cases j
    · exact hb0.symm
    · rfl
  rw [hbfun]
  -- Same vanishing ideal: evaluation factors through the embedding.
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval (fun j ↦ ψ (ta j)) f =
      ψ (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval (![w', u] : Fin 2 → Ω) f =
      (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val
        (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro h
    have h4 : ψ (MvPolynomial.aeval ta f) = ψ 0 := by
      rw [map_zero]
      exact h
    rw [ψ.injective h4, map_zero]
  · intro h
    have h4 : (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val
        (MvPolynomial.aeval ta f) =
        (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val 0 := by
      rw [map_zero]
      exact h
    rw [(adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val.injective h4,
      map_zero]

end Matching

end

end AclGeom
