/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Quadrangle
import AclGeom.Correspondence.CurveIdeal

/-!
# The atom clause: no rank-one parameter captures a generic line

Clause (iv) of Ψ at the soundness witness: for every atom `A' ≤ A`, the
generic point `X` is not below `A' ∨ Y` — concretely, for `t ∈ racl{u, v}`
transcendental, the generic direction `w` is not algebraic over
`{t, uw + v}`.

The blueprint proves this by the minimal-parameter derivation calculation;
this file follows the elementary *specialization route* instead (design
note on the project tracker): exchange converts the hypothesis into
`uw + v ∈ racl_{K₀}{w}` over the closed base `K₀ = racl{t}`; a nonzero
two-variable relation `G` over `K₀` then vanishes identically under the
substitution `X₁ ↦ uT + v` because `w` is transcendental over
`racl{u, v}`; specializing `T` at two base points `ξ₁ ≠ ξ₂` of `k` where
the `Y`-collapse of `G` stays nonzero puts `uξᵢ + v` into `racl{t}`, and
differencing recovers `u` and `v` there — contradicting the independence
of the coefficients, since `t` is interalgebraic with a rank-one closure.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness, clause (iv)).
-/

namespace AclGeom

noncomputable section

open IntermediateField

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section LineClause

/-- Elements outside a relative algebraic closure are transcendental over
it as a base field. -/
theorem transcendental_racl_of_notMem {S : Set K} {z : K}
    (h : z ∉ racl k S) : Transcendental ↥(racl k S) z := by
  intro halg
  exact h (IsRAC.mem_of_isAlgebraic (isRAC_racl S) halg)

variable {u v w t : K}

/-- Exchange reduction for the atom clause: if the generic direction `w`
were algebraic over the atom parameter and the line value, the line value
would be algebraic over `{w, t}`. -/
theorem line_mem_of_mem (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (hmem : w ∈ racl k ({t, u * w + v} : Set K)) :
    u * w + v ∈ racl k ({w, t} : Set K) := by
  have hwt : w ∉ racl k ({t} : Set K) := fun h ↦
    hw (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) h)
  have hmem' : w ∈ racl k (insert (u * w + v) ({t} : Set K)) := by
    rwa [Set.pair_comm t (u * w + v)] at hmem
  exact racl_exchange hmem' hwt

/-- The line value is algebraic over the direction alone, once the atom
closure is promoted to the base field. -/
theorem line_mem_over_base (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
  have h1 : u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w, t} : Set K) :=
    racl_subset_racl_base (racl k ({t} : Set K)) ({w, t} : Set K) h
  have ht' : t ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
    have hmem : algebraMap ↥(racl k ({t} : Set K)) K
        ⟨t, subset_racl k _ rfl⟩ ∈
        racl ↥(racl k ({t} : Set K)) ({w} : Set K) :=
      IntermediateField.algebraMap_mem _ _
    simpa using hmem
  have h2 : ({w, t} : Set K) = insert t ({w} : Set K) :=
    Set.pair_comm w t
  rw [h2, racl_insert_of_mem ht'] at h1
  exact h1

/-- A nonzero two-variable relation over the atom base: the vanishing
ideal of `(w, uw+v)` over `racl{t}` contains a nonzero polynomial. -/
theorem exists_line_relation (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    ∃ G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K)), G ≠ 0 ∧
      MvPolynomial.aeval ![w, u * w + v] G = 0 := by
  have hbot : idealOf ↥(racl k ({t} : Set K)) ![w, u * w + v] ≠ ⊥ :=
    idealOf_ne_bot_of_mem_racl _ (line_mem_over_base h)
  obtain ⟨G, hGmem, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact ⟨G, hG0, (mem_idealOf_iff _).1 hGmem⟩

end LineClause

end

end AclGeom
