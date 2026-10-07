/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobLinkIncidence
import AclGeom.Interpretation.FrobLinkRelative

/-!
# The direct Frobenius link on semantic `j`-tuples

A direct Frobenius link between two semantic `j`-tuples `j(x, a)` and `j(y, a')` twists the
parameter by a power of Frobenius: `a' = a^{q^s}` or `a = a'^{q^s}`.  This is the direct-link
step of the converse direction of blueprint Lemma `frobeq-correct` (EH95 Lemma 2.8).

The argument uses three facts about the link.
* Its multiplier point lies on the three lines `[x] ⊔ [y]`, `[ax] ⊔ [a'y]` and
  `[(1+a)x] ⊔ [(1+a')y]` (`DirectFrobLink.exists_concurrent`).
* Its rank clause makes `x, y, a` algebraically independent.
* Its shared parameter point gives `[a] = [a']`.

The algebraic incidence-rigidity theorem then concludes, in its relative form
`frobenius_of_concurrent_lines_rel`, so no closure hypothesis on `k` or `K` is needed.

Only the link's own diagrams and the two semantic witnesses are used; configuration completeness
(`JGeom → JSem`) is not.  The witnesses enter as the coordinate equations of `JSem`, so a caller
holding `hu : JSem u` writes `obtain ⟨x, a, -, hu⟩ := hu`.  The two-link bridge `FrobEq` is a
separate, later step.

**Status:** direct-link rigidity for the displayed semantic witnesses is proved over any base
field. Geometric bridge completeness remains open (#23).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Three principal closures of rank three have algebraically independent generators. -/
theorem algebraicIndependent_of_rankEq_three_points {x y a : K}
    (h : RankEq 3 (point k x ⊔ (point k y ⊔ point k a))) :
    AlgebraicIndependent k ![x, y, a] := by
  refine algebraicIndependent_of_rankEq_iSup_point (h.congr (Subtype.ext ?_))
  rw [coe_sup_point₃, coe_iSup_point, range_triple]

/-- **A direct Frobenius link between semantic `j`-tuples twists the parameter by Frobenius.**
Suppose the source `u` and the target `v` of a direct link have the semantic coordinates
`j(x, a) = ([x], [x+a], [xa], [x+xa], [a])` and `j(y, a')`.  Then `a' = a^{q^s}` or
`a = a'^{q^s}` for some `s`.

The coordinate hypotheses are the conjunctions inside `JSem`.  The independence of each witness pair
is not needed, since the link's rank clause supplies the independence of `x, y, a`. -/
theorem DirectFrobLink.frobenius_of_witnesses (q : ℕ) [ExpChar k q]
    {u v : Fin 5 → Point k K} (h : DirectFrobLink u v) {x a y a' : K}
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s := by
  obtain ⟨hu0, -, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv0, -, hv2, hv3, hv4⟩ := hv
  -- The shared parameter point: `[a] = [a']`.
  have hpar : point k a = point k a' := by
    calc point k a = (u 4).1 := hu4.symm
      _ = (v 4).1 := by rw [h.parameter_eq]
      _ = point k a' := hv4
  obtain ⟨haa', ha'a⟩ := point_eq_point_iff.1 hpar
  -- The rank clause: `x, y, a` are independent.
  have hind : AlgebraicIndependent k ![x, y, a] := by
    have hr := h.independent
    unfold PointTripleIndependent at hr
    rw [hu0, hv0, hu4] at hr
    exact algebraicIndependent_of_rankEq_three_points hr
  -- The multiplier point lies on the three lines.
  obtain ⟨C, h0, h2, h3⟩ := h.exists_concurrent
  have hL1 : C.rep ∈ racl k ({y, x} : Set K) :=
    point_rep_mem_of_le (by simpa only [hv0, hu0] using h0)
  have hL2 : C.rep ∈ racl k ({y * a', x * a} : Set K) :=
    point_rep_mem_of_le (by simpa only [hv2, hu2] using h2)
  have hL3 : C.rep ∈ racl k ({y + y * a', x + x * a} : Set K) :=
    point_rep_mem_of_le (by simpa only [hv3, hu3] using h3)
  rw [Set.pair_comm] at hL1
  rw [Set.pair_comm, mul_comm x a, mul_comm y a'] at hL2
  rw [Set.pair_comm, show x + x * a = (1 + a) * x by ring,
    show y + y * a' = (1 + a') * y by ring] at hL3
  exact frobenius_of_concurrent_lines_rel q hind (mem_point.1 ha'a) (mem_point.1 haa')
    (point_rep_notMem_empty C) hL1 hL2 hL3

/-- **Either orientation of a direct Frobenius edge twists the parameter by Frobenius.**  The
conclusion is symmetric in `a, a'`, so a direct link in either direction gives it. -/
theorem DirectFrobEdge.frobenius_of_witnesses (q : ℕ) [ExpChar k q]
    {u v : Fin 5 → Point k K} (h : DirectFrobEdge u v) {x a y a' : K}
    (hu : (u 0).1 = point k x ∧ (u 1).1 = point k (x + a) ∧ (u 2).1 = point k (x * a) ∧
      (u 3).1 = point k (x + x * a) ∧ (u 4).1 = point k a)
    (hv : (v 0).1 = point k y ∧ (v 1).1 = point k (y + a') ∧ (v 2).1 = point k (y * a') ∧
      (v 3).1 = point k (y + y * a') ∧ (v 4).1 = point k a') :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s := by
  rcases h with h | h
  · exact h.frobenius_of_witnesses q hu hv
  · obtain ⟨s, hs⟩ := h.frobenius_of_witnesses q hv hu
    exact ⟨s, hs.symm⟩

end AclGeom
