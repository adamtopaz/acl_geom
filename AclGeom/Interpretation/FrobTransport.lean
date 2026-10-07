/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Transport
import AclGeom.Interpretation.FrobClass

/-!
# Transport of the Frobenius-link relations along lattice isomorphisms

An order isomorphism `e : ClosedIF k K ≃o ClosedIF l L` of closed-subfield lattices acts on points
by `Point.map e` and on tuples by composition.  It preserves the geometric relations of the
Frobenius-link language (blueprint §10).  This is the second step of the naturality of the
interpretation (checklist I6), after `AclGeom.Config.Transport`.

* `mulPoint_map_iff`: the derived product relation `MulPoint`.
* `isJTuple_map_iff`: membership in the geometric `J`-locus.
* `pointTripleIndependent_map_iff`: the rank-three genericity clause.
* `directFrobLink_map_iff`: directed Frobenius links, with all five fields and one common
  multiplier for the three rigid coordinates.
* `frobEq_map_iff`: the bridge relation, with its bridge tuple and edge orientations.

These are invariance statements only.  They supply neither reflexivity nor transitivity of
`FrobEq`, and they do not make the derived relation `MulPoint` functional.

The proofs are purely order-theoretic.  No semantics, completeness, perfection, rank hypothesis or
fresh element is used, and the bases and ambient fields are arbitrary.  Witness points and tuples
on the target side are pulled back by the bijections `Point.map e` and
`Equiv.piCongrRight fun _ ↦ Point.map e`.

**Status:** geometric Frobenius-link transport is complete (#23/#8, I6b2a).
Conditional class/carrier and graph transport, the same geometric map bundled as a RingEquiv,
and its composition with both decodings are proved in `Naturality` under explicit carrier inputs.
Canonical image-base existence and conditional field-isomorphism existence are also proved there;
the source pair and target rank are derived inline from source rank five and the lattice map.
Both perfections, separate exponential characteristics and both ACF-completeness inputs remain
explicit. Unconditional completeness, base/scalar recovery, `Induces` and full reconstruction
remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- **The derived product relation is invariant** under order isomorphisms of closed lattices.
This is invariance only: it does not make `MulPoint` functional. -/
theorem mulPoint_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {U V W : Point k K} :
    MulPoint (Point.map e U) (Point.map e V) (Point.map e W) ↔ MulPoint U V W := by
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨S₀, rfl⟩ := (Point.map e).surjective S
    exact ⟨S₀, (q'Geom_map_iff e).1 hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨Point.map e S, (q'Geom_map_iff e).2 hS⟩

/-- **Membership in the geometric `J`-locus is invariant** under order isomorphisms of closed
lattices. -/
theorem isJTuple_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u : Fin 5 → Point k K} :
    IsJTuple (Point.map e ∘ u) ↔ IsJTuple u := by
  unfold IsJTuple
  exact jGeom_map_iff e

/-- **The rank-three genericity clause is invariant** under order isomorphisms of closed
lattices. -/
theorem pointTripleIndependent_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {X Y A : Point k K} :
    PointTripleIndependent (Point.map e X) (Point.map e Y) (Point.map e A) ↔
      PointTripleIndependent X Y A := by
  simp only [PointTripleIndependent, Point.map_coe, ← map_sup, rankEq_map_iff]

/-- **Directed Frobenius links are invariant** under order isomorphisms of closed lattices.  All
five fields transfer, with a single common multiplier for the three rigid coordinates. -/
theorem directFrobLink_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v : Fin 5 → Point k K} :
    DirectFrobLink (Point.map e ∘ u) (Point.map e ∘ v) ↔ DirectFrobLink u v := by
  constructor
  · intro h
    obtain ⟨C, hC₀, hC₂, hC₃⟩ := h.multiplier
    obtain ⟨C₀, rfl⟩ := (Point.map e).surjective C
    exact
      { source_mem := (isJTuple_map_iff e).1 h.source_mem
        target_mem := (isJTuple_map_iff e).1 h.target_mem
        parameter_eq := (Point.map e).injective h.parameter_eq
        independent := (pointTripleIndependent_map_iff e).1 h.independent
        multiplier := ⟨C₀, (mulPoint_map_iff e).1 hC₀, (mulPoint_map_iff e).1 hC₂,
          (mulPoint_map_iff e).1 hC₃⟩ }
  · intro h
    obtain ⟨C, hC₀, hC₂, hC₃⟩ := h.multiplier
    exact
      { source_mem := (isJTuple_map_iff e).2 h.source_mem
        target_mem := (isJTuple_map_iff e).2 h.target_mem
        parameter_eq := congrArg (Point.map e) h.parameter_eq
        independent := (pointTripleIndependent_map_iff e).2 h.independent
        multiplier := ⟨Point.map e C, (mulPoint_map_iff e).2 hC₀, (mulPoint_map_iff e).2 hC₂,
          (mulPoint_map_iff e).2 hC₃⟩ }

/-- **The bridge relation is invariant** under order isomorphisms of closed lattices.  A bridge
tuple and its two direct edges, in their given orientations, transfer in both directions.  This
supplies neither reflexivity nor transitivity of `FrobEq`. -/
theorem frobEq_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {u v : Fin 5 → Point k K} :
    FrobEq (Point.map e ∘ u) (Point.map e ∘ v) ↔ FrobEq u v := by
  -- Direct edges transfer link by link, in both orientations.
  have edge : ∀ a b : Fin 5 → Point k K,
      DirectFrobEdge (Point.map e ∘ a) (Point.map e ∘ b) ↔ DirectFrobEdge a b := fun _ _ ↦ by
    unfold DirectFrobEdge
    exact or_congr (directFrobLink_map_iff e) (directFrobLink_map_iff e)
  constructor
  · rintro ⟨w, hw, huw, hwv⟩
    obtain ⟨w₀, rfl⟩ := (Equiv.piCongrRight fun _ : Fin 5 ↦ Point.map e).surjective w
    exact ⟨w₀, (isJTuple_map_iff e (u := w₀)).1 hw, (edge u w₀).1 huw, (edge w₀ v).1 hwv⟩
  · rintro ⟨w, hw, huw, hwv⟩
    exact ⟨Point.map e ∘ w, (isJTuple_map_iff e).2 hw, (edge u w).2 huw, (edge w v).2 hwv⟩

end

end AclGeom
