/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Points

/-!
# Equivalence of the lattice and point-geometry presentations

The combinatorial geometry attached to `𝒢(K/k)` has as points the atoms of
the closed lattice, with closure
`pointCl S = {P | P ≤ ⨆ (Q ∈ S), Q}`. This file provides
(blueprint §Point geometry and equivalence of presentations):

* `Point k K` and `pointCl`, with extensivity, monotonicity, idempotence;
* `Point.rep`/`Point.point_rep`: a chosen generator for each point;
* `sSup_point_image`: the supremum of points of generators is the relative
  algebraic closure of the set of generators — the bridge between point
  suprema and `racl`;
* exchange for `pointCl` (`pointCl_exchange`);
* the inverse order isomorphisms between `ClosedIF k K` and the closed point
  sets (`ClosedIF.pointSetIso`).

Transport of order isomorphisms to geometry equivalences (eq. 20.3) comes
with the functorial layer; finite character of `pointCl` comes with finite
rank (F6).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M1, checklist F5).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

variable (k K) in
/-- The points of the combinatorial geometry of `K/k`: atoms of the closed
lattice `𝒢(K/k)`. -/
def Point := {P : ClosedIF k K // IsAtom P}

namespace Point

instance : PartialOrder (Point k K) := Subtype.partialOrder _

/-- A chosen generator of a point: `P = point k (P.rep)`. -/
def rep (P : Point k K) : K :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose

theorem rep_notMem_bot (P : Point k K) : P.rep ∉ (⊥ : ClosedIF k K) :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose_spec.1

@[simp] theorem point_rep (P : Point k K) : ClosedIF.point k P.rep = P.1 :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose_spec.2.symm

theorem mem_rep (P : Point k K) : P.rep ∈ P.1 := by
  rw [← point_rep]
  exact ClosedIF.mem_point_self _

end Point

variable (k) in
/-- The point attached to an element `x ∉ ⊥`. -/
def Point.mk' (x : K) (hx : x ∉ (⊥ : ClosedIF k K)) : Point k K :=
  ⟨ClosedIF.point k x, ClosedIF.isAtom_point hx⟩

/-- The closure operation of the point geometry: `P` lies in the closure of
`S` when `P` is below the join of `S` (blueprint §Foundation II). -/
def pointCl (S : Set (Point k K)) : Set (Point k K) :=
  {P | P.1 ≤ sSup (Subtype.val '' S)}

theorem mem_pointCl_iff {S : Set (Point k K)} {P : Point k K} :
    P ∈ pointCl S ↔ P.1 ≤ sSup (Subtype.val '' S) := Iff.rfl

theorem subset_pointCl (S : Set (Point k K)) : S ⊆ pointCl S :=
  fun P hP ↦ mem_pointCl_iff.2 (le_sSup ⟨P, hP, rfl⟩)

theorem pointCl_mono {S T : Set (Point k K)} (h : S ⊆ T) :
    pointCl S ⊆ pointCl T := fun _ hP ↦
  mem_pointCl_iff.2 ((mem_pointCl_iff.1 hP).trans (sSup_le_sSup (Set.image_mono h)))

/-- The join of the closure of `S` is the join of `S`. -/
theorem sSup_pointCl (S : Set (Point k K)) :
    sSup (Subtype.val '' pointCl S) = sSup (Subtype.val '' S) :=
  le_antisymm (sSup_le (by rintro - ⟨P, hP, rfl⟩; exact mem_pointCl_iff.1 hP))
    (sSup_le_sSup (Set.image_mono (subset_pointCl S)))

theorem pointCl_idem (S : Set (Point k K)) : pointCl (pointCl S) = pointCl S :=
  Set.eq_of_subset_of_subset
    (fun _ hP ↦ mem_pointCl_iff.2
      ((mem_pointCl_iff.1 hP).trans_eq (sSup_pointCl S)))
    (subset_pointCl _)

/-- The supremum of the points of a set of generators is the relative
algebraic closure of that set: the bridge between the point geometry and
`racl`. -/
theorem sSup_point_image (A : Set K) :
    (sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 = racl k A := by
  refine le_antisymm ?_ ?_
  · have h : sSup ((fun x ↦ ClosedIF.point k x) '' A) ≤
        ⟨racl k A, isRAC_racl A⟩ := by
      refine sSup_le ?_
      rintro - ⟨x, hx, rfl⟩
      exact ClosedIF.point_le_iff.2 (subset_racl k A hx)
    exact ClosedIF.le_iff.1 h
  · have h : A ⊆ ((sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 : Set K) := by
      intro x hx
      have : ClosedIF.point k x ≤ sSup ((fun x ↦ ClosedIF.point k x) '' A) :=
        le_sSup ⟨x, hx, rfl⟩
      exact (ClosedIF.le_iff.1 this) (ClosedIF.mem_point_self x)
    calc racl k A ≤ racl k ((sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 : Set K) :=
          racl_mono h
    _ = _ := isRAC_iff_racl_eq.1 (sSup ((fun x ↦ ClosedIF.point k x) '' A)).2

/-- Membership in a point closure, in terms of representatives: `P ∈ cl S`
iff the generator of `P` is algebraic over the generators of `S`. -/
theorem mem_pointCl_iff_rep_mem {S : Set (Point k K)} {P : Point k K} :
    P ∈ pointCl S ↔ P.rep ∈ racl k (Point.rep '' S) := by
  have himg : (fun x ↦ ClosedIF.point k x) '' (Point.rep '' S) = Subtype.val '' S := by
    rw [← Set.image_comp]
    exact Set.image_congr fun Q _ ↦ Q.point_rep
  have hval : ((sSup (Subtype.val '' S)).1 : IntermediateField k K)
      = racl k (Point.rep '' S) := by
    rw [← himg]
    exact sSup_point_image _
  rw [mem_pointCl_iff, ← P.point_rep, ClosedIF.point_le_iff]
  change P.rep ∈ (sSup (Subtype.val '' S)).1 ↔ _
  rw [hval]

/-- Exchange for the point geometry (blueprint §Foundation II): if
`P ∈ cl (S ∪ {Q})` but `P ∉ cl S`, then `Q ∈ cl (S ∪ {P})`. -/
theorem pointCl_exchange {S : Set (Point k K)} {P Q : Point k K}
    (hP : P ∈ pointCl (insert Q S)) (hP' : P ∉ pointCl S) :
    Q ∈ pointCl (insert P S) := by
  rw [mem_pointCl_iff_rep_mem] at hP hP' ⊢
  rw [Set.image_insert_eq] at hP ⊢
  exact racl_exchange hP hP'

section PointSetIso

variable (k K) in
/-- The closed point sets: fixed points of `pointCl`. -/
def ClosedPointSet := {S : Set (Point k K) // pointCl S = S}

instance : PartialOrder (ClosedPointSet k K) := Subtype.partialOrder _

namespace ClosedIF

/-- The set of points below a closed intermediate field. -/
def toPointSet (E : ClosedIF k K) : Set (Point k K) :=
  {P | P.1 ≤ E}

theorem pointCl_toPointSet (E : ClosedIF k K) :
    pointCl (toPointSet E) = toPointSet E := by
  refine Set.eq_of_subset_of_subset (fun P hP ↦ ?_) (subset_pointCl _)
  rw [mem_pointCl_iff] at hP
  refine hP.trans (sSup_le ?_)
  rintro - ⟨Q, hQ, rfl⟩
  exact hQ

/-- Every closed intermediate field is the join of its points
(atomisticity, packaged for the equivalence). -/
theorem sSup_toPointSet (E : ClosedIF k K) :
    sSup (Subtype.val '' toPointSet E) = E := by
  have : Subtype.val '' toPointSet E = {P : ClosedIF k K | IsAtom P ∧ P ≤ E} := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.2, hQ⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨P, h1⟩, h2, rfl⟩
  rw [this, sSup_atoms_le_eq]

variable (k K) in
/-- The two presentations of the geometry agree: the closed lattice is order
isomorphic to the lattice of closed point sets
(blueprint §Point geometry and equivalence of presentations). -/
def pointSetIso : ClosedIF k K ≃o ClosedPointSet k K where
  toFun E := ⟨toPointSet E, pointCl_toPointSet E⟩
  invFun S := sSup (Subtype.val '' S.1)
  left_inv E := sSup_toPointSet E
  right_inv S := by
    refine Subtype.ext ?_
    change toPointSet (sSup (Subtype.val '' S.1)) = S.1
    exact S.2
  map_rel_iff' {E F} := by
    constructor
    · intro h
      have h' : toPointSet E ⊆ toPointSet F := h
      have h2 : sSup (Subtype.val '' toPointSet E) ≤
          sSup (Subtype.val '' toPointSet F) := sSup_le_sSup (Set.image_mono h')
      rwa [sSup_toPointSet, sSup_toPointSet] at h2
    · intro h P hP
      exact le_trans hP h

end ClosedIF

end PointSetIso

end

end AclGeom
