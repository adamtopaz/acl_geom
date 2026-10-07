/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Geometry.FiniteRank
import AclGeom.Closure.Ambient
import Mathlib.Logic.Equiv.Set

/-!
# Transport between the point and lattice presentations

A closure-preserving equivalence of point geometries induces a unique order
isomorphism of closed intermediate-field lattices, and restricting it to atoms
recovers the original equivalence. Conversely, an order isomorphism transports
independent point tuples, finite geometric ranks, and arbitrary independent
families of field representatives. Exact finite geometric rank agrees with
transcendence degree, which is invariant with universe lifts when necessary.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.

These are the presentation and dimension interfaces used by the lattice form
of M5 transfer and the rank-five reconstruction variants (issues #7, #9, #24).

**Status:** the presentation transport and transcendence-degree invariant are
proved; the other foundational carryovers are tracked in issue #24.
-/
namespace AclGeom
noncomputable section

universe u v
variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

section PointPresentation

/-- A closure-preserving point equivalence commutes with point closure.
This helper is used to transport closed point sets to the other geometry. -/
theorem pointCl_image_of_equiv (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S)
    (S : Set (Point k K)) : pointCl (e '' S) = e '' pointCl S := by
  ext Q
  obtain ⟨P, rfl⟩ := e.surjective Q
  rw [hcl]
  simp only [Equiv.image_eq_preimage_symm, Set.mem_preimage, e.symm_apply_apply]

/-- A geometry equivalence induces an order isomorphism of closed point
sets. This is the converse presentation bridge in blueprint §4. -/
def closedPointSetIsoOfPointEquiv (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S) :
    ClosedPointSet k K ≃o ClosedPointSet l L where
  toEquiv := e.setCongr.subtypeEquiv (fun S ↦ by
    change pointCl S = S ↔ pointCl (e '' S) = e '' S
    rw [pointCl_image_of_equiv e hcl]
    constructor
    · intro hS
      rw [hS]
    · intro hS
      exact e.setCongr.injective hS)
  map_rel_iff' := Set.image_subset_image_iff e.injective

/-- A closure-preserving bijection of point geometries induces an order
isomorphism of closed intermediate-field lattices. -/
def latticeIsoOfPointEquiv (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S) :
    ClosedIF k K ≃o ClosedIF l L :=
  ((ClosedIF.pointSetIso k K).trans
    (closedPointSetIsoOfPointEquiv e hcl)).trans
      (ClosedIF.pointSetIso l L).symm

/-- The induced lattice isomorphism sends the point set of a closed field
exactly to its image under the original geometry equivalence. -/
theorem latticeIsoOfPointEquiv_toPointSet (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S)
    (E : ClosedIF k K) :
    ClosedIF.toPointSet (latticeIsoOfPointEquiv e hcl E) =
      e '' ClosedIF.toPointSet E := by
  have h := (ClosedIF.pointSetIso l L).apply_symm_apply
    (closedPointSetIsoOfPointEquiv e hcl (ClosedIF.pointSetIso k K E))
  exact congrArg Subtype.val h

/-- The closed point set of an atom is its singleton. This identifies the
point map of the lattice isomorphism induced by a geometry equivalence. -/
theorem ClosedIF.toPointSet_point (P : Point k K) :
    ClosedIF.toPointSet P.1 = {P} := by
  ext Q
  change Q.1 ≤ P.1 ↔ Q ∈ ({P} : Set (Point k K))
  rw [Set.mem_singleton_iff]
  constructor
  · intro hQ
    exact Subtype.ext ((P.2.le_iff_eq Q.2.ne_bot).1 hQ)
  · rintro rfl
    exact le_rfl

/-- The lattice isomorphism induced by a point geometry equivalence has the
prescribed action on every atom. -/
theorem latticeIsoOfPointEquiv_apply_point (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S)
    (P : Point k K) :
    latticeIsoOfPointEquiv e hcl P.1 = (e P).1 := by
  apply (ClosedIF.pointSetIso l L).injective
  apply Subtype.ext
  change ClosedIF.toPointSet (latticeIsoOfPointEquiv e hcl P.1) =
    ClosedIF.toPointSet (e P).1
  rw [latticeIsoOfPointEquiv_toPointSet, ClosedIF.toPointSet_point,
    Set.image_singleton, ClosedIF.toPointSet_point]

/-- Restricting the induced lattice isomorphism to atoms recovers the
original point geometry equivalence. -/
theorem point_map_latticeIsoOfPointEquiv (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S) :
    Point.map (latticeIsoOfPointEquiv e hcl) = e := by
  apply Equiv.ext
  intro P
  exact Subtype.ext (latticeIsoOfPointEquiv_apply_point e hcl P)

/-- An order isomorphism with the prescribed point map is the lattice
isomorphism constructed from that point geometry equivalence. -/
theorem latticeIsoOfPointEquiv_unique (e : Point k K ≃ Point l L)
    (hcl : ∀ (S : Set (Point k K)) (P : Point k K),
      e P ∈ pointCl (e '' S) ↔ P ∈ pointCl S)
    (g : ClosedIF k K ≃o ClosedIF l L) (hg : Point.map g = e) :
    g = latticeIsoOfPointEquiv e hcl := by
  apply OrderIso.ext
  funext E
  apply (ClosedIF.pointSetIso l L).injective
  apply Subtype.ext
  change ClosedIF.toPointSet (g E) =
    ClosedIF.toPointSet (latticeIsoOfPointEquiv e hcl E)
  rw [latticeIsoOfPointEquiv_toPointSet]
  ext Q
  obtain ⟨P, rfl⟩ := e.surjective Q
  rw [Equiv.image_eq_preimage_symm]
  change (e P).1 ≤ g E ↔ e.symm (e P) ∈ ClosedIF.toPointSet E
  rw [e.symm_apply_apply]
  change (e P).1 ≤ g E ↔ P.1 ≤ E
  have hP : (e P).1 = g P.1 :=
    (congrArg Subtype.val (congrArg
      (fun f : Point k K ≃ Point l L ↦ f P) hg)).symm
  rw [hP]
  exact g.le_iff_le

end PointPresentation

section FiniteRankTransport

/-- An order isomorphism preserves independence of a finite point tuple.
This is the rank-transport step used by the lattice form of reconstruction. -/
theorem pointIndep_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {n : ℕ} (f : Fin n → Point k K) :
    PointIndep l L (Point.map e ∘ f) ↔ PointIndep k K f := by
  unfold PointIndep
  apply forall_congr'
  intro i
  have himage : (Point.map e ∘ f) '' {j | j ≠ i} =
      Point.map e '' (f '' {j | j ≠ i}) :=
    (Set.image_image (Point.map e) f _).symm
  rw [himage]
  exact not_congr (pointCl_map_iff e)

/-- An order isomorphism carries the join of a tuple of points to the join
of the transported tuple. -/
theorem point_map_iSup (e : ClosedIF k K ≃o ClosedIF l L)
    {n : ℕ} (f : Fin n → Point k K) :
    (⨆ i, (Point.map e (f i)).1) = e (⨆ i, (f i).1) := by
  simp only [Point.map_coe, e.map_iSup]

/-- Order isomorphisms preserve finite geometric rank bounds. -/
theorem rankLE_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (n : ℕ) (E : ClosedIF k K) : RankLE n (e E) ↔ RankLE n E := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Point.map e.symm ∘ f, ?_⟩
    change E ≤ ⨆ i, (Point.map e.symm (f i)).1
    rw [point_map_iSup]
    simpa only [e.symm_apply_apply] using e.symm.monotone hf
  · rintro ⟨f, hf⟩
    refine ⟨Point.map e ∘ f, ?_⟩
    change e E ≤ ⨆ i, (Point.map e (f i)).1
    rw [point_map_iSup]
    exact e.monotone hf

/-- Order isomorphisms preserve exact finite geometric rank. -/
theorem rankEq_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (n : ℕ) (E : ClosedIF k K) : RankEq n (e E) ↔ RankEq n E := by
  constructor
  · rintro ⟨f, hf, hE⟩
    refine ⟨Point.map e.symm ∘ f, (pointIndep_map_iff e.symm f).2 hf, ?_⟩
    change E = ⨆ i, (Point.map e.symm (f i)).1
    rw [point_map_iSup]
    simpa only [e.symm_apply_apply] using congrArg e.symm hE
  · rintro ⟨f, hf, hE⟩
    refine ⟨Point.map e ∘ f, (pointIndep_map_iff e f).2 hf, ?_⟩
    change e E = ⨆ i, (Point.map e (f i)).1
    rw [point_map_iSup]
    exact congrArg e hE

end FiniteRankTransport

section IndependentFamilies

/-- A lattice isomorphism transports an arbitrary independent family of
point generators to independent representatives of the image points.
The named consumer is transcendence-degree preservation. -/
theorem algebraicIndependent_pointMap_rep {ι : Type*} {v : ι → K}
    (hv : AlgebraicIndependent k v) (e : ClosedIF k K ≃o ClosedIF l L) :
    AlgebraicIndependent l (fun i ↦
      (Point.map e (Point.mk' k (v i)
        (fun hi ↦ hv.transcendental i (ClosedIF.mem_bot_iff.1 hi)))).rep) := by
  classical
  let f : ι → Point k K := fun i ↦ Point.mk' k (v i)
    (fun hi ↦ hv.transcendental i (ClosedIF.mem_bot_iff.1 hi))
  change AlgebraicIndependent l (fun i ↦ (Point.map e (f i)).rep)
  rw [algebraicIndependent_iff_forall_notMem_racl]
  intro i hi
  have hp : Point.map e (f i) ∈ pointCl (Point.map e '' (f '' {i}ᶜ)) := by
    apply mem_pointCl_iff_rep_mem.2
    simpa only [Set.image_image, Function.comp_apply] using hi
  have hpi : f i ∈ pointCl (f '' {i}ᶜ) := (pointCl_map_iff e).1 hp
  have hvspan : v i ∈ sSup (Subtype.val '' (f '' {i}ᶜ)) :=
    ClosedIF.point_le_iff.1 (mem_pointCl_iff.1 hpi)
  have himage : Subtype.val '' (f '' {i}ᶜ) =
      (fun x ↦ ClosedIF.point k x) '' (v '' {i}ᶜ) := by
    exact (Set.image_image (Subtype.val : Point k K → ClosedIF k K) f {i}ᶜ).trans
      (Set.image_image (fun x ↦ ClosedIF.point k x) v {i}ᶜ).symm
  rw [himage] at hvspan
  change v i ∈ (sSup ((fun x ↦ ClosedIF.point k x) '' (v '' {i}ᶜ))).1 at hvspan
  rw [sSup_point_image] at hvspan
  exact (algebraicIndependent_iff_forall_notMem_racl.1 hv i) hvspan

section TranscendenceDegree
variable {k₁ : Type*} {K₁ : Type u} {k₂ : Type*} {K₂ : Type v}
  [Field k₁] [Field K₁] [Algebra k₁ K₁]
  [Field k₂] [Field K₂] [Algebra k₂ K₂]

/-- An order isomorphism transports a transcendence basis to an independent
family of the same cardinality, so transcendence degree cannot decrease. -/
theorem lift_trdeg_le_of_orderIso (e : ClosedIF k₁ K₁ ≃o ClosedIF k₂ K₂) :
    Cardinal.lift.{v} (Algebra.trdeg k₁ K₁) ≤
      Cardinal.lift.{u} (Algebra.trdeg k₂ K₂) := by
  classical
  obtain ⟨S, hS⟩ := exists_isTranscendenceBasis k₁ K₁
  have hi := algebraicIndependent_pointMap_rep hS.1 e
  have hcard := hi.lift_cardinalMk_le_trdeg
  simpa only [hS.cardinalMk_eq_trdeg] using hcard

/-- Transcendence degree is intrinsic to the closed-field lattice, with
universe lifts when the two ambient fields live in different universes. -/
theorem lift_trdeg_eq_of_orderIso (e : ClosedIF k₁ K₁ ≃o ClosedIF k₂ K₂) :
    Cardinal.lift.{v} (Algebra.trdeg k₁ K₁) =
      Cardinal.lift.{u} (Algebra.trdeg k₂ K₂) :=
  le_antisymm (lift_trdeg_le_of_orderIso e) (lift_trdeg_le_of_orderIso e.symm)

end TranscendenceDegree

/-- An order isomorphism of closed-field lattices preserves transcendence
degree for ambient fields in the same universe. -/
theorem trdeg_eq_of_orderIso {k₁ : Type*} {K₁ : Type u}
    {k₂ : Type*} {K₂ : Type u}
    [Field k₁] [Field K₁] [Algebra k₁ K₁]
    [Field k₂] [Field K₂] [Algebra k₂ K₂]
    (e : ClosedIF k₁ K₁ ≃o ClosedIF k₂ K₂) :
    Algebra.trdeg k₁ K₁ = Algebra.trdeg k₂ K₂ := by
  simpa only [Cardinal.lift_id] using lift_trdeg_eq_of_orderIso e

end IndependentFamilies

section NumericalRank
open IntermediateField

/-- An independent family is a transcendence basis exactly when its relative
algebraic closure is the whole field. Used by the finite-rank bridge. -/
theorem isTranscendenceBasis_iff_racl_range_eq_top {ι : Type*} {v : ι → K}
    (hv : AlgebraicIndependent k v) :
    IsTranscendenceBasis k v ↔ racl k (Set.range v) = ⊤ := by
  rw [hv.isTranscendenceBasis_iff_isAlgebraic]
  constructor
  · intro h
    have := h
    apply top_unique
    intro z _
    exact (mem_racl_iff_isAlgebraic_adjoin k).2
      (Algebra.IsAlgebraic.isAlgebraic z)
  · intro h
    refine ⟨fun z ↦ (mem_racl_iff_isAlgebraic_adjoin k).1 ?_⟩
    exact h ▸ (show z ∈ (⊤ : IntermediateField k K) from mem_top)

/-- The finite geometric rank of a closed field equals its transcendence
degree. This is the numerical rank interface in blueprint Foundation II. -/
theorem RankEq.trdeg_eq {n : ℕ} {E : ClosedIF k K} (h : RankEq n E) :
    Algebra.trdeg k (↥E.1) = n := by
  classical
  obtain ⟨f, hf, hspan⟩ := h
  have hrep : ∀ i, (f i).rep ∈ E := by
    intro i
    rw [hspan]
    exact (le_iSup (fun j ↦ (f j).1) i) (f i).mem_rep
  let v : Fin n → E.1 := fun i ↦ ⟨(f i).rep, hrep i⟩
  have hv : AlgebraicIndependent k v :=
    AlgebraicIndependent.of_comp E.1.val (algebraicIndependent_rep_of_pointIndep hf)
  have hclosure : racl k (Set.range v) = ⊤ := by
    apply top_unique
    intro z _
    apply (algHom_mem_racl_image_iff E.1.val).1
    have himage : E.1.val '' Set.range v = Set.range fun i ↦ (f i).rep := by
      ext x
      simp [v]
    rw [himage]
    have hE : E.1 = racl k (Set.range fun i ↦ (f i).rep) := by
      rw [hspan, iSup_point_val]
    exact hE ▸ z.2
  have hb : IsTranscendenceBasis k v :=
    (isTranscendenceBasis_iff_racl_range_eq_top hv).2 hclosure
  simpa using hb.lift_cardinalMk_eq_trdeg.symm

/-- A closed field of finite transcendence degree has that geometric rank.
Together with `RankEq.trdeg_eq`, this proves the numerical rank bridge. -/
theorem rankEq_of_trdeg_eq {n : ℕ} {E : ClosedIF k K}
    (h : Algebra.trdeg k (↥E.1) = n) : RankEq n E := by
  classical
  obtain ⟨S, hS⟩ := exists_isTranscendenceBasis k (↥E.1)
  let e : S ≃ Fin n := (Cardinal.mk_eq_nat_iff.1
    (hS.cardinalMk_eq_trdeg.trans h)).some
  let v : Fin n → E.1 := fun i ↦ (e.symm i).1
  have hb : IsTranscendenceBasis k v := hS.comp_equiv e.symm
  have hv : AlgebraicIndependent k (E.1.val ∘ v) :=
    hb.1.map' E.1.val.injective
  apply rankEq_of_coe_eq_racl hv
  apply le_antisymm
  · intro x hx
    have hclosure : racl k (Set.range v) = ⊤ :=
      (isTranscendenceBasis_iff_racl_range_eq_top hb.1).1 hb
    have hxv : (⟨x, hx⟩ : E.1) ∈ racl k (Set.range v) :=
      hclosure ▸ mem_top
    have hxK := (algHom_mem_racl_image_iff E.1.val).2 hxv
    simpa only [← Set.range_comp, IntermediateField.coe_val] using hxK
  · have hsubset : Set.range (E.1.val ∘ v) ⊆ (E.1 : Set K) := by
      rintro _ ⟨i, rfl⟩
      exact (v i).2
    exact (racl_mono hsubset).trans (isRAC_iff_racl_eq.1 E.2).le

/-- Exact finite geometric rank agrees with transcendence degree. -/
theorem rankEq_iff_trdeg_eq (n : ℕ) (E : ClosedIF k K) :
    RankEq n E ↔ Algebra.trdeg k (↥E.1) = n :=
  ⟨RankEq.trdeg_eq, rankEq_of_trdeg_eq⟩

end NumericalRank

end
end AclGeom
