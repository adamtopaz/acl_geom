/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Correctness
import AclGeom.Config.JAssembly
import AclGeom.Transfer.Descent
import AclGeom.Transfer.LiftConfig

/-!
# Point-level descent for `J`

Blueprint Theorem `j-descent` (§9.1) compares, for a five-tuple of points of
`K/k`, the conditions

1. it is semantically `j(x, a)` in `K`;
2. its lift is semantically `j(x, a)` in `Ω/k̄` (every point descends to `K`
   because it is a lift);
3. its lift satisfies the geometric `J` predicate over `Ω/k̄`;
4. it satisfies the geometric `J` predicate over `K/k`.

Here `Ω` is algebraically closed, `ι : K →ₐ[k] Ω`, and the role of `k̄` is
played by any subextension `K₀` of elements algebraic over `k`; points are
lifted by `liftPoint` (`AclGeom.Transfer.Lift`).  This module proves

* `(1) ⇒ (2)`: `jSem_lift_of_jSem` (no hypotheses);
* `(2) ⇒ (1)`: `jSem_of_jSem_lift`, for perfect `K` with
  `trdeg_k K ≥ 5`, from the Galois descent `mem_of_j_represented_of_five_le_trdeg`;
* `(4) ⇒ (3)`: `jGeom_lift_of_jGeom`.  Rank, join, meet and incidence are
  absolute under the lift; the three universal atom clauses of `Ψ(iv)`
  transfer by `exists_point_of_lift`.

The arrow `(1) ⇒ (4)` is `jGeom_of_jSem_of_five_le_trdeg`.  The arrow
`(3) ⇒ (2)` is the completeness half of blueprint Theorem `j-acf-correct`;
`jGeom_iff_jSem_of_lift` takes it as the explicit hypothesis
`JCompletenessACF K₀ Ω` and assembles the equivalence of geometric and
semantic `J` over `K/k`.  By `jCompletenessACF_of_completeness` that
hypothesis reduces to completeness of geometric `Q` and `Q′` over
algebraically closed fields.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M5): the arrows `(1) ⇔ (2)`, `(4) ⇒ (3)` and
`(1) ⇒ (4)` of Theorem `j-descent` are proved; `(3) ⇒ (2)` enters as a
hypothesis.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
  [Algebra k Ω] {K₀ : IntermediateField k Ω}
  (halg : ∀ y ∈ K₀, IsAlgebraic k y) (ι : K →ₐ[k] Ω)

include halg

/-- **`(4) ⇒ (3)` of blueprint Theorem `j-descent`**: geometric `J` over
`K/k` implies geometric `J` of the lifted tuple over `Ω/K₀`. -/
theorem jGeom_lift_of_jGeom [IsAlgClosed Ω] {X P Q R A : Point k K}
    (h : JGeom X P Q R A) :
    JGeom (liftPoint halg ι X) (liftPoint halg ι P) (liftPoint halg ι Q)
      (liftPoint halg ι R) (liftPoint halg ι A) :=
  ⟨h.1.lift halg ι, h.2.1.lift halg ι, h.2.2.lift halg ι⟩

/-- Pair independence is absolute along `ι`, over any algebraic base. -/
theorem algebraicIndependent_pair_lift_iff {x a : K} :
    AlgebraicIndependent (↥K₀) ![ι x, ι a] ↔ AlgebraicIndependent k ![x, a] := by
  have key : ∀ {u v : K},
      ι u ∈ racl (↥K₀) ({ι v} : Set Ω) ↔ u ∈ racl k ({v} : Set K) := fun {u v} ↦ by
    rw [← Set.image_singleton]
    exact apply_mem_racl_base_image_iff halg ι
  constructor
  · intro h
    exact algebraicIndependent_pair
      ((not_congr key).1 (AlgebraicIndependent.notMem_racl_pair' h))
      ((not_congr key).1 (AlgebraicIndependent.notMem_racl_pair h))
  · intro h
    exact algebraicIndependent_pair
      ((not_congr key).2 (AlgebraicIndependent.notMem_racl_pair' h))
      ((not_congr key).2 (AlgebraicIndependent.notMem_racl_pair h))

/-- The lift of a principal point. -/
theorem liftPoint_val_eq_point {P : Point k K} {x : K}
    (h : P.1 = ClosedIF.point k x) :
    (liftPoint halg ι P).1 = ClosedIF.point (↥K₀) (ι x) := by
  rw [liftPoint_val, h, liftClosed_point halg ι]

/-- **`(1) ⇒ (2)` of blueprint Theorem `j-descent`**: a semantic `j`-tuple
of `K/k` lifts to a semantic `j`-tuple of `Ω/K₀`. -/
theorem jSem_lift_of_jSem {X : Fin 5 → Point k K} (h : JSem X) :
    JSem (liftPoint halg ι ∘ X) := by
  obtain ⟨x, a, hind, h0, h1, h2, h3, h4⟩ := h
  refine ⟨ι x, ι a, (algebraicIndependent_pair_lift_iff halg ι).2 hind, ?_, ?_, ?_, ?_, ?_⟩
  · exact liftPoint_val_eq_point halg ι h0
  · rw [← map_add]; exact liftPoint_val_eq_point halg ι h1
  · rw [← map_mul]; exact liftPoint_val_eq_point halg ι h2
  · rw [← map_mul, ← map_add]; exact liftPoint_val_eq_point halg ι h3
  · exact liftPoint_val_eq_point halg ι h4

omit halg in
/-- A rank bound on `K/k` passes to any overfield. -/
theorem five_le_trdeg_of_algHom (f : K →ₐ[k] Ω)
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    (5 : Cardinal) ≤ Algebra.trdeg k Ω := by
  have h := (Cardinal.lift_le.2 htr).trans (lift_trdeg_le_of_injective f f.injective)
  simpa using h

/-- **`(2) ⇒ (1)` of blueprint Theorem `j-descent`**: if the lift of a
five-tuple of points of a perfect field `K` is a semantic `j`-tuple over
`Ω/K₀`, then the tuple is already a semantic `j`-tuple over `K/k`.  The
coordinates `x, a ∈ Ω` are interalgebraic with representatives in `ι(K)`,
so the Galois descent `mem_of_j_represented_of_five_le_trdeg` puts them in
`ι(K)`. -/
theorem jSem_of_jSem_lift [IsAlgClosed Ω] [PerfectField K] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X : Fin 5 → Point k K}
    (h : JSem (liftPoint halg ι ∘ X)) : JSem X := by
  obtain ⟨x, a, hind, h0, h1, h2, h3, h4⟩ := h
  have hb : ∀ {S : Set Ω} {z : Ω}, z ∈ racl (↥K₀) S ↔ z ∈ racl k S :=
    mem_racl_base_iff_of_algebraic halg
  -- Each coordinate is interalgebraic with the image of a representative.
  have hrep : ∀ {i : Fin 5} {u : Ω},
      (liftPoint halg ι (X i)).1 = ClosedIF.point (↥K₀) u →
        u ∈ racl k ({ι (X i).rep} : Set Ω) ∧
          ι (X i).rep ∈ racl k ({u} : Set Ω) := by
    intro i u hu
    have hpt : ClosedIF.point (↥K₀) (ι (X i).rep) = ClosedIF.point (↥K₀) u := by
      rw [← hu, liftPoint_val, ← (X i).point_rep, liftClosed_point halg ι]
    constructor
    · rw [← hb]
      change u ∈ ClosedIF.point (↥K₀) (ι (X i).rep)
      rw [hpt]
      exact ClosedIF.mem_point_self u
    · rw [← hb]
      change ι (X i).rep ∈ ClosedIF.point (↥K₀) u
      rw [← hpt]
      exact ClosedIF.mem_point_self _
  have hindk : AlgebraicIndependent k ![x, a] :=
    algebraicIndependent_pair
      (fun hm ↦ AlgebraicIndependent.notMem_racl_pair' hind (hb.2 hm))
      (fun hm ↦ AlgebraicIndependent.notMem_racl_pair hind (hb.2 hm))
  have : PerfectField ↥ι.fieldRange :=
    PerfectField.of_ringEquiv (AlgEquiv.ofInjectiveField ι).toRingEquiv
  have hmem : ∀ i, ι (X i).rep ∈ ι.fieldRange := fun i ↦
    AlgHom.mem_fieldRange.2 ⟨(X i).rep, rfl⟩
  obtain ⟨r0, r0'⟩ := hrep h0
  obtain ⟨r1, r1'⟩ := hrep h1
  obtain ⟨r2, r2'⟩ := hrep h2
  obtain ⟨r3, r3'⟩ := hrep h3
  obtain ⟨r4, r4'⟩ := hrep h4
  obtain ⟨hxK, haK⟩ := mem_of_j_represented_of_five_le_trdeg q
    (five_le_trdeg_of_algHom ι htr) (K₁ := ι.fieldRange) hindk
    (hmem 0) (hmem 1) (hmem 2) (hmem 3) (hmem 4)
    r0 r0' r1 r1' r2 r2' r3 r3' r4 r4'
  obtain ⟨x₀, rfl⟩ := AlgHom.mem_fieldRange.1 hxK
  obtain ⟨a₀, rfl⟩ := AlgHom.mem_fieldRange.1 haK
  have hpt : ∀ {i : Fin 5} {u : K},
      (liftPoint halg ι (X i)).1 = ClosedIF.point (↥K₀) (ι u) →
        (X i).1 = ClosedIF.point k u := by
    intro i u hu
    apply liftClosed_injective halg ι
    rw [liftClosed_point halg ι]
    exact hu
  refine ⟨x₀, a₀, (algebraicIndependent_pair_lift_iff halg ι).1 hind,
    hpt h0, hpt ?_, hpt ?_, hpt ?_, hpt h4⟩
  · rw [map_add]; exact h1
  · rw [map_mul]; exact h2
  · rw [map_add, map_mul]; exact h3

/-- Blueprint Theorem `j-descent`, `(1) ⇔ (2)`. -/
theorem jSem_lift_iff [IsAlgClosed Ω] [PerfectField K] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) {X : Fin 5 → Point k K} :
    JSem (liftPoint halg ι ∘ X) ↔ JSem X :=
  ⟨jSem_of_jSem_lift halg ι q htr, jSem_lift_of_jSem halg ι⟩

include ι in
/-- Completeness of geometric `J` over a perfect `K/k` of rank at least five,
from completeness over `Ω/K₀`: `(4) ⇒ (3) ⇒ (2) ⇒ (1)` of blueprint Theorem
`j-descent`, with the open arrow `(3) ⇒ (2)` as the hypothesis `hcomp`. -/
theorem jSem_of_jGeom_of_lift [IsAlgClosed Ω] [PerfectField K] (q : ℕ)
    [ExpChar k q] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥K₀) Ω) {X : Fin 5 → Point k K}
    (h : JGeom (X 0) (X 1) (X 2) (X 3) (X 4)) : JSem X :=
  jSem_of_jSem_lift halg ι q htr
    (hcomp (liftPoint halg ι ∘ X) (jGeom_lift_of_jGeom halg ι h))

include ι in
/-- **Correctness of `J` over arbitrary perfect fields** (blueprint Theorem
`j-descent`), conditional on completeness over `Ω/K₀`. -/
theorem jGeom_iff_jSem_of_lift [IsAlgClosed Ω] [PerfectField K]
    (q : ℕ) [ExpChar k q] (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥K₀) Ω) {X : Fin 5 → Point k K} :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) ↔ JSem X :=
  ⟨jSem_of_jGeom_of_lift halg ι q htr hcomp, jGeom_of_jSem_of_five_le_trdeg htr⟩

end

section Canonical

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The canonical instance of the lift: `Ω` is an algebraic closure of `K`
and `K₀ = k̄` is the algebraic closure of `k` in it.  The geometry of
`k̄ ⊆ Ω` has rank at least five when `K/k` does. -/
theorem five_le_trdeg_algebraicClosure (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    (5 : Cardinal) ≤ Algebra.trdeg (↥(algebraicClosure k (AlgebraicClosure K)))
      (AlgebraicClosure K) := by
  have hΩ := five_le_trdeg_of_algHom (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) htr
  have hadd := lift_trdeg_add_eq k (↥(algebraicClosure k (AlgebraicClosure K)))
    (AlgebraicClosure K)
  rw [trdeg_eq_zero, Cardinal.lift_zero, zero_add, Cardinal.lift_inj] at hadd
  rwa [hadd]

/-- **Correctness of `J` over a perfect field** (blueprint Theorem
`j-descent`) in canonical form: `Ω` is an algebraic closure of `K` and `K₀`
is the algebraic closure of `k` in `Ω`.  The only open input is the
hypothesis `hcomp`, completeness of geometric `J` over `k̄ ⊆ Ω`, an
algebraically closed pair of rank at least five
(`five_le_trdeg_algebraicClosure`). -/
theorem jGeom_iff_jSem [PerfectField K] (q : ℕ) [ExpChar k q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K)))
      (AlgebraicClosure K))
    {X : Fin 5 → Point k K} :
    JGeom (X 0) (X 1) (X 2) (X 3) (X 4) ↔ JSem X :=
  jGeom_iff_jSem_of_lift (fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz)
    (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) q htr hcomp

end Canonical

end AclGeom
