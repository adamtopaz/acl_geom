/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Equivalence

/-!
# Independent tuples and finite-rank predicates

Geometric finite rank, defined without cardinal arithmetic (blueprint, end of
§Foundation II):

* `PointIndep f`: a finite tuple of points is independent when no entry lies
  in the point closure of the others;
* `RankLE n E`: `E` is below the join of `n` points;
* `RankEq n E`: `E` is the join of an independent `n`-tuple of points;
* `iSup_point_val`: joins of finite point tuples are relative closures of the
  tuples of chosen generators;
* finite character of `pointCl` (`exists_finset_pointCl`), completing the
  pregeometry axioms of the point closure.

Agreement of `RankEq` with `Algebra.trdeg` is deliberately deferred until the
configuration API is stable, per the blueprint.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M1, checklist F6).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Finite character of the point closure: membership in `pointCl S` is
witnessed by a finite subset of `S`. -/
theorem exists_finset_pointCl {S : Set (Point k K)} {P : Point k K}
    (hP : P ∈ pointCl S) :
    ∃ T : Finset (Point k K), ↑T ⊆ S ∧ P ∈ pointCl (T : Set (Point k K)) := by
  classical
  rw [mem_pointCl_iff_rep_mem] at hP
  obtain ⟨T₀, hT₀S, hT₀⟩ := exists_finset_racl hP
  -- Pull the finite set of generators back to a finite set of points.
  choose g hgS hg using fun (t : T₀) ↦ hT₀S t.2
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hQ
    exact hgS t
  · rw [mem_pointCl_iff_rep_mem]
    refine (racl_mono ?_ : racl k (T₀ : Set K) ≤ _) hT₀
    intro t ht
    exact ⟨g ⟨t, ht⟩, by simp, hg ⟨t, ht⟩⟩

variable (k K) in
/-- A finite tuple of points is *independent* when no entry lies in the
closure of the remaining entries (blueprint §Foundation II and
Lemma 4.2 (a)). -/
def PointIndep {n : ℕ} (f : Fin n → Point k K) : Prop :=
  ∀ i, f i ∉ pointCl (f '' {j | j ≠ i})

/-- `E` has rank at most `n`: it lies below the join of `n` points
(blueprint `RankLE`). -/
def RankLE (n : ℕ) (E : ClosedIF k K) : Prop :=
  ∃ f : Fin n → Point k K, E ≤ ⨆ i, (f i).1

/-- `E` has rank exactly `n`: it is the join of an independent `n`-tuple of
points (blueprint `RankEq`). -/
def RankEq (n : ℕ) (E : ClosedIF k K) : Prop :=
  ∃ f : Fin n → Point k K, PointIndep k K f ∧ E = ⨆ i, (f i).1

/-- Joins of finite point tuples are relative algebraic closures of the
tuples of chosen generators. -/
theorem iSup_point_val {n : ℕ} (f : Fin n → Point k K) :
    (⨆ i, (f i).1).1 = racl k (Set.range fun i ↦ (f i).rep) := by
  have h1 : (⨆ i, (f i).1) =
      sSup ((fun x ↦ ClosedIF.point k x) '' Set.range fun i ↦ (f i).rep) := by
    rw [iSup, ← Set.range_comp]
    congr 1
    ext P
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (f i).point_rep⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, ((f i).point_rep).symm.trans hi⟩
  rw [h1, sSup_point_image]

theorem RankLE.mono_left {n : ℕ} {E F : ClosedIF k K} (hEF : E ≤ F)
    (hF : RankLE n F) : RankLE n E := by
  obtain ⟨f, hf⟩ := hF
  exact ⟨f, hEF.trans hf⟩

/-- Rank zero characterizes the bottom. -/
theorem rankLE_zero_iff {E : ClosedIF k K} : RankLE 0 E ↔ E = ⊥ := by
  constructor
  · rintro ⟨f, hf⟩
    rw [iSup_of_empty] at hf
    exact le_bot_iff.1 hf
  · rintro rfl
    exact ⟨Fin.elim0, by simp⟩

/-- Rank bounds may be relaxed upward (for nonzero bounds; a `0`-tuple cannot
be padded when the geometry has no points). -/
theorem RankLE.mono {m n : ℕ} (hmn : m ≤ n) {E : ClosedIF k K}
    (h : RankLE m E) (hm : m ≠ 0) : RankLE n E := by
  obtain ⟨f, hf⟩ := h
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  refine ⟨fun j ↦ if hj : (j : ℕ) < m then f ⟨j, hj⟩ else f ⟨0, hm0⟩,
    hf.trans (iSup_le fun i ↦ ?_)⟩
  refine le_iSup_of_le (Fin.castLE hmn i) ?_
  simp [i.isLt]

end

end AclGeom
