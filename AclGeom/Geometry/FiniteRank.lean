/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Geometry.Equivalence
import Mathlib.Combinatorics.Matroid.Rank.ENat

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

section RankBridge

/-! ### The rank bridge

Joins of principal closures at explicit generators, and the transfer of
algebraic independence of the generators to geometric rank. These are the
working lemmas of the configuration layer: every rank clause of a
configuration witness is verified by exhibiting generators and computing
with `racl`. -/

/-- The join of a family of principal closures is the relative algebraic
closure of the set of generators. -/
theorem coe_iSup_point {ι : Type*} (v : ι → K) :
    ((⨆ i, ClosedIF.point k (v i)).1 : IntermediateField k K) =
      racl k (Set.range v) := by
  have h1 : (⨆ i, ClosedIF.point k (v i)) =
      sSup ((fun x ↦ ClosedIF.point k x) '' Set.range v) := by
    rw [iSup]
    congr 1
    ext P
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [h1, sSup_point_image]

/-- Membership in a join of principal closures is relative algebraicity
over the generators. -/
theorem mem_iSup_point_iff {ι : Type*} {v : ι → K} {z : K} :
    z ∈ (⨆ i, ClosedIF.point k (v i)) ↔ z ∈ racl k (Set.range v) := by
  change z ∈ ((⨆ i, ClosedIF.point k (v i)).1 : IntermediateField k K) ↔ _
  rw [coe_iSup_point]

/-- Joins of principal closures agree whenever the generator sets have the
same relative algebraic closure — the absorption workhorse for rank
computations at dependent generators. -/
theorem iSup_point_congr {ι κ : Type*} {v : ι → K} {w : κ → K}
    (h : racl k (Set.range v) = racl k (Set.range w)) :
    (⨆ i, ClosedIF.point k (v i)) = ⨆ j, ClosedIF.point k (w j) :=
  Subtype.ext (by rw [coe_iSup_point, coe_iSup_point, h])

/-- An algebraically independent family of generators yields an independent
family of points. -/
theorem pointIndep_point {n : ℕ} {v : Fin n → K}
    (hv : AlgebraicIndependent k v) (h0 : ∀ i, v i ∉ (⊥ : ClosedIF k K)) :
    PointIndep k K fun i ↦ Point.mk' k (v i) (h0 i) := by
  intro i hi
  rw [mem_pointCl_iff] at hi
  have hmem : v i ∈ sSup (Subtype.val ''
      ((fun j ↦ (Point.mk' k (v j) (h0 j) : Point k K)) '' {j | j ≠ i})) :=
    ClosedIF.point_le_iff.1 hi
  have himg : Subtype.val ''
      ((fun j ↦ (Point.mk' k (v j) (h0 j) : Point k K)) '' {j | j ≠ i}) =
      (fun x ↦ ClosedIF.point k x) '' (v '' {j | j ≠ i}) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [himg] at hmem
  have hmem' : v i ∈ racl k (v '' {j | j ≠ i}) := by
    change v i ∈ (sSup ((fun x ↦ ClosedIF.point k x) ''
      (v '' {j | j ≠ i}))).1 at hmem
    rwa [sSup_point_image] at hmem
  have hne := algebraicIndependent_iff_forall_notMem_racl.1 hv i
  have hcompl : ({i}ᶜ : Set (Fin n)) = {j | j ≠ i} := by
    ext j
    simp
  rw [hcompl] at hne
  exact hne hmem'

/-- Independence of a finite point tuple is exactly algebraic independence
of any chosen representatives.  This is the reverse direction of
`pointIndep_point`; unlike that constructor it needs no separate
non-bottom hypotheses because every `Point.rep` generates its point. -/
theorem algebraicIndependent_rep_of_pointIndep {n : ℕ}
    {f : Fin n → Point k K} (hf : PointIndep k K f) :
    AlgebraicIndependent k fun i ↦ (f i).rep := by
  rw [algebraicIndependent_iff_forall_notMem_racl]
  intro i
  have hi := hf i
  rw [mem_pointCl_iff_rep_mem] at hi
  have hcompl : ({i}ᶜ : Set (Fin n)) = {j | j ≠ i} := by
    ext j
    simp
  rw [hcompl]
  simpa only [Set.image_image, Function.comp_apply] using hi

/-- The algebraic-independence matroid has `racl` as its closure operator. -/
theorem algebraicMatroid_closure_eq_racl (S : Set K) :
    (AlgebraicIndependent.matroid k K).closure S = (racl k S : Set K) := by
  ext x
  rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe,
    Subalgebra.mem_algebraicClosure]
  exact (mem_racl_iff_isAlgebraic_adjoin
    (k := k) (S := S) (x := x)).symm

/-- If an `n`-tuple of principal points spans an element of geometric rank
`n`, then its representatives are algebraically independent.  This is the
missing reverse rank bridge: a dependent `n`-tuple cannot span the same
closed element as an independent `n`-tuple.

The proof compares finite ranks in the algebraic-independence matroid.  The
witness tuple supplied by `RankEq` is an independent set of size `n`; equality
of the two `racl`-spans gives equality of matroid closures, so the explicit
tuple also has matroid rank `n`, hence is independent. -/
theorem algebraicIndependent_of_rankEq_iSup_point {n : ℕ} {v : Fin n → K}
    (h : RankEq n (⨆ i, ClosedIF.point k (v i))) :
    AlgebraicIndependent k v := by
  classical
  obtain ⟨f, hf, hspan⟩ := h
  let M := AlgebraicIndependent.matroid k K
  let s : Set K := Set.range fun i ↦ (f i).rep
  let t : Set K := Set.range v
  have hfrep : AlgebraicIndependent k fun i ↦ (f i).rep :=
    algebraicIndependent_rep_of_pointIndep hf
  have hsind : M.Indep s := by
    exact AlgebraicIndependent.matroid_indep_iff.2 hfrep.to_subtype_range
  have hsencard : s.encard = n := by
    apply le_antisymm
    · simpa [s, ← Set.image_univ] using
        (Set.encard_image_le (fun i ↦ (f i).rep) (Set.univ : Set (Fin n)))
    · simpa [s] using hfrep.injective.encard_range
  have htfinite : t.Finite := Set.finite_range v
  have htencard : t.encard ≤ n := by
    simpa [t, ← Set.image_univ] using
      (Set.encard_image_le v (Set.univ : Set (Fin n)))
  have hclosure : M.closure s = M.closure t := by
    rw [algebraicMatroid_closure_eq_racl,
      algebraicMatroid_closure_eq_racl]
    have hfields : racl k s = racl k t := by
      calc
        racl k s =
            ((⨆ i, (f i).1).1 : IntermediateField k K) :=
          (iSup_point_val f).symm
        _ = ((⨆ i, ClosedIF.point k (v i)).1 :
            IntermediateField k K) := by rw [← hspan]
        _ = racl k t := coe_iSup_point v
    exact congrArg (fun E : IntermediateField k K ↦ (E : Set K)) hfields
  have hrank : M.eRk t = n := by
    calc
      M.eRk t = M.eRk (M.closure t) := (M.eRk_closure_eq t).symm
      _ = M.eRk (M.closure s) := by rw [hclosure]
      _ = M.eRk s := M.eRk_closure_eq s
      _ = s.encard := hsind.eRk_eq_encard
      _ = n := hsencard
  have htcard : t.encard = n :=
    le_antisymm htencard (hrank ▸ M.eRk_le_encard t)
  have htind : M.Indep t :=
    (M.indep_iff_eRk_eq_encard_of_finite htfinite).2
      (hrank.trans htcard.symm)
  have hinj : Function.Injective v := by
    rw [← Set.injOn_univ]
    apply (Set.finite_univ : (Set.univ : Set (Fin n)).Finite).injOn_of_encard_image_eq
    simpa [t, Set.image_univ] using htcard
  exact (AlgebraicIndependent.of_subtype_range hinj)
    (AlgebraicIndependent.matroid_indep_iff.1 htind)

/-- The join of principal closures at an algebraically independent
`n`-tuple of generators has rank exactly `n` — the bridge from field
theory to geometric rank. -/
theorem rankEq_iSup_point {n : ℕ} {v : Fin n → K}
    (hv : AlgebraicIndependent k v) :
    RankEq n (⨆ i, ClosedIF.point k (v i)) := by
  have h0 : ∀ i, v i ∉ (⊥ : ClosedIF k K) := fun i hi ↦
    hv.transcendental i (ClosedIF.mem_bot_iff.1 hi)
  exact ⟨fun i ↦ Point.mk' k (v i) (h0 i), pointIndep_point hv h0, rfl⟩

/-- Exact rank of an explicitly generated closed element is equivalent to
algebraic independence of its representatives. -/
theorem rankEq_iSup_point_iff {n : ℕ} {v : Fin n → K} :
    RankEq n (⨆ i, ClosedIF.point k (v i)) ↔
      AlgebraicIndependent k v :=
  ⟨algebraicIndependent_of_rankEq_iSup_point, rankEq_iSup_point⟩

/-- Rank transfers along equalities of closed elements. -/
theorem RankEq.congr {n : ℕ} {E F : ClosedIF k K} (h : E = F)
    (hE : RankEq n E) : RankEq n F :=
  h ▸ hE

/-- The working form of the rank bridge: a closed element whose underlying
field is the closure of an independent `n`-tuple of generators has rank
exactly `n`. Rank clauses of configuration witnesses are verified by
computing the left-hand side with `coe_sup`/`coe_set_sup`/`coe_set_point`
and the `racl_union` absorptions. -/
theorem rankEq_of_coe_eq_racl {n : ℕ} {E : ClosedIF k K} {v : Fin n → K}
    (hv : AlgebraicIndependent k v)
    (h : (E.1 : IntermediateField k K) = racl k (Set.range v)) :
    RankEq n E := by
  have hE : E = ⨆ i, ClosedIF.point k (v i) :=
    Subtype.ext (h.trans (coe_iSup_point v).symm)
  exact (rankEq_iSup_point hv).congr hE.symm

/-- Binary suprema as indexed suprema over `Fin 2`, for feeding pair joins
to the rank bridge. -/
theorem sup_eq_iSup_two {α : Type*} [CompleteLattice α] (a b : α) :
    a ⊔ b = ⨆ i, (![a, b] : Fin 2 → α) i := by
  refine le_antisymm (sup_le ?_ ?_) (iSup_le fun i ↦ ?_)
  · exact le_iSup_of_le 0 (by simp)
  · exact le_iSup_of_le 1 (by simp)
  · fin_cases i
    · exact le_sup_left
    · exact le_sup_right

/-- The underlying field of a join of two principal closures. -/
theorem coe_sup_point₂ (z₁ z₂ : K) :
    ((ClosedIF.point k z₁ ⊔ ClosedIF.point k z₂).1 :
      IntermediateField k K) = racl k {z₁, z₂} := by
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · have h1 : z₁ ∈ racl k ({z₁, z₂} : Set K) :=
      subset_racl k _ (by simp)
    have h2 : z₂ ∈ racl k ({z₁, z₂} : Set K) :=
      subset_racl k _ (by simp)
    exact sup_le (ClosedIF.point_le_iff.2 h1) (ClosedIF.point_le_iff.2 h2)
  · rintro z (rfl | rfl)
    · exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z)
    · exact (ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self z)

/-- The underlying field of a join of three principal closures. -/
theorem coe_sup_point₃ (z₁ z₂ z₃ : K) :
    ((ClosedIF.point k z₁ ⊔ (ClosedIF.point k z₂ ⊔ ClosedIF.point k z₃)).1 :
      IntermediateField k K) = racl k {z₁, z₂, z₃} := by
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · have h1 : z₁ ∈ racl k ({z₁, z₂, z₃} : Set K) :=
      subset_racl k _ (by simp)
    have h2 : z₂ ∈ racl k ({z₁, z₂, z₃} : Set K) :=
      subset_racl k _ (by simp)
    have h3 : z₃ ∈ racl k ({z₁, z₂, z₃} : Set K) :=
      subset_racl k _ (by simp)
    exact sup_le (ClosedIF.point_le_iff.2 h1)
      (sup_le (ClosedIF.point_le_iff.2 h2) (ClosedIF.point_le_iff.2 h3))
  · rintro z (rfl | rfl | rfl)
    · exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z)
    · exact (ClosedIF.le_iff.1 (le_sup_left.trans le_sup_right))
        (ClosedIF.mem_point_self z)
    · exact (ClosedIF.le_iff.1 (le_sup_right.trans le_sup_right))
        (ClosedIF.mem_point_self z)

end RankBridge

end

end AclGeom
