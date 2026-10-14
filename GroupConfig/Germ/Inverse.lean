/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Category

/-!
# Invertible germs

Blueprint `sources/group_configuration/04-germs.tex`, `lem:inverse` (two-sided inverses,
their uniqueness and equivariance, the canonical base of the inverse up to algebraic
closure, equality of dimensions) and `lem:comp-codes`(1), in the form that does not use
the definable closure.

A point fixed by every automorphism over a small algebraically closed field `L` lies in
`L` (`mem_of_forall_algEquiv_fixed`, via `lem:fresh-conj`); hence the canonical base of
an inverse lies in the algebraic closure of the canonical base of the germ
(`Germ.IsInverse.cb_le`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** for `lem:inverse`, the uniqueness and equivariance of inverses,
`Cb(g⁻¹) ⊆ acl(Cb g)` and `dim V = dim V'` are complete, as is `lem:comp-codes`(1). The
equivalence with definability, clause (2), awaits `GroupConfig.Germ.Definable`. The exact
equality `Cb(g⁻¹) = Cb(g)` and the swapped graph ideal of the inverse await
`GroupConfig.ConfigurationConverse`; those modules are not integrated yet.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [UniversalDomain k K]

/-- A point fixed by every automorphism over a small algebraically closed subfield `L` lies
in `L`. -/
theorem mem_of_forall_algEquiv_fixed {L : IntermediateField k K} [IsAlgClosed (↥L)]
    (hL : IsSmall k (L : Set K)) {x : K} (h : ∀ σ : K ≃ₐ[↥L] K, σ x = x) : x ∈ L := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_indepOver hL (fun _ : Unit ↦ x)
    (IsSmall.of_finite (finite_singleton x))
  have hfix : (fun _ : Unit ↦ σ x) = fun _ : Unit ↦ x := funext fun _ ↦ h σ
  have hind : IndepOver k (L : Set K) {x} {x} := by
    have h' := hσ
    rw [hfix, range_const] at h'
    exact h'
  have hx : ({x} : Set K) ⊆ (racl k (L : Set K) : Set K) := hind.subset_racl_of_self
  have hL' : racl k (L : Set K) = L := isRAC_iff_racl_eq.1 (isRAC_of_isAlgClosed L)
  rw [hL'] at hx
  exact hx (mem_singleton x)

variable [IsAlgClosed k] {ι κ : Type*} [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

namespace Germ

/-! ### The identity germ and automorphisms -/

/-- The identity germ is fixed by every automorphism over `k`. -/
theorem map_id (σ : K ≃ₐ[k] K) (a : ι → K) : (Germ.id a).map σ = Germ.id a := by
  have hF : IsSmall k ((racl k (∅ : Set K) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite finite_empty).racl
  have _ : IsAlgClosed ↥(racl k (∅ : Set K)) := isAlgClosed_racl _
  have _ := isAlgClosed_map σ (racl k (∅ : Set K))
  have hF' := isSmall_map σ hF
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  have hy' : IsGenericOver ((racl k (∅ : Set K)).map σ.toAlgHom) a (⇑σ ∘ y) :=
    (isGenericOver_map_iff σ _ a y).2 hy
  refine eq_of_eval_eq hF' (cb_map_le σ (cb_id_le a _)) (cb_id_le a _) hy' ?_
  rw [eval_map _ σ hF (cb_id_le a _) hy, eval_id hF hy, eval_id hF' hy']

/-! ### Inverses -/

/-- `lem:inverse`: `h` is a two-sided inverse of `g`. -/
def IsInverse (h : Germ k a' a) (g : Germ k a a') : Prop :=
  Germ.comp h g = Germ.id a ∧ Germ.comp g h = Germ.id a'

theorem IsInverse.symm {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    IsInverse g h :=
  ⟨hi.2, hi.1⟩

/-- `lem:inverse`: two-sided inverses are unique. -/
theorem IsInverse.unique {h h' : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g)
    (hi' : IsInverse h' g) : h = h' := by
  calc h = Germ.comp h (Germ.id a') := (comp_id h).symm
    _ = Germ.comp h (Germ.comp g h') := by rw [hi'.2]
    _ = Germ.comp (Germ.comp h g) h' := (comp_assoc h g h').symm
    _ = Germ.comp (Germ.id a) h' := by rw [hi.1]
    _ = h' := id_comp h'

/-- `lem:inverse`: inverses are equivariant. -/
theorem IsInverse.map {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g)
    (σ : K ≃ₐ[k] K) : IsInverse (h.map σ) (g.map σ) :=
  ⟨by rw [← comp_map, hi.1, map_id], by rw [← comp_map, hi.2, map_id]⟩

/-- `lem:inverse`: the canonical base of an inverse lies in the algebraic closure of the
canonical base of the germ. -/
theorem IsInverse.cb_le {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    h.cb ≤ racl k (g.cb : Set K) := by
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  have hL : IsSmall k ((racl k (g.cb : Set K) : IntermediateField k K) : Set K) :=
    g.isSmall_cb.racl
  intro x hx
  refine mem_of_forall_algEquiv_fixed hL fun σ ↦ ?_
  -- `σ` fixes `g`, hence `σ h` is an inverse of `g`, hence equals `h`.
  have hσg : g.map (σ.restrictScalars k) = g :=
    (map_eq_self_iff _ g).2 fun y hy ↦ σ.commutes ⟨y, subset_racl k _ hy⟩
  have hσh : h.map (σ.restrictScalars k) = h := by
    have := hi.map (σ.restrictScalars k)
    rw [hσg] at this
    exact this.unique hi
  exact (map_eq_self_iff (σ.restrictScalars k) h).1 hσh x hx

/-- `lem:inverse`: inverse germs have interalgebraic canonical bases. -/
theorem IsInverse.racl_cb_eq {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    racl k (h.cb : Set K) = racl k (g.cb : Set K) :=
  le_antisymm (racl_le_of_subset_racl hi.cb_le) (racl_le_of_subset_racl hi.symm.cb_le)

/-- `lem:inverse`: the loci of an invertible germ have the same dimension. -/
theorem IsInverse.erk_eq {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    erk k ∅ (range a) = erk k ∅ (range a') := by
  obtain ⟨F, hF_def⟩ : ∃ F : IntermediateField k K, F = racl k ((g.cb : Set K) ∪ h.cb) :=
    ⟨_, rfl⟩
  have hF : IsSmall k (F : Set K) := hF_def ▸ (g.isSmall_cb.union h.isSmall_cb).racl
  have _ : IsAlgClosed ↥F := hF_def ▸ isAlgClosed_racl _
  have hcb : g.cb ≤ F := hF_def ▸ subset_union_left.trans (subset_racl k _)
  have hcb' : h.cb ≤ F := hF_def ▸ subset_union_right.trans (subset_racl k _)
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  have hz : IsGenericOver F a' (g.eval F y) := g.isGenericOver_eval hF hcb hy
  -- `y` and `g(y)` are interalgebraic over the field.
  have hyz : y = h.eval F (g.eval F y) := by
    rw [← comp_eval _ _ hF hcb hcb' hy, hi.1, eval_id hF hy]
  have h1 : range (g.eval F y) ⊆ racl k ((F : Set K) ∪ range y) := by
    rintro _ ⟨j, rfl⟩
    exact g.eval_mem_racl hF hcb hy j
  have h2 : range y ⊆ racl k ((F : Set K) ∪ range (g.eval F y)) := by
    rintro _ ⟨i, rfl⟩
    have hyi : y i = h.eval F (g.eval F y) i := congrFun hyz i
    rw [hyi]
    exact h.eval_mem_racl hF hcb' hz i
  rw [← hy.erk_empty_eq, ← hy.erk_coe_eq, ← hz.erk_empty_eq, ← hz.erk_coe_eq,
    ← erk_union_eq_of_subset_racl k h1, ← erk_union_eq_of_subset_racl k h2, union_comm]

/-! ### Canonical bases of composites -/

/-- `lem:comp-codes`(1): the canonical base of a composite lies in the closure of the
canonical bases. -/
theorem cb_comp_le_racl {μ : Type*} [Finite μ] {a'' : μ → K} (g' : Germ k a' a'')
    (g : Germ k a a') : (Germ.comp g' g).cb ≤ racl k ((g.cb : Set K) ∪ g'.cb) := by
  obtain ⟨F, hF_def⟩ : ∃ F : IntermediateField k K, F = racl k ((g.cb : Set K) ∪ g'.cb) :=
    ⟨_, rfl⟩
  have hF : IsSmall k (F : Set K) := hF_def ▸ (g.isSmall_cb.union g'.isSmall_cb).racl
  have _ : IsAlgClosed ↥F := hF_def ▸ isAlgClosed_racl _
  have hcb : g.cb ≤ F := hF_def ▸ subset_union_left.trans (subset_racl k _)
  have hcb' : g'.cb ≤ F := hF_def ▸ subset_union_right.trans (subset_racl k _)
  rw [← hF_def]
  exact cb_comp_le g' g hF hcb hcb'

/-- `lem:comp-codes`(1): for an invertible `g`, the canonical base of `g'` lies in the closure
of the canonical bases of `g' ∘ g` and `g`. -/
theorem cb_le_of_isInverse {μ : Type*} [Finite μ] {a'' : μ → K} (g' : Germ k a' a'')
    {g : Germ k a a'} {h : Germ k a' a} (hi : IsInverse h g) :
    g'.cb ≤ racl k (((Germ.comp g' g).cb : Set K) ∪ g.cb) := by
  have hg' : g' = Germ.comp (Germ.comp g' g) h := by
    rw [comp_assoc, hi.2, comp_id]
  have hle : (Germ.comp (Germ.comp g' g) h).cb ≤ racl k ((h.cb : Set K) ∪ (Germ.comp g' g).cb) :=
    cb_comp_le_racl (Germ.comp g' g) h
  rw [← hg'] at hle
  have h1 : ((Germ.comp g' g).cb : Set K) ⊆ racl k (((Germ.comp g' g).cb : Set K) ∪ g.cb) :=
    subset_union_left.trans (subset_racl k _)
  have h2 : (h.cb : Set K) ⊆ racl k (((Germ.comp g' g).cb : Set K) ∪ g.cb) :=
    hi.cb_le.trans (racl_mono (k := k) subset_union_right)
  exact hle.trans (racl_le_of_subset_racl (union_subset h2 h1))

end Germ

end

end GroupConfig
