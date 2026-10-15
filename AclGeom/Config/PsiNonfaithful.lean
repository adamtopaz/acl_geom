/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Psi
import GroupConfig.Rank

/-!
# A nonfaithful product-group witness of Ψ (i)–(iii)

Blueprint `sources/group_configuration/11-application.tex`, `rem:psi-hyp`(b). For independent
`s, s', t, u, u'`, let `a = (s, u)`, `b = (s', u')`, `c = (s'/s, u'/u)`, `y = t`, `x = st` and
`z = s't`. These come from the group `Gm × Gm` acting on the line through its first factor:
`b = c * a`, `x = a • y` and `z = c • x`
(`AclGeom.QWitness.Nonfaithful.firstFactorAction`, `AclGeom.QWitness.Nonfaithful.model`), and
this action is not faithful (`AclGeom.QWitness.Nonfaithful.not_injective_firstFactorAction`).

The corresponding witness `AclGeom.QWitness.Nonfaithful.witness` satisfies the Ψ clauses
(i)–(iii) (`AclGeom.QWitness.Nonfaithful.witness_psi_i_iii`), but clause (iv) fails for the atom
`A' = acl(s) ≤ A`, since `X = acl(st) ≤ A' ∨ Y` (`AclGeom.QWitness.Nonfaithful.witness_not_iv`,
`AclGeom.QWitness.Nonfaithful.not_psiCore`). The twelve remaining points of the witness are not
mentioned by clauses (i)–(iv); they are all set to `acl(t)`.

That no conclusion of `thm:main` realizes this witness is proved in
`AclGeom.Config.PsiNonfaithfulObstruction`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the product-group model and the clauses (i)–(iv) of `rem:psi-hyp`(b) are complete.
-/

namespace AclGeom

open GroupConfig Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

namespace Nonfaithful

/-! ### The product-group model -/

/-- `rem:psi-hyp`(b): the group `Gm × Gm` acting on the line through its first factor. -/
def firstFactorAction : (Kˣ × Kˣ) →* Equiv.Perm K :=
  (MulAction.toPermHom Kˣ K).comp (MonoidHom.fst Kˣ Kˣ)

/-- The first factor acts on the line by multiplication. -/
theorem firstFactorAction_apply (g : Kˣ × Kˣ) (x : K) :
    firstFactorAction g x = (g.1 : K) * x :=
  rfl

/-- An element `(1, v)` with `v ≠ 1` acts trivially. Named consumer:
`not_injective_firstFactorAction`. -/
private theorem not_injective_firstFactorAction_of_ne {v : K} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    ¬ Function.Injective (firstFactorAction (K := K)) := by
  intro h
  have h1 : ((1 : Kˣ), Units.mk0 v hv0) = 1 :=
    h (Equiv.ext fun x ↦ by simp [firstFactorAction_apply])
  have h2 := congrArg (fun g : Kˣ × Kˣ ↦ ((g.2 : Kˣ) : K)) h1
  exact hv1 (by simpa using h2)

/-! ### Independence of the parameters -/

variable {s s' t u u' : K}

/-- A set of at most four elements has at most four elements. -/
private theorem encard_le_four {α : Type*} (a b c d : α) : ({a, b, c, d} : Set α).encard ≤ 4 :=
  calc ({a, b, c, d} : Set α).encard ≤ ({b, c, d} : Set α).encard + 1 := encard_insert_le _ _
    _ ≤ ({c, d} : Set α).encard + 1 + 1 := by gcongr; exact encard_insert_le _ _
    _ ≤ ({d} : Set α).encard + 1 + 1 + 1 := by gcongr; exact encard_insert_le _ _
    _ = 4 := by rw [encard_singleton]; norm_num

/-- The point of an element transcendental over `k`. -/
private def pt (x : K) (hx : x ∉ racl k (∅ : Set K)) : Point k K :=
  Point.mk' k x fun h ↦ hx (mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 h))

/-- The carrier of a join of closed fields with known carriers. -/
private theorem coe_sup_racl {E F : ClosedIF k K} {X Y : Set K} (hE : (E : Set K) = racl k X)
    (hF : (F : Set K) = racl k Y) : ((E ⊔ F : ClosedIF k K) : Set K) = racl k (X ∪ Y) := by
  rw [ClosedIF.coe_set_sup, hE, hF, racl_union_left, racl_union_right]

/-- Membership in a closed field with a known carrier. -/
private theorem mem_iff_of_coe {E : ClosedIF k K} {X : Set K} (hE : (E : Set K) = racl k X)
    {x : K} : x ∈ E ↔ x ∈ racl k X := by
  rw [← SetLike.mem_coe, hE, SetLike.mem_coe]

/-- Two sets algebraic over each other have the same closure. -/
private theorem racl_eq_of_subset {X Y : Set K} (h₁ : X ⊆ racl k Y) (h₂ : Y ⊆ racl k X) :
    racl k X = racl k Y :=
  le_antisymm (racl_le_of_subset_racl h₁) (racl_le_of_subset_racl h₂)

variable (hind : erk k ∅ ({s, s', t, u, u'} : Set K) = 5)
include hind

/-- Five independent elements are not algebraic over four elements. -/
private theorem false_of_subset_racl {Y : Set K} (hY : Y.encard ≤ 4)
    (h : ({s, s', t, u, u'} : Set K) ⊆ racl k Y) : False := by
  have hsub : ({s, s', t, u, u'} : Set K) ⊆ racl k (∅ ∪ Y) := by
    rw [empty_union]
    exact h
  have h1 := (erk_mono k ∅ hsub).trans_eq (erk_racl k ∅ Y)
  rw [hind] at h1
  have h2 := h1.trans ((erk_le_encard k ∅ Y).trans hY)
  norm_num at h2

/-- `t` is not algebraic over the parameters `s, u, s', u'`. Named consumers:
`witness_psi_i_iii` and `AclGeom.QWitness.Nonfaithful.not_cb_a`. -/
theorem t_not_mem : t ∉ racl k ({s, u, s', u'} : Set K) := fun ht ↦
  false_of_subset_racl hind (encard_le_four s u s' u') (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    exacts [subset_racl k _ (by simp), subset_racl k _ (by simp), ht, subset_racl k _ (by simp),
      subset_racl k _ (by simp)])

private theorem s'_not_mem : s' ∉ racl k ({s} : Set K) := fun h ↦
  false_of_subset_racl hind (encard_le_four s t u u') (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    exacts [subset_racl k _ (by simp), racl_mono (k := k) (by simp) h, subset_racl k _ (by simp),
      subset_racl k _ (by simp), subset_racl k _ (by simp)])

private theorem u'_not_mem : u' ∉ racl k ({u} : Set K) := fun h ↦
  false_of_subset_racl hind (encard_le_four s s' t u) (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    exacts [subset_racl k _ (by simp), subset_racl k _ (by simp), subset_racl k _ (by simp),
      subset_racl k _ (by simp), racl_mono (k := k) (by simp) h])

/-- `u` is not algebraic over `s`. Named consumer: `AclGeom.QWitness.Nonfaithful.not_cb_a`. -/
theorem u_not_mem : u ∉ racl k ({s} : Set K) := fun h ↦
  false_of_subset_racl hind (encard_le_four s s' t u') (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    exacts [subset_racl k _ (by simp), subset_racl k _ (by simp), subset_racl k _ (by simp),
      racl_mono (k := k) (by simp) h, subset_racl k _ (by simp)])

private theorem s_not_mem_empty : s ∉ racl k (∅ : Set K) := fun h ↦
  false_of_subset_racl hind (encard_le_four s' t u u') (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    exacts [racl_mono (k := k) (empty_subset _) h, subset_racl k _ (by simp),
      subset_racl k _ (by simp), subset_racl k _ (by simp), subset_racl k _ (by simp)])

private theorem u_not_mem_empty : u ∉ racl k (∅ : Set K) := fun h ↦
  u_not_mem hind (racl_mono (k := k) (empty_subset _) h)

private theorem s'_not_mem_empty : s' ∉ racl k (∅ : Set K) := fun h ↦
  s'_not_mem hind (racl_mono (k := k) (empty_subset _) h)

private theorem u'_not_mem_empty : u' ∉ racl k (∅ : Set K) := fun h ↦
  u'_not_mem hind (racl_mono (k := k) (empty_subset _) h)

private theorem t_not_mem_empty : t ∉ racl k (∅ : Set K) := fun h ↦
  t_not_mem hind (racl_mono (k := k) (empty_subset _) h)

private theorem s_ne_zero : s ≠ 0 := fun h ↦ s_not_mem_empty hind (h ▸ zero_mem _)

private theorem s'_ne_zero : s' ≠ 0 := fun h ↦ s'_not_mem_empty hind (h ▸ zero_mem _)

private theorem u_ne_zero : u ≠ 0 := fun h ↦ u_not_mem_empty hind (h ▸ zero_mem _)

private theorem u'_ne_zero : u' ≠ 0 := fun h ↦ u'_not_mem_empty hind (h ▸ zero_mem _)

private theorem u_ne_one : u ≠ 1 := fun h ↦ u_not_mem_empty hind (h ▸ one_mem _)

/-- `rem:psi-hyp`(b): the action of `Gm × Gm` through its first factor is not faithful: `(1, u)`
acts trivially. -/
theorem not_injective_firstFactorAction : ¬ Function.Injective (firstFactorAction (K := K)) :=
  not_injective_firstFactorAction_of_ne (u_ne_zero hind) (u_ne_one hind)

/-- `rem:psi-hyp`(b): `a = (s, u)`, `b = (s', u')`, `c = (s'/s, u'/u)` satisfy `b = c * a` in
`Gm × Gm`, and the first factor sends `y = t` to `x = st` and `x` to `z = s't`. -/
theorem model :
    ((Units.mk0 s' (s'_ne_zero hind), Units.mk0 u' (u'_ne_zero hind)) : Kˣ × Kˣ) =
        (Units.mk0 (s' / s) (div_ne_zero (s'_ne_zero hind) (s_ne_zero hind)),
          Units.mk0 (u' / u) (div_ne_zero (u'_ne_zero hind) (u_ne_zero hind))) *
        (Units.mk0 s (s_ne_zero hind), Units.mk0 u (u_ne_zero hind)) ∧
      firstFactorAction (Units.mk0 s (s_ne_zero hind), Units.mk0 u (u_ne_zero hind)) t = s * t ∧
      firstFactorAction
          (Units.mk0 (s' / s) (div_ne_zero (s'_ne_zero hind) (s_ne_zero hind)),
            Units.mk0 (u' / u) (div_ne_zero (u'_ne_zero hind) (u_ne_zero hind))) (s * t) =
        s' * t := by
  refine ⟨Prod.ext (Units.ext ?_) (Units.ext ?_), rfl, ?_⟩
  · simp [div_mul_cancel₀ _ (s_ne_zero hind)]
  · simp [div_mul_cancel₀ _ (u_ne_zero hind)]
  · rw [firstFactorAction_apply]
    change s' / s * (s * t) = s' * t
    field_simp [s_ne_zero hind]

/-! ### The witness -/

private theorem sdiv_not_mem_empty : s' / s ∉ racl k (∅ : Set K) := fun h ↦ s'_not_mem hind (by
  have h' := mul_mem (racl_mono (k := k) (empty_subset ({s} : Set K)) h)
    (subset_racl k ({s} : Set K) (mem_singleton s))
  rwa [div_mul_cancel₀ _ (s_ne_zero hind)] at h')

private theorem udiv_not_mem_empty : u' / u ∉ racl k (∅ : Set K) := fun h ↦ u'_not_mem hind (by
  have h' := mul_mem (racl_mono (k := k) (empty_subset ({u} : Set K)) h)
    (subset_racl k ({u} : Set K) (mem_singleton u))
  rwa [div_mul_cancel₀ _ (u_ne_zero hind)] at h')

private theorem st_not_mem_empty : s * t ∉ racl k (∅ : Set K) := fun h ↦ t_not_mem hind (by
  have h' := div_mem (racl_mono (k := k) (empty_subset ({s, u, s', u'} : Set K)) h)
    (subset_racl k ({s, u, s', u'} : Set K) (show s ∈ ({s, u, s', u'} : Set K) by simp))
  rwa [mul_div_cancel_left₀ _ (s_ne_zero hind)] at h')

private theorem s't_not_mem_empty : s' * t ∉ racl k (∅ : Set K) := fun h ↦ t_not_mem hind (by
  have h' := div_mem (racl_mono (k := k) (empty_subset ({s, u, s', u'} : Set K)) h)
    (subset_racl k ({s, u, s', u'} : Set K) (show s' ∈ ({s, u, s', u'} : Set K) by simp))
  rwa [mul_div_cancel_left₀ _ (s'_ne_zero hind)] at h')

/-- `rem:psi-hyp`(b): the witness `A = acl(s, u)`, `B = acl(s', u')`, `C = acl(s'/s, u'/u)`,
`X = acl(st)`, `Y = acl(t)`, `Z = acl(s't)`. The remaining twelve points, which clauses
(i)–(iv) do not mention, are all `acl(t)`. -/
def witness : QWitness k K where
  A₁ := pt s (s_not_mem_empty hind)
  A₂ := pt u (u_not_mem_empty hind)
  B₁ := pt s' (s'_not_mem_empty hind)
  B₂ := pt u' (u'_not_mem_empty hind)
  C₁ := pt (s' / s) (sdiv_not_mem_empty hind)
  C₂ := pt (u' / u) (udiv_not_mem_empty hind)
  D := pt t (t_not_mem_empty hind)
  E := pt t (t_not_mem_empty hind)
  F := pt t (t_not_mem_empty hind)
  G := pt t (t_not_mem_empty hind)
  H := pt t (t_not_mem_empty hind)
  I := pt t (t_not_mem_empty hind)
  P := pt t (t_not_mem_empty hind)
  Q := pt t (t_not_mem_empty hind)
  R := pt t (t_not_mem_empty hind)
  S := pt t (t_not_mem_empty hind)
  T := pt t (t_not_mem_empty hind)
  U := pt t (t_not_mem_empty hind)
  X := pt (s * t) (st_not_mem_empty hind)
  Y := pt t (t_not_mem_empty hind)
  Z := pt (s' * t) (s't_not_mem_empty hind)

/-- The parameters `s, u, s', u'` have rank four. -/
private theorem erk_four : erk k ∅ ({s, u, s', u'} : Set K) = 4 := by
  refine le_antisymm ((erk_le_encard k ∅ _).trans (encard_le_four s u s' u')) ?_
  have hsub : ({s, s', t, u, u'} : Set K) ⊆ ({s, u, s', u'} : Set K) ∪ {t} := by
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff, mem_union] at hx ⊢
    tauto
  have h1 : (4 : ℕ∞) + 1 ≤ erk k ∅ ({s, u, s', u'} : Set K) + 1 :=
    calc (4 : ℕ∞) + 1 = 5 := by norm_num
      _ = erk k ∅ ({s, s', t, u, u'} : Set K) := hind.symm
      _ ≤ erk k ∅ (({s, u, s', u'} : Set K) ∪ {t}) := erk_mono k ∅ hsub
      _ ≤ erk k ∅ ({s, u, s', u'} : Set K) + erk k ∅ ({t} : Set K) := erk_union_le k ∅ _ _
      _ ≤ _ := by gcongr; exact (erk_le_encard k ∅ _).trans (by simp)
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h1

/-- A closed field with carrier `acl(s, u, s', u')` has rank four. -/
private theorem rankEq_four {E : ClosedIF k K}
    (hE : (E : Set K) = racl k ({s, u, s', u'} : Set K)) : RankEq 4 E := by
  rw [rankEq_iff_eRk, hE, ← erk_empty_eq]
  have h := erk_racl k ∅ ({s, u, s', u'} : Set K)
  rw [empty_union] at h
  rw [h, erk_four hind]
  rfl

/-- `rem:psi-hyp`(b): the witness satisfies the Ψ clauses (i)–(iii). -/
theorem witness_psi_i_iii :
    RankEq 4 ((witness hind).A ⊔ (witness hind).B ⊔ (witness hind).C) ∧
      RankEq 4 ((witness hind).A ⊔ (witness hind).B) ∧
      RankEq 4 ((witness hind).B ⊔ (witness hind).C) ∧
      RankEq 4 ((witness hind).A ⊔ (witness hind).C) ∧
      (witness hind).X.1 ≤ (witness hind).A ⊔ (witness hind).Y.1 ∧
      (witness hind).Z.1 ≤
        ((witness hind).B ⊔ (witness hind).Y.1) ⊓ ((witness hind).C ⊔ (witness hind).X.1) ∧
      ¬ (witness hind).X.1 ≤ (witness hind).A ⊔ (witness hind).B ⊔ (witness hind).C ∧
      ¬ (witness hind).Y.1 ≤ (witness hind).A ⊔ (witness hind).B ⊔ (witness hind).C ∧
      ¬ (witness hind).Z.1 ≤ (witness hind).A ⊔ (witness hind).B ⊔ (witness hind).C := by
  have hs0 := s_ne_zero hind
  have hs'0 := s'_ne_zero hind
  have hu0 := u_ne_zero hind
  have hu'0 := u'_ne_zero hind
  -- Carriers of the joins.
  have hA : (((witness hind).A : ClosedIF k K) : Set K) = racl k ({s} ∪ {u}) :=
    coe_sup_racl rfl rfl
  have hB : (((witness hind).B : ClosedIF k K) : Set K) = racl k ({s'} ∪ {u'}) :=
    coe_sup_racl rfl rfl
  have hC : (((witness hind).C : ClosedIF k K) : Set K) = racl k ({s' / s} ∪ {u' / u}) :=
    coe_sup_racl rfl rfl
  have hY : (((witness hind).Y.1 : ClosedIF k K) : Set K) = racl k {t} := rfl
  have hX : (((witness hind).X.1 : ClosedIF k K) : Set K) = racl k {s * t} := rfl
  -- The parameter joins all have closure `acl(s, u, s', u')`.
  have hm (x : K) (hx : x ∈ ({s, u, s', u'} : Set K)) : x ∈ racl k ({s, u, s', u'} : Set K) :=
    subset_racl k _ hx
  have hsd : s' / s ∈ racl k ({s, u, s', u'} : Set K) := div_mem (hm _ (by simp)) (hm _ (by simp))
  have hud : u' / u ∈ racl k ({s, u, s', u'} : Set K) := div_mem (hm _ (by simp)) (hm _ (by simp))
  have hABC : (((witness hind).A ⊔ (witness hind).B ⊔ (witness hind).C : ClosedIF k K) :
      Set K) = racl k ({s, u, s', u'} : Set K) := by
    rw [coe_sup_racl (coe_sup_racl hA hB) hC]
    refine congrArg _ (racl_eq_of_subset ?_ ?_)
    · intro x hx
      simp only [mem_union, mem_singleton_iff] at hx
      rcases hx with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
      exacts [hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp), hsd, hud]
    · intro x hx
      exact subset_racl k _ (by simp only [mem_insert_iff, mem_singleton_iff] at hx; simp; tauto)
  have hAB : (((witness hind).A ⊔ (witness hind).B : ClosedIF k K) : Set K) =
      racl k ({s, u, s', u'} : Set K) := by
    rw [coe_sup_racl hA hB]
    refine congrArg _ (racl_eq_of_subset ?_ ?_)
    · intro x hx
      exact subset_racl k _ (by simp only [mem_union, mem_singleton_iff] at hx; simp; tauto)
    · intro x hx
      exact subset_racl k _ (by simp only [mem_insert_iff, mem_singleton_iff] at hx; simp; tauto)
  have hBC : (((witness hind).B ⊔ (witness hind).C : ClosedIF k K) : Set K) =
      racl k ({s, u, s', u'} : Set K) := by
    rw [coe_sup_racl hB hC]
    refine congrArg _ (racl_eq_of_subset ?_ ?_)
    · intro x hx
      simp only [mem_union, mem_singleton_iff] at hx
      rcases hx with (rfl | rfl) | (rfl | rfl)
      exacts [hm _ (by simp), hm _ (by simp), hsd, hud]
    · have hs' : s' ∈ racl k (({s'} ∪ {u'} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hu' : u' ∈ racl k (({s'} ∪ {u'} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hsd' : s' / s ∈ racl k (({s'} ∪ {u'} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hud' : u' / u ∈ racl k (({s'} ∪ {u'} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · have h := div_mem hs' hsd'
        rwa [div_div_cancel₀ hs'0] at h
      · have h := div_mem hu' hud'
        rwa [div_div_cancel₀ hu'0] at h
      · exact hs'
      · exact hu'
  have hAC : (((witness hind).A ⊔ (witness hind).C : ClosedIF k K) : Set K) =
      racl k ({s, u, s', u'} : Set K) := by
    rw [coe_sup_racl hA hC]
    refine congrArg _ (racl_eq_of_subset ?_ ?_)
    · intro x hx
      simp only [mem_union, mem_singleton_iff] at hx
      rcases hx with (rfl | rfl) | (rfl | rfl)
      exacts [hm _ (by simp), hm _ (by simp), hsd, hud]
    · have hs : s ∈ racl k (({s} ∪ {u} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hu : u ∈ racl k (({s} ∪ {u} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hsd' : s' / s ∈ racl k (({s} ∪ {u} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      have hud' : u' / u ∈ racl k (({s} ∪ {u} ∪ ({s' / s} ∪ {u' / u}) : Set K)) :=
        subset_racl k _ (by simp)
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hs
      · exact hu
      · have h := mul_mem hsd' hs
        rwa [div_mul_cancel₀ _ hs0] at h
      · have h := mul_mem hud' hu
        rwa [div_mul_cancel₀ _ hu0] at h
  -- `t` and its multiples are not algebraic over the parameters.
  have ht := t_not_mem hind
  refine ⟨rankEq_four hind hABC, rankEq_four hind hAB, rankEq_four hind hBC, rankEq_four hind hAC,
    ?_, le_inf ?_ ?_, ?_, ?_, ?_⟩
  · change ClosedIF.point k (s * t) ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe (coe_sup_racl hA hY)]
    exact mul_mem (subset_racl k _ (by simp)) (subset_racl k _ (by simp))
  · change ClosedIF.point k (s' * t) ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe (coe_sup_racl hB hY)]
    exact mul_mem (subset_racl k _ (by simp)) (subset_racl k _ (by simp))
  · change ClosedIF.point k (s' * t) ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe (coe_sup_racl hC hX)]
    have h : s' * t = s' / s * (s * t) := by field_simp
    rw [h]
    exact mul_mem (subset_racl k _ (by simp)) (subset_racl k _ (by simp))
  · change ¬ ClosedIF.point k (s * t) ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe hABC]
    intro h
    exact ht (by simpa [mul_div_cancel_left₀ _ hs0] using div_mem h (hm s (by simp)))
  · change ¬ ClosedIF.point k t ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe hABC]
    exact ht
  · change ¬ ClosedIF.point k (s' * t) ≤ _
    rw [ClosedIF.point_le_iff, mem_iff_of_coe hABC]
    intro h
    exact ht (by simpa [mul_div_cancel_left₀ _ hs'0] using div_mem h (hm s' (by simp)))

/-- `rem:psi-hyp`(b): clause (iv) fails for the atom `A' = acl(s) ≤ A`, since
`X = acl(st) ≤ A' ∨ Y`. -/
theorem witness_not_iv :
    (witness hind).A₁.1 ≤ (witness hind).A ∧
      (witness hind).X.1 ≤ (witness hind).A₁.1 ⊔ (witness hind).Y.1 := by
  refine ⟨le_sup_left, ?_⟩
  change ClosedIF.point k (s * t) ≤ _
  rw [ClosedIF.point_le_iff, mem_iff_of_coe (coe_sup_racl (E := (witness hind).A₁.1) rfl rfl)]
  exact mul_mem (subset_racl k _ (by simp)) (subset_racl k _ (by simp))

/-- `rem:psi-hyp`(b): the witness is not a `PsiCore` witness. -/
theorem not_psiCore : ¬ (witness hind).PsiCore := fun h ↦
  h.X_free (witness hind).A₁ (witness_not_iv hind).1 (witness_not_iv hind).2

end Nonfaithful

end QWitness

end

end AclGeom
