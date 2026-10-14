/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Group

/-!
# Generic sets of germs

Blueprint `sources/group_configuration/05-hrushovski-weil.tex`, `def:genset` and
`lem:genset-basic`, and `sources/group_configuration/04-germs.tex`, `def:dom`.

Germs in tuple positions stand for their canonical bases (`conv:germ-tuple`):
independence of a germ from a set is independence of its canonical base, equivalently of
its finite code (`Germ.indepOver_cb_iff`).  A *generic set of germs* is the `Γ`-orbit of
an invertible germ (`Germ.orbit`); its members are invertible and all have the same rank.
Every small set admits an independent member of the orbit, unique up to conjugacy over the
algebraic closure of the set (`Germ.exists_mem_orbit_indepOver`,
`Germ.exists_algEquiv_of_mem_orbit`), a member evaluates independent generic points of the
locus to independent generic points (`Germ.isGen_eval`, `Germ.indepOver_eval`), and the
inverses of a generic set form a generic set (`Germ.orbit_inv`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `def:dom`, `lem:genset-basic` and the orbit part of `def:genset` are proved.
The parametrisation by generic points of a canonical code variety (`def:genset`, last
sentence) is proved in `GroupConfig.Germ.CanonicalCode`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Passing to the relative algebraic closure of the base does not change independence. -/
theorem indepOver_racl_base_iff (C A B : Set K) :
    IndepOver k (racl k C) A B ↔ IndepOver k C A B := by
  unfold IndepOver
  refine forall_congr' fun a ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ ?_
  rw [erk_racl_base, erk_congr_base k (racl_union_left (k := k) C B)]

/-! ### Generic points over `k` -/

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι : Type*} [Finite ι]
  {a : ι → K}

variable (k) in
/-- `def:dom`: generic points of the locus of `a` over `k`. -/
def IsGen (a y : ι → K) : Prop := idealOf k y = idealOf k a

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
theorem IsGenericOver.isGen {M : IntermediateField k K} {y : ι → K}
    (h : IsGenericOver M a y) : IsGen k a y :=
  h.idealOf_eq

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- Automorphisms over `k` carry generic points over `k` to generic points over `k`. -/
theorem IsGen.map {y : ι → K} (hy : IsGen k a y) (σ : K ≃ₐ[k] K) : IsGen k a (⇑σ ∘ y) := by
  unfold IsGen at hy ⊢
  rw [show ⇑σ ∘ y = ⇑σ.toAlgHom ∘ y from rfl, idealOf_comp_algHom, hy]

/-- A generic point over `k` independent from a small subfield is generic over it. -/
theorem IsGen.isGenericOver_of_indepOver {y : ι → K} (hy : IsGen k a y)
    {M : IntermediateField k K} (hM : IsSmall k (M : Set K))
    (h : IndepOver k ∅ (range y) (M : Set K)) : IsGenericOver M a y := by
  have := isGenericOver_self_of_indepOver hM h
  unfold IsGenericOver at this ⊢
  rw [this, hy]

/-- A generic point over `k` independent from a small set is generic over its closure. -/
theorem IsGen.isGenericOver_racl {y : ι → K} (hy : IsGen k a y) {w : Set K} (hw : IsSmall k w)
    (h : IndepOver k ∅ (range y) w) : IsGenericOver (racl k w) a y := by
  refine hy.isGenericOver_of_indepOver hw.racl ?_
  have := indepOver_racl_right_iff.2 h
  rwa [empty_union] at this

/-- Generic points over `k` exist. -/
theorem exists_isGen (a : ι → K) : ∃ y, IsGen k a y := by
  obtain ⟨y, hy⟩ := exists_isGenericOver (IsSmall.of_finite (k := k) finite_empty).racl a
  exact ⟨y, hy.isGen⟩

namespace Germ

variable {κ : Type*} [Finite κ] {a' : κ → K}

/-! ### Independence of germs -/

/-- `conv:germ-tuple`: independence of the canonical base is independence of the code. -/
theorem indepOver_cb_iff (g : Germ k a a') (C w : Set K) :
    IndepOver k C (g.cb : Set K) w ↔ IndepOver k C (g.codeSet : Set K) w := by
  constructor
  · intro h
    refine h.mono_left ?_
    rw [← adjoin_codeSet]
    exact subset_adjoin k _
  · intro h
    refine (indepOver_racl_left_iff.2 h).mono_left ?_
    rw [← adjoin_codeSet]
    exact adjoin_le_iff.2 (subset_union_right.trans (subset_racl k _))

theorem indepOver_cb_iff' (g : Germ k a a') (C w : Set K) :
    IndepOver k C w (g.cb : Set K) ↔ IndepOver k C w (g.codeSet : Set K) := by
  rw [indepOver_comm, indepOver_cb_iff, indepOver_comm]

/-- A germ is independent from a set iff adjoining the set does not lower its rank. -/
theorem indepOver_cb_of_erk_eq (g : Germ k a a') {C w : Set K}
    (h : erk k (C ∪ w) (g.cb : Set K) = erk k C (g.cb : Set K)) :
    IndepOver k C (g.cb : Set K) w := by
  rw [indepOver_cb_iff]
  refine indepOver_of_erk_eq g.codeSet.finite_toSet ?_
  rw [erk_codeSet_eq, erk_codeSet_eq]
  exact h

theorem erk_cb_eq_of_indepOver {g : Germ k a a'} {C w : Set K}
    (h : IndepOver k C (g.cb : Set K) w) :
    erk k (C ∪ w) (g.cb : Set K) = erk k C (g.cb : Set K) := by
  have := (indepOver_cb_iff g C w).1 h (subset_refl _) g.codeSet.finite_toSet
  rwa [erk_codeSet_eq, erk_codeSet_eq] at this

/-! ### Orbits of germs -/

/-- `def:genset`: the `Γ`-orbit of a germ. -/
def orbit (g₀ : Germ k a a') : Set (Germ k a a') := range fun σ : K ≃ₐ[k] K ↦ g₀.map σ

theorem map_refl (g : Germ k a a') : g.map AlgEquiv.refl = g :=
  (map_eq_self_iff AlgEquiv.refl g).2 fun _ _ ↦ rfl

theorem self_mem_orbit (g₀ : Germ k a a') : g₀ ∈ orbit g₀ := ⟨AlgEquiv.refl, map_refl g₀⟩

theorem map_mem_orbit {g₀ g : Germ k a a'} (h : g ∈ orbit g₀) (σ : K ≃ₐ[k] K) :
    g.map σ ∈ orbit g₀ := by
  obtain ⟨τ, rfl⟩ := h
  exact ⟨τ.trans σ, (map_map τ σ g₀).symm⟩

theorem orbit_eq_of_mem {g₀ g : Germ k a a'} (h : g ∈ orbit g₀) : orbit g = orbit g₀ := by
  obtain ⟨τ, rfl⟩ := h
  ext g'
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨τ.trans σ, (map_map τ σ g₀).symm⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨τ.symm.trans σ, ?_⟩
    change (g₀.map τ).map (τ.symm.trans σ) = g₀.map σ
    rw [map_map]
    congr 1
    exact AlgEquiv.ext fun x ↦ by simp

/-- All members of an orbit have the same rank. -/
theorem erk_cb_eq_of_mem_orbit {g₀ g : Germ k a a'} (h : g ∈ orbit g₀) :
    erk k ∅ (g.cb : Set K) = erk k ∅ (g₀.cb : Set K) := by
  obtain ⟨σ, rfl⟩ := h
  exact erk_cb_map σ g₀

/-- Members of the orbit of an invertible germ are invertible. -/
theorem isUnit_of_mem_orbit {g₀ g : Germ k a a} (h₀ : IsUnit g₀) (h : g ∈ orbit g₀) :
    IsUnit g := by
  obtain ⟨σ, rfl⟩ := h
  obtain ⟨h₀', hi⟩ := isUnit_iff.1 h₀
  exact isUnit_iff.2 ⟨h₀'.map σ, hi.map σ⟩

/-- `lem:genset-basic`(3): the inverses of an orbit form the orbit of the inverse. -/
theorem orbit_inv {g₀ h₀ : Germ k a a} (hi : IsInverse h₀ g₀) {g h : Germ k a a}
    (hg : g ∈ orbit g₀) (hgh : IsInverse h g) : h ∈ orbit h₀ := by
  obtain ⟨σ, rfl⟩ := hg
  exact ⟨σ, (hi.map σ).unique hgh⟩

/-! ### Independent members of an orbit -/

/-- `lem:genset-basic`(1): every small set admits an independent member of the orbit. -/
theorem exists_mem_orbit_indepOver (g₀ : Germ k a a') {w : Set K} (hw : IsSmall k w) :
    ∃ g ∈ orbit g₀, IndepOver k ∅ (g.cb : Set K) w := by
  have _ : IsAlgClosed ↥(racl k (∅ : Set K)) := isAlgClosed_racl _
  have hM : IsSmall k ((racl k (∅ : Set K) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite finite_empty).racl
  obtain ⟨σ, hσ⟩ := exists_algEquiv_indepOver (M := racl k (∅ : Set K)) hM
    (fun s : g₀.codeSet ↦ (s : K)) hw
  refine ⟨g₀.map (σ.restrictScalars k), ⟨_, rfl⟩, ?_⟩
  rw [indepOver_cb_iff, ← indepOver_racl_base_iff]
  have hcode : (((g₀.map (σ.restrictScalars k)).codeSet : Finset K) : Set K) ⊆
      racl k (((racl k (∅ : Set K) : IntermediateField k K) : Set K) ∪
        range fun s : g₀.codeSet ↦ σ (s : K)) := by
    have h1 : (((g₀.map (σ.restrictScalars k)).codeSet : Finset K) : Set K) ⊆
        ((g₀.map (σ.restrictScalars k)).cb : Set K) := by
      rw [← adjoin_codeSet]
      exact subset_adjoin k _
    refine h1.trans ?_
    rw [cb_map, ← adjoin_codeSet, adjoin_map]
    refine adjoin_le_iff.2 ?_
    rw [image_eq_range]
    exact subset_union_right.trans (subset_racl k _)
  exact (indepOver_racl_left_iff.2 hσ).mono_left hcode

/-- An automorphism fixing the code of a germ pointwise fixes the germ. -/
theorem map_eq_self_of_fixes_codeSet {g : Germ k a a'} (σ : K ≃ₐ[k] K)
    (h : ∀ x ∈ g.codeSet, σ x = x) : g.map σ = g := by
  refine (map_eq_self_iff σ g).2 fun x hx ↦ ?_
  have hle : g.cb ≤ fixedBy σ := by
    rw [← adjoin_codeSet]
    exact adjoin_le_iff.2 fun x hx ↦ h x hx
  exact hle hx

/-- `lem:genset-basic`(1): two members of an orbit independent from a small set `w` are
conjugate over the closure of `w`. -/
theorem exists_algEquiv_of_mem_orbit {g₀ g g' : Germ k a a'} (hg : g ∈ orbit g₀)
    (hg' : g' ∈ orbit g₀) {w : Set K} (hw : IsSmall k w)
    (h : IndepOver k ∅ (g.cb : Set K) w) (h' : IndepOver k ∅ (g'.cb : Set K) w) :
    ∃ τ : K ≃ₐ[↥(racl k w)] K, g.map (τ.restrictScalars k) = g' := by
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃ₐ[k] K, g.map σ = g' := by
    rw [← orbit_eq_of_mem hg] at hg'
    exact hg'
  have _ : IsAlgClosed ↥(racl k w) := isAlgClosed_racl _
  -- The code of `g` and its image under `σ` are generic points over the closure of `w`.
  let c : g.codeSet → K := fun s ↦ (s : K)
  have hrange : range c = (g.codeSet : Set K) := Subtype.range_coe_subtype
  have hc : IsGen k c c := rfl
  have hc' : IsGen k c (⇑σ ∘ c) := by
    have : ⇑σ ∘ c = ⇑σ.toAlgHom ∘ c := rfl
    unfold IsGen
    rw [this, idealOf_comp_algHom]
  have hcind : IndepOver k ∅ (range c) ((racl k w : IntermediateField k K) : Set K) := by
    have := indepOver_racl_right_iff.2 ((indepOver_cb_iff g ∅ w).1 h)
    rwa [empty_union, ← hrange] at this
  have hc'ind : IndepOver k ∅ (range (⇑σ ∘ c)) ((racl k w : IntermediateField k K) : Set K) := by
    have := indepOver_racl_right_iff.2 h'
    rw [empty_union] at this
    refine this.mono_left ?_
    rw [← hσ, cb_map, coe_map, AlgEquiv.coe_toAlgHom, range_comp, hrange, ← adjoin_codeSet]
    exact image_mono (subset_adjoin k _)
  have hcgen : IsGenericOver (racl k w) c c := hc.isGenericOver_of_indepOver hw.racl hcind
  have hcgen' : IsGenericOver (racl k w) c (⇑σ ∘ c) :=
    hc'.isGenericOver_of_indepOver hw.racl hc'ind
  obtain ⟨τ, hτ⟩ := hcgen.exists_algEquiv hcgen'
  refine ⟨τ, ?_⟩
  -- `τ⁻¹ σ` fixes the code of `τ g`, hence `τ g`.
  have hfix : (g.map (τ.restrictScalars k)).map ((τ.restrictScalars k).symm.trans σ) =
      g.map (τ.restrictScalars k) := by
    refine (map_eq_self_iff _ _).2 fun x hx ↦ ?_
    rw [cb_map, ← adjoin_codeSet, adjoin_map] at hx
    have hle : adjoin k (⇑(τ.restrictScalars k).toAlgHom '' (g.codeSet : Set K)) ≤
        fixedBy ((τ.restrictScalars k).symm.trans σ) := by
      refine adjoin_le_iff.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      change σ ((τ.restrictScalars k).symm ((τ.restrictScalars k) s)) = (τ.restrictScalars k) s
      rw [AlgEquiv.symm_apply_apply]
      exact (hτ ⟨s, hs⟩).symm
    exact hle hx
  calc g.map (τ.restrictScalars k)
      = (g.map (τ.restrictScalars k)).map ((τ.restrictScalars k).symm.trans σ) := hfix.symm
    _ = g.map ((τ.restrictScalars k).trans ((τ.restrictScalars k).symm.trans σ)) := map_map _ _ _
    _ = g.map σ := by
        congr 1
        exact AlgEquiv.ext fun x ↦ by simp
    _ = g' := hσ

/-! ### Values at independent generic points -/

/-- `def:dom`: the value of a germ at a generic point independent from its canonical base,
computed over the algebraic closure of the canonical base. -/
def evalGen (g : Germ k a a') (y : ι → K) : κ → K := g.eval (racl k (g.cb : Set K)) y

/-- `def:dom`: a generic point independent from the canonical base is generic over its
closure. -/
theorem isGenericOver_racl_cb (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) : IsGenericOver (racl k (g.cb : Set K)) a y :=
  hy.isGenericOver_racl g.isSmall_cb h

/-- The value over any larger field is the value over the closure of the canonical base. -/
theorem evalGen_eq (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y) :
    g.evalGen y = g.eval F y := by
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  exact eval_eq_of_le g g.isSmall_cb.racl hF (subset_racl k _) (racl_le_of_isAlgClosed hcb) hy

/-- `lem:genset-basic`(2): the value at an independent generic point is a generic point. -/
theorem isGen_evalGen (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) : IsGen k a' (g.evalGen y) := by
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  exact (g.isGenericOver_eval g.isSmall_cb.racl (subset_racl k _)
    (g.isGenericOver_racl_cb hy h)).isGen

/-- `lem:genset-basic`(2): the value at an independent generic point is independent from the
germ. -/
theorem indepOver_evalGen (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) :
    IndepOver k ∅ (range (g.evalGen y)) (g.cb : Set K) := by
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  exact (g.isGenericOver_eval g.isSmall_cb.racl (subset_racl k _)
    (g.isGenericOver_racl_cb hy h)).indepOver.mono_right (subset_racl k _)

/-- The value is algebraic over the canonical base and the point. -/
theorem evalGen_mem_racl (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) (j : κ) :
    g.evalGen y j ∈ racl k ((g.cb : Set K) ∪ range y) := by
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  have := g.eval_mem_racl g.isSmall_cb.racl (subset_racl k _) (g.isGenericOver_racl_cb hy h) j
  rwa [racl_union_left] at this

end Germ

end

end GroupConfig
