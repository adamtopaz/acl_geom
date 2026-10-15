/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.DefinabilityStep
import GroupConfig.ConfigurationConverse
import GroupConfig.Germ.Bijections

/-!
# Step II: the germ of a configuration and the independence hypothesis

Blueprint `sources/group_configuration/08-proof.tex`, the consequences in `prop:stepI` and
`prop:stepII`.

For a group configuration `(a, b, c, x, y, z)` over `k` in which `z` is definable over `k, b, y`
and `y` over `k, b, z`, the triple `(b; y, z)` determines (`lem:triple`) an invertible germ
`g : Loc(y) → Loc(z)` with `g(y) = z` whose canonical base is interalgebraic with `b`
(`GroupConfiguration.exists_germ`).  Replacing `b` by the code of `g` keeps a configuration,
the orbit of `g` is generically transitive (`GroupConfiguration.trans_of_config`) and it
satisfies the rank hypothesis (F) for difference germs (`GroupConfiguration.rank_of_config`,
`prop:stepII`); so `g` is a Hrushovski–Weil datum of bijections
(`GroupConfiguration.exists_isHWBij`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `prop:stepI` (consequences) and `prop:stepII` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set Germ

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace GroupConfiguration

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*}
  [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] {a : ι₁ → K}
  {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

section Ranks

variable (hc : GroupConfiguration k a b c x y z)
include hc

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- `lem:gc-ranks`: the space points `y` and `z` are independent. -/
theorem indepOver_yz : IndepOver k ∅ (range y) (range z) :=
  hc.indepOver_pts (i := 4) (j := 5) (by decide)

/-! ### The germ of the triple `(b; y, z)` -/

variable (hz : ∀ j, z j ∈ dclAdjoin (adjoin k (range b)) y)
include hz

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- The triple `(b; y, z)` of a configuration in which `z` is definable over `b, y`. -/
theorem isTriple : IsTriple k y z b y z where
  isGen_left := rfl
  isGen_right := rfl
  indep_left := hc.indepOver_by.symm
  indep_right := hc.indepOver_bz.symm
  mem_dcl := hz

/-- `prop:stepI`, consequences: the triple `(b; y, z)` determines a germ `g : Loc(y) → Loc(z)`
with `g(y) = z` whose canonical base is interalgebraic with `b`; it is invertible when `y` is
definable over `b, z`. -/
theorem exists_germ (hy : ∀ i, y i ∈ dclAdjoin (adjoin k (range b)) z) :
    ∃ g : Germ k y z, IsInvertible g ∧ g.evalGen y = z ∧
      racl k (g.cb : Set K) = racl k (range b) := by
  refine ⟨(hc.isTriple hz).germ, (hc.isTriple hz).isInvertible_iff.2 hy,
    (hc.isTriple hz).germ_evalGen, (hc.isTriple hz).racl_cb_eq_iff.2 ?_⟩
  rw [(hc.isTriple hz).germ_cb]
  exact hc.cb_b

end Ranks

/-! ### The Hrushovski–Weil datum of bijections -/

section Datum

variable {g : Germ k y z} (hb : range b = (g.codeSet : Set K))
include hb

omit [Finite ι₂] in
theorem cb_eq_adjoin_of_range_eq : g.cb = adjoin k (range b) := by
  rw [hb, adjoin_codeSet]

variable (hc : GroupConfiguration k a b c x y z)
include hc

/-- `prop:stepI`, generic transitivity of the orbit of `g`. -/
theorem trans_of_config (hgz : g.evalGen y = z) :
    ∀ f ∈ orbit g, ∀ y' : ι₅ → K, IsGen k y y' → IndepOver k ∅ (range y') (f.cb : Set K) →
      IndepOver k ∅ (range (f.evalGen y')) (range y') := by
  rintro f ⟨τ, rfl⟩ y' hy' hind
  have hygen : IsGen k y y := rfl
  have hycb : IndepOver k ∅ (range y) (g.cb : Set K) := by
    rw [cb_eq_adjoin_of_range_eq hb]
    exact indepOver_of_subset_racl (subset_racl k _) (adjoin_le_racl k _) hc.indepOver_by.symm
  refine indepOver_evalGen_range_of_conj hy' (hygen.map τ) hind ?_ ?_
  · rw [cb_map, coe_map, AlgEquiv.coe_toAlgHom]
    have := hycb.image τ
    rwa [image_empty, ← range_comp] at this
  · rw [evalGen_map τ g hygen hycb, hgz]
    have := hc.indepOver_yz.symm.image τ
    rwa [image_empty, ← range_comp, ← range_comp] at this

/-- `prop:stepII` and Step III.1 of `thm:main`, the construction: for a generic copy `b'` of
`b` over the configuration, conjugate by `σ` fixing `acl(c, z, x)` with `σ b = b'`; the
difference germ `δ = g_{b'}⁻¹ g` carries `y` to `y' = σ y`, has canonical base in
`acl(b, b')`, is interalgebraic with `b` over `b'`, is independent from `g` and from `b'`,
and has the rank of `g`. -/
theorem exists_conj_diff (hg : IsInvertible g) (hgz : g.evalGen y = z) :
    ∃ (b' : ι₂ → K) (σ : K ≃ₐ[k] K) (δ : Germ k y y),
      IndepOver k ∅ (range b') (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      ⇑σ ∘ b = b' ∧ ⇑σ ∘ c = c ∧ ⇑σ ∘ x = x ∧ ⇑σ ∘ z = z ∧
      GroupConfiguration k (⇑σ ∘ a) b' c x (⇑σ ∘ y) z ∧
      δ ∈ diffSet g ∧ δ.evalGen y = ⇑σ ∘ y ∧
      δ.cb ≤ racl k (range b ∪ range b') ∧
      range b ⊆ racl k (range b' ∪ δ.cb) ∧
      IndepOver k ∅ (δ.cb : Set K) (range b') ∧
      IndepOver k ∅ (δ.cb : Set K) (g.cb : Set K) ∧
      erk k ∅ (δ.cb : Set K) = erk k ∅ (g.cb : Set K) := by
  obtain ⟨g', hg'⟩ := hg
  have hgcb : g.cb = adjoin k (range b) := cb_eq_adjoin_of_range_eq hb
  have hracl : racl k (g.cb : Set K) = racl k (range b) := by rw [hgcb, racl_adjoin_coe]
  have hygen : IsGen k y y := rfl
  have hall : (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z).Finite :=
    (((((finite_range a).union (finite_range b)).union (finite_range c)).union
      (finite_range x)).union (finite_range y)).union (finite_range z)
  have hsub := fun i ↦ gcPoints_subset (a := a) (b := b) (c := c) (x := x) (y := y) (z := z) i
  have hycb : IndepOver k ∅ (range y) (g.cb : Set K) := by
    rw [hgcb]
    exact indepOver_of_subset_racl (subset_racl k _) (adjoin_le_racl k _) hc.indepOver_by.symm
  /- A generic copy `b'` of `b` over the closure of the configuration, and `σ` fixing
  `acl(c, z, x)` with `σ b = b'`. -/
  obtain ⟨b', hb'⟩ := exists_isGenericOver (IsSmall.of_finite (k := k) hall).racl b
  have hb'ind : IndepOver k ∅ (range b')
      (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) :=
    hb'.indepOver.mono_right (subset_racl k _)
  have hczx : (range c ∪ range z ∪ range x).Finite :=
    ((finite_range c).union (finite_range z)).union (finite_range x)
  have hczx_sub : range c ∪ range z ∪ range x ⊆
      range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z :=
    union_subset (union_subset (hsub 2) (hsub 5)) (hsub 3)
  have hbN : IsGenericOver (racl k (range c ∪ range z ∪ range x)) b b := by
    refine isGenericOver_self_of_indepOver (IsSmall.of_finite (k := k) hczx).racl ?_
    have := indepOver_racl_right_iff.2 hc.indepOver_b_czx
    rwa [empty_union] at this
  have hb'N : IsGenericOver (racl k (range c ∪ range z ∪ range x)) b b' :=
    hb'.of_le (racl_mono (k := k) hczx_sub)
  obtain ⟨σ, hσ⟩ := hbN.exists_algEquiv hb'N
  obtain ⟨σ', hσ'⟩ : ∃ τ : K ≃ₐ[k] K, τ = σ.restrictScalars k := ⟨_, rfl⟩
  have hfix : ∀ s ∈ range c ∪ range z ∪ range x, σ' s = s := fun s hs ↦ by
    rw [hσ']
    change σ s = s
    exact σ.commutes ⟨s, subset_racl k _ hs⟩
  have hσb : ⇑σ' ∘ b = b' := by
    rw [hσ']
    exact funext fun i ↦ hσ i
  have hσc : ⇑σ' ∘ c = c := funext fun i ↦
    hfix _ (subset_union_left (subset_union_left (mem_range_self i)))
  have hσz : ⇑σ' ∘ z = z := funext fun i ↦
    hfix _ (subset_union_left (subset_union_right (mem_range_self i)))
  have hσx : ⇑σ' ∘ x = x := funext fun i ↦ hfix _ (subset_union_right (mem_range_self i))
  obtain ⟨y', hy'⟩ : ∃ y' : ι₅ → K, y' = ⇑σ' ∘ y := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ι₁ → K, a' = ⇑σ' ∘ a := ⟨_, rfl⟩
  have hc' := hc.map σ'
  rw [hσb, hσc, hσz, hσx, ← hy', ← ha'] at hc'
  /- The germ `g_{b'} = σ g` with code `b'`, and `z = g_{b'}(y')`. -/
  have hy'gen : IsGen k y y' := by
    rw [hy']
    exact hygen.map σ'
  have hσgz : (g.map σ').evalGen y' = z := by
    rw [hy', evalGen_map σ' g hygen hycb, hgz, hσz]
  have hcbσ : (g.map σ').cb = adjoin k (range b') := by
    rw [cb_map, hgcb, adjoin_map, AlgEquiv.coe_toAlgHom, ← hσb, range_comp]
  have hraclσ : racl k ((g.map σ').cb : Set K) = racl k (range b') := by
    rw [hcbσ, racl_adjoin_coe]
  have hb'b : IndepOver k ∅ (range b') (range b) := hb'ind.mono_right (hsub 1)
  have hind_cb : IndepOver k ∅ ((g.map σ').cb : Set K) (g.cb : Set K) :=
    (indepOver_congr₀ hraclσ hracl).2 hb'b
  /- The difference germ `δ = g_{b'}⁻¹ g_b`. -/
  have hδmem : Germ.comp (g'.map σ') g ∈ diffSet g :=
    ⟨g.map σ', map_mem_orbit (self_mem_orbit g) σ', g, self_mem_orbit g, g'.map σ', hg'.map σ',
      hind_cb, rfl⟩
  have hyb : IndepOver k ∅ (range y) (range b ∪ range b') := by
    refine indepOver_union_right_iff.2 ⟨hc.indepOver_by.symm, ?_⟩
    rw [empty_union]
    have h1 : IndepOver k ∅ (range b') (range y ∪ range b) :=
      hb'ind.mono_right (union_subset (hsub 4) (hsub 1))
    have h2 := IndepOver.of_union_right h1
    rw [empty_union] at h2
    exact h2.symm
  have hind₁ : IndepOver k ∅ (range y) (((g'.map σ').cb : Set K) ∪ g.cb) := by
    refine indepOver_of_subset_racl (subset_racl k _) (union_subset ?_ ?_) hyb
    · refine (hg'.map σ').cb_le.trans ?_
      rw [hraclσ]
      exact racl_mono (k := k) subset_union_right
    · refine (subset_racl k _).trans ?_
      rw [hracl]
      exact racl_mono (k := k) subset_union_left
  have hy'b' : IndepOver k ∅ (range y') (range b') := hc'.indepOver_by.symm
  have hind₂ : IndepOver k ∅ (range y') ((g.map σ').cb : Set K) := by
    rw [hcbσ]
    exact indepOver_of_subset_racl (subset_racl k _) (adjoin_le_racl k _) hy'b'
  have hδy : (Germ.comp (g'.map σ') g).evalGen y = y' :=
    calc (Germ.comp (g'.map σ') g).evalGen y = (g'.map σ').evalGen (g.evalGen y) :=
          evalGen_comp _ _ hygen hind₁
      _ = (g'.map σ').evalGen ((g.map σ').evalGen y') := by rw [hgz, hσgz]
      _ = y' := (hg'.map σ').evalGen_evalGen hy'gen hind₂
  /- Claim 1: `y' ⫝ b b'`. -/
  have hy'bb' : IndepOver k ∅ (range y') (range b ∪ range b') := by
    have h1 : IndepOver k ∅ (range b') (range b ∪ range z) :=
      hb'ind.mono_right (union_subset (hsub 1) (hsub 5))
    have h2 := IndepOver.of_union_right h1
    rw [empty_union] at h2
    have h3 : IndepOver k ∅ (range b) (range z ∪ range b') :=
      indepOver_union_right_iff.2 ⟨hc.indepOver_bz, by rw [empty_union]; exact h2.symm⟩
    rw [union_comm] at h3
    have h4 := (indepOver_union_right_iff.1 h3).2
    rw [empty_union] at h4
    have h5 : IndepOver k (range b') (range y') (range b) :=
      (indepOver_congr_left hc'.racl_by_bz).1 h4.symm
    have h6 : IndepOver k ∅ (range y') (range b' ∪ range b) :=
      indepOver_union_right_iff.2 ⟨hy'b', by rw [empty_union]; exact h5⟩
    rwa [union_comm] at h6
  /- `δ` is the germ of the triple `(b b'; y, y')` (`lem:triple`). -/
  have hδcb_le' : (Germ.comp (g'.map σ') g).cb ≤ racl k (range b ∪ range b') := by
    refine (cb_comp_le_racl _ _).trans (racl_le_of_subset_racl (union_subset ?_ ?_))
    · refine (subset_racl k _).trans ?_
      rw [hracl]
      exact racl_mono (k := k) subset_union_left
    · refine (hg'.map σ').cb_le.trans ?_
      rw [hraclσ]
      exact racl_mono (k := k) subset_union_right
  have hδcb_le : (Germ.comp (g'.map σ') g).cb ≤ racl k (range (Sum.elim b b')) := by
    rw [Sum.elim_range]
    exact hδcb_le'
  have hδfix : ∀ τ : K ≃ₐ[↥(adjoin k (range (Sum.elim b b')))] K,
      (Germ.comp (g'.map σ') g).map (τ.restrictScalars k) = Germ.comp (g'.map σ') g := by
    intro τ
    have hfixτ : ∀ s ∈ range b ∪ range b', (τ.restrictScalars k) s = s := fun s hs ↦ by
      change τ s = s
      exact τ.commutes ⟨s, subset_adjoin k _ (by rwa [Sum.elim_range])⟩
    have hg_fix : g.map (τ.restrictScalars k) = g := by
      refine map_eq_self_of_fixes_codeSet _ fun w hw ↦ hfixτ w (Or.inl ?_)
      rw [hb]
      exact hw
    have hgσ_fix : (g.map σ').map (τ.restrictScalars k) = g.map σ' := by
      refine (Germ.map_eq_self_iff _ _).2 fun w hw ↦ ?_
      rw [hcbσ] at hw
      have hle : adjoin k (range b') ≤ GroupConfig.fixedBy (τ.restrictScalars k) :=
        IntermediateField.adjoin_le_iff.2 fun s hs ↦
          GroupConfig.mem_fixedBy.2 (hfixτ s (Or.inr hs))
      exact GroupConfig.mem_fixedBy.1 (hle hw)
    have hg'σ_fix : (g'.map σ').map (τ.restrictScalars k) = g'.map σ' := by
      have h1 := (hg'.map σ').map (τ.restrictScalars k)
      rw [hgσ_fix] at h1
      exact h1.unique (hg'.map σ')
    rw [Germ.comp_map, hg'σ_fix, hg_fix]
  have hδcb_dcl : (Germ.comp (g'.map σ') g).cb ≤ dcl (adjoin k (range (Sum.elim b b'))) :=
    cb_le_dcl_of_forall_map_eq _ hδfix
  have hind_δy : IndepOver k ∅ (range y) ((Germ.comp (g'.map σ') g).cb : Set K) :=
    indepOver_of_subset_racl (subset_racl k _) hδcb_le' hyb
  have hmem_dcl : ∀ j, y' j ∈ dclAdjoin (adjoin k (range (Sum.elim b b'))) y := fun j ↦ by
    rw [← hδy]
    exact evalGen_mem_dclAdjoin_of_cb_le_dcl _ hδcb_dcl hygen hind_δy j
  have htrip : IsTriple k y y (Sum.elim b b') y y' :=
    { isGen_left := hygen
      isGen_right := hy'gen
      indep_left := by
        rw [Sum.elim_range]
        exact hyb
      indep_right := by
        rw [Sum.elim_range]
        exact hy'bb'
      mem_dcl := hmem_dcl }
  have hδeq : Germ.comp (g'.map σ') g = htrip.germ := htrip.eq_germ hδcb_le hδy
  have hδcb : (Germ.comp (g'.map σ') g).cb =
      canonicalBase (racl k (range (Sum.elim b b'))) (Sum.elim y y') := by
    rw [hδeq, htrip.germ_cb]
  /- Claim 2: `Cb(y y'/b b') = Cb(y y'/a a')` (`prop:cb` (Cb2)). -/
  have hy4 : IndepOver k ∅ (range y) (range a ∪ range a' ∪ (range b ∪ range b')) := by
    have h1 : IndepOver k ∅ (range y) (range a ∪ range b ∪ range c) := hc.indepOver_y_abc
    have h2 : IndepOver k ∅ (range b') (range a ∪ range b ∪ range c ∪ range y) :=
      hb'ind.mono_right (union_subset (union_subset (union_subset (hsub 0) (hsub 1)) (hsub 2))
        (hsub 4))
    have h3 := (indepOver_union_right_iff.1 h2).2
    rw [empty_union] at h3
    have h4 : IndepOver k ∅ (range y) (range a ∪ range b ∪ range c ∪ range b') :=
      indepOver_union_right_iff.2 ⟨h1, by rw [empty_union]; exact h3.symm⟩
    have ha'sub : range a' ⊆ racl k (range b' ∪ range c) := by
      rw [← hc'.racl_ab_bc]
      exact subset_union_left.trans (subset_racl k _)
    have hsub4 : range a ∪ range a' ∪ (range b ∪ range b') ⊆
        racl k (range a ∪ range b ∪ range c ∪ range b') := by
      rintro w ((hw | hw) | (hw | hw))
      · exact subset_racl k _ (Or.inl (Or.inl (Or.inl hw)))
      · exact SetLike.coe_subset_coe.2 (racl_mono (k := k)
          (union_subset (fun v hv ↦ Or.inr hv) (fun v hv ↦ Or.inl (Or.inr hv)))) (ha'sub hw)
      · exact subset_racl k _ (Or.inl (Or.inl (Or.inr hw)))
      · exact subset_racl k _ (Or.inr hw)
    exact indepOver_of_subset_racl (subset_racl k _) hsub4 h4
  have hy'_sub_a : range y' ⊆ racl k (range a ∪ range a' ∪ range y) := by
    have h1 : range y' ⊆ racl k (range a' ∪ range x) := by
      rw [hc'.racl_ax_ay]
      exact subset_union_right.trans (subset_racl k _)
    have h2 : range x ⊆ racl k (range a ∪ range y) := by
      rw [← hc.racl_ax_ay]
      exact subset_union_right.trans (subset_racl k _)
    refine h1.trans (racl_le_of_subset_racl (union_subset ?_ (h2.trans (racl_mono (k := k) ?_))))
    · exact fun w hw ↦ subset_racl k _ (Or.inl (Or.inr hw))
    · exact union_subset (fun w hw ↦ Or.inl (Or.inl hw)) (fun w hw ↦ Or.inr hw)
  have hy'_sub_b : range y' ⊆ racl k (range b ∪ range b' ∪ range y) := by
    have h1 : range y' ⊆ racl k (range b' ∪ range z) := by
      rw [← hc'.racl_by_bz]
      exact subset_union_right.trans (subset_racl k _)
    have h2 : range z ⊆ racl k (range b ∪ range y) := by
      rw [hc.racl_by_bz]
      exact subset_union_right.trans (subset_racl k _)
    refine h1.trans (racl_le_of_subset_racl (union_subset ?_ (h2.trans (racl_mono (k := k) ?_))))
    · exact fun w hw ↦ subset_racl k _ (Or.inl (Or.inr hw))
    · exact union_subset (fun w hw ↦ Or.inl (Or.inl hw)) (fun w hw ↦ Or.inr hw)
  have hL : IsSmall k ((racl k (range (Sum.elim b b')) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range _)).racl
  have hL' : IsSmall k ((racl k (range (Sum.elim a a')) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range _)).racl
  have _ : IsAlgClosed ↥(racl k (range (Sum.elim b b'))) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (range (Sum.elim a a'))) := isAlgClosed_racl _
  have hyy'_b : racl k (range b ∪ range b' ∪ (range y ∪ range y')) =
      racl k (range b ∪ range b' ∪ range y) :=
    racl_union_eq_of_subset_racl_of_subset (union_subset (fun w hw ↦ subset_racl k _ (Or.inr hw))
      hy'_sub_b) subset_union_left
  have hyy'_a : racl k (range a ∪ range a' ∪ (range y ∪ range y')) =
      racl k (range a ∪ range a' ∪ range y) :=
    racl_union_eq_of_subset_racl_of_subset (union_subset (fun w hw ↦ subset_racl k _ (Or.inr hw))
      hy'_sub_a) subset_union_left
  have h1 : IndepOver k (racl k (range (Sum.elim b b')) : Set K) (range (Sum.elim y y'))
      (racl k (range (Sum.elim a a')) : Set K) := by
    rw [indepOver_racl_base_iff, Sum.elim_range, Sum.elim_range, Sum.elim_range]
    refine (indepOver_congr hyy'_b (racl_union_right _ _)).2 ?_
    have h := (indepOver_union_right_iff.1 (by rwa [union_comm] at hy4 :
      IndepOver k ∅ (range y) (range b ∪ range b' ∪ (range a ∪ range a')))).2
    rwa [empty_union] at h
  have h2 : IndepOver k (racl k (range (Sum.elim a a')) : Set K) (range (Sum.elim y y'))
      (racl k (range (Sum.elim b b')) : Set K) := by
    rw [indepOver_racl_base_iff, Sum.elim_range, Sum.elim_range, Sum.elim_range]
    refine (indepOver_congr hyy'_a (racl_union_right _ _)).2 ?_
    have h := (indepOver_union_right_iff.1 hy4).2
    rwa [empty_union] at h
  have hcb2 := (canonicalBase_eq_of_indepOver_of_indepOver hL hL' h1 h2).1
  rw [hcb2] at hδcb
  /- Claim 3: `b ⫝ a a'`. -/
  have hb_aa' : IndepOver k ∅ (range b) (range a ∪ range a') := by
    have h1 : IndepOver k ∅ (range b') (range b ∪ range c) :=
      hb'ind.mono_right (union_subset (hsub 1) (hsub 2))
    have h2 := IndepOver.of_union_right h1
    rw [empty_union] at h2
    have ha_sub : range a ⊆ racl k (range c ∪ range b) := by
      rw [union_comm, ← hc.racl_ab_bc]
      exact subset_union_left.trans (subset_racl k _)
    have ha'_sub : range a' ⊆ racl k (range c ∪ range b') := by
      rw [union_comm, ← hc'.racl_ab_bc]
      exact subset_union_left.trans (subset_racl k _)
    have hA : racl k (range c ∪ range b) = racl k (range c ∪ (range a ∪ range b)) :=
      (racl_union_eq_of_subset_racl_of_subset (union_subset ha_sub
        (fun w hw ↦ subset_racl k _ (Or.inr hw))) subset_union_right).symm
    have hB : racl k (range c ∪ range b') = racl k (range c ∪ (range a' ∪ range b')) :=
      (racl_union_eq_of_subset_racl_of_subset (union_subset ha'_sub
        (fun w hw ↦ subset_racl k _ (Or.inr hw))) subset_union_right).symm
    have h3 : IndepOver k (range c) (range a ∪ range b) (range a' ∪ range b') :=
      (indepOver_congr hA hB).1 h2.symm
    have h4 : IndepOver k (range c) (range a') (range a ∪ range b) :=
      h3.symm.mono_left subset_union_left
    have h5 : IndepOver k ∅ (range a') (range c ∪ (range a ∪ range b)) :=
      indepOver_union_right_iff.2 ⟨hc'.indepOver_ac, by rw [empty_union]; exact h4⟩
    have h6 : IndepOver k ∅ (range a') (range a ∪ range b) := h5.mono_right subset_union_right
    have h7 := (indepOver_union_right_iff.1 h6).2
    rw [empty_union] at h7
    exact indepOver_union_right_iff.2 ⟨hc.indepOver_ab.symm, by rw [empty_union]; exact h7.symm⟩
  /- Hence `δ ⫝ g_b`, and `rk(δ) = rk(g_{b'}) = n` by `lem:diff-basic`(2). -/
  have hδ_g : IndepOver k ∅ ((Germ.comp (g'.map σ') g).cb : Set K) (g.cb : Set K) := by
    rw [hδcb]
    refine indepOver_of_subset_racl ?_ ?_ hb_aa'.symm
    · refine (canonicalBase_le _ _).trans ?_
      rw [Sum.elim_range]
    · exact (subset_racl k _).trans hracl.le
  have hrk := (indepOver_diff_right_iff (hg'.map σ') hind_cb ⟨g', hg'⟩).1 hδ_g
  rw [erk_cb_eq_of_mem_orbit (map_mem_orbit (self_mem_orbit g) σ')] at hrk
  have hδb' : IndepOver k ∅ ((Germ.comp (g'.map σ') g).cb : Set K) (range b') := by
    have h1 := (indepOver_diff_left_iff (hg'.map σ') hind_cb).2 hrk
    rw [hcbσ] at h1
    exact h1.mono_right (subset_adjoin k _)
  have hbsub : range b ⊆ racl k (range b' ∪ (Germ.comp (g'.map σ') g).cb) := by
    have h1 := cb_right_le_diff (f₂ := g) (hg'.map σ')
    rw [hcbσ, union_comm, racl_union_adjoin, union_comm] at h1
    have hbcb : range b ⊆ (g.cb : Set K) := by
      rw [hgcb]
      exact subset_adjoin k _
    exact hbcb.trans h1
  obtain ⟨y'', rfl⟩ := hy'
  obtain ⟨a'', rfl⟩ := ha'
  exact ⟨b', σ', Germ.comp (g'.map σ') g, hb'ind, hσb, hσc, hσx, hσz, hc', hδmem, hδy,
    hδcb_le', hbsub, hδb', hδ_g, hrk⟩

/-- `prop:stepII`: the rank hypothesis (F) holds for the orbit of `g`. -/
theorem rank_of_config (hg : IsInvertible g) (hgz : g.evalGen y = z) :
    ∀ δ ∈ diffSet g, erk k ∅ (δ.cb : Set K) = erk k ∅ (g.cb : Set K) := by
  obtain ⟨_, _, _, -, -, -, -, -, -, hδmem, -, -, -, -, -, hrk⟩ := exists_conj_diff hb hc hg hgz
  exact IsHWBij.rank_of_exists hδmem hrk

/-- `prop:stepI`/`prop:stepII`: the germ of a configuration whose code is `b` is a
Hrushovski–Weil datum of bijections. -/
theorem isHWBij_of_config (hg : IsInvertible g) (hgz : g.evalGen y = z) : IsHWBij g where
  isInvertible := hg
  trans := trans_of_config hb hc hgz
  rank := rank_of_config hb hc hg hgz

end Datum

/-- `prop:stepI` (consequences) and `prop:stepII`: a configuration in which `z` is definable
over `b, y` and `y` over `b, z` yields a Hrushovski–Weil datum of bijections
`g : Loc(y) → Loc(z)` with `g(y) = z`, and the configuration with `b` replaced by the code of
`g`. -/
theorem exists_isHWBij (hc : GroupConfiguration k a b c x y z)
    (hz : ∀ j, z j ∈ dclAdjoin (adjoin k (range b)) y)
    (hy : ∀ i, y i ∈ dclAdjoin (adjoin k (range b)) z) :
    ∃ g : Germ k y z, IsHWBij g ∧ g.evalGen y = z ∧
      GroupConfiguration k a g.codeTuple c x y z ∧
      racl k (range g.codeTuple) = racl k (range b) := by
  obtain ⟨g, hg, hgz, hracl⟩ := hc.exists_germ hz hy
  have hrc : racl k (range g.codeTuple) = racl k (range b) := by rw [racl_codeTuple, hracl]
  have hc' : GroupConfiguration k a g.codeTuple c x y z := hc.ofRaclEq rfl hrc rfl rfl rfl rfl
  exact ⟨g, isHWBij_of_config (range_codeTuple g) hc' hg hgz, hgz, hc', hrc⟩

end GroupConfiguration

end

end GroupConfig
