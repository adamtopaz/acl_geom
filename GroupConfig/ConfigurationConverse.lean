/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Configuration
import GroupConfig.Germ.Triple
import GroupConfig.Germ.CanonicalCode

/-!
# Configurations of a homogeneous space

Blueprint `sources/group_configuration/07-configurations.tex`, `prop:converse`.

For a generic set of germs satisfying the Hrushovski–Weil hypotheses, two independent
members `g, h` and a generic point `y` independent from both, the codes of `g`, `h` and
`c = h g⁻¹` together with `x = g(y)`, `y` and `z = h(y)` form a group configuration
(`Germ.IsHW.groupConfiguration`), with `z = c(x)` and `h = c g`.
The literal canonical RREF-code version, including both ranks and an internally
chosen inverse, is `Germ.IsHW.groupConfiguration_code`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `prop:converse` complete. The module also proves two claims of `lem:inverse` through
the graph-point swap: the exact equality `Cb(g⁻¹) = Cb(g)` (`Germ.IsInverse.cb_eq`), and that
`Γ(g⁻¹)` is `Γ(g)` with the variables swapped (`Germ.IsInverse.graphIdeal_eq`).
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Independent triples from independence -/

theorem IndepTriple.of_indepOver {A B C : Set K} (hAB : IndepOver k ∅ A B)
    (hC : IndepOver k ∅ C (A ∪ B)) (hB : B.Finite) (hC' : C.Finite) : IndepTriple k A B C := by
  unfold IndepTriple
  rw [erk_union_eq, erk_union_eq, hAB.symm.erk_eq (subset_refl _) hB,
    hC.erk_eq (subset_refl _) hC']

/-- Replacing the second set by one interalgebraic with it over the first, of the same
rank. -/
theorem IndepTriple.of_racl_union_eq {A B C P : Set K} (h : IndepTriple k A B P)
    (hr : racl k (A ∪ C) = racl k (A ∪ B)) (he : erk k ∅ C = erk k ∅ B) :
    IndepTriple k A C P := by
  unfold IndepTriple at h ⊢
  rw [GroupConfig.erk_eq_of_racl_eq (racl_union_congr hr rfl), he]
  exact h

/-- Replacing the third set by one interalgebraic with it over the first, of the same
rank. -/
theorem IndepTriple.of_racl_union_eq' {A B C P : Set K} (h : IndepTriple k A B C)
    (hr : racl k (A ∪ P) = racl k (A ∪ C)) (he : erk k ∅ P = erk k ∅ C) :
    IndepTriple k A B P := by
  unfold IndepTriple at h ⊢
  rw [union_right_comm, GroupConfig.erk_eq_of_racl_eq (racl_union_congr hr rfl), he,
    ← union_right_comm]
  exact h

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι κ : Type*} [Finite ι]
  [Finite κ] {a : ι → K} {a' : κ → K}

namespace Germ

/-! ### Code tuples -/

/-- `conv:germ-tuple`: the code of a germ as a tuple. -/
def codeTuple (g : Germ k a a') : ↥g.codeSet → K := Subtype.val

theorem range_codeTuple (g : Germ k a a') : range g.codeTuple = (g.codeSet : Set K) :=
  Subtype.range_coe

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
theorem racl_adjoin_coe (S : Set K) :
    racl k ((adjoin k S : IntermediateField k K) : Set K) = racl k S :=
  le_antisymm (racl_le_of_subset_racl (adjoin_le_racl k S)) (racl_mono (k := k) (subset_adjoin k S))

theorem racl_codeSet (g : Germ k a a') : racl k (g.codeSet : Set K) = racl k (g.cb : Set K) := by
  rw [← adjoin_codeSet, racl_adjoin_coe]

theorem racl_codeTuple (g : Germ k a a') :
    racl k (range g.codeTuple) = racl k (g.cb : Set K) := by
  rw [range_codeTuple, racl_codeSet]

theorem codeSet_subset_racl_cb (g : Germ k a a') : (g.codeSet : Set K) ⊆ racl k (g.cb : Set K) := by
  rw [← racl_codeSet]
  exact subset_racl k _

theorem cb_subset_racl_codeSet (g : Germ k a a') :
    (g.cb : Set K) ⊆ racl k (g.codeSet : Set K) := by
  rw [racl_codeSet]
  exact subset_racl k _

theorem indepOver_codeSet_iff (g : Germ k a a') (C w : Set K) :
    IndepOver k C w (g.codeSet : Set K) ↔ IndepOver k C w (g.cb : Set K) :=
  (indepOver_cb_iff' g C w).symm

/-- `lem:comp-codes`(1) for codes. -/
theorem codeSet_mul_subset (δ γ : Germ k a a) :
    ((δ * γ).codeSet : Set K) ⊆ racl k ((δ.codeSet : Set K) ∪ γ.codeSet) := by
  have h1 : racl k ((γ.cb : Set K) ∪ δ.cb) = racl k ((δ.codeSet : Set K) ∪ γ.codeSet) := by
    rw [union_comm]
    exact racl_union_congr (racl_codeSet δ).symm (racl_codeSet γ).symm
  refine (codeSet_subset_racl_cb _).trans ?_
  rw [← h1]
  exact racl_le_of_subset_racl (cb_comp_le_racl δ γ)

theorem codeSet_inv_subset {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    (h.codeSet : Set K) ⊆ racl k (g.codeSet : Set K) := by
  rw [racl_codeSet]
  exact (codeSet_subset_racl_cb h).trans (racl_le_of_subset_racl hi.cb_le)

/-- The canonical base of a germ is the canonical base of its graph point over any small
algebraically closed field containing it. -/
theorem cb_eq_canonicalBase_eval (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed ↥F]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y) :
    g.cb = canonicalBase F (Sum.elim y (g.eval F y)) := by
  obtain ⟨r, rfl, hrM⟩ := g.exists_rep_M_eq hF hcb
  have hyM : IsGenericOver r.M a y := hrM ▸ hy
  rw [cb_mk_eq_canonicalBase r hyM, eval_eq_rep r hF hcb hrM.ge hyM]
  exact congrArg (fun L : IntermediateField k K ↦ canonicalBase L (r.graphPoint y)) hrM

/-- `lem:inverse`(1): a germ and its inverse have the same canonical base. -/
theorem IsInverse.cb_eq {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    h.cb = g.cb := by
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField k K, M = racl k ((g.cb : Set K) ∪ h.cb) := ⟨_, rfl⟩
  have _ : IsAlgClosed ↥M := hM ▸ isAlgClosed_racl _
  have hMs : IsSmall k (M : Set K) := hM ▸ (g.isSmall_cb.union h.isSmall_cb).racl
  have hg : g.cb ≤ M := by
    rw [hM]
    exact fun x hx ↦ subset_racl k _ (Or.inl hx)
  have hh : h.cb ≤ M := by
    rw [hM]
    exact fun x hx ↦ subset_racl k _ (Or.inr hx)
  obtain ⟨y, hy⟩ := exists_isGenericOver hMs a
  have hz : IsGenericOver M a' (g.eval M y) := g.isGenericOver_eval hMs hg hy
  have hhz : h.eval M (g.eval M y) = y := by
    rw [← comp_eval h g hMs hg hh hy, hi.1, eval_id hMs hy]
  rw [cb_eq_canonicalBase_eval h hMs hh hz, hhz, cb_eq_canonicalBase_eval g hMs hg hy,
    canonicalBase_sum_elim_swap]

/-- `lem:inverse`: the graph ideal of the inverse is the graph ideal of the germ with the
source and target variables swapped. -/
theorem IsInverse.graphIdeal_eq {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g) :
    h.graphIdeal = g.graphIdeal.map
      (MvPolynomial.rename (Equiv.sumComm ι κ) :
        MvPolynomial (ι ⊕ κ) K →ₐ[K] MvPolynomial (κ ⊕ ι) K).toRingHom := by
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField k K, M = racl k ((g.cb : Set K) ∪ h.cb) := ⟨_, rfl⟩
  have _ : IsAlgClosed ↥M := hM ▸ isAlgClosed_racl _
  have hMs : IsSmall k (M : Set K) := hM ▸ (g.isSmall_cb.union h.isSmall_cb).racl
  have hg : g.cb ≤ M := by
    rw [hM]
    exact fun x hx ↦ subset_racl k _ (Or.inl hx)
  have hh : h.cb ≤ M := by
    rw [hM]
    exact fun x hx ↦ subset_racl k _ (Or.inr hx)
  obtain ⟨r, rfl, hrM⟩ := g.exists_rep_M_eq hMs hg
  obtain ⟨r', rfl, hr'M⟩ := h.exists_rep_M_eq hMs hh
  obtain ⟨y, hy⟩ := exists_isGenericOver hMs a
  have hyM : IsGenericOver r.M a y := hrM ▸ hy
  obtain ⟨z, hz⟩ : ∃ z, z = r.f.eval y := ⟨_, rfl⟩
  have hzr : IsGenericOver r.M a' z := hz ▸ r.isGenericOver y hyM
  have hzM : IsGenericOver r'.M a' z := by
    rw [hr'M, ← hrM]
    exact hzr
  have hinv : r'.f.eval z = y := by
    rw [← eval_eq_rep r' hMs hh hr'M.ge hzM, hz, ← eval_eq_rep r hMs hg hrM.ge hyM,
      ← comp_eval _ _ hMs hg hh hy, hi.1, eval_id hMs hy]
  have e₁ : Germ.graphIdeal (⟦r⟧ : Germ k a a') = locusIdeal (↥M) (Sum.elim y z) := by
    rw [graphIdeal_mk, r.graphIdeal_eq hyM]
    unfold Representative.graphPoint
    rw [← hz]
    exact locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe, hrM]) _
  have e₂ : Germ.graphIdeal (⟦r'⟧ : Germ k a' a) = locusIdeal (↥M) (Sum.elim z y) := by
    rw [graphIdeal_mk, r'.graphIdeal_eq hzM]
    unfold Representative.graphPoint
    rw [hinv]
    exact locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe, hr'M]) _
  have hswap : Sum.elim z y = Sum.elim y z ∘ Equiv.sumComm κ ι := by
    funext s
    cases s <;> rfl
  rw [e₂, e₁, hswap, locusIdeal_comp_equiv, Equiv.sumComm_symm]

/-! ### The converse -/

namespace IsHW

/-- `prop:converse`: for a generic set satisfying the Hrushovski–Weil hypotheses, two
independent members `g, h` and a generic point `y` independent from them, the codes of `g`,
`h`, `c = h g⁻¹` with `x = g(y)`, `y`, `z = h(y)` form a group configuration; moreover
`z = c(x)` and `h = c g`. -/
theorem groupConfiguration {g₀ : Germ k a a} (hw : IsHW g₀) {g h : Germ k a a}
    (hg : g ∈ orbit g₀) (hh : h ∈ orbit g₀) {y : ι → K} (hy : IsGen k a y)
    (hind : IndepTriple k (g.cb : Set K) (h.cb : Set K) (range y))
    (hm : 1 ≤ erk k ∅ (range a)) {g' : Germ k a a} (hg' : IsInverse g' g) :
    GroupConfiguration k g.codeTuple h.codeTuple (h * g').codeTuple (g.evalGen y) y
        (h.evalGen y) ∧
      (h * g').evalGen (g.evalGen y) = h.evalGen y ∧ h * g' * g = h := by
  obtain ⟨h', hh'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hh)
  -- The inverse `c' = g h'` of `c = h g'`.
  have hc' : IsInverse (g * h') (h * g') := by
    constructor
    · change g * h' * (h * g') = 1
      rw [mul_assoc, ← mul_assoc h', show h' * h = 1 from hh'.1, one_mul,
        show g * g' = 1 from hg'.2]
    · change h * g' * (g * h') = 1
      rw [mul_assoc, ← mul_assoc g', show g' * g = 1 from hg'.1, one_mul,
        show h * h' = 1 from hh'.2]
  have hcg : h * g' * g = h := by rw [mul_assoc, show g' * g = 1 from hg'.1, mul_one]
  have hgh'h : g * h' * h = g := by rw [mul_assoc, show h' * h = 1 from hh'.1, mul_one]
  -- Finite code sets.
  have hAfin : (g.codeSet : Set K).Finite := g.codeSet.finite_toSet
  have hBfin : (h.codeSet : Set K).Finite := h.codeSet.finite_toSet
  have hCfin : ((h * g').codeSet : Set K).Finite := (h * g').codeSet.finite_toSet
  have hYfin : (range y).Finite := finite_range y
  have hXfin : (range (g.evalGen y)).Finite := finite_range _
  have hZfin : (range (h.evalGen y)).Finite := finite_range _
  -- Independence of `(g, h, y)` for the code sets.
  have hind' : IndepTriple k (g.codeSet : Set K) (h.codeSet : Set K) (range y) :=
    indepTriple_of_racl_eq (racl_codeSet g).symm (racl_codeSet h).symm rfl hind
  have hAB : IndepOver k ∅ (g.codeSet : Set K) (h.codeSet : Set K) :=
    hind'.indepOver_left hAfin hBfin hYfin
  have hYA : IndepOver k ∅ (range y) (g.codeSet : Set K) :=
    (hind'.perm_right.indepOver_left hAfin hYfin hBfin).symm
  have hYB : IndepOver k ∅ (range y) (h.codeSet : Set K) :=
    (hind'.perm_left.perm_right.indepOver_left hBfin hYfin hAfin).symm
  have hA_BY : IndepOver k ∅ (g.codeSet : Set K) ((h.codeSet : Set K) ∪ range y) :=
    hind'.indepOver_union hAfin hBfin hYfin
  have hB_AY : IndepOver k ∅ (h.codeSet : Set K) ((g.codeSet : Set K) ∪ range y) :=
    hind'.perm_left.indepOver_union hBfin hAfin hYfin
  have hY_AB : IndepOver k ∅ (range y) ((g.codeSet : Set K) ∪ h.codeSet) :=
    hind'.rotate.rotate.indepOver_union hYfin hAfin hBfin
  have hY_BA : IndepOver k ∅ (range y) ((h.codeSet : Set K) ∪ g.codeSet) := by
    rw [union_comm]
    exact hY_AB
  have hYAcb : IndepOver k ∅ (range y) (g.cb : Set K) := (indepOver_codeSet_iff g ∅ _).1 hYA
  have hYBcb : IndepOver k ∅ (range y) (h.cb : Set K) := (indepOver_codeSet_iff h ∅ _).1 hYB
  -- `c ∈ 𝒢`, so all three codes have rank `n`.
  have hBAcb : IndepOver k ∅ (h.cb : Set K) (g.cb : Set K) :=
    (indepOver_codeSet_iff g ∅ _).1 ((indepOver_cb_iff h ∅ _).2 hAB.symm)
  have hhg' : IndepOver k ∅ (h.cb : Set K) (g'.cb : Set K) :=
    (indepOver_racl_right_iff.2 hBAcb).mono_right (by
      rw [empty_union]
      exact hg'.cb_le)
  have hcmem : h * g' ∈ orbit g₀ := hw.comp h hh g' (hw.inv g hg g' hg') hhg'
  have hrkA : erk k ∅ (g.codeSet : Set K) = erk k ∅ (g₀.cb : Set K) := by
    rw [erk_codeSet_eq, erk_cb_eq_of_mem_orbit hg]
  have hrkB : erk k ∅ (h.codeSet : Set K) = erk k ∅ (g₀.cb : Set K) := by
    rw [erk_codeSet_eq, erk_cb_eq_of_mem_orbit hh]
  have hrkC : erk k ∅ ((h * g').codeSet : Set K) = erk k ∅ (g₀.cb : Set K) := by
    rw [erk_codeSet_eq, erk_cb_eq_of_mem_orbit hcmem]
  -- The space points are generic of rank `m`.
  have hx : IsGen k a (g.evalGen y) := g.isGen_evalGen hy hYAcb
  have hz : IsGen k a (h.evalGen y) := h.isGen_evalGen hy hYBcb
  have hrkY : erk k ∅ (range y) = erk k ∅ (range a) := erk_empty_range_eq_of_idealOf_eq hy
  have hrkX : erk k ∅ (range (g.evalGen y)) = erk k ∅ (range a) :=
    erk_empty_range_eq_of_idealOf_eq hx
  have hrkZ : erk k ∅ (range (h.evalGen y)) = erk k ∅ (range a) :=
    erk_empty_range_eq_of_idealOf_eq hz
  -- Values are independent from the codes and interalgebraic with `y` over them.
  have hXAcb : IndepOver k ∅ (range (g.evalGen y)) (g.cb : Set K) := g.indepOver_evalGen hy hYAcb
  have hZBcb : IndepOver k ∅ (range (h.evalGen y)) (h.cb : Set K) := h.indepOver_evalGen hy hYBcb
  have hXA : IndepOver k ∅ (range (g.evalGen y)) (g.codeSet : Set K) :=
    (indepOver_codeSet_iff g ∅ _).2 hXAcb
  have hZB : IndepOver k ∅ (range (h.evalGen y)) (h.codeSet : Set K) :=
    (indepOver_codeSet_iff h ∅ _).2 hZBcb
  have hXg' : IndepOver k ∅ (range (g.evalGen y)) (g'.cb : Set K) :=
    (indepOver_racl_right_iff.2 hXAcb).mono_right (by
      rw [empty_union]
      exact hg'.cb_le)
  have hZh' : IndepOver k ∅ (range (h.evalGen y)) (h'.cb : Set K) :=
    (indepOver_racl_right_iff.2 hZBcb).mono_right (by
      rw [empty_union]
      exact hh'.cb_le)
  have hX_AY : range (g.evalGen y) ⊆ racl k ((g.codeSet : Set K) ∪ range y) := by
    rintro _ ⟨j, rfl⟩
    rw [racl_union_congr (racl_codeSet g) rfl]
    exact g.evalGen_mem_racl hy hYAcb j
  have hZ_BY : range (h.evalGen y) ⊆ racl k ((h.codeSet : Set K) ∪ range y) := by
    rintro _ ⟨j, rfl⟩
    rw [racl_union_congr (racl_codeSet h) rfl]
    exact h.evalGen_mem_racl hy hYBcb j
  have hY_AX : range y ⊆ racl k ((g.codeSet : Set K) ∪ range (g.evalGen y)) := by
    rintro _ ⟨j, rfl⟩
    have hmem := g'.evalGen_mem_racl hx hXg' j
    rw [congrFun (hg'.evalGen_evalGen hy hYAcb) j] at hmem
    refine racl_le_of_subset_racl (union_subset ?_ (subset_union_right.trans (subset_racl k _)))
      hmem
    exact hg'.cb_le.trans (racl_le_of_subset_racl ((cb_subset_racl_codeSet g).trans
      (racl_mono (k := k) subset_union_left)))
  have hY_BZ : range y ⊆ racl k ((h.codeSet : Set K) ∪ range (h.evalGen y)) := by
    rintro _ ⟨j, rfl⟩
    have hmem := h'.evalGen_mem_racl hz hZh' j
    rw [congrFun (hh'.evalGen_evalGen hy hYBcb) j] at hmem
    refine racl_le_of_subset_racl (union_subset ?_ (subset_union_right.trans (subset_racl k _)))
      hmem
    exact hh'.cb_le.trans (racl_le_of_subset_racl ((cb_subset_racl_codeSet h).trans
      (racl_mono (k := k) subset_union_left)))
  -- (GC2) for `a` and `b`.
  have hAX : racl k ((g.codeSet : Set K) ∪ range (g.evalGen y)) =
      racl k ((g.codeSet : Set K) ∪ range y) :=
    le_antisymm
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hX_AY))
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hY_AX))
  have hBY : racl k ((h.codeSet : Set K) ∪ range y) =
      racl k ((h.codeSet : Set K) ∪ range (h.evalGen y)) :=
    le_antisymm
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hY_BZ))
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hZ_BY))
  -- `x` and `z` are independent from both codes.
  have hAXB : IndepOver k (g.codeSet : Set K) (range (g.evalGen y)) (h.codeSet : Set K) := by
    have h1 : IndepOver k (∅ ∪ (g.codeSet : Set K)) (range y) (h.codeSet : Set K) :=
      (indepOver_union_right_iff.1 hY_AB).2
    rw [empty_union] at h1
    exact (indepOver_congr_left hAX).1 h1
  have hX_AB : IndepOver k ∅ (range (g.evalGen y)) ((g.codeSet : Set K) ∪ h.codeSet) :=
    indepOver_union_right_iff.2 ⟨hXA, by
      rw [empty_union]
      exact hAXB⟩
  have hBZA : IndepOver k (h.codeSet : Set K) (range (h.evalGen y)) (g.codeSet : Set K) := by
    have h1 : IndepOver k (∅ ∪ (h.codeSet : Set K)) (range y) (g.codeSet : Set K) :=
      (indepOver_union_right_iff.1 hY_BA).2
    rw [empty_union] at h1
    exact (indepOver_congr_left hBY.symm).1 h1
  have hZ_BA : IndepOver k ∅ (range (h.evalGen y)) ((h.codeSet : Set K) ∪ g.codeSet) :=
    indepOver_union_right_iff.2 ⟨hZB, by
      rw [empty_union]
      exact hBZA⟩
  have hZ_AB : IndepOver k ∅ (range (h.evalGen y)) ((g.codeSet : Set K) ∪ h.codeSet) := by
    rw [union_comm]
    exact hZ_BA
  -- The code of `c` and interalgebraicity (GC1).
  have hC_AB : ((h * g').codeSet : Set K) ⊆ racl k ((g.codeSet : Set K) ∪ h.codeSet) := by
    refine (codeSet_mul_subset h g').trans (racl_le_of_subset_racl (union_subset ?_ ?_))
    · exact subset_union_right.trans (subset_racl k _)
    · exact (codeSet_inv_subset hg').trans (racl_mono (k := k) subset_union_left)
  have hB_AC : (h.codeSet : Set K) ⊆ racl k ((g.codeSet : Set K) ∪ (h * g').codeSet) := by
    have e1 : ((h * g' * g).codeSet : Set K) = (h.codeSet : Set K) :=
      congrArg (fun u : Germ k a a ↦ (u.codeSet : Set K)) hcg
    exact (e1.symm.subset.trans (codeSet_mul_subset (h * g') g)).trans
      (racl_mono (k := k) (union_comm _ _).le)
  have hA_BC : (g.codeSet : Set K) ⊆ racl k ((h.codeSet : Set K) ∪ (h * g').codeSet) := by
    have e1 : ((g * h' * h).codeSet : Set K) = (g.codeSet : Set K) :=
      congrArg (fun u : Germ k a a ↦ (u.codeSet : Set K)) hgh'h
    refine (e1.symm.subset.trans (codeSet_mul_subset (g * h') h)).trans
      (racl_le_of_subset_racl (union_subset ?_ (subset_union_left.trans (subset_racl k _))))
    exact (codeSet_inv_subset hc').trans (racl_mono (k := k) subset_union_right)
  have hAB_AC : racl k ((g.codeSet : Set K) ∪ h.codeSet) =
      racl k ((g.codeSet : Set K) ∪ (h * g').codeSet) :=
    le_antisymm
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hB_AC))
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hC_AB))
  have hAB_BC : racl k ((g.codeSet : Set K) ∪ h.codeSet) =
      racl k ((h.codeSet : Set K) ∪ (h * g').codeSet) :=
    le_antisymm
      (racl_le_of_subset_racl (union_subset hA_BC (subset_union_left.trans (subset_racl k _))))
      (racl_le_of_subset_racl (union_subset (subset_union_right.trans (subset_racl k _)) hC_AB))
  -- (GC2) for `c`: `z = c(x)` and `x = c⁻¹(z)`.
  have hXC : IndepOver k ∅ (range (g.evalGen y)) ((h * g').codeSet : Set K) :=
    (indepOver_racl_right_iff.2 hX_AB).mono_right (by
      rw [empty_union]
      exact hC_AB)
  have hZC : IndepOver k ∅ (range (h.evalGen y)) ((h * g').codeSet : Set K) :=
    (indepOver_racl_right_iff.2 hZ_AB).mono_right (by
      rw [empty_union]
      exact hC_AB)
  have hXCcb : IndepOver k ∅ (range (g.evalGen y)) ((h * g').cb : Set K) :=
    (indepOver_codeSet_iff _ ∅ _).1 hXC
  have hZCcb : IndepOver k ∅ (range (h.evalGen y)) ((h * g').cb : Set K) :=
    (indepOver_codeSet_iff _ ∅ _).1 hZC
  have hXBg' : IndepOver k ∅ (range (g.evalGen y)) ((h.cb : Set K) ∪ g'.cb) := by
    refine (indepOver_racl_right_iff.2 hX_AB).mono_right ?_
    rw [empty_union]
    exact union_subset ((cb_subset_racl_codeSet h).trans (racl_mono (k := k) subset_union_right))
      (hg'.cb_le.trans (racl_le_of_subset_racl ((cb_subset_racl_codeSet g).trans
        (racl_mono (k := k) subset_union_left))))
  have hcx : (h * g').evalGen (g.evalGen y) = h.evalGen y := by
    rw [evalGen_mul h g' hx hXBg', hg'.evalGen_evalGen hy hYAcb]
  have hZc' : IndepOver k ∅ (range (h.evalGen y)) ((g * h').cb : Set K) :=
    (indepOver_racl_right_iff.2 hZCcb).mono_right (by
      rw [empty_union]
      exact hc'.cb_le)
  have hZ_CX : range (h.evalGen y) ⊆
      racl k (((h * g').codeSet : Set K) ∪ range (g.evalGen y)) := by
    rintro _ ⟨j, rfl⟩
    have hmem := (h * g').evalGen_mem_racl hx hXCcb j
    rw [congrFun hcx j, ← racl_union_congr (racl_codeSet (h * g')) rfl] at hmem
    exact hmem
  have hX_CZ : range (g.evalGen y) ⊆
      racl k (((h * g').codeSet : Set K) ∪ range (h.evalGen y)) := by
    rintro _ ⟨j, rfl⟩
    have e := hc'.evalGen_evalGen hx hXCcb
    rw [hcx] at e
    have hmem := (g * h').evalGen_mem_racl hz hZc' j
    rw [congrFun e j] at hmem
    refine racl_le_of_subset_racl (union_subset ?_ (subset_union_right.trans (subset_racl k _)))
      hmem
    exact hc'.cb_le.trans (racl_le_of_subset_racl ((cb_subset_racl_codeSet _).trans
      (racl_mono (k := k) subset_union_left)))
  have hCX_CZ : racl k (((h * g').codeSet : Set K) ∪ range (g.evalGen y)) =
      racl k (((h * g').codeSet : Set K) ∪ range (h.evalGen y)) :=
    le_antisymm
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hX_CZ))
      (racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) hZ_CX))
  -- (GC3): the sixteen non-collinear triples.
  have hrkC_B : erk k ∅ ((h * g').codeSet : Set K) = erk k ∅ (h.codeSet : Set K) :=
    hrkC.trans hrkB.symm
  have hrkC_A : erk k ∅ ((h * g').codeSet : Set K) = erk k ∅ (g.codeSet : Set K) :=
    hrkC.trans hrkA.symm
  have hrkX_Y : erk k ∅ (range (g.evalGen y)) = erk k ∅ (range y) := hrkX.trans hrkY.symm
  have hrkZ_Y : erk k ∅ (range (h.evalGen y)) = erk k ∅ (range y) := hrkZ.trans hrkY.symm
  have hXY : IndepOver k ∅ (range (g.evalGen y)) (range y) := hw.trans g hg y hy hYAcb
  have hZY : IndepOver k ∅ (range (h.evalGen y)) (range y) := hw.trans h hh y hy hYBcb
  have t_aby : IndepTriple k (g.codeSet : Set K) (h.codeSet : Set K) (range y) := hind'
  have t_abx : IndepTriple k (g.codeSet : Set K) (h.codeSet : Set K) (range (g.evalGen y)) :=
    IndepTriple.of_indepOver hAB hX_AB hBfin hXfin
  have t_abz : IndepTriple k (g.codeSet : Set K) (h.codeSet : Set K) (range (h.evalGen y)) :=
    IndepTriple.of_indepOver hAB hZ_AB hBfin hZfin
  have hBC_BA : racl k ((h.codeSet : Set K) ∪ (h * g').codeSet) =
      racl k ((h.codeSet : Set K) ∪ g.codeSet) := by
    rw [← hAB_BC, union_comm]
  have t_acx := t_abx.of_racl_union_eq hAB_AC.symm hrkC_B
  have t_acy := t_aby.of_racl_union_eq hAB_AC.symm hrkC_B
  have t_acz := t_abz.of_racl_union_eq hAB_AC.symm hrkC_B
  have t_bcx := t_abx.perm_left.of_racl_union_eq hBC_BA hrkC_A
  have t_bcy := t_aby.perm_left.of_racl_union_eq hBC_BA hrkC_A
  have t_bcz := t_abz.perm_left.of_racl_union_eq hBC_BA hrkC_A
  have hA_YZ : IndepOver k ∅ (g.codeSet : Set K) (range y ∪ range (h.evalGen y)) :=
    (indepOver_racl_right_iff.2 hA_BY).mono_right (by
      rw [empty_union]
      exact union_subset (subset_union_right.trans (subset_racl k _)) hZ_BY)
  have hB_XY : IndepOver k ∅ (h.codeSet : Set K) (range (g.evalGen y) ∪ range y) :=
    (indepOver_racl_right_iff.2 hB_AY).mono_right (by
      rw [empty_union]
      exact union_subset hX_AY (subset_union_right.trans (subset_racl k _)))
  have t_ayz : IndepTriple k (g.codeSet : Set K) (range y) (range (h.evalGen y)) :=
    (IndepTriple.of_indepOver hZY.symm hA_YZ hZfin hAfin).rotate.rotate
  have t_axz := t_ayz.of_racl_union_eq hAX hrkX_Y
  have t_bxy : IndepTriple k (h.codeSet : Set K) (range (g.evalGen y)) (range y) :=
    (IndepTriple.of_indepOver hXY hB_XY hYfin hBfin).rotate.rotate
  have t_bxz := t_bxy.of_racl_union_eq' hBY.symm hrkZ_Y
  -- `(c, x, y)`: `c` and `h` are interalgebraic over `g`.
  have hXYA_B : erk k (range (g.evalGen y) ∪ range y ∪ (g.codeSet : Set K))
      (h.codeSet : Set K) = erk k ∅ (h.codeSet : Set K) := by
    rw [union_assoc, union_comm (range (g.evalGen y)),
      erk_base_union_of_subset_racl k (hX_AY.trans (racl_mono (k := k) (union_comm _ _).le))]
    have := hB_AY.erk_eq (subset_refl _) hBfin
    rwa [empty_union, union_comm] at this
  have hC_XY : IndepOver k ∅ ((h * g').codeSet : Set K) (range (g.evalGen y) ∪ range y) := by
    refine indepOver_of_erk_eq hCfin (le_antisymm ?_ ?_)
    · rw [empty_union]
      exact erk_base_mono k (empty_subset _) _
    · rw [empty_union]
      calc erk k ∅ ((h * g').codeSet : Set K) = erk k ∅ (h.codeSet : Set K) := hrkC_B
        _ = erk k (range (g.evalGen y) ∪ range y ∪ (g.codeSet : Set K)) (h.codeSet : Set K) :=
          hXYA_B.symm
        _ = erk k (range (g.evalGen y) ∪ range y ∪ (g.codeSet : Set K))
              ((h * g').codeSet : Set K) := by
          refine (erk_eq_of_subset_racl ?_ ?_).symm
          · exact hC_AB.trans (racl_mono (k := k) (union_subset
              (subset_union_right.trans subset_union_left) subset_union_right))
          · exact hB_AC.trans (racl_mono (k := k) (union_subset
              (subset_union_right.trans subset_union_left) subset_union_right))
        _ ≤ erk k (range (g.evalGen y) ∪ range y) ((h * g').codeSet : Set K) :=
          erk_base_mono k subset_union_left _
  have t_cxy : IndepTriple k ((h * g').codeSet : Set K) (range (g.evalGen y)) (range y) :=
    (IndepTriple.of_indepOver hXY hC_XY hYfin hCfin).rotate.rotate
  -- `(c, y, z)`: `c` and `g` are interalgebraic over `h`.
  have hYZB_A : erk k (range y ∪ range (h.evalGen y) ∪ (h.codeSet : Set K))
      (g.codeSet : Set K) = erk k ∅ (g.codeSet : Set K) := by
    rw [union_right_comm,
      erk_base_union_of_subset_racl k (hZ_BY.trans (racl_mono (k := k) (union_comm _ _).le))]
    have := hA_BY.erk_eq (subset_refl _) hAfin
    rwa [empty_union, union_comm] at this
  have hC_YZ : IndepOver k ∅ ((h * g').codeSet : Set K) (range y ∪ range (h.evalGen y)) := by
    refine indepOver_of_erk_eq hCfin (le_antisymm ?_ ?_)
    · rw [empty_union]
      exact erk_base_mono k (empty_subset _) _
    · rw [empty_union]
      calc erk k ∅ ((h * g').codeSet : Set K) = erk k ∅ (g.codeSet : Set K) := hrkC_A
        _ = erk k (range y ∪ range (h.evalGen y) ∪ (h.codeSet : Set K)) (g.codeSet : Set K) :=
          hYZB_A.symm
        _ = erk k (range y ∪ range (h.evalGen y) ∪ (h.codeSet : Set K))
              ((h * g').codeSet : Set K) := by
          refine (erk_eq_of_subset_racl ?_ ?_).symm
          · exact hC_AB.trans (racl_mono (k := k) (union_subset subset_union_right
              (subset_union_right.trans subset_union_left)))
          · exact hA_BC.trans (racl_mono (k := k) (union_subset
              (subset_union_right.trans subset_union_left) subset_union_right))
        _ ≤ erk k (range y ∪ range (h.evalGen y)) ((h * g').codeSet : Set K) :=
          erk_base_mono k subset_union_left _
  have t_cyz : IndepTriple k ((h * g').codeSet : Set K) (range y) (range (h.evalGen y)) :=
    (IndepTriple.of_indepOver hZY.symm hC_YZ hZfin hCfin).rotate.rotate
  -- `(x, y, z)`.
  have hZ_YA : IndepOver k ∅ (range (h.evalGen y)) (range y ∪ (g.codeSet : Set K)) := by
    have h1 : IndepOver k (∅ ∪ range y) (g.codeSet : Set K) (range (h.evalGen y)) :=
      (indepOver_union_right_iff.1 hA_YZ).2
    exact indepOver_union_right_iff.2 ⟨hZY, h1.symm⟩
  have hZ_XY : IndepOver k ∅ (range (h.evalGen y)) (range (g.evalGen y) ∪ range y) := by
    refine indepOver_of_erk_eq hZfin (le_antisymm ?_ ?_)
    · rw [empty_union]
      exact erk_base_mono k (empty_subset _) _
    · rw [empty_union]
      calc erk k ∅ (range (h.evalGen y))
          = erk k (∅ ∪ (range y ∪ (g.codeSet : Set K))) (range (h.evalGen y)) :=
            (hZ_YA.erk_eq (subset_refl _) hZfin).symm
        _ = erk k (range (g.evalGen y) ∪ range y ∪ (g.codeSet : Set K)) (range (h.evalGen y)) := by
            rw [empty_union, union_assoc, union_comm (range (g.evalGen y)),
              erk_base_union_of_subset_racl k
                (hX_AY.trans (racl_mono (k := k) (union_comm _ _).le))]
        _ ≤ erk k (range (g.evalGen y) ∪ range y) (range (h.evalGen y)) :=
            erk_base_mono k subset_union_left _
  have t_xyz : IndepTriple k (range (g.evalGen y)) (range y) (range (h.evalGen y)) :=
    IndepTriple.of_indepOver hXY hZ_XY hYfin hZfin
  -- Transport to the code tuples.
  have hA' : racl k (range g.codeTuple) = racl k (g.codeSet : Set K) := by rw [range_codeTuple]
  have hB' : racl k (range h.codeTuple) = racl k (h.codeSet : Set K) := by rw [range_codeTuple]
  have hC' : racl k (range (h * g').codeTuple) = racl k ((h * g').codeSet : Set K) := by
    rw [range_codeTuple]
  -- (GC4) via the dictionary between triples and germs.
  have ht_a : IsTriple k a a g.codeTuple y (g.evalGen y) :=
    { isGen_left := hy
      isGen_right := hx
      indep_left := by
        rw [range_codeTuple]
        exact hYA
      indep_right := by
        rw [range_codeTuple]
        exact hXA
      mem_dcl := fun j ↦ by
        rw [range_codeTuple, adjoin_codeSet]
        exact g.evalGen_mem_dclAdjoin hy hYAcb j }
  have ht_b : IsTriple k a a h.codeTuple y (h.evalGen y) :=
    { isGen_left := hy
      isGen_right := hz
      indep_left := by
        rw [range_codeTuple]
        exact hYB
      indep_right := by
        rw [range_codeTuple]
        exact hZB
      mem_dcl := fun j ↦ by
        rw [range_codeTuple, adjoin_codeSet]
        exact h.evalGen_mem_dclAdjoin hy hYBcb j }
  have ht_c : IsTriple k a a (h * g').codeTuple (g.evalGen y) (h.evalGen y) :=
    { isGen_left := hx
      isGen_right := hz
      indep_left := by
        rw [range_codeTuple]
        exact hXC
      indep_right := by
        rw [range_codeTuple]
        exact hZC
      mem_dcl := fun j ↦ by
        rw [range_codeTuple, adjoin_codeSet]
        have := (h * g').evalGen_mem_dclAdjoin hx hXCcb j
        rw [congrFun hcx j] at this
        exact this }
  have hga : g = ht_a.germ := ht_a.eq_germ (by
    rw [racl_codeTuple]
    exact subset_racl k _) rfl
  have hhb : h = ht_b.germ := ht_b.eq_germ (by
    rw [racl_codeTuple]
    exact subset_racl k _) rfl
  have hcc : h * g' = ht_c.germ := ht_c.eq_germ (by
    rw [racl_codeTuple]
    exact subset_racl k _) hcx
  have hcb_a := ht_a.germ_cb
  rw [← hga] at hcb_a
  have hcb_b := ht_b.germ_cb
  rw [← hhb] at hcb_b
  have hcb_c := ht_c.germ_cb
  rw [← hcc] at hcb_c
  -- (GC5).
  have hn : 1 ≤ erk k ∅ (g.codeSet : Set K) := by
    refine Order.one_le_iff_ne_zero.2 fun h0 ↦ ?_
    have hA0 : (g.codeSet : Set K) ⊆ (racl k (∅ : Set K) : Set K) := (erk_eq_zero_iff k).1 h0
    have hXY' : range (g.evalGen y) ⊆ racl k (range y) :=
      hX_AY.trans (racl_le_of_subset_racl (union_subset
        (hA0.trans (racl_mono (k := k) (empty_subset _))) (subset_racl k _)))
    have e := hXY.erk_eq (subset_refl _) hXfin
    rw [empty_union, erk_eq_zero_of_subset_racl k hXY', hrkX] at e
    rw [← e] at hm
    exact absurd hm (by decide)
  refine ⟨?_, hcx, hcg⟩
  exact
    { racl_ab_ac := by rw [racl_union_congr hA' hB', racl_union_congr hA' hC', hAB_AC]
      racl_ab_bc := by rw [racl_union_congr hA' hB', racl_union_congr hB' hC', hAB_BC]
      racl_ax_ay := by rw [racl_union_congr hA' rfl, racl_union_congr hA' rfl, hAX]
      racl_by_bz := by rw [racl_union_congr hB' rfl, racl_union_congr hB' rfl, hBY]
      racl_cx_cz := by rw [racl_union_congr hC' rfl, racl_union_congr hC' rfl, hCX_CZ]
      indep := indep_of_sixteen
        (indepTriple_of_racl_eq hA'.symm hB'.symm rfl t_abx)
        (indepTriple_of_racl_eq hA'.symm hB'.symm rfl t_aby)
        (indepTriple_of_racl_eq hA'.symm hB'.symm rfl t_abz)
        (indepTriple_of_racl_eq hA'.symm hC'.symm rfl t_acx)
        (indepTriple_of_racl_eq hA'.symm hC'.symm rfl t_acy)
        (indepTriple_of_racl_eq hA'.symm hC'.symm rfl t_acz)
        (indepTriple_of_racl_eq hA'.symm rfl rfl t_axz)
        (indepTriple_of_racl_eq hA'.symm rfl rfl t_ayz)
        (indepTriple_of_racl_eq hB'.symm hC'.symm rfl t_bcx)
        (indepTriple_of_racl_eq hB'.symm hC'.symm rfl t_bcy)
        (indepTriple_of_racl_eq hB'.symm hC'.symm rfl t_bcz)
        (indepTriple_of_racl_eq hB'.symm rfl rfl t_bxy)
        (indepTriple_of_racl_eq hB'.symm rfl rfl t_bxz)
        (indepTriple_of_racl_eq hC'.symm rfl rfl t_cxy)
        (indepTriple_of_racl_eq hC'.symm rfl rfl t_cyz)
        t_xyz
      cb_a := by
        rw [canonicalBase_sum_elim_swap, ← hcb_a, ← racl_codeTuple]
        exact subset_racl k _
      cb_b := by
        rw [← hcb_b, ← racl_codeTuple]
        exact subset_racl k _
      cb_c := by
        rw [← hcb_c, ← racl_codeTuple]
        exact subset_racl k _
      one_le_erk := by
        rw [GroupConfig.erk_eq_of_racl_eq hA']
        exact hn }

/-- `prop:converse` on the actual canonical zero-padded RREF code vectors, with
both source ranks and the action identities. The inverse and the third germ
are produced internally from the Hrushovski–Weil hypotheses. -/
theorem groupConfiguration_code {g₀ : Germ k a a} (hw : IsHW g₀) {g h : Germ k a a}
    (hg : g ∈ orbit g₀) (hh : h ∈ orbit g₀) {y : ι → K} (hy : IsGen k a y)
    (hind : IndepTriple k (g.cb : Set K) (h.cb : Set K) (range y))
    (hm : 1 ≤ erk k ∅ (range a)) :
    ∃ c : Germ k a a,
      GroupConfiguration k g.code h.code c.code (g.evalGen y) y (h.evalGen y) ∧
      erk k ∅ (range g.code) = erk k ∅ (g₀.cb : Set K) ∧
      erk k ∅ (range y) = erk k ∅ (range a) ∧
      c.evalGen (g.evalGen y) = h.evalGen y ∧ c * g = h := by
  obtain ⟨g', hg'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hg)
  obtain ⟨hc, heval, hcomp⟩ := hw.groupConfiguration hg hh hy hind hm hg'
  have he (f : Germ k a a) : racl k (range f.code) = racl k (range f.codeTuple) := by
    rw [← racl_adjoin_coe (range f.code), adjoin_range_code, racl_codeTuple]
  have hrank : erk k ∅ (range g.code) = erk k ∅ (g.cb : Set K) :=
    GroupConfig.erk_eq_of_racl_eq (by
      rw [← racl_adjoin_coe (range g.code), adjoin_range_code])
  exact ⟨h * g', hc.ofRaclEq (he g) (he h) (he (h * g')) rfl rfl rfl,
    hrank.trans (erk_cb_eq_of_mem_orbit hg), erk_empty_range_eq_of_idealOf_eq hy,
    heval, hcomp⟩

end IsHW

end Germ

end

end GroupConfig
