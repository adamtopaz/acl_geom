/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Geometry.Representatives

/-!
# Relocating an affine presentation with five fixed parameters

The relocation step of meet elimination in the corrected blueprint Lemma
`affine-grid-extraction` (#27).  Let `a, b, x, c` be independent and put `y = a x + b`.  Let
`p ∈ acl(a, b) \ acl(a)`, `δ ∈ acl(a, x) ∩ acl(p, y)` and `f ∈ acl(c, δ)`; in the
configuration these are the points `P`, `D` and `F`.  Given `a₀` fresh over `a, b, x, c`,
`exists_affine_relocation` produces a second presentation `a' x' + b' = a x + b` that keeps the
five parameters `p, y, δ, c, f` literally fixed:

* the joint vanishing ideal of `(p, y, δ, c, f; a', b', x')` equals that of
  `(p, y, δ, c, f; a, b, x)`;
* `a'` is algebraic over `p, y, c, a₀` and fresh over `a, b, x, c`;
* `p ∈ acl(a', b')`, `δ ∈ acl(a', x')` and the affine value is unchanged.

The relocated multiplier `a'` need not equal `a₀`.  The proof is the joint relocation
`exists_joint_relocation` over the fixed base `k(p, y, δ, c, f)`, whose closure is
`acl(p, y, c)`; the transfers are the vanishing-ideal transfers of `Correspondence.FunctionField`.
The existence of `a₀` is left to the caller.

**Status:** fixed-five relocation with a supplied fresh parameter proved (#27, L1b).
Coordinate extraction, linearity and guarded completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Affine relocation with five fixed parameters** (corrected blueprint Lemma
`affine-grid-extraction`, meet elimination, #27).  The presentation `y = a x + b` relocates to
`y = a' x' + b'` with `p, y, δ, c, f` literally fixed, the joint vanishing ideal unchanged, and
`a'` fresh over `a, b, x, c`. -/
theorem exists_affine_relocation [IsAlgClosed K] {a b x c p δ f a₀ : K}
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδy : δ ∈ racl k ({p, a * x + b} : Set K))
    (hf : f ∈ racl k ({c, δ} : Set K)) (ha₀ : a₀ ∉ racl k ({a, b, x, c} : Set K)) :
    ∃ a' b' x' : K,
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a', b', x']) =
        idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) ∧
      a' ∈ racl k ({p, a * x + b, c, a₀} : Set K) ∧ a' ∉ racl k ({a, b, x, c} : Set K) ∧
      p ∈ racl k ({a', b'} : Set K) ∧ δ ∈ racl k ({a', x'} : Set K) ∧
      a' * x' + b' = a * x + b := by
  classical
  have ha0 : a ≠ 0 := hind.ne_zero 0
  -- `b ∈ acl(a, p)` by exchange, and `x = ((a x + b) - b) / a`.
  have hb : b ∈ racl k ({a, p} : Set K) := by
    have h : p ∈ racl k (insert b ({a} : Set K)) := by
      rwa [Set.pair_comm] at hp
    have h' := racl_exchange h hpa
    rwa [Set.pair_comm] at h'
  have hxeq : (a * x + b - b) * a⁻¹ = x := by
    rw [add_sub_cancel_right, mul_comm a x, mul_inv_cancel_right₀ ha0]
  -- The fixed parameters lie in `acl(p, y, c)` and in `acl(a, b, x, c)`.
  have hP3 : p ∈ racl k ({p, a * x + b, c} : Set K) := subset_racl k _ (by simp)
  have hY3 : a * x + b ∈ racl k ({p, a * x + b, c} : Set K) := subset_racl k _ (by simp)
  have hC3 : c ∈ racl k ({p, a * x + b, c} : Set K) := subset_racl k _ (by simp)
  have hD3 : δ ∈ racl k ({p, a * x + b, c} : Set K) :=
    racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hP3, Set.singleton_subset_iff.2 hY3⟩) hδy
  have hF3 : f ∈ racl k ({p, a * x + b, c} : Set K) :=
    racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hC3, Set.singleton_subset_iff.2 hD3⟩) hf
  have hpyc : Set.range ![p, a * x + b, δ, c, f] ⊆ racl k ({p, a * x + b, c} : Set K) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hP3
    · exact hY3
    · exact hD3
    · exact hC3
    · exact hF3
  have hA4 : a ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
  have hB4 : b ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
  have hX4 : x ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
  have hC4 : c ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
  have hP4 : p ∈ racl k ({a, b, x, c} : Set K) :=
    racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hA4, Set.singleton_subset_iff.2 hB4⟩) hp
  have hY4 : a * x + b ∈ racl k ({a, b, x, c} : Set K) := add_mem (mul_mem hA4 hX4) hB4
  have hD4 : δ ∈ racl k ({a, b, x, c} : Set K) :=
    racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hA4, Set.singleton_subset_iff.2 hX4⟩) hδx
  have hF4 : f ∈ racl k ({a, b, x, c} : Set K) :=
    racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hC4, Set.singleton_subset_iff.2 hD4⟩) hf
  have habxc : Set.range ![p, a * x + b, δ, c, f] ⊆ racl k ({a, b, x, c} : Set K) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hP4
    · exact hY4
    · exact hD4
    · exact hC4
    · exact hF4
  -- `a, p, y, c` span the same closure as `a, b, x, c`, so `a ∉ acl(p, y, c)`.
  have hind' : AlgebraicIndependent k ![a, p, a * x + b, c] := by
    refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
    · have hAv : a ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨0, rfl⟩
      have hBv : b ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨1, rfl⟩
      have hXv : x ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨2, rfl⟩
      have hCv : c ∈ racl k (Set.range ![a, b, x, c]) := subset_racl k _ ⟨3, rfl⟩
      have hPv : p ∈ racl k (Set.range ![a, b, x, c]) :=
        racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hAv, Set.singleton_subset_iff.2 hBv⟩) hp
      intro j
      fin_cases j
      · exact hAv
      · exact hPv
      · exact add_mem (mul_mem hAv hXv) hBv
      · exact hCv
    · have hAw : a ∈ racl k (Set.range ![a, p, a * x + b, c]) := subset_racl k _ ⟨0, rfl⟩
      have hPw : p ∈ racl k (Set.range ![a, p, a * x + b, c]) := subset_racl k _ ⟨1, rfl⟩
      have hYw : a * x + b ∈ racl k (Set.range ![a, p, a * x + b, c]) :=
        subset_racl k _ ⟨2, rfl⟩
      have hCw : c ∈ racl k (Set.range ![a, p, a * x + b, c]) := subset_racl k _ ⟨3, rfl⟩
      have hBw : b ∈ racl k (Set.range ![a, p, a * x + b, c]) :=
        racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hAw, Set.singleton_subset_iff.2 hPw⟩) hb
      have hXw : x ∈ racl k (Set.range ![a, p, a * x + b, c]) := by
        have h := mul_mem (sub_mem hYw hBw) (inv_mem hAw)
        rw [hxeq] at h
        exact h
      intro i
      fin_cases i
      · exact hAw
      · exact hBw
      · exact hXw
      · exact hCw
  have ha_pyc : a ∉ racl k ({p, a * x + b, c} : Set K) := by
    have h := AlgebraicIndependent.notMem_racl_image hind' (S := {1, 2, 3}) (i := 0) (by decide)
    simpa [Set.image_insert_eq] using h
  -- The hypotheses of the joint relocation over the fixed base `k(p, y, δ, c, f)`.
  have ht : AlgebraicIndependent ↥(adjoin k (Set.range ![p, a * x + b, δ, c, f])) ![a] :=
    algebraicIndependent_unique_type_iff.2 fun hal ↦
      ha_pyc (racl_le_of_subset_racl hpyc ((mem_racl_iff k).2 hal))
  have hs : AlgebraicIndependent ↥(adjoin k (Set.range ![p, a * x + b, δ, c, f])) ![a₀] :=
    algebraicIndependent_unique_type_iff.2 fun hal ↦
      ha₀ (racl_le_of_subset_racl habxc ((mem_racl_iff k).2 hal))
  have hsub : Set.range ![a] ⊆ Set.range ![a, b, x] := by
    rw [Matrix.range_cons_empty]
    exact Set.singleton_subset_iff.2 ⟨0, rfl⟩
  have hle : adjoin ↥(adjoin k (Set.range ![p, a * x + b, δ, c, f])) (Set.range ![a]) ≤
      adjoin ↥(adjoin k (Set.range ![p, a * x + b, δ, c, f])) (Set.range ![a, b, x]) :=
    adjoin.mono _ _ _ hsub
  have hgen : ∀ z ∈ Set.range ![a, b, x], IsAlgebraic
      ↥(adjoin ↥(adjoin k (Set.range ![p, a * x + b, δ, c, f])) (Set.range ![a])) z := by
    have hA : a ∈ racl k (insert a (Set.range ![p, a * x + b, δ, c, f])) :=
      subset_racl k _ (Set.mem_insert _ _)
    have hP : p ∈ racl k (insert a (Set.range ![p, a * x + b, δ, c, f])) :=
      subset_racl k _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩)
    have hY : a * x + b ∈ racl k (insert a (Set.range ![p, a * x + b, δ, c, f])) :=
      subset_racl k _ (Set.mem_insert_of_mem _ ⟨1, rfl⟩)
    have hB : b ∈ racl k (insert a (Set.range ![p, a * x + b, δ, c, f])) :=
      racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hA, Set.singleton_subset_iff.2 hP⟩) hb
    have hX : x ∈ racl k (insert a (Set.range ![p, a * x + b, δ, c, f])) := by
      have h := mul_mem (sub_mem hY hB) (inv_mem hA)
      rw [hxeq] at h
      exact h
    rw [Matrix.range_cons_empty]
    rintro _ ⟨i, rfl⟩
    refine mem_racl_insert_iff.1 ?_
    fin_cases i
    · exact hA
    · exact hB
    · exact hX
  -- The joint relocation.
  obtain ⟨v, hrel, hvalg⟩ := exists_joint_relocation ![p, a * x + b, δ, c, f] ht hle
    (isAlgebraic_extendScalars_adjoin hle hgen) hs
  have hideal := idealOf_eq_of_aeval_iff k hrel
  have hv : ![v 0, v 1, v 2] = v := by
    funext i
    fin_cases i <;> rfl
  -- The relocated multiplier is algebraic over `p, y, c, a₀` and fresh over `a, b, x, c`.
  have hv0 : v 0 ∈ racl k (insert a₀ ({p, a * x + b, c} : Set K)) := by
    have h := hvalg 0
    rw [Matrix.range_cons_empty] at h
    refine racl_le_of_subset_racl ?_ (mem_racl_insert_iff.2 h)
    exact Set.insert_subset_iff.2 ⟨subset_racl k _ (Set.mem_insert _ _),
      fun z hz ↦ racl_mono (Set.subset_insert _ _) (hpyc hz)⟩
  have hv0pyc : v 0 ∉ racl k ({p, a * x + b, c} : Set K) := by
    have h : Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] (Sum.inr 0) ∉
        racl k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] ''
          {Sum.inl 0, Sum.inl 1, Sum.inl 3}) := by
      simpa [Set.image_insert_eq] using ha_pyc
    have h' := notMem_racl_image_of_idealOf_eq k hideal.symm h
    simpa [Set.image_insert_eq] using h'
  have hfresh : v 0 ∉ racl k ({a, b, x, c} : Set K) := by
    intro hv4
    have hex := racl_exchange hv0 hv0pyc
    refine ha₀ (racl_le_of_subset_racl ?_ hex)
    exact Set.insert_subset_iff.2 ⟨hv4, Set.insert_subset_iff.2 ⟨hP4,
      Set.insert_subset_iff.2 ⟨hY4, Set.singleton_subset_iff.2 hC4⟩⟩⟩
  have hv0' : v 0 ∈ racl k ({p, a * x + b, c, a₀} : Set K) := by
    rwa [Set.insert_comm a₀ p, Set.insert_comm a₀ (a * x + b), Set.pair_comm a₀ c] at hv0
  -- Transfers along the joint vanishing ideal.
  have hp' : p ∈ racl k ({v 0, v 1} : Set K) := by
    have h : Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] (Sum.inl 0) ∈
        racl k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] '' {Sum.inr 0, Sum.inr 1}) := by
      simpa [Set.image_insert_eq] using hp
    have h' := mem_racl_image_of_idealOf_eq k hideal.symm h
    simpa [Set.image_insert_eq] using h'
  have hδ' : δ ∈ racl k ({v 0, v 2} : Set K) := by
    have h : Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] (Sum.inl 2) ∈
        racl k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x] '' {Sum.inr 0, Sum.inr 2}) := by
      simpa [Set.image_insert_eq] using hδx
    have h' := mem_racl_image_of_idealOf_eq k hideal.symm h
    simpa [Set.image_insert_eq] using h'
  have hval : v 0 * v 2 + v 1 = a * x + b := by
    have h := aeval_eq_aeval_of_idealOf_eq k hideal.symm
      (f := X (Sum.inr 0) * X (Sum.inr 2) + X (Sum.inr 1)) (g := X (Sum.inl 1)) (by simp)
    simpa using h
  refine ⟨v 0, v 1, v 2, ?_, hv0', hfresh, hp', hδ', hval⟩
  rw [hv]
  exact hideal

end

end AclGeom
