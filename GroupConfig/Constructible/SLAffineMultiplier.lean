/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Constructible.SLUpperCurve

/-!
# The multipliers of two upper triangular curves

Let `g, h ∈ SL₂(K)` be upper triangular with eight entries of rank four over an algebraically
closed universal-domain base `k`. Let `s, t, u` be algebraic over the entries of `g`, `h` and
`h g` respectively, with `{s, t}`, `{s, u}` and `{s, t, u}` of rank two.
`upper_curve_diagonal_rows` shows that `s`, `t` and `u` are interalgebraic with the diagonal
entries `g₀₀`, `h₀₀` and `(h g)₀₀`.

The proof works over `E = acl(s, t)`, where `g`, `h` and `h g` lie on curves. The coset
structure and the unipotent/torus dichotomy of `GroupConfig.Constructible.SLUpperCurve` apply
there. In the unipotent case, independent copies over `E` force `g₀₀` to be algebraic over `s`.
In the torus case, the common fixed point `μ` of the torus gives `g⁻¹ · μ`, algebraic over `s`
and over `u` and hence over the base; then all entries of `g` are algebraic over `g₀₀`,
contradicting rank two.

The consumer is the initial affine chart `GroupConfig.exists_initial_chart_generic`. There the
rows identify the points `S, T, U` of a Ψ witness with the multipliers `a, c, a c` (#27).

**Status:** `upper_curve_diagonal_rows` is proved; the supporting lemmas are private.
-/

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-! ### Rank bookkeeping for the multiplier identification -/

/-- Cancellation of a natural summand in `ℕ∞`. -/
private theorem enat_eq_sub_of_add_eq {a c : ℕ} {x : ℕ∞} (h : (a : ℕ∞) + x = c) :
    x = ((c - a : ℕ) : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe n =>
    norm_cast at h ⊢
    omega

/-- A singleton outside a closure has rank one over its base. -/
private theorem erk_singleton_of_notMem {k K : Type*} [Field k] [Field K] [Algebra k K]
    {C : Set K} {x : K} (h : x ∉ racl k C) : erk k C ({x} : Set K) = 1 :=
  le_antisymm ((erk_le_encard k C _).trans (by simp))
    (Order.one_le_iff_ne_zero.2 fun h0 ↦ h ((erk_eq_zero_iff k).1 h0 (mem_singleton x)))

/-- The entries of an upper triangular matrix have rank at most two over any base. -/
private theorem erk_slEntries_upper_le_two {k K : Type*} [Field k] [Field K] [Algebra k K]
    (C : Set K) (m : SpecialLinearGroup (Fin 2) K) (hm : m 1 0 = 0) :
    erk k C (slEntries m) ≤ 2 := by
  have hdet : m 0 0 * m 1 1 = 1 := by
    have h := m.det_coe
    rw [Matrix.det_fin_two, hm, mul_zero, sub_zero] at h
    exact h
  have hsub : slEntries m ⊆ racl k (C ∪ {m 0 0, m 0 1}) := by
    have h0 : m 0 0 ∈ racl k (C ∪ {m 0 0, m 0 1}) := subset_racl k _ (Or.inr (Or.inl rfl))
    have h1 : m 0 1 ∈ racl k (C ∪ {m 0 0, m 0 1}) := subset_racl k _ (Or.inr (Or.inr rfl))
    have h3 : m 1 1 ∈ racl k (C ∪ {m 0 0, m 0 1}) := by
      rw [eq_inv_of_mul_eq_one_right hdet]
      exact inv_mem h0
    have h2 : m 1 0 ∈ racl k (C ∪ {m 0 0, m 0 1}) := by
      rw [hm]
      exact zero_mem _
    rintro _ ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  calc erk k C (slEntries m) ≤ erk k C (racl k (C ∪ {m 0 0, m 0 1}) : Set K) :=
        erk_mono k C hsub
    _ = erk k C {m 0 0, m 0 1} := erk_racl k C _
    _ ≤ 2 := (erk_le_encard k C _).trans ((encard_insert_le _ _).trans (by simp; norm_num))

/-- Two ranks bounded by two summing to at least four are both two. -/
private theorem enat_eq_two_of_add {x y : ℕ∞} (hx : x ≤ 2) (hy : y ≤ 2) (h : 4 ≤ x + y) :
    x = 2 ∧ y = 2 := by
  induction x using ENat.recTopCoe with
  | top => simp at hx
  | coe a =>
    induction y using ENat.recTopCoe with
    | top => simp at hy
    | coe b =>
      norm_cast at hx hy h ⊢
      omega

/-- In a pair of rank two, the second member is outside the closure of the first. -/
private theorem notMem_racl_singleton_of_pair {k K : Type*} [Field k] [Field K] [Algebra k K]
    {x y : K} (h : erk k ∅ ({x, y} : Set K) = 2) : y ∉ racl k ({x} : Set K) := by
  intro hy
  have hle : erk k ∅ ({x, y} : Set K) ≤ 1 := by
    have hsub : ({x, y} : Set K) ⊆ racl k ({x} : Set K) := by
      rintro z (rfl | rfl)
      · exact subset_racl k _ rfl
      · exact hy
    calc erk k ∅ ({x, y} : Set K) ≤ erk k ∅ (racl k ({x} : Set K) : Set K) := erk_mono k ∅ hsub
      _ = erk k ∅ ({x} : Set K) := by
          simpa only [empty_union] using erk_racl k (∅ : Set K) ({x} : Set K)
      _ ≤ 1 := (erk_le_encard k ∅ _).trans (by simp)
  rw [h] at hle
  norm_num at hle

/-- Joining a set to an independent rank-two pair: the rank formula used three times below. -/
private theorem erk_pair_base_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    {P X : Set K} {a b : ℕ} (hP : erk k ∅ P = a) (hPX : erk k ∅ (P ∪ X) = (a + b : ℕ)) :
    erk k P X = b := by
  have h := erk_union_eq k ∅ P X
  rw [empty_union, hP, hPX] at h
  have h' := enat_eq_sub_of_add_eq h.symm
  rw [h']
  norm_num

/-- **Rank preparation for the multiplier identification.** Over
`E = acl(s, t)` the two matrices and their product have rank one, they are jointly of rank two,
and `u` lies in `E`. Over the single representatives each matrix has rank one. -/
private theorem upper_curve_ranks {k K : Type*} [Field k] [Field K] [Algebra k K]
    (g h : SpecialLinearGroup (Fin 2) K) (hg10 : g 1 0 = 0) (hh10 : h 1 0 = 0)
    (hgh : erk k ∅ (slEntries g ∪ slEntries h) = 4) {s t u : K}
    (hs : s ∈ racl k (slEntries g)) (ht : t ∈ racl k (slEntries h))
    (hu : u ∈ racl k (slEntries (h * g)))
    (hst : erk k ∅ ({s, t} : Set K) = 2) (hsu : erk k ∅ ({s, u} : Set K) = 2)
    (hstu : erk k ∅ ({s, t, u} : Set K) = 2) :
    erk k ∅ (slEntries g) = 2 ∧ erk k {s, t} (slEntries g) = 1 ∧
      erk k {s, t} (slEntries h) = 1 ∧ erk k {s, t} (slEntries g ∪ slEntries h) = 2 ∧
      erk k {s, t} (slEntries (h * g)) = 1 ∧ u ∈ racl k ({s, t} : Set K) ∧
      erk k {s} (slEntries g) = 1 ∧ erk k {t} (slEntries h) = 1 ∧
      erk k {u} (slEntries (h * g)) = 1 := by
  -- Ranks of the two matrices and their independence.
  have hp10 : (h * g) 1 0 = 0 := by
    rw [sl_mul_apply, hh10, hg10, zero_mul, mul_zero, add_zero]
  obtain ⟨hG2, hH2⟩ := enat_eq_two_of_add (erk_slEntries_upper_le_two ∅ g hg10)
    (erk_slEntries_upper_le_two ∅ h hh10) (by rw [← hgh]; exact erk_union_le k ∅ _ _)
  have hGH : erk k (slEntries g) (slEntries h) = 2 :=
    erk_pair_base_eq (a := 2) (b := 2) hG2 (by rw [hgh]; rfl)
  have hinGH : (racl k (slEntries g) : Set K) ∩ racl k (slEntries h) ⊆ racl k (∅ : Set K) := by
    have hind : IndepOver k ∅ (slEntries h) (slEntries g) :=
      indepOver_of_erk_eq (finite_range _) (by rw [empty_union, hGH, hH2])
    have h := hind.racl_inter_eq
    rw [empty_union, empty_union] at h
    rw [inter_comm, h]
  have hPG : racl k (slEntries (h * g) ∪ slEntries g) = racl k (slEntries h ∪ slEntries g) :=
    racl_sl_product_union h g
  have hPG4 : erk k ∅ (slEntries (h * g) ∪ slEntries g) = 4 := by
    rw [erk_eq_of_racl_eq hPG, union_comm]
    exact hgh
  obtain ⟨hP2, -⟩ := enat_eq_two_of_add (erk_slEntries_upper_le_two ∅ (h * g) hp10)
    (erk_slEntries_upper_le_two ∅ g hg10) (by rw [← hPG4]; exact erk_union_le k ∅ _ _)
  have hGP : erk k (slEntries g) (slEntries (h * g)) = 2 :=
    erk_pair_base_eq (a := 2) (b := 2) hG2 (by rw [union_comm, hPG4]; rfl)
  have hinGP : (racl k (slEntries g) : Set K) ∩ racl k (slEntries (h * g)) ⊆
      racl k (∅ : Set K) := by
    have hind : IndepOver k ∅ (slEntries (h * g)) (slEntries g) :=
      indepOver_of_erk_eq (finite_range _) (by rw [empty_union, hGP, hP2])
    have h := hind.racl_inter_eq
    rw [empty_union, empty_union] at h
    rw [inter_comm, h]
  -- Transcendence of the representatives.
  have hs0 : s ∉ racl k (∅ : Set K) := fun h0 ↦ notMem_racl_singleton_of_pair
    (by rw [pair_comm]; exact hst) (racl_mono (empty_subset _) h0)
  have ht0 : t ∉ racl k (∅ : Set K) := fun h0 ↦ notMem_racl_singleton_of_pair hst
    (racl_mono (empty_subset _) h0)
  have hu0 : u ∉ racl k (∅ : Set K) := fun h0 ↦ notMem_racl_singleton_of_pair hsu
    (racl_mono (empty_subset _) h0)
  have hs1 : erk k ∅ ({s} : Set K) = 1 := erk_singleton_of_notMem hs0
  have ht1 : erk k ∅ ({t} : Set K) = 1 := erk_singleton_of_notMem ht0
  have hu1 : erk k ∅ ({u} : Set K) = 1 := erk_singleton_of_notMem hu0
  have htG : t ∉ racl k (slEntries g) := fun h0 ↦ ht0 (hinGH ⟨h0, ht⟩)
  have hsH : s ∉ racl k (slEntries h) := fun h0 ↦ hs0 (hinGH ⟨hs, h0⟩)
  have hsP : s ∉ racl k (slEntries (h * g)) := fun h0 ↦ hs0 (hinGP ⟨hs, h0⟩)
  -- Membership consequences of the dependent triple.
  have hmem3 : ∀ {x y z : K}, erk k ∅ ({x, y} : Set K) = 2 →
      erk k ∅ ({x, y} ∪ {z} : Set K) = 2 → z ∈ racl k ({x, y} : Set K) := by
    intro x y z hxy hxyz
    have h := erk_pair_base_eq (a := 2) (b := 0) hxy (by rw [hxyz]; rfl)
    exact (erk_singleton_eq_zero_iff k).1 h
  have huE : u ∈ racl k ({s, t} : Set K) := hmem3 hst (by
    rw [insert_union, singleton_union]
    exact hstu)
  have htSU : t ∈ racl k ({s, u} : Set K) := hmem3 hsu (by
    rw [insert_union, singleton_union, pair_comm u t]
    exact hstu)
  -- Ranks over `E` and over the single representatives.
  have h3 : ∀ {X : Set K} {x : K}, erk k ∅ X = 2 → x ∉ racl k X →
      erk k ∅ (X ∪ {x}) = ((2 + 1 : ℕ) : ℕ∞) := by
    intro X x hX hx
    rw [erk_union_eq k ∅ X {x}, empty_union, hX, erk_singleton_of_notMem hx]
    norm_num
  have hpairB : ∀ {X : Set K} {a b : K}, b ∈ racl k (X ∪ {a}) →
      racl k ({a, b} ∪ X) = racl k (X ∪ {a}) := by
    intro X a b hb
    refine le_antisymm (racl_le_of_subset_racl (union_subset ?_
      fun z hz ↦ subset_racl k _ (Or.inl hz))) (racl_le_of_subset_racl (union_subset
      (fun z hz ↦ subset_racl k _ (Or.inr hz)) ?_))
    · rintro z (rfl | rfl)
      · exact subset_racl k _ (Or.inr rfl)
      · exact hb
    · rintro z rfl
      exact subset_racl k _ (Or.inl (Or.inl rfl))
  have hsingle : ∀ {X : Set K} {x : K}, erk k ∅ X = 2 → erk k ∅ ({x} : Set K) = 1 →
      x ∈ racl k X → erk k {x} X = 1 := by
    intro X x hX hx hxX
    refine erk_pair_base_eq (a := 1) (b := 1) hx ?_
    rw [union_comm, erk_union_eq_of_subset_racl k (by
      rintro z rfl
      rwa [empty_union]), hX]
    rfl
  have hcG : racl k ({s, t} ∪ slEntries g) = racl k (slEntries g ∪ {t}) := by
    rw [pair_comm]
    exact hpairB (racl_mono subset_union_left hs)
  have hcH : racl k ({s, t} ∪ slEntries h) = racl k (slEntries h ∪ {s}) :=
    hpairB (racl_mono subset_union_left ht)
  have htPs : t ∈ racl k (slEntries (h * g) ∪ {s}) := by
    refine racl_le_of_subset_racl ?_ htSU
    rintro z (rfl | rfl)
    · exact subset_racl k _ (Or.inr rfl)
    · exact racl_mono subset_union_left hu
  have hcP : racl k ({s, t} ∪ slEntries (h * g)) = racl k (slEntries (h * g) ∪ {s}) :=
    hpairB htPs
  refine ⟨hG2, ?_, ?_, ?_, ?_, huE, hsingle hG2 hs1 hs, hsingle hH2 ht1 ht,
    hsingle hP2 hu1 hu⟩
  · exact erk_pair_base_eq (a := 2) (b := 1) hst (by rw [erk_eq_of_racl_eq hcG]; exact h3 hG2 htG)
  · exact erk_pair_base_eq (a := 2) (b := 1) hst (by rw [erk_eq_of_racl_eq hcH]; exact h3 hH2 hsH)
  · refine erk_pair_base_eq (a := 2) (b := 2) hst ?_
    rw [union_comm, erk_union_eq_of_subset_racl k (by
      rintro z (rfl | rfl)
      · rw [empty_union]
        exact racl_mono subset_union_left hs
      · rw [empty_union]
        exact racl_mono subset_union_right ht), hgh]
    rfl
  · exact erk_pair_base_eq (a := 2) (b := 1) hst (by rw [erk_eq_of_racl_eq hcP]; exact h3 hP2 hsP)


/-! ### Independent copies over `E` -/

/-- **The independent-copy claim.** Let `F ⊆ E`, and let `X, Y` be finite of rank one over both
`F` and `E`, with `Y` independent from `X` over `E`. Then `X` and `Y` are independent over `F`,
and their join is independent from `E` over `F`. -/
private theorem indep_copy_claim {k K : Type*} [Field k] [Field K] [Algebra k K]
    {E F X Y : Set K} (hFE : F ⊆ E) (hX : X.Finite) (hY : Y.Finite)
    (hXF : erk k F X = 1) (hXE : erk k E X = 1) (hYF : erk k F Y = 1) (hYE : erk k E Y = 1)
    (hind : IndepOver k E Y X) :
    (racl k (F ∪ X) : Set K) ∩ racl k (F ∪ Y) ⊆ racl k F ∧
      (racl k (F ∪ (X ∪ Y)) : Set K) ∩ racl k (F ∪ E) ⊆ racl k F := by
  have hXYE : erk k E (X ∪ Y) = 2 := by
    rw [erk_union_eq, hXE, hind.erk_eq subset_rfl hY, hYE]
    norm_num
  have hXYF : erk k F (X ∪ Y) = 2 := by
    refine le_antisymm ((erk_union_le k F X Y).trans_eq (by rw [hXF, hYF]; norm_num)) ?_
    rw [← hXYE]
    exact erk_base_mono k hFE _
  refine ⟨?_, ?_⟩
  · have hYX : erk k (F ∪ Y) X = 1 := by
      have h := erk_union_eq k F Y X
      rw [union_comm, hXYF, hYF] at h
      have h' := enat_eq_sub_of_add_eq (a := 1) (c := 2) (by exact_mod_cast h.symm)
      rw [h']
      norm_num
    have hi : IndepOver k F X Y := indepOver_of_erk_eq hX (by rw [hYX, hXF])
    rw [hi.racl_inter_eq]
  · have hi : IndepOver k F (X ∪ Y) E := indepOver_of_erk_eq (hX.union hY)
      (by rw [union_eq_right.2 hFE, hXYE, hXYF])
    rw [hi.racl_inter_eq]

/-! ### The point action of upper triangular matrices -/

/-- The point action `z ↦ m₀₀² z + m₀₀ m₀₁` of an upper triangular matrix. -/
private def slAct {K : Type*} [Field K] (m : SpecialLinearGroup (Fin 2) K) (z : K) : K :=
  m 0 0 ^ 2 * z + m 0 0 * m 0 1

private theorem slAct_mul {K : Type*} [Field K] (m₁ : SpecialLinearGroup (Fin 2) K)
    {m₂ : SpecialLinearGroup (Fin 2) K} (h₂ : m₂ 1 0 = 0) (z : K) :
    slAct (m₁ * m₂) z = slAct m₁ (slAct m₂ z) := by
  have hd : m₂ 0 0 * m₂ 1 1 = 1 := by
    have h := m₂.det_coe
    rw [Matrix.det_fin_two, h₂, mul_zero, sub_zero] at h
    exact h
  simp only [slAct, sl_mul_apply, h₂, mul_zero, add_zero]
  linear_combination (m₁ 0 0 * m₁ 0 1) * hd

private theorem slAct_one {K : Type*} [Field K] (z : K) :
    slAct (1 : SpecialLinearGroup (Fin 2) K) z = z := by
  simp [slAct]

private theorem inv_apply_one_zero {K : Type*} [Field K] {m : SpecialLinearGroup (Fin 2) K}
    (hm : m 1 0 = 0) : m⁻¹ 1 0 = 0 := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  simp [hm]

private theorem slAct_inv_slAct {K : Type*} [Field K] {m : SpecialLinearGroup (Fin 2) K}
    (hm : m 1 0 = 0) (z : K) : slAct m⁻¹ (slAct m z) = z := by
  rw [← slAct_mul m⁻¹ hm, inv_mul_cancel, slAct_one]

private theorem slAct_slAct_inv {K : Type*} [Field K] {m : SpecialLinearGroup (Fin 2) K}
    (hm : m 1 0 = 0) (z : K) : slAct m (slAct m⁻¹ z) = z := by
  rw [← slAct_mul m (inv_apply_one_zero hm), mul_inv_cancel, slAct_one]

/-- A point action value lies in the closure of the entries and the point. -/
private theorem slAct_mem {k K : Type*} [Field k] [Field K] [Algebra k K] {S : Set K}
    (m : SpecialLinearGroup (Fin 2) K) {z : K} (hm : ∀ i j, m i j ∈ racl k S)
    (hz : z ∈ racl k S) : slAct m z ∈ racl k S :=
  add_mem (mul_mem (pow_mem (hm 0 0) 2) hz) (mul_mem (hm 0 0) (hm 0 1))

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-! ### The multiplier identification -/

private theorem sl_inv_apply {K : Type*} [Field K] (m : SpecialLinearGroup (Fin 2) K) :
    m⁻¹ 0 0 = m 1 1 ∧ m⁻¹ 0 1 = -m 0 1 ∧ m⁻¹ 1 0 = -m 1 0 ∧ m⁻¹ 1 1 = m 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [SpecialLinearGroup.SL2_inv_expl] <;> rfl

/-- Two members of a rank-two pair have independent closures. -/
private theorem racl_inter_of_pair {k K : Type*} [Field k] [Field K] [Algebra k K]
    {x y : K} (h : erk k ∅ ({x, y} : Set K) = 2) :
    (racl k ({x} : Set K) : Set K) ∩ racl k ({y} : Set K) ⊆ racl k (∅ : Set K) := by
  have hy : y ∉ racl k ({x} : Set K) := notMem_racl_singleton_of_pair h
  have hy0 : y ∉ racl k (∅ : Set K) := fun h0 ↦ hy (racl_mono (empty_subset _) h0)
  have hind : IndepOver k ∅ ({y} : Set K) ({x} : Set K) := indepOver_of_erk_eq (toFinite _)
    (by rw [empty_union, erk_singleton_of_notMem hy, erk_singleton_of_notMem hy0])
  have hi := hind.racl_inter_eq
  rw [empty_union, empty_union] at hi
  rw [inter_comm, hi]

/-- A set independent from another over `E`, of rank one, is not contained in their join. -/
private theorem false_of_indep_of_subset {k K : Type*} [Field k] [Field K] [Algebra k K]
    {E X Y : Set K} (hind : IndepOver k E Y X) (hY : erk k E Y = 1)
    (hsub : Y ⊆ racl k (E ∪ X)) : False := by
  have hi := hind.racl_inter_eq
  have hYE : Y ⊆ racl k E := fun y hy ↦ hi ▸ ⟨subset_racl k _ (Or.inr hy), hsub hy⟩
  have h0 : erk k E Y = 0 := (erk_eq_zero_iff k).2 hYE
  rw [hY] at h0
  exact one_ne_zero h0

/-- An independent copy of a matrix over a small algebraically closed field `E`: it lies on the
same `E`-locus and keeps its ranks over every subset of `E`. -/
private theorem exists_indep_copy {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed K] [UniversalDomain k K] {E : IntermediateField k K} [IsAlgClosed ↥E]
    (hE : IsSmall k (E : Set K)) (x : SpecialLinearGroup (Fin 2) K) :
    ∃ x' : SpecialLinearGroup (Fin 2) K,
      IndepOver k (E : Set K) (slEntries x') (slEntries x) ∧
      idealOf (↥E) (slTuple x') = idealOf (↥E) (slTuple x) ∧
      ∀ F : Set K, F ⊆ E → erk k F (slEntries x') = erk k F (slEntries x) := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_indepOver (M := E) hE (slTuple x)
    (IsSmall.of_finite (finite_range (slTuple x)))
  refine ⟨SpecialLinearGroup.map σ.toRingHom x, hσ, idealOf_comp_algHom (↥E) σ.toAlgHom _,
    fun F hFE ↦ ?_⟩
  have hfix : (σ.restrictScalars k) '' F = F := EqOn.image_eq_self fun z hz ↦
    σ.commutes ⟨z, hFE hz⟩
  have himg : (σ.restrictScalars k) '' slEntries x =
      slEntries (SpecialLinearGroup.map σ.toRingHom x) := by
    rw [← range_comp]
    rfl
  rw [← himg]
  have h := erk_image (σ.restrictScalars k) F (slEntries x)
  rwa [hfix] at h

/-- Entries of an upper triangular matrix lie in a closure containing its first row. -/
private theorem slEntries_upper_subset {k K : Type*} [Field k] [Field K] [Algebra k K]
    {S : Set K} (m : SpecialLinearGroup (Fin 2) K) (hm : m 1 0 = 0)
    (h0 : m 0 0 ∈ racl k S) (h1 : m 0 1 ∈ racl k S) : slEntries m ⊆ racl k S := by
  have hdet : m 0 0 * m 1 1 = 1 := by
    have h := m.det_coe
    rw [Matrix.det_fin_two, hm, mul_zero, sub_zero] at h
    exact h
  have h3 : m 1 1 ∈ racl k S := by
    rw [eq_inv_of_mul_eq_one_right hdet]
    exact inv_mem h0
  have h2 : m 1 0 ∈ racl k S := by
    rw [hm]
    exact zero_mem _
  rintro _ ⟨⟨i, j⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **The multiplier identification.** Let `g, h` be independent upper triangular
matrices of rank two, and let `s, t, u` be rank-one elements algebraic over `g`, `h` and `h g`
respectively, pairwise independent for `(s, t)` and `(s, u)`, and jointly of rank two. Then the
diagonal entry of `g`, and hence its multiplier `g₀₀²`, is algebraic over `s`. -/
private theorem upper_curve_multiplier {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g h : SpecialLinearGroup (Fin 2) K) (hg10 : g 1 0 = 0) (hh10 : h 1 0 = 0)
    (hgh : erk k ∅ (slEntries g ∪ slEntries h) = 4) {s t u : K}
    (hs : s ∈ racl k (slEntries g)) (ht : t ∈ racl k (slEntries h))
    (hu : u ∈ racl k (slEntries (h * g)))
    (hst : erk k ∅ ({s, t} : Set K) = 2) (hsu : erk k ∅ ({s, u} : Set K) = 2)
    (hstu : erk k ∅ ({s, t, u} : Set K) = 2) :
    g 0 0 ∈ racl k ({s} : Set K) := by
  obtain ⟨hG2, hEg, hEh, hEgh, hEp, huE, hsg, hth, hup⟩ :=
    upper_curve_ranks g h hg10 hh10 hgh hs ht hu hst hsu hstu
  have hp10 : (h * g) 1 0 = 0 := by
    rw [sl_mul_apply, hh10, hg10, zero_mul, mul_zero, add_zero]
  -- The base `E = acl(s, t)`.
  obtain ⟨E, hEdef⟩ : ∃ E : IntermediateField k K, E = racl k ({s, t} : Set K) := ⟨_, rfl⟩
  have hEs : IsSmall k (E : Set K) := hEdef ▸ (IsSmall.of_finite (toFinite _)).racl
  have : IsAlgClosed ↥E := hEdef ▸ isAlgClosed_racl _
  have : UniversalDomain ↥E K := universalDomain_of_isSmall E hEs
  have hEk : ∀ X : Set K, erk k (E : Set K) X = erk k ({s, t} : Set K) X := fun X ↦ by
    rw [hEdef]
    exact erk_racl_base k _ X
  have hEE : ∀ X : Set K, erk (↥E) ∅ X = erk k ({s, t} : Set K) X := fun X ↦
    (erk_base_empty E X).trans (hEk X)
  have hsE : ({s} : Set K) ⊆ E := by
    rintro z rfl
    rw [hEdef]
    exact subset_racl k _ (Or.inl rfl)
  have htE : ({t} : Set K) ⊆ E := by
    rintro z rfl
    rw [hEdef]
    exact subset_racl k _ (Or.inr rfl)
  have huEs : ({u} : Set K) ⊆ E := by
    rintro z rfl
    rw [hEdef]
    exact huE
  have hsubE : ∀ {F : Set K}, F ⊆ E → racl k F ≤ E := fun hF ↦ by
    rw [hEdef]
    exact racl_le_of_subset_racl (hF.trans (by rw [hEdef]))
  -- The actual subgroup locus and both cosets over `E`.
  obtain ⟨n, hn10, hn1, H1, H2, hR, hL⟩ := exists_upper_curve_cosets (k := ↥E) g h hg10
    ((hEE _).trans hEg) ((hEE _).trans hEh) ((hEE _).trans hEgh) ((hEE _).trans hEp)
  have hdich := upper_locus_unipotent_or_torus (k := ↥E) n hn10 hn1 H1 fun d hd _ m ↦ H2 d hd m
  -- Independent copies.
  obtain ⟨g₂, hg₂i, hg₂I, hg₂r⟩ := exists_indep_copy hEs g
  obtain ⟨h₂, hh₂i, hh₂I, hh₂r⟩ := exists_indep_copy hEs h
  obtain ⟨p₂, hp₂i, hp₂I, hp₂r⟩ := exists_indep_copy hEs (h * g)
  have hEset : (E : Set K) ⊆ E := subset_rfl
  have cg := indep_copy_claim (k := k) hsE (finite_range _) (finite_range _) hsg
    ((hEk _).trans hEg) ((hg₂r _ hsE).trans hsg) ((hg₂r _ hEset).trans ((hEk _).trans hEg)) hg₂i
  have ch := indep_copy_claim (k := k) htE (finite_range _) (finite_range _) hth
    ((hEk _).trans hEh) ((hh₂r _ htE).trans hth) ((hh₂r _ hEset).trans ((hEk _).trans hEh)) hh₂i
  have cp := indep_copy_claim (k := k) huEs (finite_range _) (finite_range _) hup
    ((hEk _).trans hEp) ((hp₂r _ huEs).trans hup) ((hp₂r _ hEset).trans ((hEk _).trans hEp))
    hp₂i
  have hlocus : ∀ {x x' : SpecialLinearGroup (Fin 2) K},
      idealOf (↥E) (slTuple x') = idealOf (↥E) (slTuple x) →
      InLocus (k := ↥E) (slTuple x) (slTuple x') := fun hI ↦
    (inLocus_iff_idealOf_le _ _).2 hI.ge
  have hupper : ∀ {x x' : SpecialLinearGroup (Fin 2) K}, x 1 0 = 0 →
      idealOf (↥E) (slTuple x') = idealOf (↥E) (slTuple x) → x' 1 0 = 0 := by
    intro x x' hx hI
    have he := aeval_eq_zero_of_inLocus_base (hlocus hI) (P := MvPolynomial.X (1, 0)) (by
      rw [MvPolynomial.aeval_X]
      exact hx)
    rwa [MvPolynomial.aeval_X] at he
  have hg₂10 : g₂ 1 0 = 0 := hupper hg10 hg₂I
  have hh₂10 : h₂ 1 0 = 0 := hupper hh10 hh₂I
  have hp₂10 : p₂ 1 0 = 0 := hupper hp10 hp₂I
  have hdetg : g 0 0 * g 1 1 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero] at h
    exact h
  rcases hdich with hU | ⟨c, hT⟩
  · -- The unipotent case: the diagonal entry is constant on the locus of `g`.
    have hd := hU _ ((hR g₂).1 (hlocus hg₂I))
    rw [sl_mul_apply, (sl_inv_apply g).1, (sl_inv_apply g).2.2.1, hg10, neg_zero, mul_zero,
      add_zero] at hd
    have hgg : g₂ 0 0 = g 0 0 := by
      rw [eq_inv_of_mul_eq_one_left hd, eq_inv_of_mul_eq_one_left hdetg]
    refine cg.1 ⟨subset_racl k _ (Or.inr ⟨(0, 0), rfl⟩), ?_⟩
    rw [← hgg]
    exact subset_racl k _ (Or.inr ⟨(0, 0), rfl⟩)
  · exfalso
    obtain ⟨cK, hcK⟩ : ∃ cK : K, cK = algebraMap (↥E) K c := ⟨_, rfl⟩
    have hcKE : cK ∈ E := hcK ▸ c.2
    have hT' : ∀ d, InLocus (k := ↥E) (slTuple n) (slTuple d) →
        d 0 1 * d 0 0 = cK * (d 0 0 ^ 2 - 1) := fun d hd ↦ hcK ▸ hT d hd
    have hTfix : ∀ d, InLocus (k := ↥E) (slTuple n) (slTuple d) → slAct d (-cK) = -cK :=
      fun d hd ↦ by
        have h := hT' d hd
        unfold slAct
        linear_combination h
    -- Points of the locus of a matrix are upper triangular.
    have hupp : ∀ {x m : SpecialLinearGroup (Fin 2) K}, x 1 0 = 0 →
        InLocus (k := ↥E) (slTuple x) (slTuple m) → m 1 0 = 0 := by
      intro x m hx hm
      have he := aeval_eq_zero_of_inLocus_base hm (P := MvPolynomial.X (1, 0)) (by
        rw [MvPolynomial.aeval_X]
        exact hx)
      rwa [MvPolynomial.aeval_X] at he
    -- A torus point that is a difference of independent copies has `d₀₀² ≠ 1`.
    have hsq : ∀ {X Y : Set K} {d : SpecialLinearGroup (Fin 2) K},
        InLocus (k := ↥E) (slTuple n) (slTuple d) → d 1 0 = 0 →
        IndepOver k (E : Set K) Y X → erk k (E : Set K) Y = 1 →
        ((∀ i j, d i j ∈ racl k ((E : Set K) ∪ X)) → Y ⊆ racl k ((E : Set K) ∪ X)) →
        d 0 0 ^ 2 ≠ 1 := by
      intro X Y d hd hd10 hind hY hsub h1
      have hdet : d 0 0 * d 1 1 = 1 := by
        have h := d.det_coe
        rw [Matrix.det_fin_two, hd10, mul_zero, sub_zero] at h
        exact h
      have h00 : d 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      have h01 : d 0 1 = 0 := by
        have h := hT' d hd
        rw [h1, sub_self, mul_zero] at h
        exact (mul_eq_zero.1 h).resolve_right h00
      have halg : d 0 0 ∈ racl k (∅ : Set K) := by
        refine mem_racl_empty_of_isAlgebraic ?_
        by_contra hc
        exact sq_ne_one_of_transcendental hc h1
      have hd0 : ∀ z ∈ racl k (∅ : Set K), z ∈ racl k ((E : Set K) ∪ X) :=
        fun z hz ↦ racl_mono (empty_subset _) hz
      refine false_of_indep_of_subset hind hY (hsub fun i j ↦ ?_)
      fin_cases i <;> fin_cases j
      · exact hd0 _ halg
      · change d 0 1 ∈ _
        rw [h01]
        exact zero_mem _
      · change d 1 0 ∈ _
        rw [hd10]
        exact zero_mem _
      · change d 1 1 ∈ _
        rw [eq_inv_of_mul_eq_one_right hdet]
        exact hd0 _ (inv_mem halg)
    -- The torus constant from a difference point.
    have hconst : ∀ {d : SpecialLinearGroup (Fin 2) K} {S : Set K},
        InLocus (k := ↥E) (slTuple n) (slTuple d) → d 0 0 ^ 2 ≠ 1 →
        (∀ i j, d i j ∈ racl k S) → cK ∈ racl k S := by
      intro d S hd h1 hS
      have hl : d 0 0 ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h1
      have h := hT' d hd
      rw [show cK = d 0 1 * d 0 0 / (d 0 0 ^ 2 - 1) from (eq_div_iff hl).2 h.symm]
      exact div_mem (mul_mem (hS 0 1) (hS 0 0)) (sub_mem (pow_mem (hS 0 0) 2) (one_mem _))
    have hentries : ∀ (x : SpecialLinearGroup (Fin 2) K) {S : Set K}, slEntries x ⊆ S →
        ∀ i j, x i j ∈ racl k S := fun x S hx i j ↦ subset_racl k _ (hx ⟨(i, j), rfl⟩)
    -- the constant lies in the base.
    have hcs : cK ∈ racl k ({s} : Set K) := by
      have hd := (hR g₂).1 (hlocus hg₂I)
      have hd10 : (g₂ * g⁻¹) 1 0 = 0 := by
        rw [sl_mul_apply, hg₂10, (sl_inv_apply g).2.2.1, hg10, neg_zero, zero_mul, mul_zero,
          add_zero]
      have hmemd : ∀ i j, (g₂ * g⁻¹) i j ∈ racl k (slEntries g ∪ slEntries g₂) :=
        sl_mul_entries_mem _ (hentries g₂ subset_union_right)
          (sl_inv_entries_mem _ (hentries g subset_union_left))
      have h1 : (g₂ * g⁻¹) 0 0 ^ 2 ≠ 1 := hsq hd hd10 hg₂i
        ((hg₂r _ hEset).trans ((hEk _).trans hEg)) fun hdE ↦ by
          rintro _ ⟨⟨i, j⟩, rfl⟩
          have h := sl_mul_entries_mem _ (A := g₂ * g⁻¹) (B := g) hdE
            (hentries g subset_union_right) i j
          rwa [inv_mul_cancel_right] at h
      refine cg.2 ⟨racl_mono subset_union_right (hconst hd h1 hmemd), ?_⟩
      exact subset_racl k _ (Or.inr hcKE)
    have hct : cK ∈ racl k ({t} : Set K) := by
      have hd := (hL h₂).1 (hlocus hh₂I)
      have hd10 : (h⁻¹ * h₂) 1 0 = 0 := by
        rw [sl_mul_apply, (sl_inv_apply h).2.2.1, hh10, hh₂10, neg_zero, zero_mul, mul_zero,
          add_zero]
      have hmemd : ∀ i j, (h⁻¹ * h₂) i j ∈ racl k (slEntries h ∪ slEntries h₂) :=
        sl_mul_entries_mem _ (sl_inv_entries_mem _ (hentries h subset_union_left))
          (hentries h₂ subset_union_right)
      have h1 : (h⁻¹ * h₂) 0 0 ^ 2 ≠ 1 := hsq hd hd10 hh₂i
        ((hh₂r _ hEset).trans ((hEk _).trans hEh)) fun hdE ↦ by
          rintro _ ⟨⟨i, j⟩, rfl⟩
          have h' := sl_mul_entries_mem _ (A := h) (B := h⁻¹ * h₂)
            (hentries h subset_union_right) hdE i j
          rwa [mul_inv_cancel_left] at h'
      refine ch.2 ⟨racl_mono subset_union_right (hconst hd h1 hmemd), ?_⟩
      exact subset_racl k _ (Or.inr hcKE)
    have hc0 : cK ∈ racl k (∅ : Set K) := racl_inter_of_pair hst ⟨hcs, hct⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ : K, μ = -cK := ⟨_, rfl⟩
    have hμ0 : μ ∈ racl k (∅ : Set K) := hμdef ▸ neg_mem hc0
    have hμS : ∀ S : Set K, μ ∈ racl k S := fun S ↦ racl_mono (empty_subset _) hμ0
    -- `μ₁ = g⁻¹·μ` is constant on the locus of `g`.
    obtain ⟨μ₁, hμ₁def⟩ : ∃ x : K, x = slAct g⁻¹ μ := ⟨_, rfl⟩
    have hfixg : ∀ m, InLocus (k := ↥E) (slTuple g) (slTuple m) → slAct m μ₁ = μ :=
      fun m hm ↦ by
        have hx := hTfix _ ((hR m).1 hm)
        rwa [slAct_mul m (inv_apply_one_zero hg10), ← hμdef, ← hμ₁def] at hx
    have hμ₁ : μ₁ ∈ racl k ({s} : Set K) := by
      have h2 : μ₁ = slAct g₂⁻¹ μ := by
        rw [← hfixg g₂ (hlocus hg₂I), slAct_inv_slAct hg₂10]
      refine cg.1 ⟨?_, ?_⟩
      · rw [hμ₁def]
        exact slAct_mem _ (sl_inv_entries_mem _ (hentries g subset_union_right)) (hμS _)
      · rw [h2]
        exact slAct_mem _ (sl_inv_entries_mem _ (hentries g₂ subset_union_right)) (hμS _)
    -- `μ₂ = h·μ` is constant on the locus of `h`.
    obtain ⟨μ₂, hμ₂def⟩ : ∃ x : K, x = slAct h μ := ⟨_, rfl⟩
    have hfixh : ∀ m, InLocus (k := ↥E) (slTuple h) (slTuple m) → slAct m μ = μ₂ :=
      fun m hm ↦ by
        have hx := hTfix _ ((hL m).1 hm)
        rw [slAct_mul h⁻¹ (hupp hh10 hm), ← hμdef] at hx
        calc slAct m μ = slAct h (slAct h⁻¹ (slAct m μ)) := (slAct_slAct_inv hh10 _).symm
          _ = μ₂ := by rw [hx, hμ₂def]
    have hμ₂ : μ₂ ∈ racl k ({t} : Set K) := by
      refine ch.1 ⟨?_, ?_⟩
      · rw [hμ₂def]
        exact slAct_mem _ (hentries h subset_union_right) (hμS _)
      · rw [← hfixh h₂ (hlocus hh₂I)]
        exact slAct_mem _ (hentries h₂ subset_union_right) (hμS _)
    -- the product point equation transfers to the copy of `h g`.
    have hμ₁E : μ₁ ∈ E := hsubE hsE hμ₁
    have hμ₂E : μ₂ ∈ E := hsubE htE hμ₂
    have hpeq : slAct (h * g) μ₁ = μ₂ := by
      rw [slAct_mul h hg10, hμ₁def, slAct_slAct_inv hg10, hμ₂def]
    have hp₂eq : slAct p₂ μ₁ = μ₂ := by
      have he := aeval_eq_zero_of_inLocus_base (hlocus hp₂I)
        (P := MvPolynomial.X (0, 0) ^ 2 * MvPolynomial.C ⟨_, hμ₁E⟩ +
          MvPolynomial.X (0, 0) * MvPolynomial.X (0, 1) - MvPolynomial.C ⟨_, hμ₂E⟩) (by
          simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X,
            MvPolynomial.aeval_C]
          change slAct (h * g) μ₁ - μ₂ = 0
          rw [hpeq, sub_self])
      simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C] at he
      change slAct p₂ μ₁ - μ₂ = 0 at he
      exact sub_eq_zero.1 he
    have hp00 : (h * g) 0 0 ∉ racl k (E : Set K) := by
      intro h0
      have hdet : (h * g) 0 0 * (h * g) 1 1 = 1 := by
        have h' := (h * g).det_coe
        rw [Matrix.det_fin_two, hp10, mul_zero, sub_zero] at h'
        exact h'
      have hne : (h * g) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      have h01 : (h * g) 0 1 ∈ racl k (E : Set K) := by
        have hx : (h * g) 0 1 = (μ₂ - (h * g) 0 0 ^ 2 * μ₁) / (h * g) 0 0 := by
          rw [eq_div_iff hne, ← hpeq]
          unfold slAct
          ring
        rw [hx]
        exact div_mem (sub_mem (subset_racl k _ hμ₂E) (mul_mem (pow_mem h0 2)
          (subset_racl k _ hμ₁E))) h0
      have hz := (erk_eq_zero_iff k).2 (slEntries_upper_subset (h * g) hp10 h0 h01)
      rw [hEk, hEp] at hz
      exact one_ne_zero hz
    have hpp : (h * g) 0 0 ^ 2 ≠ p₂ 0 0 ^ 2 := by
      intro hsq2
      have hp₂0 : p₂ 0 0 ∈ racl k ((E : Set K) ∪ slEntries p₂) :=
        subset_racl k _ (Or.inr ⟨(0, 0), rfl⟩)
      have hmem : (h * g) 0 0 ∈ racl k ((E : Set K) ∪ slEntries p₂) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq2 with h' | h'
        · rw [h']
          exact hp₂0
        · rw [h']
          exact neg_mem hp₂0
      have hmem2 : (h * g) 0 0 ∈ (racl k ((E : Set K) ∪ slEntries p₂) : Set K) ∩
          racl k ((E : Set K) ∪ slEntries (h * g)) :=
        ⟨hmem, subset_racl k _ (Or.inr ⟨(0, 0), rfl⟩)⟩
      rw [hp₂i.racl_inter_eq] at hmem2
      exact hp00 hmem2
    have hden : (h * g) 0 0 ^ 2 - p₂ 0 0 ^ 2 ≠ 0 := sub_ne_zero.2 hpp
    have hx : μ₁ = (p₂ 0 0 * p₂ 0 1 - (h * g) 0 0 * (h * g) 0 1) /
        ((h * g) 0 0 ^ 2 - p₂ 0 0 ^ 2) := by
      rw [eq_div_iff hden]
      unfold slAct at hpeq hp₂eq
      linear_combination hpeq - hp₂eq
    have hμ₁u : μ₁ ∈ racl k ({u} : Set K) := by
      refine cp.2 ⟨?_, subset_racl k _ (Or.inr hμ₁E)⟩
      rw [hx]
      have hP := hentries (h * g) (S := {u} ∪ (slEntries (h * g) ∪ slEntries p₂))
        (subset_union_left.trans subset_union_right)
      have hP₂ := hentries p₂ (S := {u} ∪ (slEntries (h * g) ∪ slEntries p₂))
        (subset_union_right.trans subset_union_right)
      exact div_mem (sub_mem (mul_mem (hP₂ 0 0) (hP₂ 0 1)) (mul_mem (hP 0 0) (hP 0 1)))
        (sub_mem (pow_mem (hP 0 0) 2) (pow_mem (hP₂ 0 0) 2))
    -- the fixed point data are algebraic over the base, so `g` has rank at most one.
    have hμ₁0 : μ₁ ∈ racl k (∅ : Set K) := racl_inter_of_pair hsu ⟨hμ₁, hμ₁u⟩
    have hgfix : slAct g μ₁ = μ := by rw [hμ₁def, slAct_slAct_inv hg10]
    have hg00 : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetg
    have hgS : g 0 0 ∈ racl k ({g 0 0} : Set K) := subset_racl k _ rfl
    have h01 : g 0 1 ∈ racl k ({g 0 0} : Set K) := by
      have hxg : g 0 1 = (μ - g 0 0 ^ 2 * μ₁) / g 0 0 := by
        rw [eq_div_iff hg00, ← hgfix]
        unfold slAct
        ring
      rw [hxg]
      exact div_mem (sub_mem (hμS _) (mul_mem (pow_mem hgS 2)
        (racl_mono (empty_subset _) hμ₁0))) hgS
    have hle : erk k ∅ (slEntries g) ≤ 1 :=
      calc erk k ∅ (slEntries g) ≤ erk k ∅ (racl k ({g 0 0} : Set K) : Set K) :=
            erk_mono k ∅ (slEntries_upper_subset g hg10 hgS h01)
        _ = erk k ∅ ({g 0 0} : Set K) := by
            simpa only [empty_union] using erk_racl k (∅ : Set K) ({g 0 0} : Set K)
        _ ≤ 1 := (erk_le_encard k ∅ _).trans (by simp)
    rw [hG2] at hle
    norm_num at hle

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-! ### The three field rows -/

/-- An element of the closure of a transcendental singleton generates the same closure. -/
private theorem racl_singleton_eq_of_mem {k K : Type*} [Field k] [Field K] [Algebra k K]
    {x y : K} (hxy : x ∈ racl k ({y} : Set K)) (hx : x ∉ racl k (∅ : Set K)) :
    racl k ({x} : Set K) = racl k ({y} : Set K) := by
  have hyx : y ∈ racl k ({x} : Set K) := by
    have h := racl_exchange (S := (∅ : Set K)) (by rwa [insert_empty_eq]) hx
    rwa [insert_empty_eq] at h
  exact le_antisymm (racl_le_of_subset_racl (singleton_subset_iff.2 hxy))
    (racl_le_of_subset_racl (singleton_subset_iff.2 hyx))

/-- The diagonal entry of an upper triangular matrix of rank two is transcendental. -/
private theorem diag_notMem_of_erk_two {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m : SpecialLinearGroup (Fin 2) K) (hm : m 1 0 = 0) (h2 : erk k ∅ (slEntries m) = 2) :
    m 0 0 ∉ racl k (∅ : Set K) := by
  intro h0
  have hsub := slEntries_upper_subset (S := {m 0 1}) m hm (racl_mono (empty_subset _) h0)
    (subset_racl k _ rfl)
  have hle : erk k ∅ (slEntries m) ≤ 1 :=
    calc erk k ∅ (slEntries m) ≤ erk k ∅ (racl k ({m 0 1} : Set K) : Set K) := erk_mono k ∅ hsub
      _ = erk k ∅ ({m 0 1} : Set K) := by
          simpa only [empty_union] using erk_racl k (∅ : Set K) ({m 0 1} : Set K)
      _ ≤ 1 := (erk_le_encard k ∅ _).trans (by simp)
  rw [h2] at hle
  norm_num at hle

/-- **The diagonal rows of two upper triangular curves.** Let `g, h` be upper triangular
matrices whose eight entries have rank four, and let `s, t, u` be algebraic over the entries of
`g`, `h` and `h g` respectively, with `{s, t}`, `{s, u}` and `{s, t, u}` all of rank two.
Then `s`, `t` and `u` generate the same closures as the diagonal entries `g₀₀`, `h₀₀` and
`(h g)₀₀`. -/
theorem upper_curve_diagonal_rows {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g h : SpecialLinearGroup (Fin 2) K) (hg10 : g 1 0 = 0) (hh10 : h 1 0 = 0)
    (hgh : erk k ∅ (slEntries g ∪ slEntries h) = 4) {s t u : K}
    (hs : s ∈ racl k (slEntries g)) (ht : t ∈ racl k (slEntries h))
    (hu : u ∈ racl k (slEntries (h * g)))
    (hst : erk k ∅ ({s, t} : Set K) = 2) (hsu : erk k ∅ ({s, u} : Set K) = 2)
    (hstu : erk k ∅ ({s, t, u} : Set K) = 2) :
    racl k ({s} : Set K) = racl k ({g 0 0} : Set K) ∧
      racl k ({t} : Set K) = racl k ({h 0 0} : Set K) ∧
      racl k ({u} : Set K) = racl k ({(h * g) 0 0} : Set K) := by
  have hmult := upper_curve_multiplier g h hg10 hh10 hgh hs ht hu hst hsu hstu
  obtain ⟨hG2, -, -, -, -, huE, -, -, -⟩ :=
    upper_curve_ranks g h hg10 hh10 hgh hs ht hu hst hsu hstu
  have hp10 : (h * g) 1 0 = 0 := by
    rw [sl_mul_apply, hh10, hg10, zero_mul, mul_zero, add_zero]
  have hp00 : (h * g) 0 0 = h 0 0 * g 0 0 := by
    rw [sl_mul_apply, hg10, mul_zero, add_zero]
  obtain ⟨-, hH2⟩ := enat_eq_two_of_add (erk_slEntries_upper_le_two ∅ g hg10)
    (erk_slEntries_upper_le_two ∅ h hh10) (by rw [← hgh]; exact erk_union_le k ∅ _ _)
  have hGH : erk k (slEntries g) (slEntries h) = 2 :=
    erk_pair_base_eq (a := 2) (b := 2) hG2 (by rw [hgh]; rfl)
  have hinGH : (racl k (slEntries g) : Set K) ∩ racl k (slEntries h) ⊆ racl k (∅ : Set K) := by
    have hind : IndepOver k ∅ (slEntries h) (slEntries g) :=
      indepOver_of_erk_eq (finite_range _) (by rw [empty_union, hGH, hH2])
    have h' := hind.racl_inter_eq
    rw [empty_union, empty_union] at h'
    rw [inter_comm, h']
  have hPG : racl k (slEntries (h * g) ∪ slEntries g) = racl k (slEntries h ∪ slEntries g) :=
    racl_sl_product_union h g
  have hPG4 : erk k ∅ (slEntries (h * g) ∪ slEntries g) = 4 := by
    rw [erk_eq_of_racl_eq hPG, union_comm]
    exact hgh
  obtain ⟨hP2, -⟩ := enat_eq_two_of_add (erk_slEntries_upper_le_two ∅ (h * g) hp10)
    (erk_slEntries_upper_le_two ∅ g hg10) (by rw [← hPG4]; exact erk_union_le k ∅ _ _)
  have hg0 := diag_notMem_of_erk_two g hg10 hG2
  have hh0 := diag_notMem_of_erk_two h hh10 hH2
  have hp0 := diag_notMem_of_erk_two (h * g) hp10 hP2
  have hu0 : u ∉ racl k (∅ : Set K) := fun h0 ↦ notMem_racl_singleton_of_pair hsu
    (racl_mono (empty_subset _) h0)
  have ht0 : t ∉ racl k (∅ : Set K) := fun h0 ↦ notMem_racl_singleton_of_pair hst
    (racl_mono (empty_subset _) h0)
  have hgG : g 0 0 ∈ racl k (slEntries g) := subset_racl k _ ⟨(0, 0), rfl⟩
  have hhH : h 0 0 ∈ racl k (slEntries h) := subset_racl k _ ⟨(0, 0), rfl⟩
  have hgH : g 0 0 ∉ racl k (slEntries h) := fun h0 ↦ hg0 (hinGH ⟨hgG, h0⟩)
  -- The row `S`.
  have hS : racl k ({s} : Set K) = racl k ({g 0 0} : Set K) :=
    (racl_singleton_eq_of_mem hmult hg0).symm
  have hsg : s ∈ racl k ({g 0 0} : Set K) := hS ▸ subset_racl k _ rfl
  -- The row `U`, over the base `{(h g)₀₀}`.
  have hU : racl k ({u} : Set K) = racl k ({(h * g) 0 0} : Set K) := by
    have hC1 : erk k ∅ ({(h * g) 0 0} : Set K) = 1 := erk_singleton_of_notMem hp0
    have hp0X : (h * g) 0 0 ∈ racl k (slEntries h ∪ {g 0 0}) := by
      rw [hp00]
      exact mul_mem (racl_mono subset_union_left hhH) (subset_racl k _ (Or.inr rfl))
    have hCX : erk k ({(h * g) 0 0} : Set K) ({g 0 0} ∪ slEntries h) = 2 := by
      refine erk_pair_base_eq (a := 1) (b := 2) hC1 ?_
      have hr : racl k ({(h * g) 0 0} ∪ ({g 0 0} ∪ slEntries h)) =
          racl k (slEntries h ∪ {g 0 0}) := by
        rw [union_comm {g 0 0}]
        exact le_antisymm (racl_le_of_subset_racl (union_subset (singleton_subset_iff.2 hp0X)
          (subset_racl k _))) (racl_mono subset_union_right)
      rw [erk_eq_of_racl_eq hr, erk_union_eq k ∅ _ {g 0 0}, empty_union, hH2,
        erk_singleton_of_notMem hgH]
      norm_num
    have hCY : erk k ∅ ({(h * g) 0 0} ∪ slEntries (h * g)) = 2 := by
      rw [union_comm, erk_union_eq_of_subset_racl k (by
        rintro z rfl
        rw [empty_union]
        exact subset_racl k _ ⟨(0, 0), rfl⟩), hP2]
    have hCYX : erk k ({(h * g) 0 0} ∪ slEntries (h * g)) ({g 0 0} ∪ slEntries h) = 2 := by
      refine erk_pair_base_eq (a := 2) (b := 2) hCY ?_
      have hr : racl k (({(h * g) 0 0} ∪ slEntries (h * g)) ∪ ({g 0 0} ∪ slEntries h)) =
          racl k (slEntries g ∪ slEntries h) := by
        refine le_antisymm (racl_le_of_subset_racl ?_) (racl_le_of_subset_racl ?_)
        · have hPsub : slEntries (h * g) ⊆ racl k (slEntries g ∪ slEntries h) := by
            rintro _ ⟨⟨i, j⟩, rfl⟩
            exact sl_mul_entries_mem (racl k (slEntries g ∪ slEntries h))
              (fun i j ↦ subset_racl k (slEntries g ∪ slEntries h) (Or.inr ⟨(i, j), rfl⟩))
              (fun i j ↦ subset_racl k (slEntries g ∪ slEntries h) (Or.inl ⟨(i, j), rfl⟩)) i j
          refine union_subset (union_subset ?_ hPsub) (union_subset ?_ ?_)
          · exact singleton_subset_iff.2 (hPsub ⟨(0, 0), rfl⟩)
          · exact singleton_subset_iff.2 (racl_mono subset_union_left hgG)
          · exact fun z hz ↦ subset_racl k _ (Or.inr hz)
        · refine union_subset ?_ (fun z hz ↦ subset_racl k _ (Or.inr (Or.inr hz)))
          rintro _ ⟨⟨i, j⟩, rfl⟩
          have hm := sl_mul_entries_mem (racl k (({(h * g) 0 0} ∪ slEntries (h * g)) ∪
            ({g 0 0} ∪ slEntries h))) (A := h⁻¹) (B := h * g)
            (sl_inv_entries_mem _ fun i j ↦ subset_racl k _ (Or.inr (Or.inr ⟨(i, j), rfl⟩)))
            (fun i j ↦ subset_racl k _ (Or.inl (Or.inr ⟨(i, j), rfl⟩))) i j
          rwa [inv_mul_cancel_left] at hm
      rw [erk_eq_of_racl_eq hr, hgh]
      rfl
    have hind : IndepOver k ({(h * g) 0 0} : Set K) ({g 0 0} ∪ slEntries h)
        (slEntries (h * g)) :=
      indepOver_of_erk_eq ((finite_singleton _).union (finite_range _)) (by rw [hCYX, hCX])
    have hi := hind.racl_inter_eq
    have huX : u ∈ racl k ({(h * g) 0 0} ∪ ({g 0 0} ∪ slEntries h)) := by
      refine racl_le_of_subset_racl ?_ huE
      rintro z (rfl | rfl)
      · have hg' : g 0 0 ∈ racl k ({(h * g) 0 0} ∪ ({g 0 0} ∪ slEntries h)) :=
          subset_racl k _ (Or.inr (Or.inl rfl))
        exact racl_le_of_subset_racl (singleton_subset_iff.2 hg') hsg
      · exact racl_mono (subset_union_right.trans subset_union_right) ht
    have huY : u ∈ racl k ({(h * g) 0 0} ∪ slEntries (h * g)) := racl_mono subset_union_right hu
    have hmem : u ∈ (racl k ({(h * g) 0 0} ∪ ({g 0 0} ∪ slEntries h)) : Set K) ∩
        racl k ({(h * g) 0 0} ∪ slEntries (h * g)) := ⟨huX, huY⟩
    rw [hi] at hmem
    exact racl_singleton_eq_of_mem hmem hu0
  -- The row `T`, over the base `{h₀₀}`.
  have hT : racl k ({t} : Set K) = racl k ({h 0 0} : Set K) := by
    have hgh0 : g 0 0 ∉ racl k ({h 0 0} : Set K) := fun h0 ↦
      hgH (racl_le_of_subset_racl (singleton_subset_iff.2 hhH) h0)
    have hCX : erk k ({h 0 0} : Set K) {g 0 0} = 1 := erk_singleton_of_notMem hgh0
    have hCYX : erk k ({h 0 0} ∪ slEntries h) {g 0 0} = 1 := erk_singleton_of_notMem
      fun h0 ↦ hgH (by
        rwa [show racl k ({h 0 0} ∪ slEntries h) = racl k (slEntries h) from
          le_antisymm (racl_le_of_subset_racl (union_subset (singleton_subset_iff.2 hhH)
            (subset_racl k _))) (racl_mono subset_union_right)] at h0)
    have hind : IndepOver k ({h 0 0} : Set K) {g 0 0} (slEntries h) :=
      indepOver_of_erk_eq (finite_singleton _) (by rw [hCYX, hCX])
    have hi := hind.racl_inter_eq
    have htSU : t ∈ racl k ({s, u} : Set K) := by
      have h' := erk_pair_base_eq (a := 2) (b := 0) hsu
        (X := {t}) (by rw [insert_union, singleton_union, pair_comm u t, hstu]; rfl)
      exact (erk_singleton_eq_zero_iff k).1 h'
    have htX : t ∈ racl k ({h 0 0} ∪ {g 0 0}) := by
      refine racl_le_of_subset_racl ?_ htSU
      rintro z (rfl | rfl)
      · have hg' : g 0 0 ∈ racl k ({h 0 0} ∪ {g 0 0}) := subset_racl k _ (Or.inr rfl)
        exact racl_le_of_subset_racl (singleton_subset_iff.2 hg') hsg
      · have hpm : (h * g) 0 0 ∈ racl k ({h 0 0} ∪ {g 0 0}) := by
          rw [hp00]
          exact mul_mem (subset_racl k _ (Or.inl rfl)) (subset_racl k _ (Or.inr rfl))
        have huP : z ∈ racl k ({(h * g) 0 0} : Set K) := hU ▸ subset_racl k _ rfl
        exact racl_le_of_subset_racl (singleton_subset_iff.2 hpm) huP
    have htY : t ∈ racl k ({h 0 0} ∪ slEntries h) := racl_mono subset_union_right ht
    have hmem : t ∈ (racl k ({h 0 0} ∪ {g 0 0}) : Set K) ∩ racl k ({h 0 0} ∪ slEntries h) :=
      ⟨htX, htY⟩
    rw [hi] at hmem
    exact racl_singleton_eq_of_mem hmem ht0
  exact ⟨hS, hT, hU⟩

end

end GroupConfig
