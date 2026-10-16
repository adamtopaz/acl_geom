/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Constructible.SLClassification
import GroupConfig.Germ.Variety

/-!
# Curves of upper triangular matrices in SL₂

This module analyses one-dimensional loci of matrices in `SL₂(K)` over an algebraically closed
universal-domain base `k`. Points are compared through their entry tuples `slTuple`.

* `exists_upper_curve_cosets`: let `g` be upper triangular and `h` arbitrary, with entries of
  rank one, jointly of rank two, and with `h g` of rank one. Then one upper triangular `n` of
  rank one has a locus that contains `1` and is stable under right multiplication by its points.
  The locus of `g` is the right coset of it through `g`, and the locus of `h` is the left coset
  through `h`.
* `upper_locus_unipotent_or_torus`: on such a stable upper triangular locus, either every point
  has diagonal entry `1`, or one base constant `c` satisfies `d₀₁ d₀₀ = c (d₀₀² - 1)` at every
  point `d`.

The consumer is the multiplier identification `GroupConfig.upper_curve_diagonal_rows` in
`GroupConfig.Constructible.SLAffineMultiplier`. It gives the diagonal rows of the initial affine
chart of the actual rank-two Hrushovski–Weil action (#21, #27). This supplies auxiliary
function-field facts for `lem:affine-action` in `sources/blueprint.tex`; that statement itself
remains an obligation.

**Status:** both statements are proved; the supporting lemmas are private.
-/

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-- Replacing one factor by its difference with the other preserves their joint closure. -/
private theorem racl_sl_difference_union {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A B : SpecialLinearGroup (Fin 2) K) :
    racl k (slEntries (A * B⁻¹) ∪ slEntries B) = racl k (slEntries A ∪ slEntries B) := by
  apply le_antisymm
  · apply racl_le_of_subset_racl
    refine union_subset ?_ (subset_union_right.trans (subset_racl k _))
    let F := racl k (slEntries A ∪ slEntries B)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact sl_mul_entries_mem F
      (fun i j ↦ subset_racl k _ (Or.inl ⟨(i, j), rfl⟩))
      (sl_inv_entries_mem F (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩))) i j
  · apply racl_le_of_subset_racl
    refine union_subset ?_ (subset_union_right.trans (subset_racl k _))
    let F := racl k (slEntries (A * B⁻¹) ∪ slEntries B)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hx := sl_mul_entries_mem F (A := A * B⁻¹) (B := B)
      (fun i j ↦ subset_racl k _ (Or.inl ⟨(i, j), rfl⟩))
      (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)) i j
    change A i j ∈ F
    rw [mul_assoc, inv_mul_cancel, mul_one] at hx
    exact hx

/-- The analogous recovery from a left difference. -/
private theorem racl_sl_left_difference_union {k K : Type*}
    [Field k] [Field K] [Algebra k K] (A B : SpecialLinearGroup (Fin 2) K) :
    racl k (slEntries (A⁻¹ * B) ∪ slEntries A) = racl k (slEntries A ∪ slEntries B) := by
  apply le_antisymm
  · apply racl_le_of_subset_racl
    refine union_subset ?_ (subset_union_left.trans (subset_racl k _))
    let F := racl k (slEntries A ∪ slEntries B)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact sl_mul_entries_mem F
      (sl_inv_entries_mem F (fun i j ↦ subset_racl k _ (Or.inl ⟨(i, j), rfl⟩)))
      (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)) i j
  · apply racl_le_of_subset_racl
    refine union_subset (subset_union_right.trans (subset_racl k _)) ?_
    let F := racl k (slEntries (A⁻¹ * B) ∪ slEntries A)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hx := sl_mul_entries_mem F (A := A) (B := A⁻¹ * B)
      (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩))
      (fun i j ↦ subset_racl k _ (Or.inl ⟨(i, j), rfl⟩)) i j
    change B i j ∈ F
    rw [← mul_assoc, mul_inv_cancel, one_mul] at hx
    exact hx

/-- The two-by-two, rank-three fibre diagram forces a rank-one actual difference.
This is the dimension calculation in the multiplier-field/coset proof (#27, R6 Step 3).
The following existence consumer must choose this fibre diagram internally. -/
private theorem sl_difference_rank_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    (g g' h h' : SpecialLinearGroup (Fin 2) K) (hprod : h * g = h' * g')
    (hg' : erk k ∅ (slEntries g') = 1)
    (hgg' : erk k ∅ (slEntries g ∪ slEntries g') = 2)
    (hhh' : erk k ∅ (slEntries h ∪ slEntries h') = 2)
    (hall : erk k ∅ ((slEntries g ∪ slEntries g') ∪ (slEntries h ∪ slEntries h')) = 3) :
    erk k ∅ (slEntries (g * g'⁻¹)) = 1 ∧
      erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries g') = 2 ∧
      erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries h) = 2 := by
  let A := racl k (slEntries g ∪ slEntries g')
  let B := racl k (slEntries h ∪ slEntries h')
  have hn : g * g'⁻¹ = h⁻¹ * h' := by
    calc g * g'⁻¹ = h⁻¹ * (h * g) * g'⁻¹ := by group
      _ = h⁻¹ * (h' * g') * g'⁻¹ := by rw [hprod]
      _ = h⁻¹ * h' := by group
  have hA : slEntries (g * g'⁻¹) ⊆ A := by
    intro x hx
    exact (racl_sl_difference_union (k := k) g g').le (subset_racl k _ (Or.inl hx))
  have hB : slEntries (g * g'⁻¹) ⊆ B := by
    rw [hn]
    intro x hx
    exact (racl_sl_left_difference_union (k := k) h h').le
      (subset_racl k _ (Or.inl hx))
  have er (S : Set K) : erk k ∅ (racl k S : Set K) = erk k ∅ S := by
    simpa only [empty_union] using erk_racl k (∅ : Set K) S
  have hrA : erk k ∅ (A : Set K) = 2 := (er _).trans hgg'
  have hrB : erk k ∅ (B : Set K) = 2 := (er _).trans hhh'
  have hrAB : erk k ∅ ((A : Set K) ∪ (B : Set K)) = 3 := by
    have hc : racl k ((A : Set K) ∪ (B : Set K)) =
        racl k ((slEntries g ∪ slEntries g') ∪ (slEntries h ∪ slEntries h')) := by
      rw [AclGeom.racl_union_left, AclGeom.racl_union_right]
    exact (erk_eq_of_racl_eq hc).trans hall
  have hsub := erk_inter_add_erk_union_le k ∅ (A : Set K) (B : Set K)
  rw [hrA, hrB, hrAB] at hsub
  have hInt : erk k ∅ ((A : Set K) ∩ (B : Set K)) ≤ 1 := by
    apply (ENat.add_le_add_iff_right (by norm_num : (3 : ℕ∞) ≠ ⊤)).1
    convert hsub using 1; norm_num
  have hle : erk k ∅ (slEntries (g * g'⁻¹)) ≤ 1 :=
    (erk_mono k ∅ (subset_inter hA hB)).trans hInt
  have hng' : erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries g') = 2 :=
    (erk_eq_of_racl_eq (racl_sl_difference_union g g')).trans hgg'
  have hnh : erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries h) = 2 := by
    rw [hn]
    exact (erk_eq_of_racl_eq (racl_sl_left_difference_union h h')).trans hhh'
  have hge : 1 ≤ erk k ∅ (slEntries (g * g'⁻¹)) := by
    have hz := erk_union_le k ∅ (slEntries (g * g'⁻¹)) (slEntries g')
    rw [hng', hg'] at hz
    apply (ENat.add_le_add_iff_right (by norm_num : (1 : ℕ∞) ≠ ⊤)).1
    convert hz using 1; norm_num
  exact ⟨le_antisymm hle hge, hng', hnh⟩

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-- A product and its right factor generate the same closure as the two factors. -/
theorem racl_sl_product_union {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A B : SpecialLinearGroup (Fin 2) K) :
    racl k (slEntries (A * B) ∪ slEntries B) = racl k (slEntries A ∪ slEntries B) := by
  have h := racl_sl_difference_union (k := k) (A * B) B
  rw [mul_inv_cancel_right] at h
  exact h.symm

/-- Over a field containing a product, either factor determines the other algebraically. -/
private theorem racl_sl_factors_of_product_base {k K : Type*}
    [Field k] [Field K] [Algebra k K] (P A B : SpecialLinearGroup (Fin 2) K)
    (hprod : P = A * B) (hP : ∀ i j, P i j ∈ range (algebraMap k K)) :
    racl k (slEntries A) = racl k (slEntries B) := by
  have hp (S : IntermediateField k K) (i j : Fin 2) : P i j ∈ S := by
    obtain ⟨x, hx⟩ := hP i j
    rw [← hx]
    exact S.algebraMap_mem x
  apply le_antisymm
  · apply racl_le_of_subset_racl
    let S := racl k (slEntries B)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hm := sl_mul_entries_mem S (A := P) (B := B⁻¹) (hp S)
      (sl_inv_entries_mem S (fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩)) i j
    change A i j ∈ S
    rw [hprod, mul_inv_cancel_right] at hm
    exact hm
  · apply racl_le_of_subset_racl
    let S := racl k (slEntries A)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hm := sl_mul_entries_mem S (A := A⁻¹) (B := P)
      (sl_inv_entries_mem S (fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩)) (hp S) i j
    change B i j ∈ S
    rw [hprod, inv_mul_cancel_left] at hm
    exact hm

/-- The two factorizations of one product have exactly the expected joint field. -/
private theorem racl_sl_fibre_quad {k K : Type*} [Field k] [Field K] [Algebra k K]
    (P g g' h h' : SpecialLinearGroup (Fin 2) K)
    (hp : P = h * g) (hp' : P = h' * g') :
    racl k ((slEntries g ∪ slEntries g') ∪ (slEntries h ∪ slEntries h')) =
      racl k (slEntries P ∪ (slEntries g ∪ slEntries g')) := by
  have hh : h = P * g⁻¹ := by rw [hp]; group
  have hh' : h' = P * g'⁻¹ := by rw [hp']; group
  apply le_antisymm
  · apply racl_le_of_subset_racl
    let S := racl k (slEntries P ∪ (slEntries g ∪ slEntries g'))
    have hPS (i j : Fin 2) : P i j ∈ S := subset_racl k _ (Or.inl ⟨(i, j), rfl⟩)
    have hgS (i j : Fin 2) : g i j ∈ S := subset_racl k _ (Or.inr (Or.inl ⟨(i, j), rfl⟩))
    have hg'S (i j : Fin 2) : g' i j ∈ S := subset_racl k _ (Or.inr (Or.inr ⟨(i, j), rfl⟩))
    refine union_subset ?_ (union_subset ?_ ?_)
    · exact subset_union_right.trans (subset_racl k _)
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      have hm := sl_mul_entries_mem S hPS (sl_inv_entries_mem S hgS) i j
      change h i j ∈ S
      rwa [← hh] at hm
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      have hm := sl_mul_entries_mem S hPS (sl_inv_entries_mem S hg'S) i j
      change h' i j ∈ S
      rwa [← hh'] at hm
  · apply racl_le_of_subset_racl
    let S := racl k ((slEntries g ∪ slEntries g') ∪ (slEntries h ∪ slEntries h'))
    refine union_subset ?_ (subset_union_left.trans (subset_racl k _))
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hm := sl_mul_entries_mem S (A := h) (B := g)
      (fun i j ↦ subset_racl k _ (Or.inr (Or.inl ⟨(i, j), rfl⟩)))
      (fun i j ↦ subset_racl k _ (Or.inl (Or.inl ⟨(i, j), rfl⟩))) i j
    change P i j ∈ S
    rwa [← hp] at hm

/-- Two independent rank-one matrix parameters with a rank-one product internally yield the
rank-one difference used to construct the common curve stabilizer. No fresh fibre diagram is
an input. -/
private theorem exists_sl_rank_one_difference {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g h : SpecialLinearGroup (Fin 2) K)
    (hg : erk k ∅ (slEntries g) = 1) (hh : erk k ∅ (slEntries h) = 1)
    (hgh : erk k ∅ (slEntries g ∪ slEntries h) = 2)
    (hp : erk k ∅ (slEntries (h * g)) = 1) :
    ∃ g' h' : SpecialLinearGroup (Fin 2) K, h * g = h' * g' ∧
      idealOf k (fun ij : Fin 2 × Fin 2 ↦ g' ij.1 ij.2) =
        idealOf k (fun ij : Fin 2 × Fin 2 ↦ g ij.1 ij.2) ∧
      idealOf k (fun ij : Fin 2 × Fin 2 ↦ h' ij.1 ij.2) =
        idealOf k (fun ij : Fin 2 × Fin 2 ↦ h ij.1 ij.2) ∧
      erk k ∅ (slEntries (g * g'⁻¹)) = 1 ∧
      erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries g') = 2 ∧
      erk k ∅ (slEntries (g * g'⁻¹) ∪ slEntries h) = 2 := by
  let P := h * g
  let F := racl k (slEntries P)
  have hF : IsSmall k (F : Set K) := (IsSmall.of_finite (finite_range _)).racl
  let : IsAlgClosed ↥F := isAlgClosed_racl _
  have hpg : erk k ∅ (slEntries P ∪ slEntries g) = 2 := by
    have he := erk_eq_of_racl_eq (racl_sl_product_union (k := k) h g)
    rw [erk_union_comm k ∅ (slEntries h) (slEntries g)] at he
    exact he.trans hgh
  have hgF : erk k (F : Set K) (slEntries g) = 1 := by
    change erk k (racl k (slEntries P) : Set K) (slEntries g) = 1
    rw [erk_racl_base]
    have he := erk_union_eq k ∅ (slEntries P) (slEntries g)
    rw [empty_union, hpg, hp] at he
    exact ENat.add_right_injective_of_ne_top (n := 1) (by norm_num)
      (he.symm.trans (by norm_num : (2 : ℕ∞) = 1 + 1))
  obtain ⟨σ, hind⟩ := exists_algEquiv_indepOver (M := F) (w := slEntries g) hF
    (fun ij : Fin 2 × Fin 2 ↦ g ij.1 ij.2) (IsSmall.of_finite (finite_range _))
  let τ := σ.restrictScalars k
  let g' := SpecialLinearGroup.map σ.toRingHom g
  let h' := SpecialLinearGroup.map σ.toRingHom h
  have hentries' : slEntries g' = range (fun ij : Fin 2 × Fin 2 ↦ σ (g ij.1 ij.2)) := rfl
  rw [← hentries'] at hind
  have hfix : SpecialLinearGroup.map σ.toRingHom P = P := by
    apply SpecialLinearGroup.ext
    intro i j
    exact σ.commutes ⟨P i j, subset_racl k _ ⟨(i, j), rfl⟩⟩
  have hprod : h * g = h' * g' := by
    change P = SpecialLinearGroup.map σ.toRingHom h * SpecialLinearGroup.map σ.toRingHom g
    rw [← map_mul]
    exact hfix.symm
  have hPbase (i j : Fin 2) : P i j ∈ range (algebraMap ↥F K) :=
    ⟨⟨P i j, subset_racl k _ ⟨(i, j), rfl⟩⟩, rfl⟩
  have hfg : racl (↥F) (slEntries h) = racl (↥F) (slEntries g) :=
    racl_sl_factors_of_product_base P h g rfl hPbase
  have hfg' : racl (↥F) (slEntries h') = racl (↥F) (slEntries g') :=
    racl_sl_factors_of_product_base P h' g' hprod hPbase
  have hg'F : erk k (F : Set K) (slEntries g') = 1 := by
    rw [← erk_base_empty F]
    exact (GroupConfiguration.erk_range_comp σ (fun ij : Fin 2 × Fin 2 ↦ g ij.1 ij.2)).trans
      ((erk_base_empty F _).trans hgF)
  have hgg'F : erk k (F : Set K) (slEntries g ∪ slEntries g') = 2 := by
    rw [erk_union_eq, hgF, hind.erk_eq (subset_refl _) (finite_range _), hg'F]
    norm_num
  have hg' : erk k ∅ (slEntries g') = 1 :=
    (GroupConfiguration.erk_range_comp τ (fun ij : Fin 2 × Fin 2 ↦ g ij.1 ij.2)).trans hg
  have hh' : erk k ∅ (slEntries h') = 1 :=
    (GroupConfiguration.erk_range_comp τ (fun ij : Fin 2 × Fin 2 ↦ h ij.1 ij.2)).trans hh
  have hgg' : erk k ∅ (slEntries g ∪ slEntries g') = 2 := by
    apply le_antisymm ((erk_union_le k ∅ _ _).trans_eq (by rw [hg, hg']; norm_num))
    exact hgg'F ▸ erk_base_mono k (empty_subset (F : Set K)) _
  have hpair : racl (↥F) (slEntries h ∪ slEntries h') =
      racl (↥F) (slEntries g ∪ slEntries g') := racl_union_congr hfg hfg'
  have hhh'F : erk k (F : Set K) (slEntries h ∪ slEntries h') = 2 := by
    rw [← erk_base_empty F]
    exact (erk_eq_of_racl_eq hpair).trans ((erk_base_empty F _).trans hgg'F)
  have hhh' : erk k ∅ (slEntries h ∪ slEntries h') = 2 := by
    apply le_antisymm ((erk_union_le k ∅ _ _).trans_eq (by rw [hh, hh']; norm_num))
    exact hhh'F ▸ erk_base_mono k (empty_subset (F : Set K)) _
  have htotal : erk k ∅ (slEntries P ∪ (slEntries g ∪ slEntries g')) = 3 := by
    rw [erk_union_eq, empty_union, hp]
    change erk k (racl k (slEntries P) : Set K) _ = 2 at hgg'F
    rw [erk_racl_base] at hgg'F
    rw [hgg'F]
    norm_num
  have hall : erk k ∅ ((slEntries g ∪ slEntries g') ∪ (slEntries h ∪ slEntries h')) = 3 :=
    (erk_eq_of_racl_eq (racl_sl_fibre_quad P g g' h h' rfl hprod)).trans htotal
  refine ⟨g', h', hprod, idealOf_comp_algHom k τ.toAlgHom _,
    idealOf_comp_algHom k τ.toAlgHom _, ?_⟩
  exact sl_difference_rank_one g g' h h' hprod hg' hgg' hhh' hall

end

end GroupConfig
namespace GroupConfig

open AclGeom Set MvPolynomial Matrix

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Right multiplication, in the four matrix coordinates. -/
private def rightSl {M : IntermediateField k K} (B : SpecialLinearGroup (Fin 2) M)
    (a : Fin 2 × Fin 2 → K) : Fin 2 × Fin 2 → K :=
  fun ij ↦ a (ij.1, 0) * algebraMap M K (B 0 ij.2) +
    a (ij.1, 1) * algebraMap M K (B 1 ij.2)

private theorem rightSl_mul {M : IntermediateField k K}
    (B C : SpecialLinearGroup (Fin 2) M) (a : Fin 2 × Fin 2 → K) :
    rightSl C (rightSl B a) = rightSl (B * C) a := by
  funext ij
  simp only [rightSl, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    map_add, map_mul]
  ring

private theorem rightSl_one {M : IntermediateField k K} (a : Fin 2 × Fin 2 → K) :
    rightSl (1 : SpecialLinearGroup (Fin 2) M) a = a := by
  funext ⟨i, j⟩
  fin_cases j <;> simp [rightSl]

/-- Right translation is a polynomial map over the coefficient field. -/
private theorem rightSl_eq_aeval {M : IntermediateField k K}
    (B : SpecialLinearGroup (Fin 2) M) (a : Fin 2 × Fin 2 → K) :
    rightSl B a = fun ij : Fin 2 × Fin 2 ↦ aeval a
      (X (ij.1, 0) * C (B 0 ij.2) + X (ij.1, 1) * C (B 1 ij.2)) := by
  funext ij
  simp only [rightSl, map_add, map_mul, aeval_X, aeval_C]

/-- A generic polynomial image gives the actual forward containment of loci. -/
private theorem inLocus_rightSl {M : IntermediateField k K}
    {a x : Fin 2 × Fin 2 → K} (ha : IsGenericOver M a a)
    (hx : InLocus (k := k) a x) (B : SpecialLinearGroup (Fin 2) M) :
    InLocus (k := k) (rightSl B a) (rightSl B x) := by
  rw [rightSl_eq_aeval, rightSl_eq_aeval]
  exact inLocus_polynomial_image ha hx _

/-- If both points remain generic over the coefficient field, right translation identifies
all points of their original-base loci. This includes nongeneric points of the loci. -/
private theorem inLocus_rightSl_iff {M : IntermediateField k K}
    {a x : Fin 2 × Fin 2 → K} (B : SpecialLinearGroup (Fin 2) M)
    (ha : IsGenericOver M a a) (hb : IsGenericOver M (rightSl B a) (rightSl B a)) :
    InLocus (k := k) a x ↔ InLocus (k := k) (rightSl B a) (rightSl B x) := by
  refine ⟨fun hx ↦ inLocus_rightSl ha hx B, fun hx ↦ ?_⟩
  have h := inLocus_rightSl hb hx B⁻¹
  simpa only [rightSl_mul, mul_inv_cancel, rightSl_one] using h

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

private theorem generic_self_racl_of_rank_add {k K : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] {ι κ : Type*} [Finite ι] [Finite κ] (a : ι → K) (b : κ → K)
    (hab : erk k ∅ (range a ∪ range b) = erk k ∅ (range a) + erk k ∅ (range b)) :
    IsGenericOver (racl k (range b)) a a := by
  have hba : erk k ∅ (range b ∪ range a) = erk k ∅ (range b) + erk k ∅ (range a) := by
    rw [union_comm, hab, add_comm]
  have hr := erk_base_union_eq_of_erk_union_eq k (finite_range b) hba
  have hi : IndepOver k ∅ (range a) (range b) :=
    indepOver_of_erk_eq (finite_range a) hr
  have hi' : IndepOver k ∅ (range a) (racl k (range b) : Set K) := by
    have h := indepOver_racl_right_iff.2 hi
    simpa only [empty_union] using h
  exact isGenericOver_self_of_indepOver (IsSmall.of_finite (finite_range b)).racl hi'

/-- A determinant-one matrix descends to any intermediate field containing its entries. -/
private theorem exists_sl_over_entries {k K : Type*} [Field k] [Field K] [Algebra k K]
    (M : IntermediateField k K) (g : SpecialLinearGroup (Fin 2) K)
    (hg : ∀ i j, g i j ∈ M) :
    ∃ B : SpecialLinearGroup (Fin 2) M, SpecialLinearGroup.map (algebraMap M K) B = g := by
  let A : Matrix (Fin 2) (Fin 2) M := Matrix.of fun i j ↦ ⟨g i j, hg i j⟩
  have hd : A.det = 1 := by
    rw [Matrix.det_fin_two]
    apply Subtype.ext
    change g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1
    simpa only [Matrix.det_fin_two] using g.det_coe
  refine ⟨⟨A, hd⟩, ?_⟩
  apply SpecialLinearGroup.ext
  intro i j
  rfl

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-- The four entries of a matrix in `SL₂(K)` as a coordinate tuple. -/
abbrev slTuple {K : Type*} [Field K] (A : SpecialLinearGroup (Fin 2) K) :
    Fin 2 × Fin 2 → K := fun ij ↦ A ij.1 ij.2

private theorem inLocus_sl_map_iff {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (a m : SpecialLinearGroup (Fin 2) K) :
    InLocus (k := k) (slTuple a) (slTuple (SpecialLinearGroup.map σ.toRingHom m)) ↔
      InLocus (k := k) (slTuple a) (slTuple m) := by
  rw [inLocus_iff_idealOf_le, inLocus_iff_idealOf_le]
  change idealOf k (slTuple a) ≤ idealOf k (⇑σ.toAlgHom ∘ slTuple m) ↔ _
  rw [idealOf_comp_algHom]

/-- Translation of a base-defined curve to a base-defined curve is independent of the chosen
base-generic translating point. This is ordinary matrix homogeneity. -/
private theorem sl_curve_translate_of_same_ideal {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g n b₀ b : SpecialLinearGroup (Fin 2) K)
    (hb : idealOf k (slTuple b₀) = idealOf k (slTuple b))
    (ht : ∀ m : SpecialLinearGroup (Fin 2) K,
      InLocus (k := k) (slTuple g) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (m * b₀⁻¹))) :
    ∀ m : SpecialLinearGroup (Fin 2) K,
      InLocus (k := k) (slTuple g) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (m * b⁻¹)) := by
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq hb
  let φ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K :=
    SpecialLinearGroup.map σ.toRingHom
  let ψ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K :=
    SpecialLinearGroup.map σ.symm.toRingHom
  have hφb : φ b₀ = b := SpecialLinearGroup.ext _ _ fun i j ↦ hσ (i, j)
  have hφψ (m : SpecialLinearGroup (Fin 2) K) : φ (ψ m) = m := by
    apply SpecialLinearGroup.ext
    intro i j
    exact σ.apply_symm_apply (m i j)
  intro m
  have h := ht (ψ m)
  rw [inLocus_sl_map_iff σ.symm g m] at h
  have he : φ (ψ m * b₀⁻¹) = m * b⁻¹ := by rw [map_mul, map_inv, hφψ, hφb]
  have hi : InLocus (k := k) (slTuple n) (slTuple (ψ m * b₀⁻¹)) ↔
      InLocus (k := k) (slTuple n) (slTuple (m * b⁻¹)) := by
    rw [← he]
    exact (inLocus_sl_map_iff σ n (ψ m * b₀⁻¹)).symm
  exact h.trans hi

/-- Left multiplication by a coefficient-field matrix preserves rank over that field. -/
private theorem erk_sl_mul_left_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    (M : IntermediateField k K) (d b : SpecialLinearGroup (Fin 2) K)
    (hd : ∀ i j, d i j ∈ M) :
    erk k (M : Set K) (slEntries (d * b)) = erk k (M : Set K) (slEntries b) := by
  apply le_antisymm
  · let S := racl k ((M : Set K) ∪ slEntries b)
    have hsub : slEntries (d * b) ⊆ S := by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact sl_mul_entries_mem S
        (fun i j ↦ subset_racl k _ (Or.inl (hd i j)))
        (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)) i j
    exact (erk_mono k (M : Set K) hsub).trans_eq (erk_racl k _ _)
  · let S := racl k ((M : Set K) ∪ slEntries (d * b))
    have hsub : slEntries b ⊆ S := by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hm := sl_mul_entries_mem S (A := d⁻¹) (B := d * b)
        (sl_inv_entries_mem S (fun i j ↦ subset_racl k _ (Or.inl (hd i j))))
        (fun i j ↦ subset_racl k _ (Or.inr ⟨(i, j), rfl⟩)) i j
      change b i j ∈ S
      rwa [inv_mul_cancel_left] at hm
    exact (erk_mono k (M : Set K) hsub).trans_eq (erk_racl k _ _)

/-- A base-defined curve admitting one generic translate to a base-defined difference curve
has that difference curve stable under all its own points. All fresh points are internal. -/
private theorem sl_curve_locus_stable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g n b₀ : SpecialLinearGroup (Fin 2) K) (hg : erk k ∅ (slEntries g) = 1)
    (hb₀ : idealOf k (slTuple b₀) = idealOf k (slTuple g))
    (ht : ∀ m : SpecialLinearGroup (Fin 2) K,
      InLocus (k := k) (slTuple g) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (m * b₀⁻¹))) :
    InLocus (k := k) (slTuple n) (slTuple (1 : SpecialLinearGroup (Fin 2) K)) ∧
      ∀ d : SpecialLinearGroup (Fin 2) K, InLocus (k := k) (slTuple n) (slTuple d) →
        ∀ m : SpecialLinearGroup (Fin 2) K,
          InLocus (k := k) (slTuple n) (slTuple m) ↔
            InLocus (k := k) (slTuple n) (slTuple (m * d)) := by
  have h1 : InLocus (k := k) (slTuple n) (slTuple (1 : SpecialLinearGroup (Fin 2) K)) := by
    have hbmem : InLocus (k := k) (slTuple g) (slTuple b₀) :=
      (inLocus_iff_idealOf_le _ _).2 hb₀.ge
    simpa only [mul_inv_cancel] using (ht b₀).1 hbmem
  refine ⟨h1, fun d hd m ↦ ?_⟩
  let M := racl k (slEntries d)
  have hM : IsSmall k (M : Set K) := (IsSmall.of_finite (finite_range _)).racl
  obtain ⟨u, hu⟩ := exists_isGenericOver hM (slTuple g)
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq hu.idealOf_eq.symm
  let b := SpecialLinearGroup.map σ.toRingHom g
  have hbu : slTuple b = u := funext fun ij ↦ hσ ij
  have hbgen : IsGenericOver M (slTuple g) (slTuple b) := by rw [hbu]; exact hu
  have hbsame : idealOf k (slTuple b₀) = idealOf k (slTuple b) :=
    hb₀.trans hbgen.idealOf_eq.symm
  have hbshift := sl_curve_translate_of_same_ideal g n b₀ b hbsame ht
  have hdbmem : InLocus (k := k) (slTuple g) (slTuple (d * b)) := by
    apply (hbshift (d * b)).2
    simpa only [mul_inv_cancel_right] using hd
  have hrb : erk k (M : Set K) (slEntries b) = 1 :=
    hbgen.erk_coe_eq.trans (hbgen.erk_empty_eq.trans hg)
  have hrd : erk k (M : Set K) (slEntries (d * b)) = 1 :=
    (erk_sl_mul_left_eq M d b (fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩)).trans hrb
  have hdbgen : IsGenericOver M (slTuple g) (slTuple (d * b)) :=
    (isGenericOver_iff_erk_eq hM hdbmem).2 (hrd.trans hg.symm)
  have hdbsame : idealOf k (slTuple b₀) = idealOf k (slTuple (d * b)) :=
    hb₀.trans hdbgen.idealOf_eq.symm
  have hdbshift := sl_curve_translate_of_same_ideal g n b₀ (d * b) hdbsame ht
  have he₁ := hbshift (m * (d * b))
  have he₂ := hdbshift (m * (d * b))
  rw [show m * (d * b) * b⁻¹ = m * d by group] at he₁
  rw [mul_inv_cancel_right] at he₂
  exact he₂.symm.trans he₁

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix

noncomputable section

/-- A matrix and its inverse have entries of the same rank. -/
private theorem erk_slEntries_inv {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m : SpecialLinearGroup (Fin 2) K) :
    erk k ∅ (slEntries m⁻¹) = erk k ∅ (slEntries m) := by
  have key : ∀ m : SpecialLinearGroup (Fin 2) K, racl k (slEntries m⁻¹) ≤ racl k (slEntries m) :=
    fun m ↦ racl_le_of_subset_racl (by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact sl_inv_entries_mem (racl k (slEntries m))
        (fun i j ↦ subset_racl k (slEntries m) ⟨(i, j), rfl⟩) i j)
  refine erk_eq_of_racl_eq (le_antisymm (key m) ?_)
  simpa only [inv_inv] using key m⁻¹

/-- **Rank-one subgroups of the upper Borel.** Let `n` be upper triangular with entries of
rank one. Suppose the points of its locus contain the identity and are stable, in both
directions, under right multiplication by every rank-one point of the locus. Then either every
point `d` of the locus has `d₀₀ = 1`, or there is `c` in the base with
`d₀₁ d₀₀ = c (d₀₀² - 1)` for every point `d`. -/
theorem upper_locus_unipotent_or_torus {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (n : SpecialLinearGroup (Fin 2) K) (hn10 : n 1 0 = 0) (hn : erk k ∅ (slEntries n) = 1)
    (h1 : InLocus (k := k) (slTuple n) (slTuple 1))
    (h2 : ∀ d, InLocus (k := k) (slTuple n) (slTuple d) → erk k ∅ (slEntries d) = 1 →
      ∀ m, InLocus (k := k) (slTuple n) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (m * d))) :
    (∀ d, InLocus (k := k) (slTuple n) (slTuple d) → d 0 0 = 1) ∨
      ∃ c : k, ∀ d, InLocus (k := k) (slTuple n) (slTuple d) →
        d 0 1 * d 0 0 = algebraMap k K c * (d 0 0 ^ 2 - 1) := by
  have hdet (m : SpecialLinearGroup (Fin 2) K) : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using m.det_coe
  have hone : (1 : SpecialLinearGroup (Fin 2) K) 0 0 = 1 ∧
      (1 : SpecialLinearGroup (Fin 2) K) 0 1 = 0 := ⟨by simp, by simp⟩
  by_cases halg : n 0 0 ∈ racl k (∅ : Set K)
  · -- The unipotent case: the diagonal entry is constant on the locus.
    left
    obtain ⟨l, hl⟩ := mem_range_of_isAlgebraic_of_isAlgClosed (isAlgebraic_of_mem_racl_empty halg)
    have hP : ∀ x : Fin 2 × Fin 2 → K, InLocus (k := k) (slTuple n) x →
        x (0, 0) = algebraMap k K l := by
      intro x hx
      have h := aeval_eq_zero_of_inLocus_base hx
        (P := MvPolynomial.X (0, 0) - MvPolynomial.C l) (by
          rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hl]
          exact sub_self _)
      rwa [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] at h
    intro d hd
    exact (hP _ hd).trans ((hP _ h1).symm.trans hone.1)
  · right
    have hn00 : n 0 0 ≠ 0 := fun h ↦ halg (h ▸ zero_mem _)
    have hl1 : n 0 0 ^ 2 - 1 ≠ 0 := sub_ne_zero.2
      (sq_ne_one_of_transcendental fun h ↦ halg (mem_racl_empty_of_isAlgebraic h))
    -- A generic copy `n₂` of `n` over the field `M` of the entries of `n`.
    obtain ⟨M, hMdef⟩ : ∃ M : IntermediateField k K, M = racl k (slEntries n) := ⟨_, rfl⟩
    have hM : IsSmall k (M : Set K) := hMdef ▸ (IsSmall.of_finite (finite_range _)).racl
    have hnM (i j : Fin 2) : n i j ∈ M := hMdef ▸ subset_racl k _ ⟨(i, j), rfl⟩
    obtain ⟨a', ha'⟩ := exists_isGenericOver hM (slTuple n)
    have hloc : InLocus (k := k) (slTuple n) a' := ha'.inLocus
    have h10' : a' (1, 0) = 0 := by
      have h := aeval_eq_zero_of_inLocus_base hloc (P := MvPolynomial.X (1, 0)) (by
        rw [MvPolynomial.aeval_X]
        exact hn10)
      rwa [MvPolynomial.aeval_X] at h
    have hdet' : a' (0, 0) * a' (1, 1) - a' (0, 1) * a' (1, 0) = 1 := by
      have h := aeval_eq_zero_of_inLocus_base hloc
        (P := MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) -
          MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0) - 1) (by
          simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X]
          change n 0 0 * n 1 1 - n 0 1 * n 1 0 - 1 = 0
          rw [hdet n, sub_self])
      simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at h
      exact sub_eq_zero.1 h
    obtain ⟨n₂, hn₂⟩ : ∃ n₂ : SpecialLinearGroup (Fin 2) K, slTuple n₂ = a' :=
      ⟨⟨Matrix.of fun i j ↦ a' (i, j), by rw [Matrix.det_fin_two]; exact hdet'⟩,
        funext fun _ ↦ rfl⟩
    have hgen₂ : IsGenericOver M (slTuple n) (slTuple n₂) := hn₂ ▸ ha'
    have hD₂ : InLocus (k := k) (slTuple n) (slTuple n₂) := hgen₂.inLocus
    have hid₂ := hgen₂.idealOf_eq
    have hr₂ : erk k ∅ (slEntries n₂) = 1 :=
      (erk_empty_range_eq_of_idealOf_eq hid₂).trans hn
    have h₂10 : n₂ 1 0 = 0 := by
      rw [show n₂ 1 0 = slTuple n₂ (1, 0) from rfl, hn₂]
      exact h10'
    -- Transcendence of the diagonal entry of `n₂`.
    have halg₂ : n₂ 0 0 ∉ racl k (∅ : Set K) := by
      intro h
      obtain ⟨l, hl⟩ := mem_range_of_isAlgebraic_of_isAlgClosed (isAlgebraic_of_mem_racl_empty h)
      have hmem : MvPolynomial.X (0, 0) - MvPolynomial.C l ∈ idealOf k (slTuple n₂) :=
        (mem_idealOf_iff k).2 (by
          rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hl]
          exact sub_self _)
      rw [hid₂, mem_idealOf_iff, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        sub_eq_zero] at hmem
      have h' : n 0 0 = algebraMap k K l := hmem
      exact halg (by rw [h']; exact (racl k (∅ : Set K)).algebraMap_mem l)
    have hn₂00 : n₂ 0 0 ≠ 0 := fun h ↦ halg₂ (h ▸ zero_mem _)
    have hl2 : n₂ 0 0 ^ 2 - 1 ≠ 0 := sub_ne_zero.2
      (sq_ne_one_of_transcendental fun h ↦ halg₂ (mem_racl_empty_of_isAlgebraic h))
    -- The commutator lies on the locus.
    have hDn : InLocus (k := k) (slTuple n) (slTuple n) := inLocus_self _
    have hDinv : ∀ d, InLocus (k := k) (slTuple n) (slTuple d) → erk k ∅ (slEntries d) = 1 →
        InLocus (k := k) (slTuple n) (slTuple d⁻¹) := fun d hd hr ↦
      (h2 d hd hr d⁻¹).2 (by rw [inv_mul_cancel]; exact h1)
    obtain ⟨c, hcdef⟩ : ∃ c, c = n * n₂ * n⁻¹ * n₂⁻¹ := ⟨_, rfl⟩
    have hDc : InLocus (k := k) (slTuple n) (slTuple c) := by
      rw [hcdef]
      exact (h2 n₂⁻¹ (hDinv n₂ hD₂ hr₂) ((erk_slEntries_inv n₂).trans hr₂)
        (n * n₂ * n⁻¹)).1 ((h2 n⁻¹ (hDinv n hDn hn) ((erk_slEntries_inv n).trans hn)
          (n * n₂)).1 ((h2 n₂ hD₂ hr₂ n).1 hDn))
    have hcomm : c * (n₂ * n) = n * n₂ := by
      rw [hcdef]
      group
    have e00 : (c * (n₂ * n)) 0 0 = (n * n₂) 0 0 := by rw [hcomm]
    have e10 : (c * (n₂ * n)) 1 0 = (n * n₂) 1 0 := by rw [hcomm]
    have e01 : (c * (n₂ * n)) 0 1 = (n * n₂) 0 1 := by rw [hcomm]
    simp only [sl_mul_apply, hn10, h₂10, mul_zero, add_zero, zero_mul, zero_add] at e00 e10 e01
    have hc00 : c 0 0 = 1 := by
      have h := mul_right_cancel₀ (mul_ne_zero hn₂00 hn00)
        (e00.trans (by ring : n 0 0 * n₂ 0 0 = 1 * (n₂ 0 0 * n 0 0)))
      exact h
    have hc10 : c 1 0 = 0 := by
      have h : c 1 0 * (n₂ 0 0 * n 0 0) = 0 := e10
      exact (mul_eq_zero.1 h).resolve_right (mul_ne_zero hn₂00 hn00)
    have hc11 : c 1 1 = 1 := by
      have h := hdet c
      rw [hc00, hc10, mul_zero, sub_zero, one_mul] at h
      exact h
    -- The commutator entry is algebraic over the base, by rank.
    have hγ : c 0 1 ∈ racl k (∅ : Set K) := by
      by_contra hγ
      have hrc : erk k ∅ (slEntries c) = 1 := by
        have hracl : racl k (slEntries c) = racl k {c 0 1} := by
          refine le_antisymm (racl_le_of_subset_racl ?_)
            (racl_le_of_subset_racl (singleton_subset_iff.2 (subset_racl k _ ⟨(0, 1), rfl⟩)))
          rintro _ ⟨⟨i, j⟩, rfl⟩
          fin_cases i <;> fin_cases j
          · change c 0 0 ∈ racl k ({c 0 1} : Set K)
            rw [hc00]
            exact one_mem _
          · exact subset_racl k _ rfl
          · change c 1 0 ∈ racl k ({c 0 1} : Set K)
            rw [hc10]
            exact zero_mem _
          · change c 1 1 ∈ racl k ({c 0 1} : Set K)
            rw [hc11]
            exact one_mem _
        rw [erk_eq_of_racl_eq hracl]
        exact le_antisymm ((erk_le_encard k ∅ _).trans (by simp))
          (Order.one_le_iff_ne_zero.2 fun h0 ↦ hγ ((erk_eq_zero_iff k).1 h0 (mem_singleton _)))
      have hgc : IsGenericOver (racl k (∅ : Set K)) (slTuple n) (slTuple c) :=
        (isGenericOver_iff_erk_eq (IsSmall.of_finite finite_empty).racl hDc).2
          ((erk_racl_base k ∅ _).trans (hrc.trans hn.symm))
      have hmem : MvPolynomial.X (0, 0) - 1 ∈ idealOf k (slTuple c) :=
        (mem_idealOf_iff k).2 (by
          rw [map_sub, MvPolynomial.aeval_X, map_one, sub_eq_zero]
          exact hc00)
      rw [hgc.idealOf_eq, mem_idealOf_iff, map_sub, MvPolynomial.aeval_X, map_one,
        sub_eq_zero] at hmem
      have h' : n 0 0 = 1 := hmem
      exact halg (by rw [h']; exact one_mem _)
    -- The commutator identity.
    have hid : n₂ 0 1 * n₂ 0 0 * (n 0 0 ^ 2 - 1) - n 0 1 * n 0 0 * (n₂ 0 0 ^ 2 - 1) = c 0 1 := by
      have d1 : n 0 0 * n 1 1 = 1 := by have h := hdet n; rwa [hn10, mul_zero, sub_zero] at h
      have d2 : n₂ 0 0 * n₂ 1 1 = 1 := by
        have h := hdet n₂
        rwa [h₂10, mul_zero, sub_zero] at h
      rw [hc00] at e01
      linear_combination (-(n 0 0 * n₂ 0 0)) * e01 + (n₂ 0 1 * n₂ 0 0 +
        c 0 1 * n₂ 0 0 * n₂ 1 1) * d1 + (c 0 1 - n 0 1 * n 0 0) * d2
    -- A polynomial over `M` vanishing at the generic copy, hence on the whole locus.
    have hγM : c 0 1 ∈ M := hMdef ▸ (racl_mono (empty_subset _) hγ)
    have hl1M : n 0 0 ^ 2 - 1 ∈ M := M.sub_mem (pow_mem (hnM 0 0) 2) M.one_mem
    have hb1M : n 0 1 * n 0 0 ∈ M := M.mul_mem (hnM 0 1) (hnM 0 0)
    let Q : MvPolynomial (Fin 2 × Fin 2) M :=
      MvPolynomial.C ⟨_, hl1M⟩ * MvPolynomial.X (0, 1) * MvPolynomial.X (0, 0) -
        MvPolynomial.C ⟨_, hγM⟩ - MvPolynomial.C ⟨_, hb1M⟩ * (MvPolynomial.X (0, 0) ^ 2 - 1)
    have hQ (x : Fin 2 × Fin 2 → K) : MvPolynomial.aeval x Q =
        (n 0 0 ^ 2 - 1) * x (0, 1) * x (0, 0) - c 0 1 - n 0 1 * n 0 0 * (x (0, 0) ^ 2 - 1) := by
      simp only [Q, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C]
      rfl
    have hQd : ∀ d, InLocus (k := k) (slTuple n) (slTuple d) →
        MvPolynomial.aeval (slTuple d) Q = 0 :=
      fun d hd ↦ aeval_eq_zero_of_isGenericOver hgen₂ hd (by
        rw [hQ]
        change (n 0 0 ^ 2 - 1) * n₂ 0 1 * n₂ 0 0 - c 0 1 - n 0 1 * n 0 0 * (n₂ 0 0 ^ 2 - 1) = 0
        linear_combination hid)
    have hγ0 : c 0 1 = 0 := by
      have h := hQd 1 h1
      rw [hQ] at h
      simp only [slTuple, hone.1, hone.2] at h
      linear_combination -h
    -- The constant lies in the base.
    obtain ⟨B, hBdef⟩ : ∃ B, B = n 0 1 * n 0 0 / (n 0 0 ^ 2 - 1) := ⟨_, rfl⟩
    have hB₂ : B = n₂ 0 1 * n₂ 0 0 / (n₂ 0 0 ^ 2 - 1) := by
      rw [hBdef, div_eq_div_iff hl1 hl2]
      linear_combination -hid - hγ0
    have hBbase : B ∈ racl k (∅ : Set K) := by
      have hind : IndepOver k ∅ (range a') (M : Set K) :=
        indepOver_of_erk_eq (finite_range a') (by rw [empty_union]; exact ha'.erk_coe_eq)
      have hinter := hind.racl_inter_eq
      rw [empty_union, empty_union] at hinter
      change B ∈ (racl k (∅ : Set K) : Set K)
      rw [← hinter]
      refine ⟨?_, ?_⟩
      · rw [hB₂]
        have ha (i j : Fin 2) : n₂ i j ∈ racl k (range a') :=
          subset_racl k _ ⟨(i, j), (congrFun hn₂ (i, j)).symm⟩
        exact div_mem (mul_mem (ha 0 1) (ha 0 0)) (sub_mem (pow_mem (ha 0 0) 2) (one_mem _))
      · rw [hBdef]
        have hm (i j : Fin 2) : n i j ∈ racl k (M : Set K) := subset_racl k _ (hnM i j)
        exact div_mem (mul_mem (hm 0 1) (hm 0 0)) (sub_mem (pow_mem (hm 0 0) 2) (one_mem _))
    obtain ⟨b, hb⟩ := mem_range_of_isAlgebraic_of_isAlgClosed
      (isAlgebraic_of_mem_racl_empty hBbase)
    refine ⟨b, fun d hd ↦ ?_⟩
    have h := hQd d hd
    rw [hQ, hγ0] at h
    rw [hb, hBdef, div_mul_eq_mul_div, eq_div_iff hl1]
    simp only [slTuple] at h
    linear_combination h

end

end GroupConfig

namespace GroupConfig

open AclGeom Set Matrix MvPolynomial

noncomputable section

/-- Left multiplication in the four matrix coordinates. -/
private def leftSl {k K : Type*} [Field k] [Field K] [Algebra k K]
    {M : IntermediateField k K} (B : SpecialLinearGroup (Fin 2) M)
    (a : Fin 2 × Fin 2 → K) : Fin 2 × Fin 2 → K :=
  fun ij ↦ algebraMap M K (B ij.1 0) * a (0, ij.2) +
    algebraMap M K (B ij.1 1) * a (1, ij.2)

private theorem leftSl_mul {k K : Type*} [Field k] [Field K] [Algebra k K]
    {M : IntermediateField k K} (B C : SpecialLinearGroup (Fin 2) M)
    (a : Fin 2 × Fin 2 → K) : leftSl C (leftSl B a) = leftSl (C * B) a := by
  funext ij
  simp only [leftSl, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    map_add, map_mul]
  ring

private theorem leftSl_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    {M : IntermediateField k K} (a : Fin 2 × Fin 2 → K) :
    leftSl (1 : SpecialLinearGroup (Fin 2) M) a = a := by
  funext ⟨i, j⟩
  fin_cases i <;> simp [leftSl]

private theorem leftSl_eq_aeval {k K : Type*} [Field k] [Field K] [Algebra k K]
    {M : IntermediateField k K} (B : SpecialLinearGroup (Fin 2) M)
    (a : Fin 2 × Fin 2 → K) :
    leftSl B a = fun ij : Fin 2 × Fin 2 ↦ aeval a
      (C (B ij.1 0) * X (0, ij.2) + C (B ij.1 1) * X (1, ij.2)) := by
  funext ij
  simp only [leftSl, map_add, map_mul, aeval_X, aeval_C]

/-- Both generic points are retained over the coefficient field, so left translation
identifies their entire original-base loci. -/
private theorem inLocus_leftSl_iff {k K : Type*} [Field k] [Field K] [Algebra k K]
    {M : IntermediateField k K} {a x : Fin 2 × Fin 2 → K}
    (B : SpecialLinearGroup (Fin 2) M) (ha : IsGenericOver M a a)
    (hb : IsGenericOver M (leftSl B a) (leftSl B a)) :
    InLocus (k := k) a x ↔ InLocus (k := k) (leftSl B a) (leftSl B x) := by
  have forward {a x : Fin 2 × Fin 2 → K} (ha : IsGenericOver M a a)
      (hx : InLocus (k := k) a x) (B : SpecialLinearGroup (Fin 2) M) :
      InLocus (k := k) (leftSl B a) (leftSl B x) := by
    rw [leftSl_eq_aeval, leftSl_eq_aeval]
    exact inLocus_polynomial_image ha hx _
  refine ⟨fun hx ↦ forward ha hx B, fun hx ↦ ?_⟩
  have h := forward hb hx B⁻¹
  simpa only [leftSl_mul, inv_mul_cancel, leftSl_one] using h

/-- The concrete right-translate identity extracted from two independent curve points. -/
private theorem sl_curve_right_translate {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g n b : SpecialLinearGroup (Fin 2) K) (hn : n = g * b⁻¹)
    (hg : erk k ∅ (slEntries g) = 1) (hrn : erk k ∅ (slEntries n) = 1)
    (hb : erk k ∅ (slEntries b) = 1)
    (hgb : erk k ∅ (slEntries g ∪ slEntries b) = 2)
    (hnb : erk k ∅ (slEntries n ∪ slEntries b) = 2) :
    ∀ m : SpecialLinearGroup (Fin 2) K,
      InLocus (k := k) (slTuple g) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (m * b⁻¹)) := by
  have hga : IsGenericOver (racl k (slEntries b)) (slTuple g) (slTuple g) :=
    generic_self_racl_of_rank_add _ _ (by rw [hg, hb, hgb]; norm_num)
  have hna : IsGenericOver (racl k (slEntries b)) (slTuple n) (slTuple n) :=
    generic_self_racl_of_rank_add _ _ (by rw [hrn, hb, hnb]; norm_num)
  let M := racl k (slEntries b)
  obtain ⟨B, hB⟩ := exists_sl_over_entries M b fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩
  have hB' : SpecialLinearGroup.map (algebraMap M K) B⁻¹ = b⁻¹ := by rw [map_inv, hB]
  have hright (m : SpecialLinearGroup (Fin 2) K) : rightSl B⁻¹ (slTuple m) =
      slTuple (m * b⁻¹) := by
    funext ij
    change m ij.1 0 * (SpecialLinearGroup.map (algebraMap M K) B⁻¹) 0 ij.2 +
      m ij.1 1 * (SpecialLinearGroup.map (algebraMap M K) B⁻¹) 1 ij.2 = (m * b⁻¹) ij.1 ij.2
    rw [hB', SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have himage : rightSl B⁻¹ (slTuple g) = slTuple n := by rw [hright, ← hn]
  intro m
  have he := inLocus_rightSl_iff (x := slTuple m) B⁻¹ hga (by rw [himage]; exact hna)
  rwa [himage, hright] at he

/-- The matching left-translate identity uses the same actual difference. -/
private theorem sl_curve_left_translate {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (h n b : SpecialLinearGroup (Fin 2) K) (hn : n = b⁻¹ * h)
    (hh : erk k ∅ (slEntries h) = 1) (hrn : erk k ∅ (slEntries n) = 1)
    (hb : erk k ∅ (slEntries b) = 1)
    (hhb : erk k ∅ (slEntries h ∪ slEntries b) = 2)
    (hnb : erk k ∅ (slEntries n ∪ slEntries b) = 2) :
    ∀ m : SpecialLinearGroup (Fin 2) K,
      InLocus (k := k) (slTuple h) (slTuple m) ↔
        InLocus (k := k) (slTuple n) (slTuple (b⁻¹ * m)) := by
  have hha : IsGenericOver (racl k (slEntries b)) (slTuple h) (slTuple h) :=
    generic_self_racl_of_rank_add _ _ (by rw [hh, hb, hhb]; norm_num)
  have hna : IsGenericOver (racl k (slEntries b)) (slTuple n) (slTuple n) :=
    generic_self_racl_of_rank_add _ _ (by rw [hrn, hb, hnb]; norm_num)
  let M := racl k (slEntries b)
  obtain ⟨B, hB⟩ := exists_sl_over_entries M b fun i j ↦ subset_racl k _ ⟨(i, j), rfl⟩
  have hB' : SpecialLinearGroup.map (algebraMap M K) B⁻¹ = b⁻¹ := by rw [map_inv, hB]
  have hleft (m : SpecialLinearGroup (Fin 2) K) : leftSl B⁻¹ (slTuple m) =
      slTuple (b⁻¹ * m) := by
    funext ij
    change (SpecialLinearGroup.map (algebraMap M K) B⁻¹) ij.1 0 * m 0 ij.2 +
      (SpecialLinearGroup.map (algebraMap M K) B⁻¹) ij.1 1 * m 1 ij.2 = (b⁻¹ * m) ij.1 ij.2
    rw [hB', SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have himage : leftSl B⁻¹ (slTuple h) = slTuple n := by rw [hleft, ← hn]
  intro m
  have he := inLocus_leftSl_iff (x := slTuple m) B⁻¹ hha (by rw [himage]; exact hna)
  rwa [himage, hleft] at he

/-- **Coset structure of a product of curves.** Let `g` be upper triangular and `h` a matrix,
with entries of rank one over `k`, jointly of rank two, such that the entries of `h g` have rank
one. Then an upper triangular `n` with entries of rank one has a locus containing `1` and
stable under right multiplication by its points; the locus of `g` is its right coset through
`g` and the locus of `h` is its left coset through `h`. -/
theorem exists_upper_curve_cosets {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (g h : SpecialLinearGroup (Fin 2) K) (hg10 : g 1 0 = 0)
    (hg : erk k ∅ (slEntries g) = 1) (hh : erk k ∅ (slEntries h) = 1)
    (hgh : erk k ∅ (slEntries g ∪ slEntries h) = 2)
    (hp : erk k ∅ (slEntries (h * g)) = 1) :
    ∃ n : SpecialLinearGroup (Fin 2) K, n 1 0 = 0 ∧ erk k ∅ (slEntries n) = 1 ∧
      InLocus (k := k) (slTuple n) (slTuple (1 : SpecialLinearGroup (Fin 2) K)) ∧
      (∀ d : SpecialLinearGroup (Fin 2) K, InLocus (k := k) (slTuple n) (slTuple d) →
        ∀ m : SpecialLinearGroup (Fin 2) K,
          InLocus (k := k) (slTuple n) (slTuple m) ↔
            InLocus (k := k) (slTuple n) (slTuple (m * d))) ∧
      (∀ m : SpecialLinearGroup (Fin 2) K,
        InLocus (k := k) (slTuple g) (slTuple m) ↔
          InLocus (k := k) (slTuple n) (slTuple (m * g⁻¹))) ∧
      ∀ m : SpecialLinearGroup (Fin 2) K,
        InLocus (k := k) (slTuple h) (slTuple m) ↔
          InLocus (k := k) (slTuple n) (slTuple (h⁻¹ * m)) := by
  obtain ⟨g', h', hprod, ht, ht', hn, hng', hnh⟩ :=
    exists_sl_rank_one_difference g h hg hh hgh hp
  let n := g * g'⁻¹
  have hn' : n = h⁻¹ * h' := by
    change g * g'⁻¹ = h⁻¹ * h'
    calc g * g'⁻¹ = h⁻¹ * (h * g) * g'⁻¹ := by group
      _ = h⁻¹ * (h' * g') * g'⁻¹ := by rw [hprod]
      _ = h⁻¹ * h' := by group
  have hg' : erk k ∅ (slEntries g') = 1 := (erk_empty_range_eq_of_idealOf_eq ht).trans hg
  have hh' : erk k ∅ (slEntries h') = 1 := (erk_empty_range_eq_of_idealOf_eq ht').trans hh
  have hgg' : erk k ∅ (slEntries g ∪ slEntries g') = 2 :=
    (erk_eq_of_racl_eq (racl_sl_difference_union (k := k) g g')).symm.trans hng'
  have hhh' : erk k ∅ (slEntries h' ∪ slEntries h) = 2 := by
    rw [union_comm]
    exact (erk_eq_of_racl_eq (racl_sl_left_difference_union (k := k) h h')).symm.trans
      (by rw [← hn']; exact hnh)
  have hright := sl_curve_right_translate g n g' rfl hg hn hg' hgg' hng'
  have hleft := sl_curve_left_translate h' n h hn' hh' hn hh hhh' hnh
  obtain ⟨h1, h2⟩ := sl_curve_locus_stable g n g' hg ht hright
  have hg'10 : g' 1 0 = 0 := by
    have hm : InLocus (k := k) (slTuple g) (slTuple g') :=
      (inLocus_iff_idealOf_le _ _).2 ht.ge
    have he := aeval_eq_zero_of_inLocus_base hm (P := X (1, 0)) (by
      rw [aeval_X]; exact hg10)
    rwa [aeval_X] at he
  have hn10 : n 1 0 = 0 := by
    change (g * g'⁻¹) 1 0 = 0
    rw [sl_mul_apply, hg10, zero_mul, zero_add]
    have hinv : g'⁻¹ 1 0 = -g' 1 0 := by rw [SpecialLinearGroup.SL2_inv_expl]; rfl
    rw [hinv, hg'10, neg_zero, mul_zero]
  refine ⟨n, hn10, hn, h1, h2,
    sl_curve_translate_of_same_ideal g n g' g ht hright, fun m ↦ ?_⟩
  have hi : InLocus (k := k) (slTuple h) (slTuple m) ↔
      InLocus (k := k) (slTuple h') (slTuple m) := by
    rw [inLocus_iff_idealOf_le, inLocus_iff_idealOf_le, ht']
  exact hi.trans (hleft m)

end

end GroupConfig
