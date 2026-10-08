/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.AffinePointNormalization
import AclGeom.Geometry.Representatives
import AclGeom.Config.ShiftedAffineMeets
import AclGeom.Config.RemainingAffineMeets
import AclGeom.Config.PsiLattice
import AclGeom.Config.AtomClause
import AclGeom.Config.AffineGrid

/-!
# Affine-grid coordinates from an explicit chart and supplied inputs

Let `w` be a `Ψ`-witness with the ratio guard `I ≠ D` over algebraically closed `k ⊆ K`.
Suppose independent `a, b, c, d, x` give the joins `A = acl(a, b)`, `B = acl(c, d)` and
`C = acl(ac, bc + d)` and the points `S, T, U, X, Y, Z` of table (8.5).

* `QWitness.Psi.hasAffineGridCoordinates_of_chart_supplied_inputs`: the original prime curve of
  `F` and its span come before every first family of fresh inputs, which yields `κ ∈ k`.  The
  original prime curve of `H⁻¹` and its span come before every second family.  After both
  families, `w` has affine-grid coordinates.

In the proof the new chart is `a, b + (a - 1) κ - η, c, d + (c - 1) κ + (c - 1) η, x - κ` for
some `η ∈ k`.  All three joins and fifteen points are derived:
* the rows `D, E, F, G, H, I, Q` and the new independence come from the private guarded
  two-family composition, which derives every raw input from `Ψ`, `I ≠ D` and the chart;
* `S, T, U` come from the chart;
* the points `P, R, X, Y, Z` change only by elements algebraic over `k`;
* the second generators of the joins `A, B, C` change only by elements algebraic over the first.

The six generator points of `A, B, C` are not constrained.  No common shift or uniqueness is
claimed.

**Status:** one conditional chart-to-grid producer for supplied inputs proved (#27, P4).
The actual PRIVATE consumer derives the grid before applying the existing Q-semantic theorem.
A separate canonical-table check jointly realizes `Ψ`, `I ≠ D` and all nine chart equalities,
without ACF; it does not supply the fresh inputs or a chart for an arbitrary witness.
Initial chart existence, input existence/enlargement/descent, actions, classification and scheme
bridges, guarded and unconditional extraction/completeness, #11 and frozen117 remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The reciprocal Q tuple is derived from the original five-coordinate chart. -/
private theorem reciprocal_Q_tuple_independent {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    AlgebraicIndependent k ![c, d, b, (a * c)⁻¹] := by
  classical
  let e : Fin 4 → Fin 5 := ![2, 3, 1, 0]
  have he : Function.Injective e := by decide
  have heq : (fun q : Fin 4 ↦ (![a, b, c, d, x] : Fin 5 → K) (e q)) =
      ![c, d, b, a] := by
    funext q
    fin_cases q <;> rfl
  have h4 : AlgebraicIndependent k ![c, d, b, a] := heq ▸ hind.comp e he
  have hc0 : c ≠ 0 := hind.ne_zero 2
  have hi : c * (a * c)⁻¹ = a⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  refine AlgebraicIndependent.of_racl_range_eq h4 (racl_range_eq_of_mem ?_ ?_)
  · have hm (i : Fin 4) : ![c, d, b, a] i ∈ racl k (Set.range ![c, d, b, a]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · exact inv_mem (mul_mem (hm 3) (hm 0))
  · have hm (i : Fin 4) : ![c, d, b, (a * c)⁻¹] i ∈
        racl k (Set.range ![c, d, b, (a * c)⁻¹]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · have h := inv_mem (mul_mem (hm 0) (hm 3))
      change (c * (a * c)⁻¹)⁻¹ ∈ _ at h
      rwa [hi, inv_inv] at h

/-- Inverting one generator preserves a pair closure; consumed in both raw H conversions. -/
private theorem reciprocal_pair_closure (u v : K) :
    racl k ({u⁻¹, v} : Set K) = racl k ({u, v} : Set K) := by
  have h := congrArg
    (fun L : IntermediateField k K ↦ racl k ((L : Set K) ∪ ({v} : Set K)))
    (racl_inv (k := k) u)
  simpa only [racl_union_left, Set.singleton_union] using h

/-- Actual reciprocal substitution derives Q's shift from raw q/g/h incidences.
No H or Q normal form is supplied. The original h-inverse curve precedes every second INPUT
family; ambient/base ACF and supplied INPUT existence remain explicit. -/
private theorem reciprocal_Q_from_raw [IsAlgClosed k] [IsAlgClosed K] {a b c d x q g h : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hqc : q ∈ racl k ({c, d} : Set K)) (hqT : q ∉ racl k ({c} : Set K))
    (hgPT : g ∈ racl k ({b, c} : Set K))
    (hgQR : g ∈ racl k ({q, b * c + d} : Set K))
    (hgT : g ∉ racl k ({c} : Set K))
    (hhUG : h ∈ racl k ({a * c, g} : Set K))
    (hhA : h ∈ racl k ({a, b} : Set K))
    (hhS : h ∉ racl k ({a} : Set K)) :
    ∃ F : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({h⁻¹} : Set K)),
      Prime F ∧
      idealOf ↥(IntermediateField.adjoin k ({h⁻¹} : Set K)) ![a⁻¹, b] =
        Ideal.span {F} ∧
      ∀ t : ℕ → K,
        (∀ n < 2 * F.totalDegree + 1,
          t n ∉ racl k ({c, d, b, (a * c)⁻¹} ∪ t '' Set.Iio n)) →
        ∃ η : k, racl k ({q} : Set K) =
          racl k ({d + (c - 1) * algebraMap k K η} : Set K) := by
  have h4 := reciprocal_Q_tuple_independent hind
  have hc0 : c ≠ 0 := hind.ne_zero 2
  have hi : c * (a * c)⁻¹ = a⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hδx : g ∈ racl k ({c, b} : Set K) := by
    simpa only [Set.pair_comm] using hgPT
  have hδy : g ∈ racl k ({q, c * b + d} : Set K) := by
    simpa only [mul_comm c b] using hgQR
  have hf : h⁻¹ ∈ racl k ({(a * c)⁻¹, g} : Set K) := by
    rw [reciprocal_pair_closure]
    exact inv_mem hhUG
  have hfm : h⁻¹ ∈ racl k ({c * (a * c)⁻¹, b} : Set K) := by
    rw [hi, reciprocal_pair_closure]
    exact inv_mem hhA
  have hfu : h⁻¹ ∉ racl k ({c * (a * c)⁻¹} : Set K) := by
    rw [hi, racl_inv]
    intro hh
    exact hhS (by simpa only [inv_inv] using inv_mem hh)
  have H := racl_normalized_P_of_supplied_fresh_inputs h4 hqc hqT
    hδx hgT hδy hf hfm hfu
  simpa only [hi] using H


/-- Equal point closures can replace one generator in an actual raw incidence pair. -/
private theorem pair_closure_of_singleton_eq {u v : K}
    (huv : racl k ({u} : Set K) = racl k ({v} : Set K)) (w : K) :
    racl k ({u, w} : Set K) = racl k ({v, w} : Set K) := by
  have h := congrArg
    (fun L : IntermediateField k K ↦ racl k ((L : Set K) ∪ ({w} : Set K))) huv
  simpa only [racl_union_left, Set.singleton_union] using h

/-- The same rank-two join has the shifted translation generator, with both directions derived. -/
private theorem affine_pair_shift (u v : K) (κ : k) :
    racl k ({u, v + (u - 1) * algebraMap k K κ} : Set K) =
      racl k ({u, v} : Set K) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · have hu : u ∈ racl k ({u, v} : Set K) := subset_racl k _ (Set.mem_insert _ _)
    have hv : v ∈ racl k ({u, v} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    exact Set.insert_subset_iff.2 ⟨hu, Set.singleton_subset_iff.2
      (add_mem hv (mul_mem (sub_mem hu (one_mem _)) ((racl k _).algebraMap_mem κ)))⟩
  · have hu : u ∈ racl k ({u, v + (u - 1) * algebraMap k K κ} : Set K) :=
      subset_racl k _ (Set.mem_insert _ _)
    have hv : v + (u - 1) * algebraMap k K κ ∈
        racl k ({u, v + (u - 1) * algebraMap k K κ} : Set K) :=
      subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    have h := sub_mem hv
      (mul_mem (sub_mem hu (one_mem _)) ((racl k _).algebraMap_mem κ))
    have hv0 : v ∈ racl k ({u, v + (u - 1) * algebraMap k K κ} : Set K) := by
      simpa only [add_sub_cancel_right] using h
    exact Set.insert_subset_iff.2 ⟨hu, Set.singleton_subset_iff.2 hv0⟩

/-- The first producer's four-coordinate independence is derived from the original chart. -/
private theorem original_P_tuple_independent {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    AlgebraicIndependent k ![a, b, x, c] := by
  classical
  let e : Fin 4 → Fin 5 := ![0, 1, 4, 2]
  have he : Function.Injective e := by decide
  have heq : (fun q : Fin 4 ↦ (![a, b, c, d, x] : Fin 5 → K) (e q)) =
      ![a, b, x, c] := by
    funext q
    fin_cases q <;> rfl
  exact heq ▸ hind.comp e he

/-- A base translation preserves a raw pair closure; used for original X/Y/Z incidences. -/
private theorem pair_translate (u v : K) (κ : k) :
    racl k ({u, v + algebraMap k K κ} : Set K) = racl k ({u, v} : Set K) := by
  have h := pair_closure_of_singleton_eq (racl_add_algebraMap (k := k) v κ) u
  simpa only [Set.pair_comm] using h

/-- Two actual family calls derive first P/D/F/R and then Q from raw original incidences.
Each original prime/span precedes ALL inputs of its own family. Actual transported i/e
incidences then derive G/H/I/E and final independence. No normal-form or output-freshness
oracle; k/ambient ACF, supplied INPUTs, strong Q-side NFs and raw i/e nonconstancy stay explicit.
Initial chart, actual guarded-Psi consequences, ambient existence/descent and completeness
remain open. -/
private theorem two_family_remaining_rows
    [IsAlgClosed k] [IsAlgClosed K] {a b c d x p δ f ρ q g h i e : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδa : δ ∉ racl k ({a} : Set K))
    (hδy : δ ∈ racl k ({p, a * x + b} : Set K)) (hf : f ∈ racl k ({c, δ} : Set K))
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K))
    (hρFZ : ρ ∈ racl k ({f, c * (a * x + b) + d} : Set K))
    (hρC : ρ ∈ racl k ({a * c, b * c + d} : Set K))
    (hρ0 : ρ ∉ racl k (∅ : Set K))
    (hqc : q ∈ racl k ({c, d} : Set K)) (hqT : q ∉ racl k ({c} : Set K))
    (hgPT : g ∈ racl k ({p, c} : Set K))
    (hgQR : g ∈ racl k ({q, ρ} : Set K)) (hgT : g ∉ racl k ({c} : Set K))
    (hhUG : h ∈ racl k ({a * c, g} : Set K))
    (hhA : h ∈ racl k ({a, b} : Set K)) (hhS : h ∉ racl k ({a} : Set K))
    (hiH : i ∈ racl k ({h, x} : Set K))
    (hiP : i ∈ racl k ({p, a * x + b} : Set K)) (hi0 : i ∉ racl k (∅ : Set K))
    (heT : e ∈ racl k ({c, a * x + b} : Set K))
    (heQ : e ∈ racl k ({q, c * (a * x + b) + d} : Set K))
    (he0 : e ∉ racl k (∅ : Set K)) :
    ∃ FP : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({f} : Set K)), Prime FP ∧
      idealOf ↥(IntermediateField.adjoin k ({f} : Set K)) ![a * c, x] = Ideal.span {FP} ∧
      ∀ tP : ℕ → K,
        (∀ n < 2 * FP.totalDegree + 1,
          tP n ∉ racl k ({a, b, x, c} ∪ tP '' Set.Iio n)) →
        ∃ κ : k, racl k ({p} : Set K) =
            racl k ({b + (a - 1) * algebraMap k K κ} : Set K) ∧
          racl k ({δ} : Set K) = racl k ({a * (x - algebraMap k K κ)} : Set K) ∧
          racl k ({f} : Set K) = racl k ({a * c * (x - algebraMap k K κ)} : Set K) ∧
          racl k ({ρ} : Set K) =
            racl k ({b * c + d + a * c * algebraMap k K κ} : Set K) ∧
          let B := b + (a - 1) * algebraMap k K κ
          let D := d + (c - 1) * algebraMap k K κ
          ∃ FQ : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({h⁻¹} : Set K)),
            Prime FQ ∧
            idealOf ↥(IntermediateField.adjoin k ({h⁻¹} : Set K)) ![a⁻¹, B] =
              Ideal.span {FQ} ∧
            ∀ tQ : ℕ → K,
              (∀ n < 2 * FQ.totalDegree + 1,
                tQ n ∉ racl k ({c, D, B, (a * c)⁻¹} ∪ tQ '' Set.Iio n)) →
              ∃ η : k, racl k ({q} : Set K) =
                  racl k ({D + (c - 1) * algebraMap k K η} : Set K) ∧
                AlgebraicIndependent k ![a, B - algebraMap k K η,
                  c, D + (c - 1) * algebraMap k K η, x - algebraMap k K κ] ∧
                racl k ({g} : Set K) = racl k ({(B - algebraMap k K η) * c} : Set K) ∧
                racl k ({h} : Set K) = racl k ({a / (B - algebraMap k K η)} : Set K) ∧
                racl k ({i} : Set K) =
                  racl k ({a * (x - algebraMap k K κ) / (B - algebraMap k K η)} : Set K) ∧
                racl k ({e} : Set K) =
                  racl k ({c * (a * (x - algebraMap k K κ) +
                    (B - algebraMap k K η))} : Set K) := by
  obtain ⟨FP, hFP, hSpanP, HP⟩ := racl_normalized_P_of_supplied_fresh_inputs
    (original_P_tuple_independent hind) hp hpa hδx hδa hδy hf hfm hfu
  refine ⟨FP, hFP, hSpanP, fun tP htP ↦ ?_⟩
  obtain ⟨κ, hP⟩ := HP tP htP
  have hRows := racl_shifted_D_F_R_of_normalized_P hind κ hP
    hδx hδy hδa hf hfm hfu hρFZ hρC hρ0
  have hStar := algebraicIndependent_table_shift hind κ
  let B := b + (a - 1) * algebraMap k K κ
  let D := d + (c - 1) * algebraMap k K κ
  have hA : racl k ({a, B} : Set K) = racl k ({a, b} : Set K) :=
    affine_pair_shift a b κ
  have hB : racl k ({c, D} : Set K) = racl k ({c, d} : Set K) :=
    affine_pair_shift c d κ
  have hqD : q ∈ racl k ({c, D} : Set K) := by
    rw [hB]
    exact hqc
  have hhAB : h ∈ racl k ({a, B} : Set K) := by
    rw [hA]
    exact hhA
  have hgBC : g ∈ racl k ({B, c} : Set K) := by
    rw [← pair_closure_of_singleton_eq hP c]
    exact hgPT
  have heq : b * c + d + a * c * algebraMap k K κ =
      (B * c + D) + algebraMap k K κ := by
    dsimp [B, D]
    ring
  have hρW : racl k ({ρ} : Set K) = racl k ({B * c + D} : Set K) :=
    hRows.2.2.trans (by rw [heq]; exact racl_add_algebraMap (B * c + D) κ)
  have hgQW : g ∈ racl k ({q, B * c + D} : Set K) := by
    have h : g ∈ racl k ({ρ, q} : Set K) := by
      simpa only [Set.pair_comm] using hgQR
    rw [pair_closure_of_singleton_eq hρW q] at h
    simpa only [Set.pair_comm] using h
  obtain ⟨FQ, hFQ, hSpanQ, HQ⟩ := reciprocal_Q_from_raw hStar
    hqD hqT hgBC hgQW hgT hhUG hhAB hhS
  refine ⟨κ, hP, hRows.1, hRows.2.1, hRows.2.2, FQ, hFQ, hSpanQ, fun tQ htQ ↦ ?_⟩
  obtain ⟨η, hQ⟩ := HQ tQ htQ
  have hFinal := algebraicIndependent_table_Q_shift hStar η
  have hx : x = (x - algebraMap k K κ) + algebraMap k K κ := by ring
  have hy : a * x + b =
      (a * (x - algebraMap k K κ) + B) + algebraMap k K κ := by
    dsimp [B]
    ring
  have hz : c * (a * x + b) + d =
      (c * (a * (x - algebraMap k K κ) + B) + D) + algebraMap k K κ := by
    dsimp [B, D]
    ring
  have hiHXstar : i ∈ racl k ({h, x - algebraMap k K κ} : Set K) := by
    have hI := hiH
    rw [hx, pair_translate] at hI
    exact hI
  have hiPstar : i ∈ racl k ({p, a * (x - algebraMap k K κ) + B} : Set K) := by
    have hI := hiP
    rw [hy, pair_translate] at hI
    exact hI
  have heTstar : e ∈ racl k ({c, a * (x - algebraMap k K κ) + B} : Set K) := by
    have hE := heT
    rw [hy, pair_translate] at hE
    exact hE
  have heQstar : e ∈ racl k
      ({q, c * (a * (x - algebraMap k K κ) + B) + D} : Set K) := by
    have hE := heQ
    rw [hz, pair_translate] at hE
    exact hE
  have hg0 : g ∉ racl k (∅ : Set K) :=
    fun h0 ↦ hgT (racl_mono (Set.empty_subset _) h0)
  have hh0 : h ∉ racl k (∅ : Set K) :=
    fun h0 ↦ hhS (racl_mono (Set.empty_subset _) h0)
  have hNew := racl_shifted_G_H_I_E_of_normalized_P_Q hStar η hP hQ hρW
    hgPT hgQR hg0 hhUG hhAB hh0 hiHXstar hiPstar hi0 heTstar heQstar he0
  exact ⟨η, hQ, hFinal, hNew.1, hNew.2.1, hNew.2.2.1, hNew.2.2.2⟩

/-- A point distinct from the chosen principal point has a representative outside it.
Consumed for P, D, F, Q, G and H; no field-level non-membership is supplied. -/
private theorem point_rep_notMem_of_ne {P S : Point k K} {s : K}
    (hS : S.1 = ClosedIF.point k s) (hPS : P ≠ S) :
    P.rep ∉ racl k ({s} : Set K) := by
  intro hmem
  have hle : P.1 ≤ S.1 := by
    rw [← P.point_rep, hS]
    exact ClosedIF.point_le_iff.2 (ClosedIF.mem_point.2 hmem)
  exact hPS (Subtype.ext ((S.2.le_iff_eq P.2.1).1 hle))

/-- An actual guarded Psi witness supplies every raw input of the two-family producer.
Initial AI5/chart and base/ambient ACF remain explicit; both original curves still precede ALL
supplied INPUT families. The chart's existence, input existence/enlargement/descent, combined
presentation, actions, extraction and completeness remain open. -/
private theorem guarded_two_family_rows [IsAlgClosed k] [IsAlgClosed K] {w : QWitness k K}
    (hw : w.Psi) (hID : w.I ≠ w.D) {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hA : w.A = ClosedIF.point k a ⊔ ClosedIF.point k b)
    (hB : w.B = ClosedIF.point k c ⊔ ClosedIF.point k d)
    (hC : w.C = ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d))
    (hS : w.S.1 = ClosedIF.point k a) (hT : w.T.1 = ClosedIF.point k c)
    (hU : w.U.1 = ClosedIF.point k (a * c)) (hX : w.X.1 = ClosedIF.point k x)
    (hY : w.Y.1 = ClosedIF.point k (a * x + b))
    (hZ : w.Z.1 = ClosedIF.point k (c * (a * x + b) + d)) :
    ∃ FP : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({w.F.rep} : Set K)), Prime FP ∧
      idealOf ↥(IntermediateField.adjoin k ({w.F.rep} : Set K)) ![a * c, x] = Ideal.span {FP} ∧
      ∀ tP : ℕ → K,
        (∀ n < 2 * FP.totalDegree + 1,
          tP n ∉ racl k ({a, b, x, c} ∪ tP '' Set.Iio n)) →
        ∃ κ : k, racl k ({w.P.rep} : Set K) =
            racl k ({b + (a - 1) * algebraMap k K κ} : Set K) ∧
          racl k ({w.D.rep} : Set K) = racl k ({a * (x - algebraMap k K κ)} : Set K) ∧
          racl k ({w.F.rep} : Set K) = racl k ({a * c * (x - algebraMap k K κ)} : Set K) ∧
          racl k ({w.R.rep} : Set K) =
            racl k ({b * c + d + a * c * algebraMap k K κ} : Set K) ∧
          let B := b + (a - 1) * algebraMap k K κ
          let D := d + (c - 1) * algebraMap k K κ
          ∃ FQ : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({w.H.rep⁻¹} : Set K)),
            Prime FQ ∧
            idealOf ↥(IntermediateField.adjoin k ({w.H.rep⁻¹} : Set K)) ![a⁻¹, B] =
              Ideal.span {FQ} ∧
            ∀ tQ : ℕ → K,
              (∀ n < 2 * FQ.totalDegree + 1,
                tQ n ∉ racl k ({c, D, B, (a * c)⁻¹} ∪ tQ '' Set.Iio n)) →
              ∃ η : k, racl k ({w.Q.rep} : Set K) =
                  racl k ({D + (c - 1) * algebraMap k K η} : Set K) ∧
                AlgebraicIndependent k ![a, B - algebraMap k K η,
                  c, D + (c - 1) * algebraMap k K η, x - algebraMap k K κ] ∧
                racl k ({w.G.rep} : Set K) = racl k ({(B - algebraMap k K η) * c} : Set K) ∧
                racl k ({w.H.rep} : Set K) = racl k ({a / (B - algebraMap k K η)} : Set K) ∧
                racl k ({w.I.rep} : Set K) =
                  racl k ({a * (x - algebraMap k K κ) / (B - algebraMap k K η)} : Set K) ∧
                racl k ({w.E.rep} : Set K) =
                  racl k ({c * (a * (x - algebraMap k K κ) +
                    (B - algebraMap k K η))} : Set K) := by
  have hp : w.P.rep ∈ racl k ({a, b} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hA]
    exact hw.P_le_A hID
  have hpa : w.P.rep ∉ racl k ({a} : Set K) :=
    point_rep_notMem_of_ne hS hw.P_ne_S
  have hδx : w.D.rep ∈ racl k ({a, x} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hw.meet_D, hS, hX]
    exact inf_le_right
  have hδa : w.D.rep ∉ racl k ({a} : Set K) :=
    point_rep_notMem_of_ne hS (hw.D_ne_S hID)
  have hδy : w.D.rep ∈ racl k ({w.P.rep, a * x + b} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.P.point_rep, ← hw.meet_D, hY]
    exact inf_le_left
  have hf : w.F.rep ∈ racl k ({c, w.D.rep} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.D.point_rep, ← hw.meet_F, hT]
    exact inf_le_right
  have hfm : w.F.rep ∈ racl k ({a * c, x} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hw.meet_F, hU, hX]
    exact inf_le_left
  have hfu : w.F.rep ∉ racl k ({a * c} : Set K) :=
    point_rep_notMem_of_ne hU (hw.F_ne_U hID)
  have hρFZ : w.R.rep ∈ racl k ({w.F.rep, c * (a * x + b) + d} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.F.point_rep, ← hw.meet_R, hZ]
    exact inf_le_left
  have hρC : w.R.rep ∈ racl k ({a * c, b * c + d} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hw.meet_R, hC]
    exact inf_le_right
  have hρ0 : w.R.rep ∉ racl k (∅ : Set K) := point_rep_notMem_empty w.R
  have hqc : w.Q.rep ∈ racl k ({c, d} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hB]
    exact hw.Q_le_B
  have hqT : w.Q.rep ∉ racl k ({c} : Set K) :=
    point_rep_notMem_of_ne hT (hw.Q_ne_T hID)
  have hgPT : w.G.rep ∈ racl k ({w.P.rep, c} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.P.point_rep, ← hw.meet_G, hT]
    exact inf_le_left
  have hgQR : w.G.rep ∈ racl k ({w.Q.rep, w.R.rep} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.Q.point_rep, w.R.point_rep, ← hw.meet_G]
    exact inf_le_right
  have hgT : w.G.rep ∉ racl k ({c} : Set K) :=
    point_rep_notMem_of_ne hT (hw.G_ne_T hID)
  have hhUG : w.H.rep ∈ racl k ({a * c, w.G.rep} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.G.point_rep, ← hw.meet_H, hU]
    exact inf_le_left
  have hhA : w.H.rep ∈ racl k ({a, b} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hw.meet_H, hA]
    exact inf_le_right
  have hhS : w.H.rep ∉ racl k ({a} : Set K) :=
    point_rep_notMem_of_ne hS (hw.H_ne_S hID)
  have hiH : w.I.rep ∈ racl k ({w.H.rep, x} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.H.point_rep, ← hw.meet_I, hX]
    exact inf_le_left
  have hiP : w.I.rep ∈ racl k ({w.P.rep, a * x + b} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.P.point_rep, ← hw.meet_I, hY]
    exact inf_le_right
  have hi0 : w.I.rep ∉ racl k (∅ : Set K) := point_rep_notMem_empty w.I
  have heT : w.E.rep ∈ racl k ({c, a * x + b} : Set K) := by
    apply point_rep_mem_of_le
    rw [← hw.meet_E, hT, hY]
    exact inf_le_left
  have heQ : w.E.rep ∈ racl k ({w.Q.rep, c * (a * x + b) + d} : Set K) := by
    apply point_rep_mem_of_le
    rw [w.Q.point_rep, ← hw.meet_E, hZ]
    exact inf_le_right
  have he0 : w.E.rep ∉ racl k (∅ : Set K) := point_rep_notMem_empty w.E
  exact two_family_remaining_rows hind hp hpa hδx hδa hδy hf hfm hfu
    hρFZ hρC hρ0 hqc hqT hgPT hgQR hgT hhUG hhA hhS hiH hiP hi0 heT heQ he0

/-- A point whose representative is interalgebraic with `u` is the principal point of `u`. -/
private theorem point_eq_of_rep_racl_eq {P : Point k K} {u : K}
    (h : racl k ({P.rep} : Set K) = racl k ({u} : Set K)) : P.1 = ClosedIF.point k u :=
  P.point_rep.symm.trans (Subtype.ext h)

/-- Elements differing by an element algebraic over `k` have the same principal point. -/
private theorem point_eq_point_of_sub_mem {v v' : K} (h : v - v' ∈ racl k (∅ : Set K)) :
    ClosedIF.point k v = ClosedIF.point k v' := by
  have hv : v ∈ racl k ({v} : Set K) := subset_racl k _ rfl
  have hv' : v' ∈ racl k ({v'} : Set K) := subset_racl k _ rfl
  refine ClosedIF.point_eq_point_iff.2 ⟨?_, ?_⟩
  · rw [ClosedIF.mem_point]
    have hmem := add_mem hv' (racl_mono (Set.empty_subset _) h)
    have heq : v' + (v - v') = v := by ring
    rwa [heq] at hmem
  · rw [ClosedIF.mem_point]
    have hmem := sub_mem hv (racl_mono (Set.empty_subset _) h)
    have heq : v - (v - v') = v' := by ring
    rwa [heq] at hmem

/-- Moving the second generator of a join by an element algebraic over the first generator
does not change the join. -/
private theorem sup_point_eq_of_sub_mem {u v v' : K} (h : v' - v ∈ racl k ({u} : Set K)) :
    ClosedIF.point k u ⊔ ClosedIF.point k v = ClosedIF.point k u ⊔ ClosedIF.point k v' := by
  have hsub (z : K) : racl k ({u} : Set K) ≤ racl k ({u, z} : Set K) :=
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hu (z : K) : u ∈ racl k ({u, z} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hz (z : K) : z ∈ racl k ({u, z} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact ClosedIF.point_le_iff.2 (ClosedIF.mem_sup_point_iff.2 (hu v'))
  · refine ClosedIF.point_le_iff.2 (ClosedIF.mem_sup_point_iff.2 ?_)
    have hmem := sub_mem (hz v') (hsub v' h)
    have heq : v' - (v' - v) = v := by ring
    rwa [heq] at hmem
  · exact ClosedIF.point_le_iff.2 (ClosedIF.mem_sup_point_iff.2 (hu v))
  · refine ClosedIF.point_le_iff.2 (ClosedIF.mem_sup_point_iff.2 ?_)
    have hmem := add_mem (hz v) (hsub v h)
    have heq : v + (v' - v) = v' := by ring
    rwa [heq] at hmem

/-- The table rows give affine-grid coordinates.  They are stated for independent variables, so
the identification with the fields of `qWitness` happens once, at the level of atoms. -/
private theorem hasAffineGridCoordinates_of_rows {w : QWitness k K} {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hA : w.A = ClosedIF.point k a ⊔ ClosedIF.point k b)
    (hB : w.B = ClosedIF.point k c ⊔ ClosedIF.point k d)
    (hC : w.C = ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d))
    (hD : w.D.1 = ClosedIF.point k (a * x))
    (hE : w.E.1 = ClosedIF.point k (c * (a * x + b)))
    (hF : w.F.1 = ClosedIF.point k (a * c * x)) (hG : w.G.1 = ClosedIF.point k (b * c))
    (hH : w.H.1 = ClosedIF.point k (a / b)) (hI : w.I.1 = ClosedIF.point k (a * x / b))
    (hP : w.P.1 = ClosedIF.point k b) (hQ : w.Q.1 = ClosedIF.point k d)
    (hR : w.R.1 = ClosedIF.point k (b * c + d)) (hS : w.S.1 = ClosedIF.point k a)
    (hT : w.T.1 = ClosedIF.point k c) (hU : w.U.1 = ClosedIF.point k (a * c))
    (hX : w.X.1 = ClosedIF.point k x) (hY : w.Y.1 = ClosedIF.point k (a * x + b))
    (hZ : w.Z.1 = ClosedIF.point k (c * (a * x + b) + d)) :
    w.HasAffineGridCoordinates :=
  ⟨a, b, c, d, x, hind, hA, hB, hC, Subtype.ext hD, Subtype.ext hE, Subtype.ext hF,
    Subtype.ext hG, Subtype.ext hH, Subtype.ext hI, Subtype.ext hP, Subtype.ext hQ,
    Subtype.ext hR, Subtype.ext hS, Subtype.ext hT, Subtype.ext hU, Subtype.ext hX,
    Subtype.ext hY, Subtype.ext hZ⟩

/-- The final rows give affine-grid coordinates in the chart
`a, b + (a - 1) t - s, c, d + (c - 1) t + (c - 1) s, x - t` for constants `t` and `s`.  The joins
and the points `P, R, X, Y, Z` are moved from the initial chart by elements algebraic over the
base or over the first generator. -/
private theorem hasAffineGridCoordinates_of_final_rows {w : QWitness k K} {a b c d x t s : K}
    (ht : t ∈ racl k (∅ : Set K)) (hs : s ∈ racl k (∅ : Set K))
    (hA : w.A = ClosedIF.point k a ⊔ ClosedIF.point k b)
    (hB : w.B = ClosedIF.point k c ⊔ ClosedIF.point k d)
    (hC : w.C = ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d))
    (hS : w.S.1 = ClosedIF.point k a) (hT : w.T.1 = ClosedIF.point k c)
    (hU : w.U.1 = ClosedIF.point k (a * c)) (hX : w.X.1 = ClosedIF.point k x)
    (hY : w.Y.1 = ClosedIF.point k (a * x + b))
    (hZ : w.Z.1 = ClosedIF.point k (c * (a * x + b) + d))
    (hFinal : AlgebraicIndependent k
      ![a, b + (a - 1) * t - s, c, d + (c - 1) * t + (c - 1) * s, x - t])
    (hP : racl k ({w.P.rep} : Set K) = racl k ({b + (a - 1) * t} : Set K))
    (hD : racl k ({w.D.rep} : Set K) = racl k ({a * (x - t)} : Set K))
    (hF : racl k ({w.F.rep} : Set K) = racl k ({a * c * (x - t)} : Set K))
    (hR : racl k ({w.R.rep} : Set K) = racl k ({b * c + d + a * c * t} : Set K))
    (hQ : racl k ({w.Q.rep} : Set K) = racl k ({d + (c - 1) * t + (c - 1) * s} : Set K))
    (hG : racl k ({w.G.rep} : Set K) = racl k ({(b + (a - 1) * t - s) * c} : Set K))
    (hH : racl k ({w.H.rep} : Set K) = racl k ({a / (b + (a - 1) * t - s)} : Set K))
    (hI : racl k ({w.I.rep} : Set K) =
      racl k ({a * (x - t) / (b + (a - 1) * t - s)} : Set K))
    (hE : racl k ({w.E.rep} : Set K) =
      racl k ({c * (a * (x - t) + (b + (a - 1) * t - s))} : Set K)) :
    w.HasAffineGridCoordinates := by
  have htS (S : Set K) : t ∈ racl k S := racl_mono (Set.empty_subset S) ht
  have hsS (S : Set K) : s ∈ racl k S := racl_mono (Set.empty_subset S) hs
  -- The joins: each second generator moves by an element algebraic over the first.
  have hA' : w.A = ClosedIF.point k a ⊔ ClosedIF.point k (b + (a - 1) * t - s) := by
    have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
    have hdiff : b + (a - 1) * t - s - b = (a - 1) * t - s := by ring
    have hmem : b + (a - 1) * t - s - b ∈ racl k ({a} : Set K) := by
      rw [hdiff]
      exact sub_mem (mul_mem (sub_mem ha (one_mem _)) (htS _)) (hsS _)
    rw [hA]
    exact sup_point_eq_of_sub_mem hmem
  have hB' : w.B =
      ClosedIF.point k c ⊔ ClosedIF.point k (d + (c - 1) * t + (c - 1) * s) := by
    have hc : c ∈ racl k ({c} : Set K) := subset_racl k _ rfl
    have hdiff : d + (c - 1) * t + (c - 1) * s - d = (c - 1) * t + (c - 1) * s := by ring
    have hmem : d + (c - 1) * t + (c - 1) * s - d ∈ racl k ({c} : Set K) := by
      rw [hdiff]
      exact add_mem (mul_mem (sub_mem hc (one_mem _)) (htS _))
        (mul_mem (sub_mem hc (one_mem _)) (hsS _))
    rw [hB]
    exact sup_point_eq_of_sub_mem hmem
  have hC' : w.C = ClosedIF.point k (a * c) ⊔
      ClosedIF.point k ((b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s)) := by
    have hac : a * c ∈ racl k ({a * c} : Set K) := subset_racl k _ rfl
    have hdiff : (b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s) - (b * c + d) =
        a * c * t - t - s := by ring
    have hmem : (b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s) - (b * c + d) ∈
        racl k ({a * c} : Set K) := by
      rw [hdiff]
      exact sub_mem (sub_mem (mul_mem hac (htS _)) (htS _)) (hsS _)
    rw [hC]
    exact sup_point_eq_of_sub_mem hmem
  -- The points `P, R, X, Y, Z`: each moves by an element algebraic over `k`.
  have hP' : w.P.1 = ClosedIF.point k (b + (a - 1) * t - s) := by
    have hdiff : b + (a - 1) * t - (b + (a - 1) * t - s) = s := by ring
    have hmem : b + (a - 1) * t - (b + (a - 1) * t - s) ∈ racl k (∅ : Set K) := by
      rw [hdiff]
      exact hs
    rw [point_eq_of_rep_racl_eq hP]
    exact point_eq_point_of_sub_mem hmem
  have hR' : w.R.1 =
      ClosedIF.point k ((b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s)) := by
    have hdiff : b * c + d + a * c * t -
        ((b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s)) = t + s := by ring
    have hmem : b * c + d + a * c * t -
        ((b + (a - 1) * t - s) * c + (d + (c - 1) * t + (c - 1) * s)) ∈
          racl k (∅ : Set K) := by
      rw [hdiff]
      exact add_mem ht hs
    rw [point_eq_of_rep_racl_eq hR]
    exact point_eq_point_of_sub_mem hmem
  have hX' : w.X.1 = ClosedIF.point k (x - t) := by
    have hdiff : x - (x - t) = t := by ring
    have hmem : x - (x - t) ∈ racl k (∅ : Set K) := by
      rw [hdiff]
      exact ht
    rw [hX]
    exact point_eq_point_of_sub_mem hmem
  have hY' : w.Y.1 = ClosedIF.point k (a * (x - t) + (b + (a - 1) * t - s)) := by
    have hdiff : a * x + b - (a * (x - t) + (b + (a - 1) * t - s)) = t + s := by ring
    have hmem : a * x + b - (a * (x - t) + (b + (a - 1) * t - s)) ∈
        racl k (∅ : Set K) := by
      rw [hdiff]
      exact add_mem ht hs
    rw [hY]
    exact point_eq_point_of_sub_mem hmem
  have hZ' : w.Z.1 = ClosedIF.point k
      (c * (a * (x - t) + (b + (a - 1) * t - s)) + (d + (c - 1) * t + (c - 1) * s)) := by
    have hdiff : c * (a * x + b) + d -
        (c * (a * (x - t) + (b + (a - 1) * t - s)) + (d + (c - 1) * t + (c - 1) * s)) =
          t + s := by ring
    have hmem : c * (a * x + b) + d -
        (c * (a * (x - t) + (b + (a - 1) * t - s)) + (d + (c - 1) * t + (c - 1) * s)) ∈
          racl k (∅ : Set K) := by
      rw [hdiff]
      exact add_mem ht hs
    rw [hZ]
    exact point_eq_point_of_sub_mem hmem
  exact hasAffineGridCoordinates_of_rows hFinal hA' hB' hC' (point_eq_of_rep_racl_eq hD)
    (point_eq_of_rep_racl_eq hE) (point_eq_of_rep_racl_eq hF) (point_eq_of_rep_racl_eq hG)
    (point_eq_of_rep_racl_eq hH) (point_eq_of_rep_racl_eq hI) hP'
    (point_eq_of_rep_racl_eq hQ) hR' hS hT hU hX' hY' hZ'

namespace QWitness

/-- **Affine-grid coordinates from an explicit chart and supplied inputs** (#27, P4).  Let `w`
satisfy `Ψ` and `I ≠ D` over algebraically closed `k ⊆ K`.  Let independent `a, b, c, d, x` give
the joins `A, B, C` and the points `S, T, U, X, Y, Z` of the table.  The original prime curve of
`F` and its span precede the first family of fresh inputs; the original prime curve of `H⁻¹` and
its span precede the second.  After both families, `w` has affine-grid coordinates.  The chart,
the input families and algebraic closedness are hypotheses; their existence is not proved. -/
theorem Psi.hasAffineGridCoordinates_of_chart_supplied_inputs [IsAlgClosed k] [IsAlgClosed K]
    {w : QWitness k K} (hw : w.Psi) (hID : w.I ≠ w.D) {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x])
    (hA : w.A = ClosedIF.point k a ⊔ ClosedIF.point k b)
    (hB : w.B = ClosedIF.point k c ⊔ ClosedIF.point k d)
    (hC : w.C = ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d))
    (hS : w.S.1 = ClosedIF.point k a) (hT : w.T.1 = ClosedIF.point k c)
    (hU : w.U.1 = ClosedIF.point k (a * c)) (hX : w.X.1 = ClosedIF.point k x)
    (hY : w.Y.1 = ClosedIF.point k (a * x + b))
    (hZ : w.Z.1 = ClosedIF.point k (c * (a * x + b) + d)) :
    ∃ FP : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({w.F.rep} : Set K)), Prime FP ∧
      idealOf ↥(IntermediateField.adjoin k ({w.F.rep} : Set K)) ![a * c, x] = Ideal.span {FP} ∧
      ∀ tP : ℕ → K,
        (∀ n < 2 * FP.totalDegree + 1, tP n ∉ racl k ({a, b, x, c} ∪ tP '' Set.Iio n)) →
        ∃ κ : k,
          ∃ FQ : MvPolynomial (Fin 2) ↥(IntermediateField.adjoin k ({w.H.rep⁻¹} : Set K)),
            Prime FQ ∧
            idealOf ↥(IntermediateField.adjoin k ({w.H.rep⁻¹} : Set K))
              ![a⁻¹, b + (a - 1) * algebraMap k K κ] = Ideal.span {FQ} ∧
            ∀ tQ : ℕ → K,
              (∀ n < 2 * FQ.totalDegree + 1,
                tQ n ∉ racl k ({c, d + (c - 1) * algebraMap k K κ,
                  b + (a - 1) * algebraMap k K κ, (a * c)⁻¹} ∪ tQ '' Set.Iio n)) →
              w.HasAffineGridCoordinates := by
  obtain ⟨FP, hFP, hSpanP, HP⟩ :=
    guarded_two_family_rows hw hID hind hA hB hC hS hT hU hX hY hZ
  refine ⟨FP, hFP, hSpanP, fun tP htP ↦ ?_⟩
  obtain ⟨κ, hP, hD, hF, hR, FQ, hFQ, hSpanQ, HQ⟩ := HP tP htP
  refine ⟨κ, FQ, hFQ, hSpanQ, fun tQ htQ ↦ ?_⟩
  obtain ⟨η, hQ, hFinal, hG, hH, hI, hE⟩ := HQ tQ htQ
  exact hasAffineGridCoordinates_of_final_rows (t := algebraMap k K κ) (s := algebraMap k K η)
    ((racl k (∅ : Set K)).algebraMap_mem κ) ((racl k (∅ : Set K)).algebraMap_mem η)
    hA hB hC hS hT hU hX hY hZ hFinal hP hD hF hR hQ hG hH hI hE

end QWitness

end AclGeom
