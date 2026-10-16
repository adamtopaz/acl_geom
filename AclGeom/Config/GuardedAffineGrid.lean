/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import GroupConfig.FiniteIncidenceDescent
import GroupConfig.ChartAssembly
import GroupConfig.BaseClosure
import GroupConfig.ConfigurationBaseChange
import AclGeom.Config.UniversalConfigurationInput
import AclGeom.Config.Transport
import AclGeom.Transfer.LiftConfig
import AclGeom.Config.AffineGridNormalization

/-!
# Guarded affine-grid extraction over algebraically closed pairs

The actual Ψ witness yields the nine initial chart rows through its rank-two HW action.
Move the finite witness to make the coefficient field fresh, then descend the finite
polynomial closure table coherently to the original field. The actual Ψ rank clauses
make its five coordinates independent; the existing chart normalization supplies the
remaining rows. Both guards `I ≠ D` and `I ≠ P` remain visible in the public result.

**Status:** `GuardedAffineGridExtraction` and `GuardedQCompletenessACF` are proved for
every algebraically closed pair, with no universal-domain or supplied-chart hypothesis.
The original scheme/action bridge and bypassed source statements remain obligations.
-/

namespace AclGeom

open GroupConfig Set MvPolynomial

noncomputable section

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]

private def initialChartPolynomials (k : Type*) [Field k] :
    Fin 9 → Fin 2 → MvPolynomial (Fin 5) k :=
  ![![X 0, X 1], ![X 2, X 3], ![X 0 * X 2, X 1 * X 2 + X 3],
    ![X 0, X 0], ![X 2, X 2], ![X 0 * X 2, X 0 * X 2], ![X 4, X 4],
    ![X 0 * X 4 + X 1, X 0 * X 4 + X 1],
    ![X 2 * (X 0 * X 4 + X 1) + X 3, X 2 * (X 0 * X 4 + X 1) + X 3]]

private def initialWitnessPolynomials (k : Type*) [Field k] :
    Fin 9 → Fin 2 → MvPolynomial (Fin 21) k :=
  ![![X 0, X 1], ![X 2, X 3], ![X 4, X 5], ![X 15, X 15], ![X 16, X 16],
    ![X 17, X 17], ![X 18, X 18], ![X 19, X 19], ![X 20, X 20]]

private def initialChartValues {F : Type*} [Field F] (v : Fin 5 → F) : Fin 9 → Fin 2 → F :=
  ![![v 0, v 1], ![v 2, v 3], ![v 0 * v 2, v 1 * v 2 + v 3],
    ![v 0, v 0], ![v 2, v 2], ![v 0 * v 2, v 0 * v 2], ![v 4, v 4],
    ![v 0 * v 4 + v 1, v 0 * v 4 + v 1],
    ![v 2 * (v 0 * v 4 + v 1) + v 3, v 2 * (v 0 * v 4 + v 1) + v 3]]

private def initialWitnessValues (w : QWitness k K) : Fin 9 → Fin 2 → K :=
  ![![w.A₁.rep, w.A₂.rep], ![w.B₁.rep, w.B₂.rep], ![w.C₁.rep, w.C₂.rep],
    ![w.S.rep, w.S.rep], ![w.T.rep, w.T.rep], ![w.U.rep, w.U.rep],
    ![w.X.rep, w.X.rep], ![w.Y.rep, w.Y.rep], ![w.Z.rep, w.Z.rep]]

private theorem aeval_initialChartPolynomials {F : Type*} [Field F] [Algebra k F]
    (v : Fin 5 → F) (j : Fin 9) (i : Fin 2) :
    aeval v (initialChartPolynomials k j i) = initialChartValues v j i := by
  fin_cases j <;> fin_cases i <;>
    simp [initialChartPolynomials, initialChartValues]

private theorem aeval_initialWitnessPolynomials (f : K →ₐ[k] Ω) (w : QWitness k K)
    (j : Fin 9) (i : Fin 2) :
    aeval (f ∘ w.repTuple) (initialWitnessPolynomials k j i) =
      f (initialWitnessValues w j i) := by
  fin_cases j <;> fin_cases i <;>
    simp [initialWitnessPolynomials, initialWitnessValues, QWitness.repTuple,
      Function.comp_def]

/-- The two-generator row equality is precisely equality of the displayed joins. -/
private theorem pair_point_eq_of_racl (P Q : Point k K) (a b : K)
    (h : racl k (range (![P.rep, Q.rep] : Fin 2 → K)) =
      racl k (range (![a, b] : Fin 2 → K))) :
    P.1 ⊔ Q.1 = ClosedIF.point k a ⊔ ClosedIF.point k b := by
  rw [Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty,
    ← coe_sup_point₂, ← coe_sup_point₂, P.point_rep, Q.point_rep] at h
  exact Subtype.ext h

/-- A duplicated singleton row gives equality of the original point with its coordinate. -/
private theorem single_point_eq_of_racl (P : Point k K) (a : K)
    (h : racl k (range (![P.rep, P.rep] : Fin 2 → K)) =
      racl k (range (![a, a] : Fin 2 → K))) : P.1 = ClosedIF.point k a := by
  simpa only [sup_idem] using pair_point_eq_of_racl P P a a h

/-- The actual nine-row affine chart descends to the original algebraically closed ambient
field through any embedding in a universal domain. All finite formulas and the original-field
coordinate point are produced internally; the five coordinates are independent by actual Ψ. -/
private theorem initialChart_descent [IsAlgClosed k] [IsAlgClosed K] [IsAlgClosed Ω]
    [UniversalDomain k Ω] {w : QWitness k K} (hw : w.Psi) (hID : w.I ≠ w.D)
    (f : K →ₐ[k] Ω) (L : IntermediateField k Ω)
    (hL : IndepOver k ∅ (L : Set Ω) (range (f ∘ w.repTuple)))
    (v : Fin 5 → Ω)
    (hrows : ∀ j : Fin 9, racl (↥L) (range (f ∘ initialWitnessValues w j)) =
      racl (↥L) (range (initialChartValues v j))) : w.HasAffineGridCoordinates := by
  have htable (j : Fin 9) :
      racl (↥L) (range fun i ↦ aeval (f ∘ w.repTuple) (initialWitnessPolynomials k j i)) =
        racl (↥L) (range fun i ↦ aeval v (initialChartPolynomials k j i)) := by
    have hl : (fun i ↦ aeval (f ∘ w.repTuple) (initialWitnessPolynomials k j i)) =
        f ∘ initialWitnessValues w j := by
      funext i
      exact aeval_initialWitnessPolynomials f w j i
    have hr : (fun i ↦ aeval v (initialChartPolynomials k j i)) =
        initialChartValues v j := by
      funext i
      exact aeval_initialChartPolynomials v j i
    rw [hl, hr]
    exact hrows j
  obtain ⟨v₀, hv₀⟩ := GroupConfig.exists_polynomial_closure_table_descent_to
    f L w.repTuple v hL (initialWitnessPolynomials k) (initialChartPolynomials k) htable
  have htable₀ (j : Fin 9) : racl k (range (initialWitnessValues w j)) =
      racl k (range (initialChartValues v₀ j)) := by
    have he (i : Fin 2) : aeval w.repTuple (initialWitnessPolynomials k j i) =
        initialWitnessValues w j i := by
      simpa only [AlgHom.id_apply, AlgHom.coe_id, Function.id_comp] using
        aeval_initialWitnessPolynomials (AlgHom.id k K) w j i
    simpa only [he, aeval_initialChartPolynomials] using hv₀ j
  have hA : w.A = ClosedIF.point k (v₀ 0) ⊔ ClosedIF.point k (v₀ 1) :=
    pair_point_eq_of_racl w.A₁ w.A₂ _ _ (htable₀ 0)
  have hB : w.B = ClosedIF.point k (v₀ 2) ⊔ ClosedIF.point k (v₀ 3) :=
    pair_point_eq_of_racl w.B₁ w.B₂ _ _ (htable₀ 1)
  have hC : w.C = ClosedIF.point k (v₀ 0 * v₀ 2) ⊔
      ClosedIF.point k (v₀ 1 * v₀ 2 + v₀ 3) :=
    pair_point_eq_of_racl w.C₁ w.C₂ _ _ (htable₀ 2)
  have hS : w.S.1 = ClosedIF.point k (v₀ 0) := single_point_eq_of_racl w.S _ (htable₀ 3)
  have hT : w.T.1 = ClosedIF.point k (v₀ 2) := single_point_eq_of_racl w.T _ (htable₀ 4)
  have hU : w.U.1 = ClosedIF.point k (v₀ 0 * v₀ 2) := single_point_eq_of_racl w.U _ (htable₀ 5)
  have hX : w.X.1 = ClosedIF.point k (v₀ 4) := single_point_eq_of_racl w.X _ (htable₀ 6)
  have hY : w.Y.1 = ClosedIF.point k (v₀ 0 * v₀ 4 + v₀ 1) :=
    single_point_eq_of_racl w.Y _ (htable₀ 7)
  have hZ : w.Z.1 = ClosedIF.point k (v₀ 2 * (v₀ 0 * v₀ 4 + v₀ 1) + v₀ 3) :=
    single_point_eq_of_racl w.Z _ (htable₀ 8)
  have hXnot : ¬ w.X.1 ≤ w.A ⊔ w.B := fun h ↦ hw.X_notLe (h.trans le_sup_left)
  have hrank : RankEq 5 (w.A ⊔ w.B ⊔ w.X.1) := hw.rank_AB.sup_point_of_not_le hXnot
  have hspan : w.A ⊔ w.B ⊔ w.X.1 = ⨆ i : Fin 5, ClosedIF.point k (v₀ i) := by
    rw [hA, hB, hX]
    apply le_antisymm
    · refine sup_le (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) ?_
      · exact le_iSup_of_le 0 le_rfl
      · exact le_iSup_of_le 1 le_rfl
      · exact le_iSup_of_le 2 le_rfl
      · exact le_iSup_of_le 3 le_rfl
      · exact le_iSup_of_le 4 le_rfl
    · refine iSup_le fun i ↦ ?_
      fin_cases i
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
      · exact le_sup_of_le_left (le_sup_of_le_right le_sup_left)
      · exact le_sup_of_le_left (le_sup_of_le_right le_sup_right)
      · exact le_sup_right
  have hi : AlgebraicIndependent k v₀ :=
    algebraicIndependent_of_rankEq_iSup_point (hspan ▸ hrank)
  have hiv : AlgebraicIndependent k ![v₀ 0, v₀ 1, v₀ 2, v₀ 3, v₀ 4] := by
    convert hi using 1
    ext i
    fin_cases i <;> rfl
  exact hw.hasAffineGridCoordinates_of_chart hID hiv hA hB hC hS hT hU hX hY hZ

/-- Lift a point into an extension and retain the original base through the carrier-preserving
base-closure equivalence. -/
private def liftPointSameBase (f : K →ₐ[k] Ω) (P : Point k K) : Point k Ω :=
  Point.map (ClosedIF.baseClosureEquiv k Ω)
    (liftPoint (fun _ hz ↦ isAlgebraic_of_mem_racl_empty hz) f P)

/-- The chosen representative of the same-base lift is interalgebraic with the literal image
of the original representative. No equality of arbitrary representative choices is asserted. -/
private theorem liftPointSameBase_racl (f : K →ₐ[k] Ω) (P : Point k K) :
    racl k ({(liftPointSameBase f P).rep} : Set Ω) = racl k ({f P.rep} : Set Ω) := by
  have hP : (liftPointSameBase f P).1 = ClosedIF.point k (f P.rep) := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change ((liftClosed (racl k (∅ : Set Ω)) f P.1).1 : Set Ω) = _
    rw [← P.point_rep, liftClosed_point (fun _ hz ↦ isAlgebraic_of_mem_racl_empty hz) f]
    exact racl_baseClosure_coe _
  exact congrArg Subtype.val ((liftPointSameBase f P).point_rep.trans hP)

/-- The lifted witness expressed over the same base field. -/
private def liftWitnessSameBase (f : K →ₐ[k] Ω) (w : QWitness k K) : QWitness k Ω :=
  (w.lift (fun _ hz ↦ isAlgebraic_of_mem_racl_empty hz) f).map
    (ClosedIF.baseClosureEquiv k Ω)

/-- Full Ψ, including the universal atom clauses, survives the same-base lift. -/
private theorem liftWitnessSameBase_psi [IsAlgClosed Ω] (f : K →ₐ[k] Ω) {w : QWitness k K}
    (hw : w.Psi) : (liftWitnessSameBase f w).Psi :=
  (hw.lift (fun _ hz ↦ isAlgebraic_of_mem_racl_empty hz) f).map
    (ClosedIF.baseClosureEquiv k Ω)

private def witnessPoints (w : QWitness k K) : Fin 21 → Point k K :=
  ![w.A₁, w.A₂, w.B₁, w.B₂, w.C₁, w.C₂, w.D, w.E, w.F, w.G, w.H, w.I,
    w.P, w.Q, w.R, w.S, w.T, w.U, w.X, w.Y, w.Z]

private theorem repTuple_eq_witnessPoints (w : QWitness k K) :
    w.repTuple = fun i ↦ (witnessPoints w i).rep := by
  funext i
  fin_cases i <;> rfl

private theorem witnessPoints_liftSame (f : K →ₐ[k] Ω) (w : QWitness k K) (i : Fin 21) :
    witnessPoints (liftWitnessSameBase f w) i = liftPointSameBase f (witnessPoints w i) := by
  fin_cases i <;> rfl

/-- Every lifted representative is interalgebraic over the original base with its literal
embedded source. This also controls freshness of all twenty-one representatives jointly. -/
private theorem liftWitnessSameBase_rep_racl (f : K →ₐ[k] Ω) (w : QWitness k K) (i : Fin 21) :
    racl k ({(liftWitnessSameBase f w).repTuple i} : Set Ω) =
      racl k ({f (w.repTuple i)} : Set Ω) := by
  rw [repTuple_eq_witnessPoints, repTuple_eq_witnessPoints]
  change racl k ({(witnessPoints (liftWitnessSameBase f w) i).rep} : Set Ω) = _
  rw [witnessPoints_liftSame]
  exact liftPointSameBase_racl f (witnessPoints w i)

/-- Pointwise interalgebraicity of two tuples gives equality of their joint closures. -/
private theorem racl_range_congr_singletons {ι : Type*} (a b : ι → K)
    (h : ∀ i, racl k ({a i} : Set K) = racl k ({b i} : Set K)) :
    racl k (range a) = racl k (range b) := by
  apply racl_congr_of_subset_racl
  · rintro _ ⟨i, rfl⟩
    apply racl_mono (singleton_subset_iff.2 (mem_range_self i))
    rw [← h i]
    exact subset_racl k _ rfl
  · rintro _ ⟨i, rfl⟩
    apply racl_mono (singleton_subset_iff.2 (mem_range_self i))
    rw [h i]
    exact subset_racl k _ rfl


private def initialWitnessIndices : Fin 9 → Fin 2 → Fin 21 :=
  ![![0, 1], ![2, 3], ![4, 5], ![15, 15], ![16, 16], ![17, 17],
    ![18, 18], ![19, 19], ![20, 20]]

private theorem initialWitnessValues_eq_repTuple (w : QWitness k K) (j : Fin 9) (i : Fin 2) :
    initialWitnessValues w j i = w.repTuple (initialWitnessIndices j i) := by
  fin_cases j <;> fin_cases i <;> rfl

/-- A moved chart of the actual lifted witness gives the full original-field grid. Both
the lift's arbitrary representatives and the automorphism are absorbed by the embedding;
freshness and all nine row equalities are transported using actual closure identities. -/
private theorem initialChart_descent_of_lift [IsAlgClosed k] [IsAlgClosed K] [IsAlgClosed Ω]
    [UniversalDomain k Ω] {w : QWitness k K} (hw : w.Psi) (hID : w.I ≠ w.D)
    (f : K →ₐ[k] Ω) (σ : Ω ≃ₐ[k] Ω) (L : IntermediateField k Ω)
    (hL : IndepOver k ∅ (L : Set Ω) (range (σ ∘ (liftWitnessSameBase f w).repTuple)))
    (v : Fin 5 → Ω)
    (hrows : ∀ j : Fin 9,
      racl (↥L) (range (σ ∘ initialWitnessValues (liftWitnessSameBase f w) j)) =
        racl (↥L) (range (initialChartValues v j))) : w.HasAffineGridCoordinates := by
  let q := liftWitnessSameBase f w
  let g := σ.toAlgHom.comp f
  have hscalar (i : Fin 21) : racl k ({σ (q.repTuple i)} : Set Ω) =
      racl k ({g (w.repTuple i)} : Set Ω) := by
    have h := congrArg (fun E : IntermediateField k Ω ↦ E.map σ.toAlgHom)
      (liftWitnessSameBase_rep_racl f w i)
    rw [racl_map, racl_map, image_singleton, image_singleton] at h
    exact h
  have htuple : racl k (range (σ ∘ q.repTuple)) = racl k (range (g ∘ w.repTuple)) :=
    racl_range_congr_singletons _ _ hscalar
  have hLg : IndepOver k ∅ (L : Set Ω) (range (g ∘ w.repTuple)) :=
    (indepOver_congr₀ rfl htuple).1 hL
  apply initialChart_descent hw hID g L hLg v
  intro j
  have hj : racl k (range (σ ∘ initialWitnessValues q j)) =
      racl k (range (g ∘ initialWitnessValues w j)) := by
    apply racl_range_congr_singletons
    intro i
    change racl k ({σ (initialWitnessValues q j i)} : Set Ω) =
      racl k ({g (initialWitnessValues w j i)} : Set Ω)
    rw [initialWitnessValues_eq_repTuple, initialWitnessValues_eq_repTuple]
    exact hscalar (initialWitnessIndices j i)
  exact (GroupConfig.racl_base_congr L hj).symm.trans (hrows j)

/-- The guarded extraction theorem over arbitrary algebraically closed pairs. The actual
group chart, its coefficient field, the universal lift and the original-field coordinates are
all constructed internally. Both stated output guards remain visible. -/
theorem guardedAffineGridExtraction [IsAlgClosed k] [IsAlgClosed K] :
    GuardedAffineGridExtraction k K := by
  intro w hw hID _hIP
  let Ω := ConfigurationAmbient K
  let f : K →ₐ[k] Ω := configurationEmbedding k K
  let q := liftWitnessSameBase f w
  have hq : q.Psi := liftWitnessSameBase_psi f hw
  obtain ⟨σ, L, hL, a, b, c, d, x, hA, hB, hC, hS, hT, hU, hX, hY, hZ⟩ :=
    hq.exists_initial_chart_rows
  apply initialChart_descent_of_lift hw hID f σ L hL ![a, b, c, d, x]
  simp only [Matrix.range_cons_cons_empty] at hA hB hC
  have hrange (p q : Ω) : range (σ ∘ (![p, q] : Fin 2 → Ω)) = {σ p, σ q} := by
    have he : σ ∘ (![p, q] : Fin 2 → Ω) = ![σ p, σ q] := by
      funext i
      fin_cases i <;> rfl
    rw [he, Matrix.range_cons_cons_empty]
  intro j
  fin_cases j
  · change racl (↥L) (range (σ ∘ (![q.A₁.rep, q.A₂.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![a, b] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    exact hA
  · change racl (↥L) (range (σ ∘ (![q.B₁.rep, q.B₂.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![c, d] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    exact hB
  · change racl (↥L) (range (σ ∘ (![q.C₁.rep, q.C₂.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![a * c, b * c + d] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    exact hC
  · change racl (↥L) (range (σ ∘ (![q.S.rep, q.S.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![a, a] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hS
  · change racl (↥L) (range (σ ∘ (![q.T.rep, q.T.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![c, c] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hT
  · change racl (↥L) (range (σ ∘ (![q.U.rep, q.U.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![a * c, a * c] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hU
  · change racl (↥L) (range (σ ∘ (![q.X.rep, q.X.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![x, x] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hX
  · change racl (↥L) (range (σ ∘ (![q.Y.rep, q.Y.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![a * x + b, a * x + b] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hY
  · change racl (↥L) (range (σ ∘ (![q.Z.rep, q.Z.rep] : Fin 2 → Ω))) =
      racl (↥L) (range (![c * (a * x + b) + d, c * (a * x + b) + d] : Fin 2 → Ω))
    rw [hrange, Matrix.range_cons_cons_empty]
    simpa only [Set.pair_eq_singleton] using hZ

/-- Guarded witness-level Q completeness follows from the actual extracted grid. -/
theorem guardedQCompletenessACF [IsAlgClosed k] [IsAlgClosed K] :
    GuardedQCompletenessACF k K :=
  fun _ hw hID hIP ↦ QWitness.qSem_of_hasAffineGridCoordinates
    (guardedAffineGridExtraction _ hw hID hIP)

end

end AclGeom
