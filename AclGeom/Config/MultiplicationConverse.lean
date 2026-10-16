/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Multiplication
import AclGeom.Config.Semantic
import AclGeom.Config.MeetEquations
import AclGeom.Correspondence.AmbientAutomorphism
import AclGeom.Correspondence.Multiplicative
import AclGeom.Correspondence.MultiplierDescent
import AclGeom.Correspondence.PartialQuadrangle
import AclGeom.Geometry.Representatives
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The coordinates of a multiplication diagram

Over an algebraically closed ambient field of transcendence degree at least
five, an actual multiplication diagram whose ratio comes from a semantic `Q`
quadruple has the semantic product output. The proof fixes the closed field
of two corners, relocates the auxiliary point, and applies the multiplicative
correspondence theorem. Two product meets and exchange descend the result
from the fresh parameter field to the original base.

Coherent specialization to the original base then produces the full auxiliary
coordinate table when the base is algebraically closed. This proves both
converse clauses of blueprint Lemma `mul-diagram` under the stated ACF and
rank-five hypotheses. Guarded geometric `Q` completeness is proved in `Config.GuardedAffineGrid`;
together these give rank-five ACF `Q′` and `J` correctness in `Config.Completeness`.
The original group-extraction statements remain separate source obligations.
-/

namespace AclGeom

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Changing the base to an intermediate field adds that field's elements
to the closure parameters. This isolates the dependent field rewrite. -/
private theorem mem_racl_intermediate_base_iff (E : IntermediateField k K)
    {S : Set K} {x : K} :
    x ∈ racl ↥E S ↔ x ∈ racl k ((E : Set K) ∪ S) := by
  let Result (F : IntermediateField k K) : Prop :=
    x ∈ racl ↥F S ↔ x ∈ racl k ((E : Set K) ∪ S)
  have h : Result (adjoin k (E : Set K)) := mem_racl_adjoin_base_iff
  have hfinal : Result E := (adjoin_self k E) ▸ h
  exact hfinal

/-- Over a closed parameter field, base change is exactly adjoining the
original parameters to the closure. Used at both auxiliary closed bases. -/
private theorem mem_racl_closed_base_iff {P S : Set K} {x : K} :
    x ∈ racl ↥(racl k P) S ↔ x ∈ racl k (P ∪ S) := by
  rw [mem_racl_intermediate_base_iff, racl_union_left]

/-- Equal literal products in the multiplicative correspondence theorem
force a common scalar ratio algebraic over the base. No coprime-exponent
or separability assumption is needed. -/
private theorem common_ratio_of_mul_eq [IsAlgClosed k] [IsAlgClosed K]
    (S : MulCorrSetup k K) {s : K} (hs : s ∉ racl k {S.x₁, S.x₂})
    (hmul : S.x₁ * S.x₂ = S.y₁ * S.y₂) :
    S.x₁ / S.y₁ ∈ racl k (∅ : Set K) := by
  obtain ⟨p, q, c₁, c₂, hp, hq, -, -, h₁, h₂⟩ := S.exists_coset_equations hs
  have hprod : S.x₁ * S.x₂ ∉ racl k (∅ : Set K) := by
    intro h
    apply AlgebraicIndependent.notMem_racl_pair' S.indep
    have hm := racl_mono (Set.empty_subset ({S.x₂} : Set K)) h
    have hx₂ := subset_racl k ({S.x₂} : Set K) rfl
    have heq : S.x₁ = S.x₁ * S.x₂ / S.x₂ := by
      rw [mul_div_cancel_right₀ _ S.x₂_ne]
    rw [heq]
    exact div_mem hm hx₂
  have hpower : (S.x₁ * S.x₂) ^ (p + q) = algebraMap k K (c₁ * c₂) := by
    calc
      (S.x₁ * S.x₂) ^ (p + q) =
          (S.x₁ * S.x₂) ^ p * (S.y₁ * S.y₂) ^ q := by
        rw [← hmul, zpow_add₀ S.mul_fst_ne]
      _ = (S.x₁ ^ p * S.y₁ ^ q) * (S.x₂ ^ p * S.y₂ ^ q) := by
        simp only [mul_zpow]
        ring
      _ = algebraMap k K (c₁ * c₂) := by rw [h₁, h₂, map_mul]
  have hsum : p + q = 0 := by
    by_contra hne
    apply hprod (mem_racl_empty_of_zpow hne ?_)
    rw [hpower]
    exact IntermediateField.algebraMap_mem _ _
  have hq' : q = -p := by omega
  have hr : (S.x₁ / S.y₁) ^ p = algebraMap k K c₁ := by
    rw [div_zpow, div_eq_mul_inv, ← zpow_neg, ← hq']
    exact h₁
  apply mem_racl_empty_of_zpow hp
  rw [hr]
  exact IntermediateField.algebraMap_mem _ _

/-- Arbitrary representatives of distinct geometric points are independent
in the direction needed for line exchange. -/
private theorem notMem_of_distinct_points {P Q : Point k K} {p q : K}
    (hP : P.1 = ClosedIF.point k p) (hQ : Q.1 = ClosedIF.point k q)
    (hPQ : P ≠ Q) : p ∉ racl k {q} := by
  intro hp
  have hle : P.1 ≤ Q.1 := by
    rw [hP, hQ]
    exact ClosedIF.point_le_iff.mpr hp
  exact hPQ (Subtype.ext ((Q.2.le_iff_eq P.2.1).mp hle))

/-- The third coordinate on an actual rank-two line is algebraic over
either pair of distinct coordinates, independently of representative choices. -/
private theorem third_mem_of_line {P Q R : Point k K} {p q r : K}
    (hP : P.1 = ClosedIF.point k p) (hQ : Q.1 = ClosedIF.point k q)
    (hR : R.1 = ClosedIF.point k r) (hPQ : P ≠ Q)
    (hline : RankEq 2 (P.1 ⊔ (Q.1 ⊔ R.1))) : r ∈ racl k {p, q} := by
  have heq := pair_sup_eq_triple_of_rankEq_two hPQ hline
  have hle : R.1 ≤ P.1 ⊔ Q.1 := by
    rw [heq]
    exact le_sup_of_le_right le_sup_right
  rw [hP, hQ, hR] at hle
  exact ClosedIF.mem_sup_point_iff.mp (ClosedIF.point_le_iff.mp hle)

/-- The literal multiplication diagram supplies all finite incidences used
by the fixed-field automorphism proof. No product-form correspondence is assumed. -/
private theorem multiplication_incidence_data {X Y V E A B C D : Point k K}
    (h : MulDiagram X Y V E A B C D) {x y : K}
    (hX : X.1 = ClosedIF.point k x) (hY : Y.1 = ClosedIF.point k y)
    (hV : V.1 = ClosedIF.point k (x / y)) :
    AlgebraicIndependent k ![A.rep, x, y] ∧
      B.rep ∈ racl k {A.rep, x} ∧ x ∈ racl k {A.rep, B.rep} ∧
      C.rep ∈ racl k {A.rep, y} ∧ y ∈ racl k {A.rep, C.rep} ∧
      x / y ∈ racl k {B.rep, C.rep} ∧
      D.rep ∈ racl k {B.rep, y} ∧ D.rep ∈ racl k {x, C.rep} ∧
      E.rep ∈ racl k {A.rep, D.rep} ∧ E.rep ∈ racl k {x, y} ∧
      x ∉ racl k {B.rep} := by
  have hAI : AlgebraicIndependent k ![A.rep, x, y] := by
    apply algebraicIndependent_of_rankEq_iSup_point
    apply RankEq.congr _ h.rank_XYA
    calc
      X.1 ⊔ (Y.1 ⊔ A.1) =
          ClosedIF.point k A.rep ⊔ (ClosedIF.point k x ⊔ ClosedIF.point k y) := by
        rw [hX, hY, A.point_rep]
        ac_rfl
      _ = ⨆ i, (![ClosedIF.point k A.rep, ClosedIF.point k x,
          ClosedIF.point k y] : Fin 3 → ClosedIF k K) i := sup_eq_iSup_three _ _ _
      _ = ⨆ i, ClosedIF.point k ((![A.rep, x, y] : Fin 3 → K) i) := by
        congr 1
        funext i
        fin_cases i <;> rfl
  have hXA : X ≠ A := by simpa using h.distinct.ne (show (0 : Fin 8) ≠ 4 by decide)
  have hAB : A ≠ B := by simpa using h.distinct.ne (show (4 : Fin 8) ≠ 5 by decide)
  have hAY : A ≠ Y := by simpa using h.distinct.ne (show (4 : Fin 8) ≠ 1 by decide)
  have hAC : A ≠ C := by simpa using h.distinct.ne (show (4 : Fin 8) ≠ 6 by decide)
  have hBC : B ≠ C := by simpa using h.distinct.ne (show (5 : Fin 8) ≠ 6 by decide)
  have hBY : B ≠ Y := by simpa using h.distinct.ne (show (5 : Fin 8) ≠ 1 by decide)
  have hXC : X ≠ C := by simpa using h.distinct.ne (show (0 : Fin 8) ≠ 6 by decide)
  have hAD : A ≠ D := by simpa using h.distinct.ne (show (4 : Fin 8) ≠ 7 by decide)
  have hXY : X ≠ Y := by simpa using h.distinct.ne (show (0 : Fin 8) ≠ 1 by decide)
  have hXB : X ≠ B := by simpa using h.distinct.ne (show (0 : Fin 8) ≠ 5 by decide)
  refine ⟨hAI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply third_mem_of_line A.point_rep.symm hX B.point_rep.symm hXA.symm
    simpa [sup_assoc, sup_comm, sup_left_comm] using h.line_XAB
  · apply third_mem_of_line A.point_rep.symm B.point_rep.symm hX hAB
    simpa [sup_assoc, sup_comm, sup_left_comm] using h.line_XAB
  · exact third_mem_of_line A.point_rep.symm hY C.point_rep.symm hAY h.line_AYC
  · apply third_mem_of_line A.point_rep.symm C.point_rep.symm hY hAC
    simpa [sup_assoc, sup_comm, sup_left_comm] using h.line_AYC
  · exact third_mem_of_line B.point_rep.symm C.point_rep.symm hV hBC h.line_BCV
  · exact third_mem_of_line B.point_rep.symm hY D.point_rep.symm hBY h.line_BYD
  · exact third_mem_of_line hX C.point_rep.symm D.point_rep.symm hXC h.line_XCD
  · apply third_mem_of_line A.point_rep.symm D.point_rep.symm E.point_rep.symm hAD
    simpa [sup_assoc, sup_comm, sup_left_comm] using h.line_AED
  · have heq : X.1 ⊔ Y.1 = X.1 ⊔ (Y.1 ⊔ (E.1 ⊔ V.1)) :=
      RankEq.eq_of_le (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
        (rankEq_two_sup_of_ne hXY) h.line_XYEV
    have hle : E.1 ≤ X.1 ⊔ Y.1 := by
      rw [heq]
      exact le_sup_of_le_right (le_sup_of_le_right le_sup_left)
    rw [hX, hY, ← E.point_rep] at hle
    exact ClosedIF.mem_sup_point_iff.mp (ClosedIF.point_le_iff.mp hle)
  · exact notMem_of_distinct_points hX B.point_rep.symm hXB

/-- Retaining a nonzero factor permits multiplication of the other
generator without changing the two-generator closure. Used in both meets. -/
private theorem product_pair_closure {u v : K} (hv : v ≠ 0) :
    racl k {u * v, v} = racl k {u, v} := by
  apply racl_congr_of_subset_racl
  · refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact mul_mem (subset_racl k ({u, v} : Set K) (Set.mem_insert _ _))
        (subset_racl k ({u, v} : Set K) (Set.mem_insert_of_mem _ rfl))
    · exact subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  · refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · have hu := subset_racl k ({u * v, v} : Set K) (Set.mem_insert _ _)
      have hv' := subset_racl k ({u * v, v} : Set K) (Set.mem_insert_of_mem _ rfl)
      simpa [mul_div_cancel_right₀ _ hv] using div_mem hu hv'
    · exact subset_racl k _ (Set.mem_insert_of_mem _ rfl)

/-- The two oblique product planes meet in their common product point.
The established birational-independence and closure-exchange APIs supply
the argument; no scheme or group extraction is used. -/
private theorem mem_racl_product_meet {a x y d : K}
    (h : AlgebraicIndependent k ![a, x, y])
    (h₁ : d ∈ racl k {a * x, y}) (h₂ : d ∈ racl k {x, a * y}) :
    d ∈ racl k {a * x * y} := by
  have hax := algebraicIndependent_mul_left h
  have hperm := hax.comp (![0, 2, 1] : Fin 3 → Fin 3) (by decide)
  have haxy : AlgebraicIndependent k ![a * x, y, x] := by
    convert hperm using 1
    funext i
    fin_cases i <;> rfl
  have hm := algebraicIndependent_mul_left haxy
  have hx : x ∉ racl k {y, a * x * y} := by
    have hi := AlgebraicIndependent.notMem_racl_image hm (S := {0, 1}) (i := 2) (by decide)
    simpa [Set.image_insert_eq, Set.pair_comm] using hi
  have hd₁ : d ∈ racl k {y, a * x * y} := by
    rw [Set.pair_comm, product_pair_closure (u := a * x) (v := y) (h.ne_zero 2)]
    exact h₁
  have hd₂ : d ∈ racl k {x, a * x * y} := by
    have heq : racl k {x, a * x * y} = racl k {x, a * y} := by
      rw [Set.pair_comm]
      convert product_pair_closure (u := a * y) (h.ne_zero 1) using 1 <;>
        simp [Set.pair_comm, mul_comm, mul_left_comm]
    rw [heq]
    exact h₂
  exact mem_racl_of_mem_racl_insert hd₁ hd₂ hx

/-- The plane of the auxiliary parameter and product meets the bottom
plane precisely in the product point. This removes the multiplier from
that meet; descent from the auxiliary base field is a separate exchange step. -/
private theorem mem_racl_bottom_product_meet {a x y e : K}
    (h : AlgebraicIndependent k ![a, x, y])
    (h₁ : e ∈ racl k {a, x * y}) (h₂ : e ∈ racl k {x, y}) :
    e ∈ racl k {x * y} := by
  have hp := h.comp (![2, 1, 0] : Fin 3 → Fin 3) (by decide)
  have hyxa : AlgebraicIndependent k ![y, x, a] := by
    convert hp using 1
    funext i
    fin_cases i <;> rfl
  have hm := algebraicIndependent_mul_left hyxa
  have hx : x ∉ racl k {a, x * y} := by
    have hi := AlgebraicIndependent.notMem_racl_image hm (S := {0, 2}) (i := 1) (by decide)
    simpa [Set.image_insert_eq, Set.pair_comm, mul_comm] using hi
  have he₂ : e ∈ racl k {x, x * y} := by
    have heq : racl k {x, x * y} = racl k {x, y} := by
      rw [Set.pair_comm]
      convert product_pair_closure (u := y) (h.ne_zero 1) using 1 <;>
        simp [Set.pair_comm, mul_comm]
    rw [heq]
    exact h₂
  exact mem_racl_of_mem_racl_insert h₁ he₂ hx

/-- The last two entries of an independent four-tuple stay independent
over the closed field of the first two entries. -/
private theorem independent_over_closed_pair {a a₀ x y : K}
    (h : AlgebraicIndependent k ![a, a₀, x, y]) :
    AlgebraicIndependent ↥(racl k {a, a₀}) ![x, y] := by
  apply algebraicIndependent_pair
  · intro hx
    rw [mem_racl_closed_base_iff] at hx
    have hi := AlgebraicIndependent.notMem_racl_image h (S := {0, 1, 3}) (i := 2) (by decide)
    apply hi
    have hset : ({a, a₀} : Set K) ∪ {y} =
        (![a, a₀, x, y] : Fin 4 → K) '' {0, 1, 3} := by
      ext z
      simp [Set.image_insert_eq]; tauto
    exact hset ▸ hx
  · intro hy
    rw [mem_racl_closed_base_iff] at hy
    have hi := AlgebraicIndependent.notMem_racl_image h (S := {0, 1, 2}) (i := 3) (by decide)
    apply hi
    have hset : ({a, a₀} : Set K) ∪ {x} =
        (![a, a₀, x, y] : Fin 4 → K) '' {0, 1, 2} := by
      ext z
      simp [Set.image_insert_eq]; tauto
    exact hset ▸ hy

/-- A generic change of the auxiliary coordinate fixes the entire closed
field of the two intermediate corners, and thus also their semantic ratio.
This uses an actual ambient automorphism rather than a conjugate branch. -/
private theorem exists_fixed_bc_automorphism [IsAlgClosed K] {a b c a₀ : K}
    (h : AlgebraicIndependent k ![a, b, c])
    (ha₀ : a₀ ∉ racl k {a, b, c}) :
    ∃ σ : K ≃ₐ[k] K, σ a = a₀ ∧
      ∀ z ∈ racl k {b, c}, σ z = z := by
  let E₀ := racl k ({b, c} : Set K)
  have ha : a ∉ racl k {b, c} := by
    have hi := AlgebraicIndependent.notMem_racl_image h (S := {1, 2}) (i := 0) (by decide)
    simpa [Set.image_insert_eq] using hi
  have ha₀' : a₀ ∉ racl k {b, c} :=
    fun hx ↦ ha₀ (racl_mono (by intro z hz; simp_all) hx)
  have hA : AlgebraicIndependent ↥E₀ ![a] := by
    rw [algebraicIndependent_unique_type_iff]
    change Transcendental ↥E₀ a
    intro hx
    have hm := mem_racl_empty_of_isAlgebraic hx
    rw [mem_racl_closed_base_iff, Set.union_empty] at hm
    exact ha hm
  have hA₀ : AlgebraicIndependent ↥E₀ ![a₀] := by
    rw [algebraicIndependent_unique_type_iff]
    change Transcendental ↥E₀ a₀
    intro hx
    have hm := mem_racl_empty_of_isAlgebraic hx
    rw [mem_racl_closed_base_iff, Set.union_empty] at hm
    exact ha₀' hm
  have hI : idealOf ↥E₀ ![a] = idealOf ↥E₀ ![a₀] := by
    rw [(idealOf_eq_bot_iff ↥E₀).mpr hA, (idealOf_eq_bot_iff ↥E₀).mpr hA₀]
  obtain ⟨τ, -, hτ⟩ := exists_ambientAutomorphism_of_idealOf_eq hI
  let σ : K ≃ₐ[k] K := τ.restrictScalars k
  refine ⟨σ, hτ 0, ?_⟩
  intro z hz
  exact τ.commutes (⟨z, hz⟩ : E₀)

/-- Closed parameter fields in an algebraically closed ambient field are
algebraically closed. The multiplicative theorem consumes this at its base. -/
private theorem isAlgClosed_closed_parameters [IsAlgClosed K] (P : Set K) :
    IsAlgClosed ↥(racl k P) := by
  apply (IsAlgClosed.algebraicClosure_eq_bot_iff ↥(racl k P) K).mp
  apply bot_unique
  intro x hx
  exact IntermediateField.mem_bot.mpr
    ⟨⟨x, isRAC_racl P x (mem_algebraicClosure_iff.mp hx)⟩, rfl⟩

/-- The genuine rank-five hypothesis supplies a fresh element over the
closed two-parameter field and two additional coordinates. -/
private theorem exists_fresh_over_closed_pair (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (a a₀ x y : K) : ∃ s, s ∉ racl ↥(racl k {a, a₀}) {x, y} := by
  classical
  obtain ⟨s, hs⟩ := fresh_four_of_five_le_trdeg htr {a, a₀, x, y} Finset.card_le_four
  refine ⟨s, ?_⟩
  intro hm
  rw [mem_racl_closed_base_iff] at hm
  apply hs
  have hset : ({a, a₀} : Set K) ∪ {x, y} =
      (({a, a₀, x, y} : Finset K) : Set K) := by
    ext z
    simp; tauto
  rw [← hset]
  exact hm

/-- A literal fixed-corner relocation of the ratio diagram supplies an
actual multiplicative correspondence over the two auxiliary parameters.
Its equal products derive a scaling ratio in their closed field. -/
private theorem common_ratio_of_fixed_relocation [IsAlgClosed K]
    {a a₀ b c x y : K} (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (h : AlgebraicIndependent k ![a, a₀, b, c])
    (hxy : AlgebraicIndependent k ![x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (σ : K ≃ₐ[k] K) (ha : σ a = a₀) (hb : σ b = b) (hc : σ c = c)
    (hv : σ (x / y) = x / y) : σ x / x ∈ racl k {a, a₀} := by
  classical
  let E := racl k ({a, a₀} : Set K)
  let : IsAlgClosed E := isAlgClosed_closed_parameters _
  have hxb₀ : σ x ∈ racl k {a₀, b} := by
    simpa [Set.image_insert_eq, ha, hb] using mem_racl_map σ hxb
  have hbx₀ : b ∈ racl k {a₀, σ x} := by
    simpa [Set.image_insert_eq, ha, hb] using mem_racl_map σ hbx
  have hyc₀ : σ y ∈ racl k {a₀, c} := by
    simpa [Set.image_insert_eq, ha, hc] using mem_racl_map σ hyc
  have hcy₀ : c ∈ racl k {a₀, σ y} := by
    simpa [Set.image_insert_eq, ha, hc] using mem_racl_map σ hcy
  have hxB : x ∈ racl E {b} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hxb
  have hBx : b ∈ racl E {x} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hbx
  have hyC : y ∈ racl E {c} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hyc
  have hCy : c ∈ racl E {y} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hcy
  have hx₀B : σ x ∈ racl E {b} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hxb₀
  have hBx₀ : b ∈ racl E {σ x} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hbx₀
  have hy₀C : σ y ∈ racl E {c} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hyc₀
  have hCy₀ : c ∈ racl E {σ y} := by
    rw [mem_racl_closed_base_iff]
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hcy₀
  have hBC : AlgebraicIndependent E ![b, c] := independent_over_closed_pair h
  have hXY₀ : AlgebraicIndependent E ![σ x, y] := by
    apply (algebraicIndependent_congr_racl (v := ![b, c]) (w := ![σ x, y]) ?_).mp hBC
    intro i
    fin_cases i
    · exact racl_singleton_congr hBx₀ hx₀B
    · exact racl_singleton_congr hCy hyC
  have hx : x ≠ 0 := hxy.ne_zero 0
  have hy : y ≠ 0 := hxy.ne_zero 1
  have hy₀ : σ y ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hy
  have hprod : σ x * y = x * σ y := by
    have heq : σ x / σ y = x / y := by rwa [map_div₀] at hv
    exact (div_eq_div_iff hy₀ hy).mp heq
  let S : MulCorrSetup E K := {
    x₁ := σ x, y₁ := x, x₂ := y, y₂ := σ y
    indep := hXY₀, y₁_ne := hx, y₂_ne := hy₀
    y₁_mem := racl_le_of_subset_racl (Set.singleton_subset_iff.mpr hBx₀) hxB
    x₁_mem := racl_le_of_subset_racl (Set.singleton_subset_iff.mpr hBx) hx₀B
    y₂_mem := racl_le_of_subset_racl (Set.singleton_subset_iff.mpr hCy) hy₀C
    x₂_mem := racl_le_of_subset_racl (Set.singleton_subset_iff.mpr hCy₀) hyC
    mul_mem := hprod ▸ subset_racl E {σ x * y} rfl
    mul_mem' := hprod.symm ▸ subset_racl E {x * σ y} rfl }
  obtain ⟨s, hsE⟩ := exists_fresh_over_closed_pair htr a a₀ (σ x) y
  have halg := common_ratio_of_mul_eq S hsE hprod
  rw [mem_racl_closed_base_iff, Set.union_empty] at halg
  exact halg

/-- The actual two finite incidences replace the semantic coordinates by
the intermediate corners without changing the rank-three closed field. -/
private theorem incidence_corners_independent {a b c x y : K}
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c}) :
    AlgebraicIndependent k ![a, b, c] ∧
      racl k {a, b, c} = racl k {a, x, y} := by
  have ha := subset_racl k (Set.range ![a, x, y]) ⟨0, rfl⟩
  have hx := subset_racl k (Set.range ![a, x, y]) ⟨1, rfl⟩
  have hy := subset_racl k (Set.range ![a, x, y]) ⟨2, rfl⟩
  have ha' := subset_racl k (Set.range ![a, b, c]) ⟨0, rfl⟩
  have hb' := subset_racl k (Set.range ![a, b, c]) ⟨1, rfl⟩
  have hc' := subset_racl k (Set.range ![a, b, c]) ⟨2, rfl⟩
  have heq : racl k (Set.range ![a, x, y]) = racl k (Set.range ![a, b, c]) := by
    apply racl_range_eq_of_mem
    · intro i
      fin_cases i
      · exact ha
      · exact racl_le_of_subset_racl
          (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hx⟩) hbx
      · exact racl_le_of_subset_racl
          (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hy⟩) hcy
    · intro i
      fin_cases i
      · exact ha'
      · exact racl_le_of_subset_racl
          (Set.insert_subset_iff.mpr ⟨ha', Set.singleton_subset_iff.mpr hb'⟩) hxb
      · exact racl_le_of_subset_racl
          (Set.insert_subset_iff.mpr ⟨ha', Set.singleton_subset_iff.mpr hc'⟩) hyc
  refine ⟨AlgebraicIndependent.of_racl_range_eq h heq, ?_⟩
  simpa only [range_triple] using heq.symm

/-- Extend a genuine independent corner triple by a fresh coordinate,
in the order consumed by the closed two-parameter scaling argument. -/
private theorem independent_four_of_fresh_three {a b c a₀ : K}
    (h : AlgebraicIndependent k ![a, b, c]) (ha₀ : a₀ ∉ racl k {a, b, c}) :
    AlgebraicIndependent k ![a, a₀, b, c] := by
  have hrange : Set.range ![a, b, c] = ({a, b, c} : Set K) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]; tauto
  have hs := algebraicIndependent_snoc h (by rwa [hrange])
  have h4 : AlgebraicIndependent k ![a, b, c, a₀] := by
    convert hs using 1
    funext i
    fin_cases i <;> rfl
  have hp := h4.comp (![0, 3, 1, 2] : Fin 4 → Fin 4) (by decide)
  convert hp using 1
  funext i
  fin_cases i <;> rfl

/-- The last three independent coordinates stay independent over the
closed field of the first coordinate. Used for the fresh-base normalization. -/
private theorem independent_over_closed_singleton {a₀ a x y : K}
    (h : AlgebraicIndependent k ![a₀, a, x, y]) :
    AlgebraicIndependent ↥(racl k {a₀}) ![a, x, y] := by
  rw [algebraicIndependent_iff_forall_notMem_racl]
  intro i hm
  rw [mem_racl_closed_base_iff] at hm
  have hnot : i.succ ∉ insert (0 : Fin 4) (Fin.succ '' ({i}ᶜ : Set (Fin 3))) := by
    rintro (hi | ⟨j, hj, hji⟩)
    · exact Fin.succ_ne_zero i hi
    · exact hj (by simpa only [Set.mem_singleton_iff] using Fin.succ_inj.mp hji)
  have hi := AlgebraicIndependent.notMem_racl_image h hnot
  have hcomp : (![a₀, a, x, y] : Fin 4 → K) ∘ Fin.succ = ![a, x, y] := by
    funext j
    fin_cases j <;> rfl
  have hset : (![a₀, a, x, y] : Fin 4 → K) ''
      insert 0 (Fin.succ '' ({i}ᶜ : Set (Fin 3))) =
      ({a₀} : Set K) ∪ (![a, x, y] '' ({i}ᶜ : Set (Fin 3))) := by
    rw [Set.image_insert_eq, Set.image_image]
    change insert a₀ (((![a₀, a, x, y] : Fin 4 → K) ∘ Fin.succ) '' {i}ᶜ) = _
    rw [hcomp, Set.singleton_union]
  apply hi
  rw [hset]
  simpa only [Matrix.cons_val_succ] using hm

/-- A nontrivial fixed-corner relocation cannot have its ratio in the
fresh parameter field: the two independent presentations would then identify
the original coordinate with its distinct intermediate corner. -/
private theorem ratio_notMem_fresh_base {a a₀ b x x₀ : K}
    (hxb : x ∈ racl k {a, b}) (hx₀b : x₀ ∈ racl k {a₀, b})
    (ha₀ : a₀ ∉ racl k {a, b}) (hxb' : x ∉ racl k {b})
    (hx : x ≠ 0) (hx₀ : x₀ ≠ 0) : x₀ / x ∉ racl k {a₀} := by
  intro hratio
  have hr : x₀ / x ∈ racl k {a₀, b} :=
    racl_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hratio
  have hx' : x ∈ racl k {a₀, b} := by
    have heq : x₀ / (x₀ / x) = x := by field_simp
    have hm := div_mem hx₀b hr
    rwa [heq] at hm
  exact hxb' (mem_racl_of_mem_racl_insert hxb hx' ha₀)

/-- The actual ratio incidences admit simultaneous product coordinates
over one fresh closed parameter field. The common multiplier and its
independence are derived from the fixed-field automorphism and the proved
multiplicative correspondence theorem. -/
private theorem exists_normalized_corners [IsAlgClosed K] {a b c x y : K}
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (hv : x / y ∈ racl k {b, c}) (hxb' : x ∉ racl k {b}) :
    ∃ a₀ α : K, a₀ ∉ racl k {a, x, y} ∧
      AlgebraicIndependent ↥(racl k {a₀}) ![α, x, y] ∧
      a ∈ racl ↥(racl k {a₀}) {α} ∧
      b ∈ racl ↥(racl k {a₀}) {α * x} ∧
      c ∈ racl ↥(racl k {a₀}) {α * y} := by
  classical
  obtain ⟨habc, hclosed⟩ := incidence_corners_independent h hbx hxb hcy hyc
  obtain ⟨a₀, ha₀⟩ := fresh_three_of_five_le_trdeg htr {a, b, c} Finset.card_le_three
  have ha₀' : a₀ ∉ racl k {a, b, c} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using ha₀
  have ha₀xy : a₀ ∉ racl k {a, x, y} := by rwa [← hclosed]
  have h4bc := independent_four_of_fresh_three habc ha₀'
  have h4xy' := independent_four_of_fresh_three h ha₀xy
  have hp := h4xy'.comp (![1, 0, 2, 3] : Fin 4 → Fin 4) (by decide)
  have h4xy : AlgebraicIndependent k ![a₀, a, x, y] := by
    convert hp using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨σ, hσa, hfix⟩ := exists_fixed_bc_automorphism habc ha₀'
  have hσb := hfix b (subset_racl k _ (Set.mem_insert _ _))
  have hσc := hfix c (subset_racl k _ (Set.mem_insert_of_mem _ rfl))
  have hσv := hfix (x / y) hv
  have hxy : AlgebraicIndependent k ![x, y] := AlgebraicIndependent.pair_one_two h
  let α := σ x / x
  have hα : α ∈ racl k {a, a₀} :=
    common_ratio_of_fixed_relocation htr h4bc hxy hbx hxb hcy hyc σ hσa hσb hσc hσv
  have hσxb : σ x ∈ racl k {a₀, b} := by
    simpa [Set.image_insert_eq, hσa, hσb] using mem_racl_map σ hxb
  have ha₀ab : a₀ ∉ racl k {a, b} := by
    intro hm
    apply ha₀'
    exact racl_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hm
  have hx : x ≠ 0 := hxy.ne_zero 0
  have hy : y ≠ 0 := hxy.ne_zero 1
  have hx₀ : σ x ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hx
  have hy₀ : σ y ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hy
  have hαnot : α ∉ racl k {a₀} :=
    ratio_notMem_fresh_base hxb hσxb ha₀ab hxb' hx hx₀
  let k₀ := racl k ({a₀} : Set K)
  have hαa : α ∈ racl k₀ {a} := by
    rw [mem_racl_closed_base_iff]
    simpa [Set.singleton_union, Set.pair_comm] using hα
  have hαempty : α ∉ racl k₀ (∅ : Set K) := by
    intro hm
    rw [mem_racl_closed_base_iff, Set.union_empty] at hm
    exact hαnot hm
  have haα : a ∈ racl k₀ {α} := by
    have he := racl_exchange (S := (∅ : Set K)) (by simpa using hαa) hαempty
    simpa using he
  have hai : AlgebraicIndependent k₀ ![a, x, y] := independent_over_closed_singleton h4xy
  have hαi : AlgebraicIndependent k₀ ![α, x, y] := by
    apply (algebraicIndependent_congr_racl (v := ![a, x, y]) (w := ![α, x, y]) ?_).mp hai
    intro i
    fin_cases i
    · exact racl_singleton_congr haα hαa
    · rfl
    · rfl
  have hprod : σ x * y = x * σ y := by
    have heq : σ x / σ y = x / y := by rwa [map_div₀] at hσv
    exact (div_eq_div_iff hy₀ hy).mp heq
  have hxα : σ x = α * x := by
    dsimp [α]
    rw [div_mul_cancel₀ _ hx]
  have hyα : σ y = α * y := by
    apply mul_right_cancel₀ hx
    calc
      σ y * x = σ x * y := by simpa only [mul_comm] using hprod.symm
      _ = α * y * x := by rw [hxα]; ring
  have hbα : b ∈ racl k₀ {α * x} := by
    have hm := mem_racl_map σ hbx
    rw [mem_racl_closed_base_iff]
    simpa [Set.image_insert_eq, hσa, hσb, hxα,
      Set.singleton_union, Set.pair_comm] using hm
  have hcα : c ∈ racl k₀ {α * y} := by
    have hm := mem_racl_map σ hcy
    rw [mem_racl_closed_base_iff]
    simpa [Set.image_insert_eq, hσa, hσc, hyα,
      Set.singleton_union, Set.pair_comm] using hm
  exact ⟨a₀, α, ha₀xy, hαi, haα, hbα, hcα⟩

/-- The normalized corners force the bottom product by the two product
meets. Its consumer applies this over the fresh closed parameter field. -/
private theorem product_mem_of_normalized_corners {α a b c d e x y : K}
    (h : AlgebraicIndependent k ![α, x, y])
    (ha : a ∈ racl k {α}) (hb : b ∈ racl k {α * x})
    (hc : c ∈ racl k {α * y})
    (hd₁ : d ∈ racl k {b, y}) (hd₂ : d ∈ racl k {x, c})
    (he₁ : e ∈ racl k {a, d}) (he₂ : e ∈ racl k {x, y}) :
    e ∈ racl k {x * y} := by
  have hd₁' : d ∈ racl k {α * x, y} := by
    refine racl_le_of_subset_racl (S := {α * x, y}) (T := {b, y}) ?_ hd₁
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact racl_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hb
    · exact subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hd₂' : d ∈ racl k {x, α * y} := by
    refine racl_le_of_subset_racl (S := {x, α * y}) (T := {x, c}) ?_ hd₂
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_mono (Set.subset_insert _ _) hc
  have hd := mem_racl_product_meet h hd₁' hd₂'
  refine mem_racl_bottom_product_meet h ?_ he₂
  refine racl_le_of_subset_racl (S := {α, x * y}) (T := {a, d}) ?_ he₁
  refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
  · exact racl_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) ha
  · refine racl_le_of_subset_racl (S := {α, x * y}) (T := {α * x * y}) ?_ hd
    apply Set.singleton_subset_iff.mpr
    have hm := mul_mem (subset_racl k ({α, x * y} : Set K) (Set.mem_insert _ _))
      (subset_racl k ({α, x * y} : Set K) (Set.mem_insert_of_mem _ rfl))
    simpa only [SetLike.mem_coe, mul_assoc] using hm

/-- A multiplication diagram with an actual semantic ratio produces the
semantic product over an algebraically closed ambient field of transcendence
degree at least five. All corner normalizations are derived internally;
no group extraction, separability or supplied product representatives are needed.
This proves the product-output assertion of blueprint Lemma `mul-diagram`.
Geometric `Q′` completeness still requires guarded geometric `Q` completeness. -/
theorem q'Sem_of_qSem_of_mulDiagram [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X Y S V E A B C D : Point k K}
    (hq : QSem X Y S V) (hmul : MulDiagram X Y V E A B C D) :
    Q'Sem X Y S E := by
  classical
  obtain ⟨x, y, hxy, hX, hY, hS, hV⟩ := hq
  obtain ⟨haxy, hb, hx, hc, hy, hv, hd₁, hd₂, he₁, he₂, hxb⟩ :=
    multiplication_incidence_data hmul hX hY hV
  obtain ⟨a₀, α, ha₀, hα, ha, hbα, hcα⟩ :=
    exists_normalized_corners htr haxy hb hx hc hy hv hxb
  let k₀ := racl k ({a₀} : Set K)
  have he : E.rep ∈ racl k₀ {x * y} :=
    product_mem_of_normalized_corners hα ha hbα hcα
      (racl_subset_racl_base k₀ _ hd₁) (racl_subset_racl_base k₀ _ hd₂)
      (racl_subset_racl_base k₀ _ he₁) (racl_subset_racl_base k₀ _ he₂)
  have he' : E.rep ∈ racl k {a₀, x * y} := by
    rw [mem_racl_closed_base_iff] at he
    simpa only [Set.singleton_union] using he
  have hproduct : x * y ∈ racl k {x, y} :=
    mul_mem (subset_racl k _ (Set.mem_insert _ _))
      (subset_racl k _ (Set.mem_insert_of_mem _ rfl))
  have heproduct : E.rep ∈ racl k {x * y} := by
    by_contra hn
    have hex := racl_exchange he' hn
    have ha₀xy : a₀ ∈ racl k {x, y} :=
      racl_le_of_subset_racl
        (Set.insert_subset_iff.mpr ⟨he₂, Set.singleton_subset_iff.mpr hproduct⟩) hex
    exact ha₀ (racl_mono (Set.subset_insert _ _) ha₀xy)
  have hle : E.1 ≤ ClosedIF.point k (x * y) := by
    rw [← E.point_rep]
    exact ClosedIF.point_le_iff.mpr (ClosedIF.mem_point.mpr heproduct)
  have hnb : x * y ∉ (⊥ : ClosedIF k K) := by
    intro hm
    have hz := ClosedIF.point_eq_bot_iff.mpr hm
    rw [hz] at hle
    exact E.2.1 (le_bot_iff.mp hle)
  have hE : E.1 = ClosedIF.point k (x * y) :=
    ((ClosedIF.isAtom_point hnb).le_iff_eq E.2.1).mp hle
  exact ⟨x, y, hxy, hX, hY, hS, hE⟩

/-- Convert the fresh closed-base normalization into finite closure relations
over the original base, before choosing a specialization. -/
private theorem exists_specializable_corners [IsAlgClosed K]
    {a b c x y : K} (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (hv : x / y ∈ racl k {b, c}) (hxb' : x ∉ racl k {b}) :
    ∃ t α : K, t ∉ racl k {a, x, y} ∧ α ≠ 0 ∧ α ∈ racl k {t, a} ∧
      b ∈ racl k {t, α * x} ∧ c ∈ racl k {t, α * y} := by
  classical
  obtain ⟨t, α, ht, hαi, ha, hb, hc⟩ :=
    exists_normalized_corners htr h hbx hxb hcy hyc hv hxb'
  have h4 := independent_four_of_fresh_three h ht
  have hai : AlgebraicIndependent ↥(racl k {t}) ![a, x, y] :=
    independent_over_closed_singleton (by
      convert h4.comp (![1, 0, 2, 3] : Fin 4 → Fin 4) (by decide) using 1
      ext i
      fin_cases i <;> rfl)
  have haempty : a ∉ racl ↥(racl k {t}) (∅ : Set K) :=
    notMem_racl_empty_of_transcendental (hai.transcendental 0)
  have hαa : α ∈ racl k {t, a} := by
    have ham : a ∈ racl ↥(racl k {t}) (insert α (∅ : Set K)) := by simpa using ha
    have hm := racl_exchange ham haempty
    have hm' : α ∈ racl ↥(racl k {t}) {a} := by simpa using hm
    rwa [mem_racl_closed_base_iff, Set.singleton_union] at hm'
  have hb' : b ∈ racl k {t, α * x} := by
    rwa [mem_racl_closed_base_iff, Set.singleton_union] at hb
  have hc' : c ∈ racl k {t, α * y} := by
    rwa [mem_racl_closed_base_iff, Set.singleton_union] at hc
  exact ⟨t, α, ht, hαi.ne_zero 0, hαa, hb', hc'⟩

/-- Specialize the corner relations while fixing the entire original closed
coordinate field. The finite-type homomorphism produces the common multiplier. -/
private theorem exists_descended_corner_memberships [IsAlgClosed K] [Infinite k]
    {a b c x y : K} (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (hv : x / y ∈ racl k {b, c}) (hxb' : x ∉ racl k {b}) :
    ∃ β : K, β ≠ 0 ∧ β ∈ racl k {a} ∧
      b ∈ racl k {β * x} ∧ c ∈ racl k {β * y} := by
  obtain ⟨t, α, ht, hα0, hαa, hb', hc'⟩ :=
    exists_specializable_corners htr h hbx hxb hcy hyc hv hxb'
  let F := racl k ({a, x, y} : Set K)
  let : IsAlgClosed F := isAlgClosed_closed_parameters _
  have htF : Transcendental F t := by
    intro halg
    exact ht (isRAC_racl _ t halg)
  have haF : a ∈ F := subset_racl k _ (by simp)
  have hxF : x ∈ F := subset_racl k _ (by simp)
  have hyF : y ∈ F := subset_racl k _ (by simp)
  have hbF : b ∈ F := by
    change b ∈ racl k ({a, x, y} : Set K)
    exact racl_mono (k := k) (K := K) (S := {a, x}) (T := {a, x, y})
      (Set.insert_subset (Set.mem_insert _ _) (Set.singleton_subset_iff.mpr
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hbx
  have hcF : c ∈ F := by
    change c ∈ racl k ({a, x, y} : Set K)
    exact racl_mono (k := k) (K := K) (S := {a, y}) (T := {a, x, y})
      (Set.insert_subset (Set.mem_insert _ _) (Set.singleton_subset_iff.mpr
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))) hcy
  exact exists_multiplier_descent (k := k) (K := K) (F := F) (t := t) (α := α)
    (⟨a, haF⟩ : F) ⟨b, hbF⟩ ⟨c, hcF⟩ ⟨x, hxF⟩ ⟨y, hyF⟩ htF h
    hα0 hαa hb' hc'

/-- A descended multiplier is nonconstant by the actual corner distinctness;
exchange and the original independent coordinates finish the normalization. -/
private theorem exists_original_normalized_corners [IsAlgClosed K] [Infinite k]
    {a b c x y : K} (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (hv : x / y ∈ racl k {b, c}) (hxb' : x ∉ racl k {b}) :
    ∃ β : K, AlgebraicIndependent k ![β, x, y] ∧
      a ∈ racl k {β} ∧ b ∈ racl k {β * x} ∧ c ∈ racl k {β * y} := by
  obtain ⟨β, -, hβa, hbβ, hcβ⟩ :=
    exists_descended_corner_memberships htr h hbx hxb hcy hyc hv hxb'
  have hβempty : β ∉ racl k (∅ : Set K) := by
    intro hm
    have hβx : β * x ∈ racl k {x} := mul_mem
      (racl_mono (Set.empty_subset _) hm) (subset_racl k _ rfl)
    have hbx' : b ∈ racl k {x} := racl_le_of_subset_racl
      (Set.singleton_subset_iff.mpr hβx) hbβ
    obtain ⟨habc, -⟩ := incidence_corners_independent h hbx hxb hcy hyc
    have hbempty : b ∉ racl k (∅ : Set K) :=
      notMem_racl_empty_of_transcendental (habc.transcendental 1)
    have hex := racl_exchange (S := (∅ : Set K)) (by simpa using hbx') hbempty
    exact hxb' (by simpa using hex)
  have haβ : a ∈ racl k {β} := by
    have hex := racl_exchange (S := (∅ : Set K)) (by simpa using hβa) hβempty
    simpa using hex
  refine ⟨β, ?_, haβ, hbβ, hcβ⟩
  apply (algebraicIndependent_congr_racl (v := ![a, x, y]) (w := ![β, x, y]) ?_).mp h
  intro i
  fin_cases i
  · exact racl_singleton_congr haβ hβa
  · rfl
  · rfl

/-- A genuine point contained in a principal rank-one closure is that point.
The point hypothesis supplies nontriviality of the target closure. -/
private theorem point_eq_of_rep_mem {P : Point k K} {z : K}
    (h : P.rep ∈ racl k {z}) : P.1 = ClosedIF.point k z := by
  have hle : P.1 ≤ ClosedIF.point k z := by
    rw [← P.point_rep]
    exact ClosedIF.point_le_iff.mpr h
  have hz : z ∉ (⊥ : ClosedIF k K) := by
    intro hm
    rw [ClosedIF.point_eq_bot_iff.mpr hm] at hle
    exact P.2.1 (le_bot_iff.mp hle)
  exact ((ClosedIF.isAtom_point hz).le_iff_eq P.2.1).mp hle

/-- The full original-base coordinate table of a multiplication diagram.
Over algebraically closed fields with ambient transcendence degree at least
five, the actual bottom representatives and ratio determine one independent
multiplier for all four auxiliary points and the original product point.
No corner normalization, algebraic group or specialization oracle is assumed. -/
theorem mulDiagram_coordinates [IsAlgClosed k] [IsAlgClosed K]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {X Y V E A B C D : Point k K} {x y : K}
    (hmul : MulDiagram X Y V E A B C D)
    (hX : X.1 = ClosedIF.point k x) (hY : Y.1 = ClosedIF.point k y)
    (hV : V.1 = ClosedIF.point k (x / y)) :
    ∃ a : K, AlgebraicIndependent k ![a, x, y] ∧
      A.1 = ClosedIF.point k a ∧ B.1 = ClosedIF.point k (a * x) ∧
      C.1 = ClosedIF.point k (a * y) ∧ D.1 = ClosedIF.point k (a * x * y) ∧
      E.1 = ClosedIF.point k (x * y) := by
  obtain ⟨haxy, hb, hx, hc, hy, hv, hd₁, hd₂, he₁, he₂, hxb⟩ :=
    multiplication_incidence_data hmul hX hY hV
  obtain ⟨a, ha, hA, hB, hC⟩ :=
    exists_original_normalized_corners htr haxy hb hx hc hy hv hxb
  have hd₁' : D.rep ∈ racl k {a * x, y} := by
    refine racl_le_of_subset_racl (S := {a * x, y}) (T := {B.rep, y}) ?_ hd₁
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact racl_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hB
    · exact subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hd₂' : D.rep ∈ racl k {x, a * y} := by
    refine racl_le_of_subset_racl (S := {x, a * y}) (T := {x, C.rep}) ?_ hd₂
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_mono (Set.subset_insert _ _) hC
  have hD := mem_racl_product_meet ha hd₁' hd₂'
  have hE := product_mem_of_normalized_corners ha hA hB hC hd₁ hd₂ he₁ he₂
  exact ⟨a, ha, point_eq_of_rep_mem hA, point_eq_of_rep_mem hB,
    point_eq_of_rep_mem hC, point_eq_of_rep_mem hD, point_eq_of_rep_mem hE⟩

/-- Adding five independent variables and taking an algebraic closure supplies
all fresh elements needed by the multiplication normalization. -/
private theorem five_le_trdeg_polynomial_algebraicClosure :
    (5 : Cardinal) ≤
      Algebra.trdeg k (AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) K))) := by
  let Ω := AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) K))
  let φ : MvPolynomial (Fin 5) K →ₐ[K] Ω :=
    IsScalarTower.toAlgHom K (MvPolynomial (Fin 5) K) Ω
  have hφ : Function.Injective φ := by
    change Function.Injective (algebraMap (MvPolynomial (Fin 5) K) Ω)
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 5) K)
      (FractionRing (MvPolynomial (Fin 5) K)) Ω]
    exact (algebraMap (FractionRing (MvPolynomial (Fin 5) K)) Ω).injective.comp
      (IsFractionRing.injective (MvPolynomial (Fin 5) K)
        (FractionRing (MvPolynomial (Fin 5) K)))
  have hX := (MvPolynomial.algebraicIndependent_X (Fin 5) K).map' hφ
  have hXk := AlgebraicIndependent.restrictScalars (algebraMap k K).injective hX
  simpa using hXk.lift_cardinalMk_le_trdeg

/-- An element algebraic over one original coordinate descends from an
ambient extension when the original field is algebraically closed. -/
private theorem exists_preimage_of_mem_racl_singleton [IsAlgClosed K]
    {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    {a : K} {z : Ω} (hz : z ∈ racl k {algebraMap K Ω a}) :
    ∃ b : K, algebraMap K Ω b = z := by
  let τ : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
  obtain ⟨p, hp, hpz, hpc⟩ := mem_racl_iff_exists_poly.mp hz
  have hle : adjoin k ({algebraMap K Ω a} : Set Ω) ≤ τ.fieldRange := by
    apply adjoin_le_iff.mpr
    rintro _ rfl
    exact ⟨a, rfl⟩
  have hcoeff : ∀ n, p.coeff n ∈ Set.range (algebraMap K Ω) := fun n ↦ hle (hpc n)
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := algebraMap K Ω) p).mp
    ((Polynomial.lifts_iff_coeff_lifts p).mpr hcoeff)
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at hq
    exact hp hq.symm
  have hza : IsAlgebraic K z := by
    refine ⟨q, hq0, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq]
    exact hpz
  have heq : algebraicClosure K Ω = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hm : z ∈ algebraicClosure K Ω := mem_algebraicClosure_iff.mpr hza
  rw [heq] at hm
  exact IntermediateField.mem_bot.mp hm

/-- Extend the ambient field to perform normalization, then descend the
multiplier because it is algebraic over an original coordinate. -/
private theorem exists_original_normalized_corners_without_trdeg
    [IsAlgClosed K] [Infinite k] {a b c x y : K}
    (h : AlgebraicIndependent k ![a, x, y])
    (hbx : b ∈ racl k {a, x}) (hxb : x ∈ racl k {a, b})
    (hcy : c ∈ racl k {a, y}) (hyc : y ∈ racl k {a, c})
    (hv : x / y ∈ racl k {b, c}) (hxb' : x ∉ racl k {b}) :
    ∃ β : K, AlgebraicIndependent k ![β, x, y] ∧
      a ∈ racl k {β} ∧ b ∈ racl k {β * x} ∧ c ∈ racl k {β * y} := by
  let Ω := AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) K))
  let τ : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
  have hmap (u v w : K) : τ ∘ ![u, v, w] = ![τ u, τ v, τ w] := by
    funext i
    fin_cases i <;> rfl
  have hΩ : AlgebraicIndependent k ![τ a, τ x, τ y] := by
    rw [← hmap]
    exact h.map' τ.injective
  have hpair (z u v : K) : τ z ∈ racl k {τ u, τ v} ↔ z ∈ racl k {u, v} := by
    simpa only [Set.image_insert_eq, Set.image_singleton] using
      algHom_mem_racl_image_iff τ (x := z) (S := {u, v})
  have hvΩ : τ x / τ y ∈ racl k {τ b, τ c} := by
    rw [← map_div₀]
    exact (hpair _ _ _).mpr hv
  have hxbΩ : τ x ∉ racl k {τ b} := by
    rw [algHom_mem_racl_singleton_iff]
    exact hxb'
  obtain ⟨βΩ, hβΩ, haΩ, hbΩ, hcΩ⟩ :=
    exists_original_normalized_corners (k := k) (K := Ω)
      (five_le_trdeg_polynomial_algebraicClosure (k := k) (K := K)) hΩ
      ((hpair _ _ _).mpr hbx) ((hpair _ _ _).mpr hxb)
      ((hpair _ _ _).mpr hcy) ((hpair _ _ _).mpr hyc) hvΩ hxbΩ
  have haempty : τ a ∉ racl k (∅ : Set Ω) :=
    notMem_racl_empty_of_transcendental (hΩ.transcendental 0)
  have hβa : βΩ ∈ racl k {τ a} := by
    have he := racl_exchange (S := (∅ : Set Ω)) (by simpa using haΩ) haempty
    simpa using he
  obtain ⟨β, hβ⟩ := exists_preimage_of_mem_racl_singleton (k := k) (K := K) hβa
  change τ β = βΩ at hβ
  rw [← hβ] at hβΩ haΩ hbΩ hcΩ
  refine ⟨β, ?_, (algHom_mem_racl_singleton_iff τ).mp haΩ, ?_, ?_⟩
  · apply AlgebraicIndependent.of_comp τ
    rw [hmap]
    exact hβΩ
  · rw [← map_mul] at hbΩ
    exact (algHom_mem_racl_singleton_iff τ).mp hbΩ
  · rw [← map_mul] at hcΩ
    exact (algHom_mem_racl_singleton_iff τ).mp hcΩ

/-- Every actual multiplication diagram over algebraically closed fields
has the complete original-base coordinate table. No ambient transcendence-degree
bound is needed: an auxiliary extension supplies fresh parameters, and its
normalized multiplier descends to the original algebraically closed field. -/
theorem MulDiagram.exists_coordinates [IsAlgClosed k] [IsAlgClosed K]
    {X Y V E A B C D : Point k K} {x y : K}
    (hmul : MulDiagram X Y V E A B C D)
    (hX : X.1 = ClosedIF.point k x) (hY : Y.1 = ClosedIF.point k y)
    (hV : V.1 = ClosedIF.point k (x / y)) :
    ∃ a : K, AlgebraicIndependent k ![a, x, y] ∧
      A.1 = ClosedIF.point k a ∧ B.1 = ClosedIF.point k (a * x) ∧
      C.1 = ClosedIF.point k (a * y) ∧ D.1 = ClosedIF.point k (a * x * y) ∧
      E.1 = ClosedIF.point k (x * y) := by
  obtain ⟨haxy, hb, hx, hc, hy, hv, hd₁, hd₂, he₁, he₂, hxb⟩ :=
    multiplication_incidence_data hmul hX hY hV
  obtain ⟨a, ha, hA, hB, hC⟩ :=
    exists_original_normalized_corners_without_trdeg haxy hb hx hc hy hv hxb
  have hd₁' : D.rep ∈ racl k {a * x, y} := by
    refine racl_le_of_subset_racl (S := {a * x, y}) (T := {B.rep, y}) ?_ hd₁
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact racl_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hB
    · exact subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hd₂' : D.rep ∈ racl k {x, a * y} := by
    refine racl_le_of_subset_racl (S := {x, a * y}) (T := {x, C.rep}) ?_ hd₂
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_mono (Set.subset_insert _ _) hC
  have hD := mem_racl_product_meet ha hd₁' hd₂'
  have hE := product_mem_of_normalized_corners ha hA hB hC hd₁ hd₂ he₁ he₂
  exact ⟨a, ha, point_eq_of_rep_mem hA, point_eq_of_rep_mem hB,
    point_eq_of_rep_mem hC, point_eq_of_rep_mem hD, point_eq_of_rep_mem hE⟩

end AclGeom
