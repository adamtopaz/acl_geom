/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import GroupConfig.Descent
import AclGeom.Closure.Ambient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Coherent descent of finite algebraicity tables

For `rem:finite-trdeg` and the application descent in the supplemental blueprint,
choose genuine annihilators for finitely many algebraicity incidences. Their finite
coefficient parameters, nonzero denominators and nonzero annihilator coefficients form
one constructible relation. Descent specializes the parameters coherently, and a point
of the resulting finite fibre lies in the original algebraically closed ambient field.

`exists_polynomial_closure_table_descent_to` applies this to both inclusions of every row
of a finite polynomial closure table. Its named consumer is the nine-row chart in
`AclGeom.Config.GuardedAffineGrid`. The coefficient field need not be algebraically
closed or small; only its independence from the original tuple is required.

**Status:** finite polynomial closure-table descent is proved over an algebraically
closed base and original ambient. No degree-only constructibility assertion is used.
-/

namespace GroupConfig

open AclGeom Set MvPolynomial IntermediateField

noncomputable section

universe u

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Finitely many polynomials can be expressed using one finite tuple of their coefficients.
The coefficient variables are introduced linearly, without asserting a ring homomorphism from
the coefficient field into a polynomial ring. -/
private theorem exists_polynomial_parameters {ι α : Type u} [Finite α]
    (L : IntermediateField k K) (P : α → MvPolynomial ι L) :
    ∃ (η : Type u) (_ : Finite η) (e : η → L) (F : α → MvPolynomial (η ⊕ ι) k),
      ∀ a z, aeval (Sum.elim (algebraMap L K ∘ e) z) (F a) = aeval z (P a) := by
  classical
  let η := Σ a, ↥(P a).support
  let e : η → L := fun p ↦ (P p.1).coeff p.2
  let F (a : α) : MvPolynomial (η ⊕ ι) k :=
    ∑ m ∈ (P a).support.attach,
      X (Sum.inl ⟨a, m⟩) * rename Sum.inr (monomial (m : ι →₀ ℕ) (1 : k))
  refine ⟨η, inferInstance, e, F, fun a z ↦ ?_⟩
  have hmono (m : ι →₀ ℕ) :
      aeval (Sum.elim (algebraMap L K ∘ e) z)
          (rename Sum.inr (monomial m (1 : k))) =
        m.prod (fun i n ↦ z i ^ n) := by
    rw [aeval_rename]
    simp [aeval_monomial]
  simp only [F, map_sum, map_mul, aeval_X, Sum.elim_inl, Function.comp_apply, hmono]
  dsimp only [e]
  exact (Finset.sum_attach (P a).support (fun m ↦
    algebraMap L K ((P a).coeff m) * m.prod (fun i n ↦ z i ^ n))).trans
      (MvPolynomial.eval₂_eq (algebraMap L K) z (P a)).symm

/-- Clearing the finitely many coefficient denominators in an annihilating polynomial. -/
private theorem sum_clear_denominators {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → K) (d : α → ℕ) (y : K) (hq : ∀ i, q i ≠ 0) :
    (∑ i, p i * (∏ j ∈ Finset.univ.erase i, q j) * y ^ d i) =
      (∏ i, q i) * (∑ i, p i / q i * y ^ d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)]
  field_simp [hq]

/-- A nonzero coefficient in the cleared annihilator certifies genuine algebraicity. -/
private theorem mem_racl_of_cleared_relation {α : Type*} [Fintype α] [DecidableEq α]
    {S : Set K} (d : α → ℕ) (hd : Function.Injective d) (j : α) (p q : α → K) (y : K)
    (hpS : ∀ i, p i ∈ racl k S) (hqS : ∀ i, q i ∈ racl k S)
    (hq : ∀ i, q i ≠ 0) (hpj : p j ≠ 0)
    (hz : (∑ i, p i * (∏ r ∈ Finset.univ.erase i, q r) * y ^ d i) = 0) :
    y ∈ racl k S := by
  let R := racl k S
  let c (i : α) : R := ⟨p i / q i, div_mem (hpS i) (hqS i)⟩
  let f : Polynomial R := ∑ i, Polynomial.monomial (d i) (c i)
  have hcoeff : f.coeff (d j) = c j := by
    simp [f, Polynomial.coeff_monomial, hd.eq_iff]
  have hf : f ≠ 0 := by
    intro h0
    have hc := hcoeff
    rw [h0, Polynomial.coeff_zero] at hc
    have hcz := congrArg (fun x : R ↦ (x : K)) hc
    exact (div_ne_zero hpj (hq j)) hcz.symm
  have hprod : (∏ i, q i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hq i
  have hsum : (∑ i, p i / q i * y ^ d i) = 0 := by
    rw [sum_clear_denominators p q d y hq] at hz
    exact (mul_eq_zero.1 hz).resolve_left hprod
  have hy : IsAlgebraic R y := ⟨f, hf, by simpa [f, c] using hsum⟩
  exact (isRAC_racl (k := k) S) y hy

/-- A field-generated coefficient is a rational function with a nonzero denominator. -/
private theorem exists_fraction_nonzero {L : IntermediateField k K} {ι : Type*}
    (z : ι → K) {c : K} (hc : c ∈ adjoin (↥L) (range z)) :
    ∃ P Q : MvPolynomial ι L, aeval z Q ≠ 0 ∧ c = aeval z P / aeval z Q := by
  obtain ⟨P, Q, h⟩ := (mem_adjoin_range_iff (↥L) z c).1 hc
  by_cases hQ : aeval z Q = 0
  · refine ⟨0, 1, by simp, ?_⟩
    simpa [hQ] using h
  · exact ⟨P, Q, hQ, h⟩

/-- The fixed, cleared annihilator relation is constructible over its base. -/
private theorem isConstructible_cleared_relation {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → ℕ) (j : α) : IsConstructibleOver k
      {c : ((α ⊕ α) ⊕ Unit) → K |
        (∏ i, c (Sum.inl (Sum.inr i))) ≠ 0 ∧ c (Sum.inl (Sum.inl j)) ≠ 0 ∧
          (∑ i, c (Sum.inl (Sum.inl i)) *
            (∏ r ∈ Finset.univ.erase i, c (Sum.inl (Sum.inr r))) *
              c (Sum.inr ()) ^ d i) = 0} := by
  classical
  let R : MvPolynomial ((α ⊕ α) ⊕ Unit) k :=
    ∑ i, X (Sum.inl (Sum.inl i)) *
      (∏ r ∈ Finset.univ.erase i, X (Sum.inl (Sum.inr r))) * X (Sum.inr ()) ^ d i
  let D : MvPolynomial ((α ⊕ α) ⊕ Unit) k := ∏ i, X (Sum.inl (Sum.inr i))
  convert ((IsConstructibleOver.polynomial_ne_zero D).inter
    (IsConstructibleOver.polynomial_ne_zero (X (Sum.inl (Sum.inl j))))).inter
      (IsConstructibleOver.polynomial_zero R) using 1
  ext c
  simp only [mem_ofPred_eq, mem_inter_iff, R, D, map_sum, map_mul, map_prod, map_pow, aeval_X]
  tauto

/-- One actual algebraicity incidence admits finite coefficient parameters and a fixed
constructible witness. Every base-field specialization satisfying that witness retains the
incidence, because all denominator and nonzero-coefficient conditions are included. -/
private theorem exists_constructible_algebraicity_witness {ι : Type} [Finite ι]
    (L : IntermediateField k K) (z : ι → K) (y : K) (hy : y ∈ racl (↥L) (range z)) :
    ∃ (η : Type) (_ : Finite η) (e : η → L)
      (Φ : Set ((η ⊕ (ι ⊕ Unit)) → K)), IsConstructibleOver k Φ ∧
        Sum.elim (algebraMap L K ∘ e) (Sum.elim z fun _ ↦ y) ∈ Φ ∧
        ∀ (e₀ : η → k) (z₀ : ι → K) (y₀ : K),
          Sum.elim (algebraMap k K ∘ e₀) (Sum.elim z₀ fun _ ↦ y₀) ∈ Φ →
            y₀ ∈ racl k (range z₀) := by
  classical
  obtain ⟨q, hq, hqy, hc⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff _).1 hy)
  let α := ↥q.support
  let d : α → ℕ := fun i ↦ i
  have hd : Function.Injective d := Subtype.val_injective
  have hsupp : q.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (by simpa using hq)
  obtain ⟨j₀, hj₀⟩ := hsupp
  let j : α := ⟨j₀, hj₀⟩
  choose P Q hQ hfrac using fun i : α ↦ exists_fraction_nonzero z (hc i)
  obtain ⟨η, iη, e, F, hF⟩ := exists_polynomial_parameters L (Sum.elim P Q)
  let emb : η ⊕ ι → η ⊕ (ι ⊕ Unit) := Sum.map id Sum.inl
  let f : ((α ⊕ α) ⊕ Unit) → MvPolynomial (η ⊕ (ι ⊕ Unit)) k :=
    Sum.elim (fun i ↦ rename emb (F i)) fun _ ↦ X (Sum.inr (Sum.inr ()))
  let Φ : Set ((η ⊕ (ι ⊕ Unit)) → K) :=
    {θ | (∏ i, aeval θ (f (Sum.inl (Sum.inr i)))) ≠ 0 ∧
      aeval θ (f (Sum.inl (Sum.inl j))) ≠ 0 ∧
        (∑ i, aeval θ (f (Sum.inl (Sum.inl i))) *
          (∏ r ∈ Finset.univ.erase i, aeval θ (f (Sum.inl (Sum.inr r)))) *
            aeval θ (f (Sum.inr ())) ^ d i) = 0}
  have hf (a : α ⊕ α) (e' : η → K) (z' : ι → K) (y' : K) :
      aeval (Sum.elim e' (Sum.elim z' fun _ ↦ y')) (f (Sum.inl a)) =
        aeval (Sum.elim e' z') (F a) := by
    rw [show f (Sum.inl a) = rename emb (F a) from rfl, aeval_rename]
    have he : Sum.elim e' (Sum.elim z' fun _ ↦ y') ∘ emb = Sum.elim e' z' := by
      funext i
      cases i <;> rfl
    rw [he]
  have hfy (e' : η → K) (z' : ι → K) (y' : K) :
      aeval (Sum.elim e' (Sum.elim z' fun _ ↦ y')) (f (Sum.inr ())) = y' := by
    rw [show f (Sum.inr ()) = X (Sum.inr (Sum.inr ())) from rfl, aeval_X]
    rfl
  refine ⟨η, iη, e, Φ, (isConstructible_cleared_relation d j).preimage_polynomial f, ?_, ?_⟩
  · change _ ∧ _ ∧ _
    simp only [hf, hfy, hF, Sum.elim_inl, Sum.elim_inr]
    refine ⟨Finset.prod_ne_zero_iff.2 (fun i _ ↦ hQ i), ?_, ?_⟩
    · intro hpj
      have h := Polynomial.mem_support_iff.1 j.2
      rw [hfrac j, hpj, zero_div] at h
      exact h rfl
    · rw [sum_clear_denominators _ _ d y hQ]
      have heval : (∑ i : α, q.coeff i * y ^ d i) = q.eval y := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def, ← Finset.sum_attach q.support]
        simp only [Finset.attach_eq_univ]
        rfl
      simp_rw [← hfrac]
      rw [heval, hqy, mul_zero]
  · intro e₀ z₀ y₀ hθ
    change _ ∧ _ ∧ _ at hθ
    simp only [hf, hfy] at hθ
    have hD : ∀ i, aeval (Sum.elim (algebraMap k K ∘ e₀) z₀) (F (Sum.inr i)) ≠ 0 :=
      fun i ↦ (Finset.prod_ne_zero_iff.1 hθ.1) i (Finset.mem_univ i)
    have hmem (a : α ⊕ α) :
        aeval (Sum.elim (algebraMap k K ∘ e₀) z₀) (F a) ∈ racl k (range z₀) := by
      apply MvPolynomial.eval₂_mem (fun m _ ↦ (racl k (range z₀)).algebraMap_mem _)
      intro i
      cases i with
      | inl i => exact (racl k (range z₀)).algebraMap_mem (e₀ i)
      | inr i => exact subset_racl k _ ⟨i, rfl⟩
    exact mem_racl_of_cleared_relation d hd j _ _ y₀
      (fun i ↦ hmem (Sum.inl i)) (fun i ↦ hmem (Sum.inr i)) hD hθ.2.1 hθ.2.2

/-- Coherent original-base descent of any finite list of polynomial algebraicity incidences.
All finite coefficient witnesses and their nonvanishing constraints are chosen internally,
then specialized simultaneously while the original tuple stays fixed. -/
private theorem exists_finite_incidence_descent_to [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] {J ι κ μ : Type} [Finite J] [Finite ι] [Finite κ] [Finite μ]
    {F : Type*} [Field F] [Algebra k F] [IsAlgClosed F] (f : F →ₐ[k] K)
    (L : IntermediateField k K) (w : κ → F) (v : ι → K)
    (hind : IndepOver k ∅ (L : Set K) (range (f ∘ w)))
    (S : J → μ → MvPolynomial (κ ⊕ ι) k) (T : J → MvPolynomial (κ ⊕ ι) k)
    (hinc : ∀ j, aeval (Sum.elim (f ∘ w) v) (T j) ∈
      racl (↥L) (range fun i ↦ aeval (Sum.elim (f ∘ w) v) (S j i))) :
    ∃ v₀ : ι → F, ∀ j, aeval (Sum.elim w v₀) (T j) ∈
      racl k (range fun i ↦ aeval (Sum.elim w v₀) (S j i)) := by
  classical
  let : Algebra F K := f.toRingHom.toAlgebra
  let : IsScalarTower k F K := IsScalarTower.of_algHom f
  choose η iη e Φ hΦ hactual hspecial using fun j ↦
    exists_constructible_algebraicity_witness L
      (fun i ↦ aeval (Sum.elim (f ∘ w) v) (S j i)) (aeval (Sum.elim (f ∘ w) v) (T j)) (hinc j)
  let (j : J) : Finite (η j) := iη j
  let Ε := Σ j, η j
  let E : Ε → K := fun p ↦ algebraMap L K (e p.1 p.2)
  let emb : κ ⊕ ι → (Ε ⊕ κ) ⊕ ι := Sum.map Sum.inr id
  let p (j : J) : (η j ⊕ (μ ⊕ Unit)) → MvPolynomial ((Ε ⊕ κ) ⊕ ι) k :=
    Sum.elim (fun i ↦ X (Sum.inl (Sum.inl ⟨j, i⟩)))
      (Sum.elim (fun i ↦ rename emb (S j i)) fun _ ↦ rename emb (T j))
  let H : Set (((Ε ⊕ κ) ⊕ ι) → K) := {θ | ∀ j, (fun i ↦ aeval θ (p j i)) ∈ Φ j}
  have hH : IsConstructibleOver k H := by
    have h := IsConstructibleOver.iInter fun j ↦ (hΦ j).preimage_polynomial (p j)
    convert h using 1
    ext θ
    simp only [H, mem_ofPred_eq, mem_iInter, mem_preimage]
  have heval (j : J) (e' : Ε → K) (w' : κ → K) (v' : ι → K) :
      (fun i ↦ aeval (Sum.elim (Sum.elim e' w') v') (p j i)) =
        Sum.elim (fun i ↦ e' ⟨j, i⟩)
          (Sum.elim (fun i ↦ aeval (Sum.elim w' v') (S j i))
            fun _ ↦ aeval (Sum.elim w' v') (T j)) := by
    have hraw : Sum.elim (Sum.elim e' w') v' ∘ emb = Sum.elim w' v' := by
      funext i
      cases i <;> rfl
    funext i
    cases i with
    | inl i => simp only [p, Sum.elim_inl, aeval_X]
    | inr i =>
      cases i with
      | inl i => simp only [p, Sum.elim_inr, Sum.elim_inl, aeval_rename, hraw]
      | inr i => simp only [p, Sum.elim_inr, aeval_rename, hraw]
  have hEx : IsConstructibleOver k
      {cv : (Ε ⊕ κ) → K | ∃ v', Sum.elim cv v' ∈ H} := by
    apply IsConstructibleOver.exists
    convert hH using 1
    ext θ
    have hθ : Sum.elim (θ ∘ Sum.inl) (θ ∘ Sum.inr) = θ := by
      funext i
      cases i <;> rfl
    simp only [mem_ofPred_eq, hθ]
  have hEL : range E ⊆ L := by
    rintro _ ⟨p, rfl⟩
    exact (e p.1 p.2).2
  have hact : Sum.elim E (f ∘ w) ∈ {cv : (Ε ⊕ κ) → K | ∃ v', Sum.elim cv v' ∈ H} := by
    refine ⟨v, fun j ↦ ?_⟩
    rw [heval]
    exact hactual j
  obtain ⟨e₀, vΩ, hvΩ⟩ := descent hEx (hind.mono_left hEL) hact
  -- Reflect this one finite system into the original algebraically closed field `F`.
  let q : ((Ε ⊕ κ) ⊕ ι) → MvPolynomial ι F :=
    Sum.elim (Sum.elim (fun i ↦ C (algebraMap k F (e₀ i))) (fun i ↦ C (w i))) X
  have hq (z : ι → K) : (fun i ↦ aeval z (q i)) =
      Sum.elim (Sum.elim (algebraMap k K ∘ e₀) (f ∘ w)) z := by
    funext i
    cases i with
    | inl i =>
      cases i with
      | inl i => simp only [q, Sum.elim_inl, aeval_C, Function.comp_apply]; exact f.commutes _
      | inr i => simp only [q, Sum.elim_inl, Sum.elim_inr, aeval_C]; rfl
    | inr i => simp only [q, Sum.elim_inr, aeval_X]
  have hFiber := (hH.extend_base (L := F)).preimage_polynomial q
  obtain ⟨v₀, hv₀⟩ := hFiber.exists_kpoint ⟨vΩ, by
    change (fun i ↦ aeval vΩ (q i)) ∈ H
    rw [hq]
    exact hvΩ⟩
  change (fun i ↦ aeval (algebraMap F K ∘ v₀) (q i)) ∈ H at hv₀
  rw [hq] at hv₀
  have hpoly (P : MvPolynomial (κ ⊕ ι) k) :
      aeval (Sum.elim (f ∘ w) (f ∘ v₀)) P = f (aeval (Sum.elim w v₀) P) := by
    rw [MvPolynomial.comp_aeval_apply]
    have he : Sum.elim (f ∘ w) (f ∘ v₀) = fun i ↦ f (Sum.elim w v₀ i) := by
      funext i
      cases i <;> rfl
    rw [he]
  refine ⟨v₀, fun j ↦ ?_⟩
  have hj := hv₀ j
  rw [heval] at hj
  have hmem := hspecial j (fun i ↦ e₀ ⟨j, i⟩)
    (fun i ↦ aeval (Sum.elim (f ∘ w) (f ∘ v₀)) (S j i))
    (aeval (Sum.elim (f ∘ w) (f ∘ v₀)) (T j)) hj
  apply (algHom_mem_racl_image_iff f).1
  simp only [hpoly] at hmem
  change f (aeval (Sum.elim w v₀) (T j)) ∈
    racl k (range (f ∘ fun i ↦ aeval (Sum.elim w v₀) (S j i))) at hmem
  rwa [range_comp] at hmem

/-- A finite polynomial closure table descends through one coherent specialization of its
fresh coefficient parameters, preserving every row over the original base simultaneously. -/
theorem exists_polynomial_closure_table_descent_to [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] {J ι κ μ : Type} [Finite J] [Finite ι] [Finite κ] [Finite μ]
    {F : Type*} [Field F] [Algebra k F] [IsAlgClosed F] (f : F →ₐ[k] K)
    (L : IntermediateField k K) (w : κ → F) (v : ι → K)
    (hind : IndepOver k ∅ (L : Set K) (range (f ∘ w)))
    (R : J → μ → MvPolynomial κ k) (C : J → μ → MvPolynomial ι k)
    (hrows : ∀ j, racl (↥L) (range fun i ↦ aeval (f ∘ w) (R j i)) =
      racl (↥L) (range fun i ↦ aeval v (C j i))) :
    ∃ v₀ : ι → F, ∀ j, racl k (range fun i ↦ aeval w (R j i)) =
      racl k (range fun i ↦ aeval v₀ (C j i)) := by
  classical
  let S (p : J × Bool × μ) (i : μ) : MvPolynomial (κ ⊕ ι) k :=
    if p.2.1 then rename Sum.inl (R p.1 i) else rename Sum.inr (C p.1 i)
  let T (p : J × Bool × μ) : MvPolynomial (κ ⊕ ι) k :=
    if p.2.1 then rename Sum.inr (C p.1 p.2.2) else rename Sum.inl (R p.1 p.2.2)
  have hl (w' : κ → K) (v' : ι → K) (P : MvPolynomial κ k) :
      aeval (Sum.elim w' v') (rename Sum.inl P) = aeval w' P := by
    rw [aeval_rename]
    rfl
  have hr (w' : κ → K) (v' : ι → K) (P : MvPolynomial ι k) :
      aeval (Sum.elim w' v') (rename Sum.inr P) = aeval v' P := by
    rw [aeval_rename]
    rfl
  have hinc (p : J × Bool × μ) : aeval (Sum.elim (f ∘ w) v) (T p) ∈
      racl (↥L) (range fun i ↦ aeval (Sum.elim (f ∘ w) v) (S p i)) := by
    rcases p with ⟨j, b, i⟩
    cases b
    · simpa only [S, T, Bool.false_eq_true, ↓reduceIte, hl, hr] using
        (hrows j ▸ subset_racl (↥L) (range fun i ↦ aeval (f ∘ w) (R j i)) (mem_range_self i))
    · simpa only [S, T, ↓reduceIte, hl, hr] using
        ((hrows j).symm ▸ subset_racl (↥L) (range fun i ↦ aeval v (C j i)) (mem_range_self i))
  obtain ⟨v₀, hv₀⟩ := exists_finite_incidence_descent_to f L w v hind S T hinc
  refine ⟨v₀, fun j ↦ le_antisymm (racl_le_of_subset_racl ?_) (racl_le_of_subset_racl ?_)⟩
  · rintro _ ⟨i, rfl⟩
    change aeval w (R j i) ∈ racl k (range fun i ↦ aeval v₀ (C j i))
    simpa only [S, T, Bool.false_eq_true, ↓reduceIte, aeval_rename, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr] using hv₀ (j, false, i)
  · rintro _ ⟨i, rfl⟩
    change aeval v₀ (C j i) ∈ racl k (range fun i ↦ aeval w (R j i))
    simpa only [S, T, ↓reduceIte, aeval_rename, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr] using hv₀ (j, true, i)

end

end GroupConfig
