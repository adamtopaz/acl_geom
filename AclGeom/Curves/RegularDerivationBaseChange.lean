/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.ConstantExtension
import AclGeom.Curves.DerivationBaseChange
import AclGeom.Curves.TensorFractionFields

/-!
# Regular derivations under extension of constants

Let `F` be a function field of one variable over an algebraically closed field `k`, with a
separating transcendental element, and let `C ⊆ K` be field extensions of `k`. Write
`F_C = Frac(C ⊗[k] F)` and `F_K = Frac(K ⊗[k] F)`, with the canonical map
`Φ : F_C → F_K` (`baseChangeFractionMap`). Two `C`-linearly independent `C`-derivations of
`F_C` which preserve every proper valuation subring containing `C` extend along `Φ` to two
`K`-linearly independent `K`-derivations of `F_K` which preserve every proper valuation subring
containing `K` (`exists_regular_derivations_baseChange`).

The field `F_K` is identified with `Frac(K ⊗[C] F_C)`, since `K ⊗[C] F_C` is a localization of
`K ⊗[C] (C ⊗[k] F) = K ⊗[k] F`. This yields the derivations
(`exists_linearIndependent_derivations_baseChange`). Regularity passes through the integral
closures of `L[1 ⊗ t]` and `L[1 ⊗ t⁻¹]`. These are the images of `L ⊗[k] B` for `L = C, K`, by
`isIntegral_adjoin_iff_mem_range`, and they detect all places
(`derivation_mem_valuationSubring_of_integralClosure`).

In the genus argument the derivations are the `C`-linear curve variations. They are not
derivations of `C`, which are never extended to the ambient field.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

open TensorProduct

noncomputable section


/-! ### The comparison map -/

variable {k C K F : Type*} [Field k] [Field C] [Field K] [Field F] [Algebra k C] [Algebra k K]
  [Algebra k F] [Algebra C K] [IsScalarTower k C K] [IsAlgClosed k]

attribute [local instance] isDomain_tensorProduct_of_isAlgClosed

variable (k C K F) in
/-- Extension of constants `C ⊗[k] F → K ⊗[k] F`. -/
private def tensorMap : C ⊗[k] F →ₐ[C] K ⊗[k] F :=
  Algebra.TensorProduct.map (Algebra.ofId C K) (AlgHom.id k F)

omit [IsAlgClosed k] in
private theorem tensorMap_injective : Function.Injective (tensorMap k C K F) := by
  have h : (tensorMap k C K F).toLinearMap.restrictScalars k =
      ((Algebra.ofId C K).toLinearMap.restrictScalars k).rTensor F :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hinj : Function.Injective (((Algebra.ofId C K).toLinearMap.restrictScalars k).rTensor F) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap C K).injective
  intro x y hxy
  apply hinj
  rw [← h]
  exact hxy

variable (k C K F) in
/-- The canonical map `Frac(C ⊗[k] F) → Frac(K ⊗[k] F)`. -/
def baseChangeFractionMap : FractionRing (C ⊗[k] F) →ₐ[C] FractionRing (K ⊗[k] F) :=
  IsFractionRing.liftAlgHom (A := C ⊗[k] F)
    (g := (IsScalarTower.toAlgHom C (K ⊗[k] F) (FractionRing (K ⊗[k] F))).comp
      (tensorMap k C K F))
    (show Function.Injective ((IsScalarTower.toAlgHom C (K ⊗[k] F)
        (FractionRing (K ⊗[k] F))).comp (tensorMap k C K F)) from
      (IsFractionRing.injective (K ⊗[k] F) (FractionRing (K ⊗[k] F))).comp tensorMap_injective)

theorem baseChangeFractionMap_algebraMap (x : C ⊗[k] F) :
    baseChangeFractionMap k C K F (algebraMap (C ⊗[k] F) _ x) =
      algebraMap (K ⊗[k] F) _ (Algebra.TensorProduct.map (Algebra.ofId C K) (AlgHom.id k F) x) := by
  rw [baseChangeFractionMap, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem baseChangeFractionMap_tmul (c : C) (f : F) :
    baseChangeFractionMap k C K F (algebraMap (C ⊗[k] F) _ (c ⊗ₜ f)) =
      algebraMap (K ⊗[k] F) _ (algebraMap C K c ⊗ₜ f) := by
  rw [baseChangeFractionMap_algebraMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

/-- `Frac(K ⊗[k] F)` is the fraction field of the domain `K ⊗[C] Frac(C ⊗[k] F)`, compatibly
with `baseChangeFractionMap`. -/
private theorem isDomain_and_exists_fractionEquiv :
    IsDomain (K ⊗[C] FractionRing (C ⊗[k] F)) ∧
      ∃ e : FractionRing (K ⊗[C] FractionRing (C ⊗[k] F)) ≃ₐ[K] FractionRing (K ⊗[k] F),
        ∀ x, e (algebraMap (K ⊗[C] FractionRing (C ⊗[k] F)) _ ((1 : K) ⊗ₜ x)) =
          baseChangeFractionMap k C K F x := by
  have _ : IsDomain (K ⊗[C] (C ⊗[k] F)) :=
    (Algebra.TensorProduct.cancelBaseChange k C K K F).toMulEquiv.isDomain
  obtain ⟨hdom, e₁, he₁⟩ := isDomain_and_exists_tensorFractionEquiv (k := C) (C := K)
    (A := C ⊗[k] F)
  refine ⟨hdom, (e₁.trans (IsFractionRing.algEquivOfAlgEquiv
      (Algebra.TensorProduct.cancelBaseChange k C K K F))), fun x ↦ ?_⟩
  -- Both sides are ring homomorphisms out of `Frac(C ⊗[k] F)`; compare on `C ⊗[k] F`.
  let φ₁ : FractionRing (C ⊗[k] F) →+* FractionRing (K ⊗[k] F) :=
    ((e₁.trans (IsFractionRing.algEquivOfAlgEquiv
      (Algebra.TensorProduct.cancelBaseChange k C K K F))).toRingHom.comp
      (algebraMap (K ⊗[C] FractionRing (C ⊗[k] F)) _)).comp
        (Algebra.TensorProduct.includeRight : FractionRing (C ⊗[k] F) →ₐ[C] _).toRingHom
  have hφ : φ₁ = (baseChangeFractionMap k C K F).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (C ⊗[k] F)) (RingHom.ext fun y ↦ ?_)
    induction y using TensorProduct.inductionOn with
    | tmul c f =>
      change (e₁.trans (IsFractionRing.algEquivOfAlgEquiv
      (Algebra.TensorProduct.cancelBaseChange k C K K F)))
        (algebraMap (K ⊗[C] FractionRing (C ⊗[k] F)) _
          ((1 : K) ⊗ₜ algebraMap (C ⊗[k] F) _ (c ⊗ₜ f))) =
        baseChangeFractionMap k C K F (algebraMap (C ⊗[k] F) _ (c ⊗ₜ f))
      rw [AlgEquiv.trans_apply, he₁, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
        baseChangeFractionMap_tmul]
      congr 1
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    | add y z hy hz =>
      rw [map_add, map_add, hy, hz]
  exact RingHom.congr_fun hφ x

/-! ### Regularity -/

variable [IsFunctionFieldOneVar k F]

omit [IsFunctionFieldOneVar k F] in
/-- A derivation of `F_C` preserving every proper valuation subring over `C` preserves the
integral closure of `C[1 ⊗ s]`. -/
private theorem mem_integralClosure_of_regular {s : F}
    (δ : Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (hreg : ∀ V : ValuationSubring (FractionRing (C ⊗[k] F)),
      (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ x ∈ V)
    {y : FractionRing (C ⊗[k] F)}
    (hy : y ∈ integralClosure (Algebra.adjoin C
      {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)}) _) :
    δ y ∈ integralClosure (Algebra.adjoin C
      {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)}) _ := by
  have hR : (integralClosure (Algebra.adjoin C
      {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)})
        (FractionRing (C ⊗[k] F))).toSubring = ⨅ V : {V : ValuationSubring
          (FractionRing (C ⊗[k] F)) // (integralClosure (Algebra.adjoin C
            {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)})
              (FractionRing (C ⊗[k] F))).toSubring ≤ V.toSubring}, V.1.toSubring :=
    Subring.eq_iInf_of_isIntegrallyClosedIn
  rw [← Subalgebra.mem_toSubring, hR, Subring.mem_iInf]
  rintro ⟨V, hV⟩
  by_cases hVtop : V = ⊤
  · subst hVtop
    exact ValuationSubring.mem_top _
  refine hreg V (fun c ↦ hV ?_) hVtop y (hV (Subalgebra.mem_toSubring.2 hy))
  exact Subalgebra.mem_toSubring.2 (Subalgebra.algebraMap_mem _
    (algebraMap C (Algebra.adjoin C
      {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)}) c))

omit [IsFunctionFieldOneVar k F] in
/-- `Φ` maps the image of `C ⊗[k] B` into the image of `K ⊗[k] B`. -/
private theorem baseChangeFractionMap_mem_range (s : F)
    (w : C ⊗[k] ((integralClosure (Algebra.adjoin k ({s} : Set F)) F).restrictScalars k)) :
    baseChangeFractionMap k C K F (integralClosureBaseChange C s w) ∈
      (integralClosureBaseChange K s).range := by
  induction w using TensorProduct.inductionOn with
  | tmul c b =>
    refine (AlgHom.mem_range _).2 ⟨algebraMap C K c ⊗ₜ b, ?_⟩
    change algebraMap (K ⊗[k] F) _ (algebraMap C K c ⊗ₜ (b : F)) =
      baseChangeFractionMap k C K F (algebraMap (C ⊗[k] F) _ (c ⊗ₜ (b : F)))
    rw [baseChangeFractionMap_tmul]
  | add v w hv hw =>
    rw [map_add, map_add]
    exact add_mem hv hw

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
private theorem algebraMap_mem_range_integralClosureBaseChange (s : F) (l : K) :
    algebraMap K (FractionRing (K ⊗[k] F)) l ∈ (integralClosureBaseChange K s).range :=
  (AlgHom.mem_range _).2 ⟨l ⊗ₜ 1, by
    change algebraMap (K ⊗[k] F) _ (l ⊗ₜ (1 : F)) = _
    rw [IsScalarTower.algebraMap_apply K (K ⊗[k] F), Algebra.TensorProduct.algebraMap_apply]
    rfl⟩

omit [IsFunctionFieldOneVar k F] in
private theorem integralClosureBaseChange_tmul_eq (s : F) (l : K)
    (b : (integralClosure (Algebra.adjoin k ({s} : Set F)) F).restrictScalars k) :
    integralClosureBaseChange K s (l ⊗ₜ b) = algebraMap K _ l *
      baseChangeFractionMap k C K F (algebraMap (C ⊗[k] F) _ ((1 : C) ⊗ₜ (b : F))) := by
  rw [baseChangeFractionMap_tmul, map_one (algebraMap C K)]
  change algebraMap (K ⊗[k] F) _ (l ⊗ₜ (b : F)) = _
  rw [IsScalarTower.algebraMap_apply K (K ⊗[k] F) (FractionRing (K ⊗[k] F)), ← map_mul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]
  rfl

/-- A regular derivation maps `1 ⊗ b` into the image of `C ⊗[k] B`. -/
private theorem derivation_one_tmul_mem_range {s : F} (hs : Transcendental k s)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({s} : Set F)) F]
    (δ : Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (hreg : ∀ V : ValuationSubring (FractionRing (C ⊗[k] F)),
      (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ x ∈ V)
    (b : (integralClosure (Algebra.adjoin k ({s} : Set F)) F).restrictScalars k) :
    δ (algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ (b : F))) ∈
      (integralClosureBaseChange C s).range := by
  have hy : algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ (b : F)) ∈
      integralClosure (Algebra.adjoin C
        {algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) ((1 : C) ⊗ₜ[k] s)}) _ := by
    rw [mem_integralClosure_iff, isIntegral_adjoin_iff_mem_range hs]
    exact (AlgHom.mem_range _).2 ⟨1 ⊗ₜ b, rfl⟩
  have hδy := mem_integralClosure_of_regular δ hreg hy
  rwa [mem_integralClosure_iff, isIntegral_adjoin_iff_mem_range hs] at hδy

/-- The extended derivation preserves the image of `K ⊗[k] B`. -/
private theorem derivation_mem_range_baseChange {s : F} (hs : Transcendental k s)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({s} : Set F)) F]
    (δ : Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (hreg : ∀ V : ValuationSubring (FractionRing (C ⊗[k] F)),
      (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ x ∈ V)
    (δ' : Derivation K (FractionRing (K ⊗[k] F)) (FractionRing (K ⊗[k] F)))
    (hcompat : ∀ x, δ' (baseChangeFractionMap k C K F x) = baseChangeFractionMap k C K F (δ x))
    (w : K ⊗[k] ((integralClosure (Algebra.adjoin k ({s} : Set F)) F).restrictScalars k)) :
    δ' (integralClosureBaseChange K s w) ∈ (integralClosureBaseChange K s).range := by
  induction w using TensorProduct.inductionOn with
  | tmul l b =>
    obtain ⟨w', hw'⟩ := (AlgHom.mem_range _).1 (derivation_one_tmul_mem_range hs δ hreg b)
    rw [integralClosureBaseChange_tmul_eq (C := C), Derivation.leibniz, Derivation.map_algebraMap,
      smul_zero, add_zero, hcompat, ← hw', smul_eq_mul]
    exact mul_mem (algebraMap_mem_range_integralClosureBaseChange s l)
      (baseChangeFractionMap_mem_range s w')
  | add v w hv hw =>
    rw [map_add, map_add]
    exact add_mem hv hw

/-- One chart of the regularity transfer: the extended derivation preserves the integral
closure of `K[1 ⊗ s]`. -/
private theorem mem_integralClosure_baseChange {s : F} (hs : Transcendental k s)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({s} : Set F)) F]
    (δ : Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (hreg : ∀ V : ValuationSubring (FractionRing (C ⊗[k] F)),
      (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ x ∈ V)
    (δ' : Derivation K (FractionRing (K ⊗[k] F)) (FractionRing (K ⊗[k] F)))
    (hcompat : ∀ x, δ' (baseChangeFractionMap k C K F x) = baseChangeFractionMap k C K F (δ x)) :
    ∀ x ∈ integralClosure (Algebra.adjoin K
        {algebraMap (K ⊗[k] F) (FractionRing (K ⊗[k] F)) ((1 : K) ⊗ₜ[k] s)}) _,
      δ' x ∈ integralClosure (Algebra.adjoin K
        {algebraMap (K ⊗[k] F) (FractionRing (K ⊗[k] F)) ((1 : K) ⊗ₜ[k] s)}) _ := by
  intro x hx
  rw [mem_integralClosure_iff, isIntegral_adjoin_iff_mem_range hs] at hx ⊢
  obtain ⟨w, rfl⟩ := (AlgHom.mem_range _).1 hx
  exact derivation_mem_range_baseChange hs δ hreg δ' hcompat w

/-- **Regular derivations under extension of constants.** Two `C`-linearly independent
derivations of `Frac(C ⊗[k] F)` over `C` preserving every proper valuation subring containing
`C` extend along `baseChangeFractionMap` to two `K`-linearly independent derivations of
`Frac(K ⊗[k] F)` over `K` preserving every proper valuation subring containing `K`. -/
theorem exists_regular_derivations_baseChange {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (δ : Fin 2 → Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (hδ : LinearIndependent C δ)
    (hreg : ∀ i (V : ValuationSubring (FractionRing (C ⊗[k] F))),
      (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ i x ∈ V) :
    ∃ δ' : Fin 2 → Derivation K (FractionRing (K ⊗[k] F)) (FractionRing (K ⊗[k] F)),
      LinearIndependent K δ' ∧
        (∀ i x, δ' i (baseChangeFractionMap k C K F x) =
          baseChangeFractionMap k C K F (δ i x)) ∧
        ∀ i (V : ValuationSubring (FractionRing (K ⊗[k] F))),
          (∀ c : K, algebraMap K _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ' i x ∈ V := by
  classical
  obtain ⟨_, e, he⟩ := isDomain_and_exists_fractionEquiv (k := k) (C := C) (K := K) (F := F)
  obtain ⟨D, hDind, hDf⟩ := exists_linearIndependent_derivations_baseChange (K := K) δ hδ
  have hcompat : ∀ i x, (D i).transport e (baseChangeFractionMap k C K F x) =
      baseChangeFractionMap k C K F (δ i x) := by
    intro i x
    change e (D i (e.symm (baseChangeFractionMap k C K F x))) = _
    rw [← he x, AlgEquiv.symm_apply_apply, hDf, he]
  refine ⟨fun i ↦ (D i).transport e, ?_, hcompat, fun i V hKV hV x hx ↦ ?_⟩
  · -- Independence transports along `e`.
    have hD2 : D = ![D 0, D 1] := by
      ext i : 1
      fin_cases i <;> rfl
    have hpair : LinearIndependent K ![D 0, D 1] := by
      rw [← hD2]
      exact hDind
    have hfun : (fun i ↦ (D i).transport e) =
        ![(D 0).transport e, (D 1).transport e] := by
      ext i : 1
      fin_cases i <;> rfl
    rw [hfun, LinearIndependent.pair_iff]
    intro a b hab
    apply LinearIndependent.pair_iff.1 hpair
    ext y
    have h := congrArg (fun D' : Derivation K (FractionRing (K ⊗[k] F))
      (FractionRing (K ⊗[k] F)) ↦ D' (e y)) hab
    simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.zero_apply] at h
    change a • e (D 0 (e.symm (e y))) + b • e (D 1 (e.symm (e y))) = 0 at h
    rw [AlgEquiv.symm_apply_apply, ← map_smul e a, ← map_smul e b, ← map_add,
      map_eq_zero_iff _ e.injective] at h
    simpa only [Derivation.add_apply, Derivation.smul_apply, Derivation.zero_apply] using h
  · -- Regularity, chart by chart.
    obtain ⟨ht', hadj⟩ := transcendental_inv_and_adjoin_inv ht
    have _ : Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
      rw [hadj]; infer_instance
    have hD₁ := mem_integralClosure_baseChange ht (δ i) (hreg i) _ (hcompat i)
    have hD₂ := mem_integralClosure_baseChange ht' (δ i) (hreg i) _ (hcompat i)
    rw [algebraMap_one_tmul_inv] at hD₂
    exact derivation_mem_valuationSubring_of_integralClosure ht _ hD₁ hD₂ V hKV hV hx

end

end AclGeom
