/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.PointwiseFaithfulness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fin.VecNotation

/-!
# Rational affine coefficients from point specializations

**Status:** proved algebraic inputs for `SchemeAffineParameters` (#21). The Cramer criterion
constructs a nonzero common denominator from pointwise affine tensor identities over an ACF
base. The two-parameter criterion proves a finite field extension and transcendence basis.
Its algebraicity and rank premises are explicit; the actual group consumer derives them.
These are algebraic criteria, not a scheme finite-cover or full curve-action classifier.
-/

namespace AclGeom.AffineCoefficients

noncomputable section

open scoped TensorProduct

section Evaluation

variable {k F A : Type*} [CommRing k] [CommRing F] [Algebra k F]
  [CommRing A] [Algebra k A]

/-- Evaluate only the parameter coefficients. Named consumers: the Cramer criterion and
 the actual parameter/point function-field comparison. -/
def tensorPointEval (φ : A →ₐ[k] k) : A ⊗[k] F →ₐ[k] F :=
  Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ) (AlgHom.id k F)
    (fun _ _ ↦ Commute.all _ _)

/-- Evaluating coefficients specializes scalar multiplication as well.
 Named consumer: the localized affine formula for the actual point action. -/
theorem tensorPointEval_smul (φ : A →ₐ[k] k) (a : A) (z : A ⊗[k] F) :
    tensorPointEval φ (a • z) = φ a • tensorPointEval φ z := by
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change tensorPointEval φ ((a ⊗ₜ[k] (1 : F)) * z) = φ a • tensorPointEval φ z
  rw [map_mul, Algebra.smul_def]
  have h_eval : tensorPointEval φ (a ⊗ₜ[k] (1 : F)) = algebraMap k F (φ a) := by
    change algebraMap k F (φ a) * 1 = _
    exact mul_one _
  rw [h_eval]

end Evaluation

variable {k F A : Type*} [Field k] [Field F] [Algebra k F]
  [CommRing A] [Algebra k A]

private theorem exists_minor {ι : Type*} (B : Module.Basis ι k F)
    {t x : F} (ht : Transcendental k t) (hx : x ≠ 0) :
    ∃ i j, B.repr (t * x) i * B.repr x j - B.repr (t * x) j * B.repr x i ≠ 0 := by
  classical
  by_contra! h
  have hex : ∃ j, B.repr x j ≠ 0 := by
    by_contra! hh
    apply hx
    apply B.repr.injective
    ext j
    simpa only [map_zero, Finsupp.zero_apply] using hh j
  obtain ⟨j, hj⟩ := hex
  have he : t * x = (B.repr (t * x) j / B.repr x j) • x := by
    apply B.repr.injective
    ext i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (eq_div_iff hj).2
    exact sub_eq_zero.mp (h i j)
  have ht' : t = algebraMap k F (B.repr (t * x) j / B.repr x j) := by
    apply mul_right_cancel₀ hx
    exact he.trans (Algebra.smul_def _ _)
  exact ht (ht' ▸ isAlgebraic_algebraMap _)

/-- Pointwise affine expressions have one nonzero common denominator over the parameter
 domain. The actual scheme consumer derives both pointwise premises from its action. -/
theorem exists_cleared_coefficients [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A]
    {t : F} (ht : Transcendental k t) (U S : A ⊗[k] F)
    (hS : ∀ φ : A →ₐ[k] k, tensorPointEval φ S ≠ 0)
    (hU : ∀ φ : A →ₐ[k] k, ∃ a b : k,
      tensorPointEval φ U =
        (algebraMap k F a * t + algebraMap k F b) * tensorPointEval φ S) :
    ∃ d a b : A, d ≠ 0 ∧
      d • U = a • ((1 ⊗ₜ[k] t) * S) + b • S := by
  classical
  let B := Module.Free.chooseBasis k F
  let c := (B.baseChange A).repr
  let V := (1 ⊗ₜ[k] t) * S
  have hcoord (φ : A →ₐ[k] k) (z : A ⊗[k] F) (i) :
      B.repr (tensorPointEval φ z) i = φ (c z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul a f =>
      change B.repr ((Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ)
        (AlgHom.id k F) (fun _ _ ↦ Commute.all _ _)) (a ⊗ₜ[k] f)) i = _
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        AlgHom.id_apply, Algebra.ofId_apply, c, Module.Basis.baseChange_repr_tmul]
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, map_smul]
      exact mul_comm _ _
    | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]
  have hV (φ : A →ₐ[k] k) : tensorPointEval φ V = t * tensorPointEval φ S := by
    change tensorPointEval φ ((1 ⊗ₜ[k] t) * S) = _
    rw [map_mul]
    have h_eval : tensorPointEval φ (1 ⊗ₜ[k] t) = t := by
      change algebraMap k F (φ 1) * t = t
      rw [map_one, map_one, one_mul]
    rw [h_eval]
  have hex : Nonempty (A →ₐ[k] k) := by
    by_contra hn
    have hh : IsNilpotent (1 : A) := isNilpotent_of_forall_algHom_eq_zero
      (fun φ ↦ False.elim (hn ⟨φ⟩))
    exact not_isNilpotent_one hh
  let φ0 : A →ₐ[k] k := Classical.choice hex
  obtain ⟨i, j, hij⟩ := exists_minor B ht (hS φ0)
  let d := c V i * c S j - c V j * c S i
  let a := c U i * c S j - c U j * c S i
  let b := c V i * c U j - c V j * c U i
  have hd : d ≠ 0 := by
    intro hz
    apply hij
    rw [← hV φ0, hcoord, hcoord, hcoord, hcoord]
    rw [← map_mul, ← map_mul, ← map_sub]
    simpa only [map_zero] using congrArg φ0 hz
  refine ⟨d, a, b, hd, ?_⟩
  apply c.injective
  ext l
  simp only [map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
  change d * c U l = a * c V l + b * c S l
  apply sub_eq_zero.mp
  apply IsNilpotent.eq_zero
  apply isNilpotent_of_forall_algHom_eq_zero (k := k)
  intro φ
  obtain ⟨α, β, hαβ⟩ := hU φ
  have hrow (l) : φ (c U l) = α * φ (c V l) + β * φ (c S l) := by
    have he : tensorPointEval φ U = α • tensorPointEval φ V +
        β • tensorPointEval φ S := by
      rw [hV, hαβ, Algebra.smul_def, Algebra.smul_def]
      ring
    rw [← hcoord φ U l, ← hcoord φ V l, ← hcoord φ S l, he,
      map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [map_sub, map_add, map_mul, d, a, b, hrow]
  ring

end

end AclGeom.AffineCoefficients

namespace AclGeom.AffineCoefficients

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

/-- An algebraic two-parameter presentation at rank at least two is a finite field cover
 of two independent rational parameters. Named consumer: the actual group coefficients. -/
theorem finite_pair_parameters {k C : Type*} [Field k] [Field C] [Algebra k C]
    [Algebra.EssFiniteType k C] (a b : C)
    (htr : (2 : Cardinal) ≤ Algebra.trdeg k C)
    [Algebra.IsAlgebraic (IntermediateField.adjoin k ({a, b} : Set C)) C] :
    FiniteDimensional (IntermediateField.adjoin k ({a, b} : Set C)) C ∧
      IsTranscendenceBasis k (![a, b] : Fin 2 → C) := by
  let C0 := IntermediateField.adjoin k ({a, b} : Set C)
  have : Algebra.EssFiniteType C0 C := Algebra.EssFiniteType.of_comp k C0 C
  have hfinite : FiniteDimensional C0 C := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : Algebra.IsAlgebraic (Algebra.adjoin k ({a, b} : Set C)) C :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin k ({a, b} : Set C)) C0 C
  have hrange : Set.range (![a, b] : Fin 2 → C) = ({a, b} : Set C) :=
    Matrix.range_cons_cons_empty a b ![]
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (![a, b] : Fin 2 → C))) C := by
    rw [hrange]
    infer_instance
  refine ⟨hfinite, ?_⟩
  apply Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k
  simpa using htr

end

end AclGeom.AffineCoefficients
