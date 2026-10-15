/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.ConstantExtension
import AclGeom.Curves.DerivationExtension

/-!
# Coefficient connections and regular curve variations

On the formal constant extension `Frac(C ⊗[k] F)`, a derivation of the ordinary coefficient
field extends to a connection fixing `F`. Conjugating by a `C`-automorphism and subtracting
the connection gives a `C`-linear curve derivation. Horizontal regularity and valuation
comaps prove that these variations are regular. An injective variation map sends two
independent coefficient derivations to two independent regular curve derivations.

**Status:** proved, with no unproved hypotheses (#21). Used by the actual Hrushovski–Weil
genus theorem in `GroupConfig.Germ.CurveGenus`.
-/

namespace AclGeom

open scoped TensorProduct

noncomputable section

section CoefficientConnection

variable {k F C : Type*} [Field k] [Field F] [Field C] [Algebra k F] [Algebra k C]
  [IsAlgClosed k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : IsDomain (C ⊗[k] F) := isDomain_tensorProduct_of_isAlgClosed

/-- The coefficient connection on the formal constant extension. It fixes the
function field factor, without extending a coefficient derivation to an algebraic closure. -/
def coefficientConnection (D : Derivation k C C) :
    Derivation F (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)) :=
  Derivation.extendOfFormallyEtale
    ((Algebra.linearMap (C ⊗[k] F) (FractionRing (C ⊗[k] F))).compDer
      (D.extendOfPushout F (C ⊗[k] F)))

omit [IsAlgClosed k] in
theorem coefficientConnection_coeff (D : Derivation k C C) (c : C) :
    coefficientConnection (F := F) D (algebraMap C (FractionRing (C ⊗[k] F)) c) =
      algebraMap C (FractionRing (C ⊗[k] F)) (D c) := by
  rw [IsScalarTower.algebraMap_apply C (C ⊗[k] F) (FractionRing (C ⊗[k] F)) c]
  rw [coefficientConnection, Derivation.extendOfFormallyEtale_algebraMap]
  change algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F))
    (D.extendOfPushout F (C ⊗[k] F) (algebraMap C (C ⊗[k] F) c)) = _
  rw [Derivation.extendOfPushout_algebraMap, ← IsScalarTower.algebraMap_apply]

omit [IsAlgClosed k] in
theorem coefficientConnection_function (D : Derivation k C C) (f : F) :
    coefficientConnection (F := F) D (algebraMap F (FractionRing (C ⊗[k] F)) f) = 0 :=
  Derivation.map_algebraMap _ _

private theorem fractionDerivation_ext' {R A E : Type*} [CommRing R] [CommRing A]
    [Field E] [Algebra R E] [Algebra A E] [IsFractionRing A E]
    (D₁ D₂ : Derivation R E E)
    (h : ∀ a : A, D₁ (algebraMap A E a) = D₂ (algebraMap A E a)) : D₁ = D₂ := by
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [Derivation.leibniz_div, Derivation.leibniz_div, h, h]

/-- A connection fixing the function-field factor is determined by its coefficient values. -/
private theorem coefficientConnection_ext'
    (D₁ D₂ : Derivation F (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)))
    (h : ∀ c : C, D₁ (algebraMap C (FractionRing (C ⊗[k] F)) c) =
      D₂ (algebraMap C (FractionRing (C ⊗[k] F)) c)) : D₁ = D₂ := by
  apply fractionDerivation_ext' (A := C ⊗[k] F)
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul c f =>
    have ht : algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) (c ⊗ₜ[k] f) =
        algebraMap F (FractionRing (C ⊗[k] F)) f *
          algebraMap C (FractionRing (C ⊗[k] F)) c := by
      rw [IsScalarTower.algebraMap_apply F (C ⊗[k] F) (FractionRing (C ⊗[k] F)),
        IsScalarTower.algebraMap_apply C (C ⊗[k] F) (FractionRing (C ⊗[k] F)), ← map_mul]
      simp only [Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.algebraMap_self_apply]
    rw [ht, Derivation.leibniz, Derivation.leibniz, h,
      Derivation.map_algebraMap, Derivation.map_algebraMap]
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Coefficient derivations act linearly on the formal constant extension. -/
private def coefficientConnectionLinear' :
    Derivation k C C →ₗ[C]
      Derivation F (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)) where
  toFun := coefficientConnection
  map_add' D₁ D₂ := by
    apply coefficientConnection_ext'
    intro c
    simp only [coefficientConnection_coeff, Derivation.add_apply, map_add]
  map_smul' c D := by
    apply coefficientConnection_ext'
    intro d
    simp only [coefficientConnection_coeff, Derivation.smul_apply, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self_apply, RingHom.id_apply]

/-- The infinitesimal variation of a coefficient-field automorphism is a
coefficient-linear derivation, although the connection itself differentiates coefficients. -/
def coefficientVariation
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (D : Derivation k C C) :
    Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)) where
  toFun x := g (coefficientConnection D (g.symm x)) - coefficientConnection D x
  map_add' x y := by simp only [map_add]; ring
  map_smul' c x := by
    simp only [smul_eq_mul, Algebra.smul_def, RingHom.id_apply, map_mul,
      AlgEquiv.commutes, Derivation.leibniz,
      coefficientConnection_coeff, map_add, AlgEquiv.apply_symm_apply]
    ring
  map_one_eq_zero' := by
    change g (coefficientConnection D (g.symm 1)) - coefficientConnection D 1 = 0
    simp only [map_one, Derivation.map_one_eq_zero, map_zero, sub_self]
  leibniz' x y := by
    change g (coefficientConnection D (g.symm (x * y))) -
      coefficientConnection D (x * y) =
        x • (g (coefficientConnection D (g.symm y)) - coefficientConnection D y) +
        y • (g (coefficientConnection D (g.symm x)) - coefficientConnection D x)
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, AlgEquiv.apply_symm_apply]
    ring

omit [IsAlgClosed k] in
private theorem coefficientVariation_apply
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (D : Derivation k C C) (x : FractionRing (C ⊗[k] F)) :
    coefficientVariation g D x =
      g (coefficientConnection D (g.symm x)) - coefficientConnection D x := rfl

omit [IsAlgClosed k] in
theorem coefficientVariation_eq_zero_iff
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (D : Derivation k C C) : coefficientVariation g D = 0 ↔
      ∀ x, coefficientConnection D (g x) = g (coefficientConnection D x) := by
  constructor
  · intro h x
    have hx := Derivation.congr_fun h (g x)
    change g (coefficientConnection D (g.symm (g x))) - coefficientConnection D (g x) = 0 at hx
    rw [g.symm_apply_apply] at hx
    exact (sub_eq_zero.mp hx).symm
  · intro h
    ext x
    change g (coefficientConnection D (g.symm x)) - coefficientConnection D x = 0
    rw [← h (g.symm x), g.apply_symm_apply, sub_self]

/-- Linear dependence of the variation on the ordinary coefficient derivation. -/
def coefficientVariationLinear
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F)) :
    Derivation k C C →ₗ[C]
      Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)) where
  toFun := coefficientVariation g
  map_add' D₁ D₂ := by
    ext x
    have h := (coefficientConnectionLinear' (k := k) (F := F) (C := C)).map_add D₁ D₂
    simp only [coefficientVariation_apply, show coefficientConnection (D₁ + D₂) =
      coefficientConnection (F := F) D₁ + coefficientConnection D₂ from h,
      Derivation.add_apply, map_add]
    ring
  map_smul' c D := by
    ext x
    have h := (coefficientConnectionLinear' (k := k) (F := F) (C := C)).map_smul c D
    simp only [coefficientVariation_apply, show coefficientConnection (c • D) =
      c • coefficientConnection (F := F) D from h,
      Derivation.smul_apply, map_smul, smul_sub, RingHom.id_apply]

/-- A zero-kernel criterion stated before specializing the formal base field. -/
theorem coefficientVariationLinear_injective
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (h : ∀ D : Derivation k C C, coefficientVariation g D = 0 → D = 0) :
    Function.Injective (coefficientVariationLinear (k := k) g) :=
  (injective_iff_map_eq_zero _).mpr h

section Regularity

variable [IsFunctionFieldOneVar k F] {t : F} (ht : Transcendental k t)
  [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]

include ht

/-- The actual horizontal coefficient connection preserves every proper valuation ring
containing the ordinary coefficient field. -/
theorem coefficientConnection_regular (D : Derivation k C C)
    (V : ValuationSubring (FractionRing (C ⊗[k] F)))
    (hCV : ∀ c : C, algebraMap C (FractionRing (C ⊗[k] F)) c ∈ V) (hV : V ≠ ⊤)
    {x : FractionRing (C ⊗[k] F)} (hx : x ∈ V) : coefficientConnection D x ∈ V := by
  apply derivation_mem_valuationSubring_of_horizontal (k := k) (L := C) ht
    (coefficientConnection D) ?_ ?_ V hCV hV hx
  · intro c
    rw [coefficientConnection_coeff]
    exact ⟨D c, rfl⟩
  · intro f
    change coefficientConnection D
      (algebraMap (C ⊗[k] F) (FractionRing (C ⊗[k] F)) (algebraMap F (C ⊗[k] F) f)) = 0
    rw [← IsScalarTower.algebraMap_apply]
    exact coefficientConnection_function D f

/-- Conjugating the horizontal connection permutes the coefficient valuation rings;
its coefficient-linear variation is therefore regular at every one of them. -/
theorem coefficientVariation_regular
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F)) (D : Derivation k C C)
    (V : ValuationSubring (FractionRing (C ⊗[k] F)))
    (hCV : ∀ c : C, algebraMap C (FractionRing (C ⊗[k] F)) c ∈ V) (hV : V ≠ ⊤)
    {x : FractionRing (C ⊗[k] F)} (hx : x ∈ V) : coefficientVariation g D x ∈ V := by
  let W := V.comap g.toRingEquiv.toRingHom
  have hCW (c : C) : algebraMap C (FractionRing (C ⊗[k] F)) c ∈ W := by
    change g (algebraMap C (FractionRing (C ⊗[k] F)) c) ∈ V
    rw [g.commutes]
    exact hCV c
  have hW : W ≠ ⊤ := by
    intro h
    apply hV
    apply top_unique
    intro z _
    have hz : g.symm z ∈ W := by rw [h]; exact ValuationSubring.mem_top _
    change g (g.symm z) ∈ V at hz
    simpa only [g.apply_symm_apply] using hz
  have hix : g.symm x ∈ W := by
    change g (g.symm x) ∈ V
    simpa only [g.apply_symm_apply] using hx
  have hconj := coefficientConnection_regular ht D W hCW hW hix
  change g (coefficientConnection D (g.symm x)) ∈ V at hconj
  change g (coefficientConnection D (g.symm x)) - coefficientConnection D x ∈ V
  exact V.sub_mem hconj (coefficientConnection_regular ht D V hCV hV hx)

/-- An injective variation map sends two independent coefficient derivations to two
independent regular curve derivations. The actual HW consumer supplies injectivity and rank. -/
theorem exists_independent_regular_variations
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (hg : Function.Injective (coefficientVariationLinear (k := k) g))
    (D : Fin 2 → Derivation k C C) (hD : LinearIndependent C D) :
    ∃ δ : Fin 2 → Derivation C (FractionRing (C ⊗[k] F)) (FractionRing (C ⊗[k] F)),
      LinearIndependent C δ ∧
        ∀ i (V : ValuationSubring (FractionRing (C ⊗[k] F))),
          (∀ c : C, algebraMap C _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, δ i x ∈ V := by
  let L := coefficientVariationLinear (k := k) g
  refine ⟨L ∘ D, hD.map' L (LinearMap.ker_eq_bot.mpr hg), ?_⟩
  intro i V hCV hV x hx
  exact coefficientVariation_regular ht g (D i) V hCV hV hx

end Regularity

end CoefficientConnection

end

end AclGeom
