/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeAffineParameter
import AclGeom.Correspondence.SchemeActionCoefficientAlgebraicity
import AclGeom.Correspondence.SchemeEffectiveFunctionField
import AclGeom.Curves.CoefficientDerivations
import AclGeom.Curves.RegularDerivationBaseChange
import AclGeom.Curves.GenusZeroOfDerivations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Genus zero after constants for an actual regular affine action

Named source consumer: the genus step of blueprint `lem:affine-action` (#21).

**Status:** proved after an internally chosen algebraically closed constant extension for
an integral locally finite-type group of dimension at least two acting regularly and
faithfully on an integral affine locally finite-type dimension-one curve over an ACF base.
All chart, coefficient, rank, regularity, domain and one-variable inputs are derived.
Original-base genus/rationality descent, non-affine and rational-action cases, the normal
subgroup and arbitrary-action classifier remain open; all eight original #21 items stay open.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  isDomain_tensorProduct_of_isAlgClosed

private theorem exists_separating_parameter {F : Type u} [Field F] [Algebra k F]
    [PerfectField k] [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F = 1) :
    ∃ t : F, Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h
    exact_mod_cast h
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hcard
  have halg := hs.isAlgebraic_field
  have hr : Set.range ((↑) : ({t} : Finset F) → F) = {t} := by
    ext
    simp
  rw [hr] at halg
  rw [Finset.coe_singleton] at hsep
  have : Algebra.EssFiniteType (IntermediateField.adjoin k ({t} : Set F)) F :=
    Algebra.EssFiniteType.of_comp k _ _
  exact ⟨t, hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩,
    Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

private theorem exists_separating_function [PerfectField k]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] (hdim : topologicalKrullDim V.left = 1) :
    ∃ t : V.left.functionField, Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set V.left.functionField))
        V.left.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set V.left.functionField))
        V.left.functionField := by
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have : IsScalarTower k Γ(V.left, ⊤) V.left.functionField :=
    sections_functionField_isScalarTower V
  have := finiteType_sections V
  have : Algebra.EssFiniteType Γ(V.left, ⊤) V.left.functionField :=
    Algebra.EssFiniteType.of_isLocalization V.left.functionField (nonZeroDivisors Γ(V.left, ⊤))
  have : Algebra.EssFiniteType k V.left.functionField :=
    Algebra.EssFiniteType.comp k Γ(V.left, ⊤) V.left.functionField
  have he := IsHomeomorph.topologicalKrullDim_eq _ V.left.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim V.left = topologicalKrullDim (PrimeSpectrum Γ(V.left, ⊤)) at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  obtain ⟨m, hm, ht⟩ :=
    exists_ringKrullDim_trdeg_eq_of_finiteType k Γ(V.left, ⊤) V.left.functionField
  have hm1 : m = 1 := by exact_mod_cast hm.symm.trans (he.symm.trans hdim)
  apply exists_separating_parameter
  simpa only [hm1, Nat.cast_one] using ht

/-- A faithful regular action of an integral locally finite-type group of dimension at least
 two on an integral affine curve has genus zero after an internally chosen algebraically
 closed constant extension. Every chart, coefficient, rank and regularity premise is derived
 from the actual action. Original-base descent is the next named consumer. -/
theorem exists_constantExtension_genus_eq_zero [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom]
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimG : (2 : WithBot ℕ∞) ≤ topologicalKrullDim G.left)
    (hdimV : topologicalKrullDim V.left = 1) :
    letI := ActionFunctionField.functionFieldAlgebra V
    ∃ (K : Type u) (hK : Field K),
      letI := hK
      ∃ hAlg : Algebra k K,
      letI := hAlg
      ∃ (hACF : IsAlgClosed K) (hDom : IsDomain (K ⊗[k] V.left.functionField)),
      letI := hACF
      letI := hDom
      ∃ hOne : IsFunctionFieldOneVar K (FractionRing (K ⊗[k] V.left.functionField)),
      letI := hOne
      genus K (FractionRing (K ⊗[k] V.left.functionField)) = 0 := by
  obtain ⟨W, hI, hA, j, hOpen, hft, hrank⟩ := exists_affine_parameter G 2 hdimG
  have := hI
  have := hA
  have := hOpen
  let A := Γ(W.left, ⊤)
  let : Algebra k A := sectionsAlgebra W
  have : Algebra.FiniteType k A := hft
  let C := FractionRing A
  let g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G := (sectionsSpecIso W).inv ≫ j
  have : Mono j := Over.mono_of_mono_left j
  have : Mono g := inferInstance
  let φ : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  obtain ⟨s, hs, n, v, cA, hv, hcA, C0, c0, hC0, hfg, hgen, hcoe,
      τ, hτ, hmat, h0, hC, hF, rest⟩ := exists_effective_functionFieldAut V g φ
  have := h0
  have := hC
  have := hF
  obtain ⟨τF, _, _, hfaith, _⟩ := rest
  have hmem (e : Bool) (i : s) (j : Fin n) : algebraMap A C (cA e i j) ∈ C0 := by
    change φ (cA e i j) ∈ C0
    rw [← hcoe e i j]
    exact (c0 e i j).property
  have : Algebra.IsAlgebraic C0 C :=
    isAlgebraic_of_faithful_coefficients V hker g s hs v cA
      (fun ψ i ↦ hcA k ψ true i) C0 hmem
  have : FaithfulSMul k C0 :=
    (faithfulSMul_iff_algebraMap_injective k C0).2 (algebraMap k C0).injective
  have : FaithfulSMul C0 C :=
    (faithfulSMul_iff_algebraMap_injective C0 C).2 (algebraMap C0 C).injective
  have htr := trdeg_add_eq k C0 (A := C)
  rw [trdeg_eq_zero (R := C0) (A := C), add_zero] at htr
  have htr0 : (2 : Cardinal) ≤ Algebra.trdeg k C0 := hrank.trans_eq htr.symm
  have : Algebra.EssFiniteType k C0 := hfg
  obtain ⟨D, hD⟩ := exists_linearIndependent_derivations htr0
  obtain ⟨t, ht, hfin, hsep⟩ := exists_separating_function V hdimV
  have : IsFunctionFieldOneVar k V.left.functionField := ⟨⟨t, ht, hfin⟩⟩
  have := hsep
  obtain ⟨δ, hδ, hreg⟩ := exists_independent_regular_variations ht τF hfaith D hD
  let K := AlgebraicClosure C0
  have : IsScalarTower k C0 K := inferInstance
  obtain ⟨δ', hδ', _, hreg'⟩ :=
    exists_regular_derivations_baseChange (K := K) ht δ hδ hreg
  have hDom : IsDomain (K ⊗[k] V.left.functionField) := isDomain_tensorProduct_of_isAlgClosed
  let T := algebraMap (K ⊗[k] V.left.functionField)
    (FractionRing (K ⊗[k] V.left.functionField)) ((1 : K) ⊗ₜ[k] t)
  have hT : Transcendental K T := by
    intro hbad
    apply transcendental_one_tmul (C := K) ht
    exact (isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (K ⊗[k] V.left.functionField)
        (FractionRing (K ⊗[k] V.left.functionField)))
      (IsFractionRing.injective (K ⊗[k] V.left.functionField)
        (FractionRing (K ⊗[k] V.left.functionField)))).mp hbad
  have hOne : IsFunctionFieldOneVar K (FractionRing (K ⊗[k] V.left.functionField)) :=
    ⟨⟨T, hT, (finiteDimensional_isSeparable_adjoin (L := K) ht).1⟩⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, hDom, hOne, ?_⟩
  have := hOne
  exact genus_eq_zero_of_linearIndependent_regular δ' hδ' hreg'

end

end AclGeom.SchemeGenericTranslate
