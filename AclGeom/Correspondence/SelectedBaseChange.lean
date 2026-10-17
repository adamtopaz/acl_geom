/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.CurveEquation
import AclGeom.Correspondence.LocusDimension
import AclGeom.Correspondence.LocusIncomparability
import AclGeom.Correspondence.AmbientAutomorphism
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Selected branches after extending a coefficient field

A scalar finite-correspondence branch stays a selected minimal prime after coefficient
extension whenever its endpoints still present a finite correspondence. The extended ideal
may split. Named intended consumer: the literal parameter-field branch of the six-point
incidence calculation (8.4c) in `Config.ParameterField`.

The selected ideal may be a proper component of the extension. Conversely, in an
algebraically closed ambient field with an element transcendental over the larger field, every
minimal prime of the extension is the ideal of a finite correspondence over the larger field at an
automorphic image of the original endpoints over the smaller field, whose source stays
transcendental over the larger field
(`FiniteCorrespondencePair.exists_conjugate_of_mem_minimalPrimes_baseChange`). The automorphism
need not preserve the larger field, so this is a parametrization of the branches by conjugate
points, not an action on them. Named consumer: the literal family branches of the six-point
incidence calculation in `Config.ParameterField`. A coherent choice of branches and a common
normal cover require separate arguments.

**Status:** selected-branch minimality is proved over arbitrary fields, and the description of
every minimal prime by a generic conjugate in an algebraically closed ambient field. A coherent
choice of branches, the common normal cover and the parameter-family forms of (8.4c) and (8.6)
remain open (#5).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open MvPolynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The same finite-correspondence endpoints select a minimal prime of the extended curve
ideal over a larger coefficient field. Neither coefficient field needs to be closed. -/
theorem FiniteCorrespondencePair.ideal_mem_minimalPrimes_baseChange
    {E F : IntermediateField k Ω} (hEF : E ≤ F)
    (P : FiniteCorrespondencePair E Ω) (Q : FiniteCorrespondencePair F Ω)
    (hs : P.source = Q.source) (ht : P.target = Q.target) :
    Q.ideal ∈ (P.ideal.map
      (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F))).minimalPrimes := by
  have hle :
      P.ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F)) ≤ Q.ideal := by
    simpa only [FiniteCorrespondencePair.ideal, hs, ht] using
      idealOf_map_le_of_intermediateField_le hEF ![Q.source, Q.target]
  have hnonzero :
      MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F) P.curveEquation ≠ 0 := by
    intro h
    exact P.curveEquation_prime.ne_zero
      ((MvPolynomial.map_injective _ (IntermediateField.inclusion hEF).injective)
        (h.trans (map_zero _).symm))
  have hsmall : Q.ideal.height ≤ 1 := by
    rw [Q.ideal_eq_span_curveEquation]
    exact Ideal.height_span_singleton_le_one Q.curveEquation_prime.not_isUnit
  have hlarge :
      1 ≤ (P.ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F))).height := by
    rw [P.ideal_eq_span_curveEquation, Ideal.map_span, Set.image_singleton]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero)
  have : Q.ideal.IsPrime := by
    change (idealOf F ![Q.source, Q.target]).IsPrime
    infer_instance
  exact Ideal.mem_minimalPrimes_of_height_le hle (hsmall.trans hlarge)

/-- Relative algebraicity over a coefficient field persists over a larger coefficient field. -/
private theorem mem_racl_of_le {E F : IntermediateField k Ω} (hEF : E ≤ F) {S : Set Ω} {x : Ω}
    (hx : x ∈ racl E S) : x ∈ racl F S := by
  rw [mem_racl_iff] at hx ⊢
  have hle : (IntermediateField.adjoin E S).restrictScalars k ≤
      (IntermediateField.adjoin F S).restrictScalars k := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.restrictScalars_adjoin_eq_sup]
    exact sup_le_sup_right hEF _
  have hx' : IsAlgebraic ((IntermediateField.adjoin E S).restrictScalars k) x := hx
  exact isAlgebraic_of_le hle hx'

/-- Maximal ideals of the polynomial ring in two variables over a field have height two. -/
private theorem height_eq_two_of_isMaximal {F : Type*} [Field F]
    (J : Ideal (MvPolynomial (Fin 2) F)) [J.IsMaximal] : J.height = 2 := by
  let e₁ : MvPolynomial (Fin 1) F ≃+* Polynomial F :=
    ((MvPolynomial.finSuccEquiv F 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv F (Fin 0)))).toRingEquiv
  let e : MvPolynomial (Fin 2) F ≃+* Polynomial (Polynomial F) :=
    (MvPolynomial.finSuccEquiv F 1).toRingEquiv.trans (Polynomial.mapEquiv e₁)
  rw [← e.height_map J]
  have : ((J.map e).under (Polynomial F)).IsMaximal :=
    Polynomial.isMaximal_comap_C_of_isJacobsonRing _
  rw [Polynomial.height_eq_height_add_one ((J.map e).under (Polynomial F)) (J.map e),
    IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField F)]
  exact one_add_one_eq_two

/-- **Every branch of an extended curve ideal is a generic conjugate.** Let `E ≤ F` be
intermediate fields of an algebraically closed field `Ω` containing an element transcendental
over `F`, and let `(x, y)` present a finite correspondence over `E`. Every minimal prime of the
extension to `F` of its curve ideal is the ideal of a finite correspondence over `F` at
`(σ x, σ y)` for some automorphism `σ` of `Ω` over `E`; in particular `σ x` is transcendental
over `F`. The automorphism need not preserve `F`. -/
theorem FiniteCorrespondencePair.exists_conjugate_of_mem_minimalPrimes_baseChange
    [IsAlgClosed Ω] {E F : IntermediateField k Ω} (hEF : E ≤ F)
    (P : FiniteCorrespondencePair E Ω) {z : Ω} (hz : z ∉ racl F (∅ : Set Ω))
    {J : Ideal (MvPolynomial (Fin 2) F)}
    (hJ : J ∈ (P.ideal.map
      (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F))).minimalPrimes) :
    ∃ (Q : FiniteCorrespondencePair F Ω) (σ : Ω ≃ₐ[E] Ω),
      Q.ideal = J ∧ Q.source = σ P.source ∧ Q.target = σ P.target := by
  have : J.IsPrime := hJ.1.1
  let g := MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F) P.curveEquation
  have hg0 : g ≠ 0 := by
    intro h
    exact P.curveEquation_prime.ne_zero
      ((MvPolynomial.map_injective _ (IntermediateField.inclusion hEF).injective)
        (h.trans (map_zero _).symm))
  have hspan : P.ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F)) =
      Ideal.span {g} := by
    rw [P.ideal_eq_span_curveEquation, Ideal.map_span, Set.image_singleton]
  have hgJ : Ideal.span {g} ≤ J := hspan ▸ hJ.1.2
  -- Minimality over a principal ideal bounds the height of `J`.
  have hht : J.height ≤ 1 := by
    have : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ J (hspan ▸ hJ)
  -- Realize `J` by a tuple of `Ω`.
  obtain ⟨n, hn, hiff⟩ := exists_idealOf_eq_iff (k := F) (Ω := Ω) J
  have hn1 : n ≤ 1 := by
    have hdim : ringKrullDim (MvPolynomial (Fin 2) F) = 2 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    have hle : ringKrullDim (MvPolynomial (Fin 2) F ⧸ J) + 1 ≤ 2 :=
      (add_le_add (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hgJ))
        le_rfl).trans ((ringKrullDim_quotient_succ_le_of_nonZeroDivisor
          (mem_nonZeroDivisors_of_ne_zero hg0)).trans_eq hdim)
    rw [hn] at hle
    have h2 : n + 1 ≤ 2 := by exact_mod_cast hle
    exact Nat.le_of_lt_succ h2
  have htr : (1 : Cardinal) ≤ Algebra.trdeg F Ω := by
    have hind : AlgebraicIndependent F (fun _ : Fin 1 ↦ z) :=
      algebraicIndependent_unique_type_iff.2 fun h ↦ hz (mem_racl_empty_of_isAlgebraic h)
    simpa using hind.lift_cardinalMk_le_trdeg
  obtain ⟨w, hw⟩ := hiff.2 ((Nat.cast_le.2 hn1).trans (by simpa using htr))
  -- The original curve ideal vanishes at the realized tuple.
  have hPw : P.ideal ≤ idealOf E w := by
    intro p hp
    have hmap : MvPolynomial.map (IntermediateField.inclusion hEF : E →+* F) p ∈ idealOf F w :=
      hw ▸ hJ.1.2 (Ideal.mem_map_of_mem _ hp)
    rw [mem_idealOf_iff] at hmap ⊢
    change MvPolynomial.eval₂ (algebraMap F Ω) w (MvPolynomial.map _ p) = 0 at hmap
    rw [MvPolynomial.eval₂_map] at hmap
    exact hmap
  -- The realized tuple is not algebraic over `F`: otherwise `J` would be maximal.
  have hnalg : ∃ i, w i ∉ racl F (∅ : Set Ω) := by
    by_contra! hall
    obtain ⟨m, hm, hmtr⟩ := exists_locusCoordinateRing_dimension (k := F) w
    have : Algebra.IsAlgebraic F (IntermediateField.adjoin F (Set.range w)) :=
      IntermediateField.isAlgebraic_adjoin
        (Set.forall_mem_range.2 fun i ↦ (isAlgebraic_of_mem_racl_empty (hall i)).isIntegral)
    have hm0 : m = 0 := by exact_mod_cast hmtr.symm.trans trdeg_eq_zero
    rw [hm0, hw] at hm
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin 2) F ⧸ J) := Ring.krullDimLE_iff.2 hm.le
    have : J.IsMaximal := Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain
    rw [height_eq_two_of_isMaximal J] at hht
    exact absurd (by exact_mod_cast hht : (2 : ℕ) ≤ 1) (by norm_num)
  -- Hence the realized tuple has the original locus over `E`.
  have hEq : P.ideal = idealOf E w := by
    obtain ⟨i, hi⟩ := id hnalg
    have hiE : w i ∉ racl E (∅ : Set Ω) := fun h ↦ hi (mem_racl_of_le hEF h)
    have hbot (c : Ω) (hc : c ∉ racl E (∅ : Set Ω)) : idealOf E (fun _ : Fin 1 ↦ c) = ⊥ :=
      algebraicIndependent_iff_ker_eq_bot.1
        (algebraicIndependent_unique_type_iff.2 fun h ↦ hc (mem_racl_empty_of_isAlgebraic h))
    refine (idealOf_eq_of_le_of_comap_eq (k := E) ![P.source, P.target] (fun _ : Fin 1 ↦ i)
      ?_ hPw ?_).symm
    · have hr : Set.range (![P.source, P.target] ∘ fun _ : Fin 1 ↦ i) =
          {![P.source, P.target] i} := Set.range_const
      intro j
      rw [hr]
      fin_cases i <;> fin_cases j
      · exact subset_racl E _ (Set.mem_singleton _)
      · exact P.target_mem_source
      · exact P.source_mem_target
      · exact subset_racl E _ (Set.mem_singleton _)
    · rw [← idealOf_eq_comap_rename (k := E) (a := w) (b := w ∘ fun _ : Fin 1 ↦ i)
        (g := fun _ : Fin 1 ↦ i) rfl]
      change idealOf E (fun _ : Fin 1 ↦ w i) = idealOf E (fun _ : Fin 1 ↦ ![P.source, P.target] i)
      rw [hbot _ hiE, hbot]
      fin_cases i
      · exact P.source_generic
      · exact P.target_generic
  -- The ambient automorphism carrying the original endpoints to the realized tuple.
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := E)
    (a := ![P.source, P.target]) (b := w) hEq
  have hσ0 : σ P.source = w 0 := hσ 0
  have hσ1 : σ P.target = w 1 := hσ 1
  have hy : w 1 ∈ racl E {w 0} := by
    have h := (algHom_mem_racl_image_iff (σ : Ω →ₐ[E] Ω) (S := {P.source})).2 P.target_mem_source
    simpa [Set.image_singleton, hσ0, hσ1] using h
  have hx : w 0 ∈ racl E {w 1} := by
    have h := (algHom_mem_racl_image_iff (σ : Ω →ₐ[E] Ω) (S := {P.target})).2 P.source_mem_target
    simpa [Set.image_singleton, hσ0, hσ1] using h
  -- The conjugate source stays transcendental over `F`.
  have h0 : w 0 ∉ racl F (∅ : Set Ω) := by
    intro h0
    have h1 : w 1 ∈ racl F (∅ : Set Ω) :=
      racl_le_of_subset_racl (Set.singleton_subset_iff.2 h0) (mem_racl_of_le hEF hy)
    obtain ⟨i, hi⟩ := hnalg
    fin_cases i
    · exact hi h0
    · exact hi h1
  refine ⟨⟨w 0, w 1, h0, mem_racl_of_le hEF hy, mem_racl_of_le hEF hx⟩, σ, ?_, hσ0.symm,
    hσ1.symm⟩
  change idealOf F ![w 0, w 1] = J
  rw [← hw]
  congr 1
  funext j
  fin_cases j <;> rfl

end AclGeom
