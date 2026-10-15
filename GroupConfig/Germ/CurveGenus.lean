/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.CoefficientConnection
import AclGeom.Curves.CoefficientDerivations
import AclGeom.Curves.ConstantExtension
import AclGeom.Curves.GenusZeroOfDerivations
import AclGeom.Curves.RegularDerivationBaseChange
import AclGeom.Curves.TensorFractionFields
import GroupConfig.Germ.BaseFunctionField
import GroupConfig.Germ.DerivationConstants
import GroupConfig.Germ.FunctionFieldAction
import GroupConfig.Germ.FunctionFieldGraph
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Genus zero for an actual Hrushovski–Weil curve action

For genuine HW data on a finite tuple of rank one, ordinary canonical-base rank at least two
forces the actual locus function field to have genus zero over the universal domain. The
proof derives a faithful infinitesimal variation over the ordinary coefficient field,
constructs two independent regular curve derivations and extends them to the ambient
constants. The one-variable structure and all comparison, inverse and regularity data are
derived internally.

**Status:** `Germ.IsHW.genus_eq_zero` is proved (#21). The original scheme/action bridge,
normal-subgroup producer, Möbius and affine classification, chart descent and full
reconstruction remain obligations.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set
open scoped TensorProduct

noncomputable section

section FormalCoordinateRing

variable {k C : Type*} [CommRing k] [CommRing C] [Algebra k C] {ι : Type*}

/-- The formal coordinate ring commutes with constant extension. Its consumer identifies
formal tensor fraction fields with the actual ordinary-coefficient field of the locus. -/
private def tensorCoordinateQuotientEquiv' (I : Ideal (MvPolynomial ι k)) :
    C ⊗[k] (MvPolynomial ι k ⧸ I) ≃ₐ[C]
      MvPolynomial ι C ⧸ I.map (MvPolynomial.map (algebraMap k C)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := k) C (MvPolynomial ι k) C I).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv k C) (by
      change I.map (MvPolynomial.map (algebraMap k C)) =
        (I.map (Algebra.TensorProduct.includeRight : MvPolynomial ι k →ₐ[k]
          C ⊗[k] MvPolynomial ι k).toRingHom).map
            (MvPolynomial.algebraTensorAlgEquiv k C).toRingHom
      rw [Ideal.map_map]
      congr 1
      apply RingHom.ext
      intro P
      change MvPolynomial.map (algebraMap k C) P =
        MvPolynomial.algebraTensorAlgEquiv k C ((1 : C) ⊗ₜ[k] P)
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]))

private theorem tensorCoordinateQuotientEquiv'_tmul (I : Ideal (MvPolynomial ι k))
    (c : C) (P : MvPolynomial ι k) :
    tensorCoordinateQuotientEquiv' I (c ⊗ₜ[k] Ideal.Quotient.mk I P) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k C)))
        (c • MvPolynomial.map (algebraMap k C) P) := by
  simp only [tensorCoordinateQuotientEquiv', AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

private theorem tensorCoordinateQuotientEquiv'_X (I : Ideal (MvPolynomial ι k)) (i : ι) :
    tensorCoordinateQuotientEquiv' (C := C) I
      ((1 : C) ⊗ₜ[k] Ideal.Quotient.mk I (X i : MvPolynomial ι k)) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k C))) (X i : MvPolynomial ι C) := by
  simpa only [MvPolynomial.map_X, one_smul] using
    tensorCoordinateQuotientEquiv'_tmul (k := k) (C := C) I 1 (X i : MvPolynomial ι k)

end FormalCoordinateRing



/-- An injective coefficient-algebra map identifies the polynomial kernels of tuples
which it identifies coordinatewise. Its consumer is the actual rational graph comparison. -/
private theorem ker_aeval_eq_of_injective' {R A B ι : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    (hφ : Function.Injective φ) (x : ι → A) (y : ι → B) (hxy : ∀ i, φ (x i) = y i) :
    RingHom.ker (aeval (R := R) x).toRingHom =
      RingHom.ker (aeval (R := R) y).toRingHom := by
  have heval (P : MvPolynomial ι R) : φ (aeval x P) = aeval y P := by
    rw [MvPolynomial.comp_aeval_apply]
    exact congrArg (fun z ↦ aeval z P) (funext hxy)
  ext P
  change aeval x P = 0 ↔ aeval y P = 0
  rw [← heval, map_eq_zero_iff _ hφ]

section RegularDerivationTransport

variable {R A B : Type*} [Field R] [Field A] [Field B] [Algebra R A] [Algebra R B]

private theorem transportDerivation'_regular (e : A ≃ₐ[R] B) (D : Derivation R A A)
    (hD : ∀ W : ValuationSubring A, (∀ c : R, algebraMap R A c ∈ W) → W ≠ ⊤ →
      ∀ x ∈ W, D x ∈ W)
    (V : ValuationSubring B) (hRV : ∀ c : R, algebraMap R B c ∈ V) (hV : V ≠ ⊤)
    {x : B} (hx : x ∈ V) : D.transport e x ∈ V := by
  let W := V.comap e.toRingHom
  have hRW (c : R) : algebraMap R A c ∈ W := by
    change e (algebraMap R A c) ∈ V
    rw [e.commutes]
    exact hRV c
  have hW : W ≠ ⊤ := by
    intro h
    apply hV
    apply top_unique
    intro z _
    have hz : e.symm z ∈ W := by rw [h]; exact ValuationSubring.mem_top _
    change e (e.symm z) ∈ V at hz
    simpa only [e.apply_symm_apply] using hz
  have hix : e.symm x ∈ W := by
    change e (e.symm x) ∈ V
    simpa only [e.apply_symm_apply] using hx
  exact hD W hRW hW _ hix

end RegularDerivationTransport


section CoefficientComponents

variable {C K : Type*} [Field C] [Field K] [Algebra C K] {ι κ : Type*}

private theorem coordPoly_sub' (l : K →ₗ[C] C) (P Q : MvPolynomial ι K) :
    coordPoly l (P - Q) = coordPoly l P - coordPoly l Q := by
  ext m
  simp only [coeff_coordPoly, coeff_sub, map_sub]

private theorem coordPoly_mul_X' (l : K →ₗ[C] C) (P : MvPolynomial ι K) (i : ι) :
    coordPoly l (P * X i) = coordPoly l P * X i := by
  simpa only [MvPolynomial.map_X] using coordPoly_mul_map l P (X i)

/-- A linear graph relation descends to the ordinary field of definition, retaining a
nonzero denominator. Its concrete consumer is the coefficient-field rational expression. -/
private theorem exists_fraction_relation {I : Ideal (MvPolynomial (ι ⊕ κ) K)}
    {J : Ideal (MvPolynomial ι K)}
    (hI : I = (I.comap (MvPolynomial.map (algebraMap C K))).map
      (MvPolynomial.map (algebraMap C K)))
    {P Q : MvPolynomial ι K} (hQ : Q ∉ J) (j : κ)
    (hPQ : rename Sum.inl Q * X (Sum.inr j) - rename Sum.inl P ∈ I) :
    ∃ p q : MvPolynomial ι C, MvPolynomial.map (algebraMap C K) q ∉ J ∧
      MvPolynomial.map (algebraMap C K)
        (rename Sum.inl q * X (Sum.inr j) - rename Sum.inl p) ∈ I := by
  classical
  let b := Module.Basis.ofVectorSpace C K
  obtain ⟨i, hi⟩ : ∃ i, MvPolynomial.map (algebraMap C K) (coordPoly (b.coord i) Q) ∉ J := by
    by_contra! hall
    apply hQ
    rw [← sum_smul_map_coordPoly b Q]
    exact J.sum_mem fun i _ ↦ Submodule.smul_of_tower_mem J (b i) (hall i)
  refine ⟨coordPoly (b.coord i) P, coordPoly (b.coord i) Q, hi, ?_⟩
  have hcomp := coordPoly_mem_of_mem_map (b.coord i) (hI ▸ hPQ)
  rw [coordPoly_sub', coordPoly_mul_X', coordPoly_rename _ Sum.inl_injective,
    coordPoly_rename _ Sum.inl_injective] at hcomp
  exact hcomp

end CoefficientComponents

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

attribute [local instance] isDomain_tensorProduct_of_isAlgClosed

private abbrev baseCoordinateRing' := MvPolynomial ι k ⧸ idealOf k v

private abbrev coefficientIdeal' (C : IntermediateField k K) : Ideal (MvPolynomial ι C) :=
  (idealOf k v).map (MvPolynomial.map (algebraMap k C))

private abbrev coefficientRing' (C : IntermediateField k K) :=
  MvPolynomial ι C ⧸ coefficientIdeal' (v := v) C

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficientIdeal'_eq_comap (C : IntermediateField k K) :
    coefficientIdeal' (v := v) C =
      (locusIdeal k v).comap (MvPolynomial.map (algebraMap C K)) := by
  rw [locusIdeal, ← map_comp_map_algebraMap C, ← Ideal.map_map,
    comap_map_mvPolynomial_eq_self]

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficient_aeval_eq_zero_iff' (C : IntermediateField k K)
    (P : MvPolynomial ι C) :
    aeval (LocusFunctionField.coord k v) P = 0 ↔ P ∈ coefficientIdeal' (v := v) C := by
  have h : aeval (LocusFunctionField.coord k v) P =
      LocusFunctionField.mk k v (MvPolynomial.map (algebraMap C K) P) := by
    rw [← LocusFunctionField.aeval_coord, aeval_map_algebraMap]
  rw [h, LocusFunctionField.mk_eq_zero_iff, coefficientIdeal'_eq_comap]
  rfl

private instance coefficientIdeal'_isPrime (C : IntermediateField k K) :
    (coefficientIdeal' (v := v) C).IsPrime := by
  rw [coefficientIdeal'_eq_comap]
  infer_instance

/-- The actual coefficient coordinate ring embeds into the actual locus function field. -/
private def coefficientRingMap' (C : IntermediateField k K) :
    coefficientRing' (v := v) C →ₐ[C] LocusFunctionField k v :=
  Ideal.Quotient.liftₐ (coefficientIdeal' (v := v) C)
    (aeval (LocusFunctionField.coord k v))
      (fun P hP ↦ (coefficient_aeval_eq_zero_iff' C P).mpr hP)

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficientRingMap'_injective (C : IntermediateField k K) :
    Function.Injective (coefficientRingMap' (v := v) C) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  change aeval (LocusFunctionField.coord k v) P = 0 at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((coefficient_aeval_eq_zero_iff' C P).mp hx)

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficientRingMap'_range (C : IntermediateField k K) :
    (coefficientRingMap' (v := v) C).range =
      Algebra.adjoin C (range (LocusFunctionField.coord k v)) := by
  rw [← MvPolynomial.aeval_range]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨P, rfl⟩
  · rintro ⟨P, rfl⟩
    exact ⟨Ideal.Quotient.mk (coefficientIdeal' (v := v) C) P, rfl⟩

/-- The fraction field of the actual coefficient coordinate ring maps canonically to
its field of formal coordinates inside the locus function field. -/
private def coefficientFractionMap' (C : IntermediateField k K) :
    FractionRing (coefficientRing' (v := v) C) →ₐ[C] LocusFunctionField k v :=
  IsFractionRing.liftAlgHom (coefficientRingMap'_injective (v := v) C)

/-- The actual rational representative has a linear graph relation in each coordinate. -/
private theorem rational_graph_relation (r : Representative k K v v) (hr : r.f.e = 0)
    (j : ι) :
    rename Sum.inl (MvPolynomial.map (algebraMap r.M K) (r.f.den j)) * X (Sum.inr j) -
      rename Sum.inl (MvPolynomial.map (algebraMap r.M K) (r.f.num j)) ∈ r.graphIdeal := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall v
  rw [r.graphIdeal_eq hy]
  have h := map_mem_locusIdeal (↥r.M) ((mem_idealOf_iff (↥r.M)).2 (show
      aeval (r.graphPoint y)
        (rename Sum.inl (r.f.den j) * X (Sum.inr j) - rename Sum.inl (r.f.num j)) = 0 by
    simp only [map_sub, map_mul, aeval_X, aeval_rename, Representative.graphPoint,
      Sum.elim_comp_inl, Sum.elim_inr]
    rw [QuasiRational.eval_apply, hr, pRoot_zero]
    field_simp [r.isDefinedAt y hy j]
    simp))
  simpa only [map_sub, map_mul, MvPolynomial.map_X,
    MvPolynomial.map_rename] using h

/-- A rational map whose graph is defined over an ordinary coefficient field descends
as rational fractions over that field. -/
private theorem exists_rational_over_field_strong (r : Representative k K v v) (hr : r.f.e = 0)
    (C : IntermediateField k K) (hC : IdealDefinedOver C.toSubfield r.graphIdeal)
    (hCM : C ≤ r.M) :
    ∃ f : QuasiRational C ι ι, f.e = 0 ∧
      (∀ j, MvPolynomial.map (algebraMap C K) (f.den j) ∉ locusIdeal k v) ∧
      (∀ y, IsGenericOver C v y → f.IsDefinedAt y) ∧
      (∀ y, IsGenericOver r.M v y → f.eval y = r.f.eval y) := by
  classical
  have hI : r.graphIdeal = (r.graphIdeal.comap (MvPolynomial.map (algebraMap C K))).map
      (MvPolynomial.map (algebraMap C K)) := hC
  have hex (j : ι) : ∃ p q : MvPolynomial ι C,
      MvPolynomial.map (algebraMap C K) q ∉ locusIdeal k v ∧
        MvPolynomial.map (algebraMap C K)
          (rename Sum.inl q * X (Sum.inr j) - rename Sum.inl p) ∈ r.graphIdeal := by
    obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall v
    have hQ : MvPolynomial.map (algebraMap r.M K) (r.f.den j) ∉ locusIdeal k v := by
      rw [LocusFunctionField.map_mem_locusIdeal_iff_aeval hy]
      exact r.isDefinedAt y hy j
    exact exists_fraction_relation hI hQ j (rational_graph_relation r hr j)
  choose P Q hQ hrel using hex
  let f : QuasiRational C ι ι := ⟨0, P, Q⟩
  have hden (y : ι → K) (hy : IsGenericOver C v y) (j : ι) : aeval y (Q j) ≠ 0 := by
    intro h0
    exact hQ j ((LocusFunctionField.map_mem_locusIdeal_iff_aeval hy (Q j)).2 h0)
  refine ⟨f, rfl, hQ, hden, fun y hy ↦ funext fun j ↦ ?_⟩
  have hzero := aeval_eq_zero_of_mem_locusIdeal (↥r.M)
    ((r.graphIdeal_eq hy) ▸ hrel j)
  simp only [aeval_map_algebraMap, map_sub, map_mul, aeval_rename, aeval_X,
    Representative.graphPoint, Sum.elim_comp_inl, Sum.elim_inr] at hzero
  have heq : r.f.eval y j = aeval y (P j) / aeval y (Q j) :=
    (eq_div_iff (hden y (hy.of_le hCM) j)).2
      (by simpa only [mul_comm] using sub_eq_zero.mp hzero)
  change pRoot K 0 (aeval y (P j) / aeval y (Q j)) = _
  rw [pRoot_zero, heq]

/-- The descended fractions are identities in the actual locus function field. -/
private theorem subst_coord_eq_fraction_over_field' (r : Representative k K v v)
    (hr : r.f.e = 0) (C : IntermediateField k K) (hCM : C ≤ r.M)
    (f : QuasiRational C ι ι) (hf0 : f.e = 0)
    (hdef : ∀ y, IsGenericOver C v y → f.IsDefinedAt y)
    (heval : ∀ y, IsGenericOver r.M v y → f.eval y = r.f.eval y) (i : ι) :
    r.subst hr (LocusFunctionField.coord k v i) =
      LocusFunctionField.mk k v (MvPolynomial.map (algebraMap C K) (f.num i)) /
        LocusFunctionField.mk k v (MvPolynomial.map (algebraMap C K) (f.den i)) := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall v
  have hmap (P : MvPolynomial ι C) :
      MvPolynomial.map (algebraMap r.M K)
          (MvPolynomial.map (IntermediateField.inclusion hCM).toRingHom P) =
        MvPolynomial.map (algebraMap C K) P := by
    rw [MvPolynomial.map_map]
    rfl
  have h₁ : LocusFunctionField.HasValue r.M y
      (r.subst hr (LocusFunctionField.coord k v i)) (r.f.eval y i) := by
    refine ⟨r.f.num i, r.f.den i, r.isDefinedAt y hy i, r.subst_coord hr i, ?_⟩
    rw [QuasiRational.eval_apply, hr, pRoot_zero]
  apply LocusFunctionField.HasValue.eq hy h₁
  refine ⟨MvPolynomial.map (IntermediateField.inclusion hCM).toRingHom (f.num i),
    MvPolynomial.map (IntermediateField.inclusion hCM).toRingHom (f.den i), ?_, ?_, ?_⟩
  · rw [aeval_map_inclusion]
    exact hdef y (hy.of_le hCM) i
  · rw [hmap, hmap]
  · rw [aeval_map_inclusion, aeval_map_inclusion]
    calc
      r.f.eval y i = f.eval y i := congrFun (heval y hy).symm i
      _ = _ := by rw [QuasiRational.eval_apply, hf0, pRoot_zero]

/-- The formal coefficient field generated by the locus coordinates, inside the actual
function field. This is not a compositum with the original tuple in the ambient field. -/
private def coefficientField' (C : IntermediateField k K) :
    IntermediateField C (LocusFunctionField k v) :=
  IntermediateField.adjoin C (range (LocusFunctionField.coord k v))

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficientFractionMap'_fieldRange (C : IntermediateField k K) :
    (coefficientFractionMap' (v := v) C).fieldRange = coefficientField' (v := v) C :=
  IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq
    (coefficientRingMap'_injective C) (coefficientRingMap'_range C)

/-- The actual ordinary-coefficient field is the fraction field of the formal coefficient
coordinate ring, with its canonical scalar action retained. -/
private def coefficientFractionEquiv' (C : IntermediateField k K) :
    FractionRing (coefficientRing' (v := v) C) ≃ₐ[C] coefficientField' (v := v) C :=
  (AlgEquiv.ofInjectiveField (coefficientFractionMap' C)).trans
    (IntermediateField.equivOfEq (coefficientFractionMap'_fieldRange C))

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem coefficientFractionEquiv'_coord (C : IntermediateField k K) (i : ι) :
    ((coefficientFractionEquiv' (v := v) C (algebraMap (coefficientRing' (v := v) C)
      (FractionRing (coefficientRing' (v := v) C))
        (tensorCoordinateQuotientEquiv' (C := C) (idealOf k v)
          ((1 : C) ⊗ₜ[k] Ideal.Quotient.mk (idealOf k v) (X i : MvPolynomial ι k))))).val :
            LocusFunctionField k v) = LocusFunctionField.coord k v i := by
  rw [tensorCoordinateQuotientEquiv'_X]
  change coefficientFractionMap' C (algebraMap (coefficientRing' C)
    (FractionRing (coefficientRing' C)) (Ideal.Quotient.mk (coefficientIdeal' C) (X i))) = _
  rw [coefficientFractionMap', IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change aeval (R := C) (LocusFunctionField.coord k v) (X i) = _
  exact aeval_X _ _

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- The actual locus function field is the formal extension of the old function field
by the ambient constants, with the old coordinates sent to the actual formal coordinates. -/
private theorem exists_tensorLocusFieldEquiv' :
    ∃ e : FractionRing (K ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v))) ≃ₐ[K]
        LocusFunctionField k v,
      ∀ (i : ι), e (algebraMap (K ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v)))
          (FractionRing (K ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v))))
          ((1 : K) ⊗ₜ[k] algebraMap (baseCoordinateRing' (k := k) (v := v))
            (FractionRing (baseCoordinateRing' (k := k) (v := v)))
              (Ideal.Quotient.mk (idealOf k v) (X i)))) =
        LocusFunctionField.coord k v i := by
  let A := baseCoordinateRing' (k := k) (v := v)
  let q : K ⊗[k] A ≃ₐ[K] MvPolynomial ι K ⧸ locusIdeal k v :=
    tensorCoordinateQuotientEquiv' (idealOf k v)
  have : IsDomain (K ⊗[k] A) :=
    MulEquiv.isDomain (MvPolynomial ι K ⧸ locusIdeal k v) q.toRingEquiv.toMulEquiv
  obtain ⟨_, e₁, he₁⟩ := isDomain_and_exists_tensorFractionEquiv (k := k) (C := K) (A := A)
  let e₀ : FractionRing (K ⊗[k] A) ≃ₐ[K] LocusFunctionField k v :=
    IsFractionRing.algEquivOfAlgEquiv q
  refine ⟨e₁.trans e₀, fun i ↦ ?_⟩
  change e₀ (e₁ (algebraMap (K ⊗[k] FractionRing A) (FractionRing (K ⊗[k] FractionRing A))
    ((1 : K) ⊗ₜ[k] algebraMap A (FractionRing A)
      (Ideal.Quotient.mk (idealOf k v) (X i))))) = _
  rw [he₁]
  change IsFractionRing.algEquivOfAlgEquiv q (algebraMap (K ⊗[k] A)
    (FractionRing (K ⊗[k] A)) ((1 : K) ⊗ₜ[k] Ideal.Quotient.mk (idealOf k v) (X i))) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap (MvPolynomial ι K ⧸ locusIdeal k v) (LocusFunctionField k v)
    (tensorCoordinateQuotientEquiv' (C := K) (idealOf k v)
      ((1 : K) ⊗ₜ[k] Ideal.Quotient.mk (idealOf k v) (X i : MvPolynomial ι k))) = _
  rw [tensorCoordinateQuotientEquiv'_X]
  rfl

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- The actual ordinary-coefficient field is the formal constant extension of the old
function field. Its old coordinate generators map to the actual formal locus coordinates. -/
private theorem exists_tensorCoefficientFieldEquiv' (C : IntermediateField k K) :
    ∃ e : FractionRing (C ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v))) ≃ₐ[C]
        coefficientField' (v := v) C,
      ∀ (i : ι), (e (algebraMap (C ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v)))
          (FractionRing (C ⊗[k] FractionRing (baseCoordinateRing' (k := k) (v := v))))
          ((1 : C) ⊗ₜ[k] algebraMap (baseCoordinateRing' (k := k) (v := v))
            (FractionRing (baseCoordinateRing' (k := k) (v := v)))
              (Ideal.Quotient.mk (idealOf k v) (X i))))).val =
        LocusFunctionField.coord k v i := by
  let A := baseCoordinateRing' (k := k) (v := v)
  let q : C ⊗[k] A ≃ₐ[C] coefficientRing' (v := v) C :=
    tensorCoordinateQuotientEquiv' (idealOf k v)
  have : IsDomain (C ⊗[k] A) :=
    MulEquiv.isDomain (coefficientRing' (v := v) C) q.toRingEquiv.toMulEquiv
  obtain ⟨_, e₁, he₁⟩ := isDomain_and_exists_tensorFractionEquiv (k := k) (C := C) (A := A)
  let e₀ : FractionRing (C ⊗[k] A) ≃ₐ[C] FractionRing (coefficientRing' (v := v) C) :=
    IsFractionRing.algEquivOfAlgEquiv q
  let e := e₁.trans (e₀.trans (coefficientFractionEquiv' (v := v) C))
  refine ⟨e, fun i ↦ ?_⟩
  have hinner : e₀ (e₁ (algebraMap (C ⊗[k] FractionRing A)
      (FractionRing (C ⊗[k] FractionRing A))
      ((1 : C) ⊗ₜ[k] algebraMap A (FractionRing A)
        (Ideal.Quotient.mk (idealOf k v) (X i))))) =
      algebraMap (coefficientRing' (v := v) C) (FractionRing (coefficientRing' (v := v) C))
        (q ((1 : C) ⊗ₜ[k] Ideal.Quotient.mk (idealOf k v) (X i))) := by
    rw [he₁]
    exact IsFractionRing.algEquivOfAlgEquiv_algebraMap q _
  exact (congrArg (fun a ↦ (coefficientFractionEquiv' (v := v) C a).val) hinner).trans
    (coefficientFractionEquiv'_coord (k := k) (K := K) (v := v) C i)

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
private theorem mk_map_mem_coefficientField' (C : IntermediateField k K)
    (P : MvPolynomial ι C) :
    LocusFunctionField.mk k v (MvPolynomial.map (algebraMap C K) P) ∈
      coefficientField' (v := v) C := by
  have h : aeval (LocusFunctionField.coord k v) P ∈ coefficientField' (v := v) C := by
    induction P using MvPolynomial.induction_on with
    | C c => simpa only [aeval_C] using (coefficientField' (v := v) C).algebraMap_mem c
    | add p q hp hq => simpa only [map_add] using (coefficientField' C).add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]
      exact (coefficientField' C).mul_mem hp
        (IntermediateField.subset_adjoin C _ (mem_range_self i))
  rw [← LocusFunctionField.aeval_coord]
  simpa only [aeval_map_algebraMap] using h

private theorem subst_coord_mem_coefficientField' (r : Representative k K v v)
    (hr : r.f.e = 0) (C : IntermediateField k K)
    (hC : IdealDefinedOver C.toSubfield r.graphIdeal) (hCM : C ≤ r.M) (i : ι) :
    r.subst hr (LocusFunctionField.coord k v i) ∈ coefficientField' (v := v) C := by
  obtain ⟨f, hf0, _, hdef, heval⟩ := exists_rational_over_field_strong r hr C hC hCM
  rw [subst_coord_eq_fraction_over_field' r hr C hCM f hf0 hdef heval]
  exact (coefficientField' C).div_mem
    (mk_map_mem_coefficientField' C _) (mk_map_mem_coefficientField' C _)

private theorem subst_mem_coefficientField' (r : Representative k K v v) (hr : r.f.e = 0)
    (C : IntermediateField k K) (hC : IdealDefinedOver C.toSubfield r.graphIdeal) (hCM : C ≤ r.M)
    {x : LocusFunctionField k v} (hx : x ∈ coefficientField' (v := v) C) :
    r.subst hr x ∈ coefficientField' (v := v) C := by
  have hle : (coefficientField' (v := v) C).map ((r.subst hr).restrictScalars C) ≤
      coefficientField' (v := v) C := by
    rw [coefficientField', IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact subst_coord_mem_coefficientField' r hr C hC hCM i
  exact hle ⟨x, hx, rfl⟩

/-- The actual descended rational substitution on the formal ordinary-coefficient field. -/
private def coefficientSubst' (r : Representative k K v v) (hr : r.f.e = 0)
    (C : IntermediateField k K) (hC : IdealDefinedOver C.toSubfield r.graphIdeal) (hCM : C ≤ r.M) :
    coefficientField' (v := v) C →ₐ[C] coefficientField' (v := v) C :=
  (((r.subst hr).restrictScalars C).comp (coefficientField' C).val).codRestrict
    (coefficientField' C).toSubalgebra
    (fun x ↦ subst_mem_coefficientField' r hr C hC hCM x.property)

private theorem subst_comp_eq_id_of_inverse' (r s : Representative k K v v)
    (hr : r.f.e = 0) (hs : s.f.e = 0)
    (hi : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v)) :
    (r.subst hr).comp (s.subst hs) = AlgHom.id K (LocusFunctionField k v) := by
  calc
    _ = (s.comp r).subst (Representative.comp_f_e_eq_zero hr hs) :=
      (Representative.subst_comp hr hs).symm
    _ = (Representative.id v).subst rfl :=
      Representative.subst_eq_of_equivalent _ _ (Quotient.exact hi.1)
    _ = _ := Representative.subst_id

/-- Genuine rational inverse representatives yield an automorphism of the formal ordinary
coefficient field. The following HW producer supplies these representatives internally. -/
private def coefficientSubstEquiv' (r s : Representative k K v v)
    (hr : r.f.e = 0) (hs : s.f.e = 0)
    (hi : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v))
    (C : IntermediateField k K) (hC : IdealDefinedOver C.toSubfield r.graphIdeal)
    (hS : IdealDefinedOver C.toSubfield s.graphIdeal) (hCM : C ≤ r.M) (hCS : C ≤ s.M) :
    coefficientField' (v := v) C ≃ₐ[C] coefficientField' (v := v) C :=
  AlgEquiv.ofAlgHom (coefficientSubst' r hr C hC hCM) (coefficientSubst' s hs C hS hCS)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change r.subst hr (s.subst hs x) = x
      exact AlgHom.congr_fun (subst_comp_eq_id_of_inverse' r s hr hs hi) x)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change s.subst hs (r.subst hr x) = x
      exact AlgHom.congr_fun (subst_comp_eq_id_of_inverse' s r hs hr hi.symm) x)

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- A coefficient field defining an ideal also defines every variable-renamed image. -/
private theorem idealDefinedOver_rename' {σ τ : Type*} (F : Subfield K)
    {I : Ideal (MvPolynomial σ K)} (hI : IdealDefinedOver F I) (f : σ → τ) :
    IdealDefinedOver F (I.map (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)) := by
  let J := I.comap (mapF F)
  have heq : I.map (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) =
      (J.map (rename f : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)).map (mapF F) := by
    calc
      _ = (J.map (mapF F)).map
          (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) :=
        congrArg (fun A : Ideal (MvPolynomial σ K) ↦
          A.map (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)) hI
      _ = _ := by
        change (J.map (mapF F)).map
            (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom =
          (J.map (rename f : MvPolynomial σ F →ₐ[F] MvPolynomial τ F).toRingHom).map (mapF F)
        rw [Ideal.map_map (mapF F)
          (rename f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom,
          Ideal.map_map (rename f : MvPolynomial σ F →ₐ[F] MvPolynomial τ F).toRingHom
            (mapF F)]
        congr 1
        exact (MvPolynomial.map_comp_rename F.subtype f).symm
  rw [heq]
  exact (Ideal.map_comap_map
    (I := J.map (rename f : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)) (f := mapF F)).symm

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- Reversing the two coordinate blocks reverses the locus graph. -/
private theorem locusIdeal_swap' (N : IntermediateField k K) (y z : ι → K) :
    (locusIdeal (↥N) (Sum.elim y z)).map
        (rename Sum.swap : MvPolynomial (ι ⊕ ι) K →ₐ[K] MvPolynomial (ι ⊕ ι) K) =
      locusIdeal (↥N) (Sum.elim z y) := by
  have hc : (locusIdeal (↥N) (Sum.elim z y)).comap
      (rename Sum.swap : MvPolynomial (ι ⊕ ι) K →ₐ[K] MvPolynomial (ι ⊕ ι) K) =
      locusIdeal (↥N) (Sum.elim y z) := by
    unfold locusIdeal
    rw [comap_rename_map_eq (K := K) (↥N) (f := (Sum.swap : ι ⊕ ι → ι ⊕ ι))
      (by intro a b h; simpa using congrArg Sum.swap h)]
    congr 1
    ext P
    rw [Ideal.mem_comap, mem_idealOf_iff, mem_idealOf_iff, aeval_rename]
    have he : (Sum.elim z y) ∘ Sum.swap = Sum.elim y z := by
      funext i
      cases i <;> rfl
    rw [he]
  rw [← hc]
  exact Ideal.map_comap_of_surjective _ (renameEquiv K (Equiv.sumComm ι ι)).surjective _

/-- A genuine inverse has exactly the block-reversed graph ideal. -/
private theorem inverse_graph_eq' (r s : Representative k K v v)
    (hi : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v)) :
    s.graphIdeal = r.graphIdeal.map
      (rename Sum.swap : MvPolynomial (ι ⊕ ι) K →ₐ[K] MvPolynomial (ι ⊕ ι) K) := by
  have hsr : (s.comp r).Equivalent (Representative.id v) := Quotient.exact hi.1
  let N := racl k (((s.comp r).M : Set K) ∪ (Representative.id (k := k) v).M)
  have hN : IsAlgClosed ↥N := isAlgClosed_racl _
  have hNs : IsSmall k (N : Set K) :=
    ((s.comp r).isSmall.union (Representative.id (k := k) v).isSmall).racl
  have hcN : (s.comp r).M ≤ N := subset_union_left.trans (subset_racl k _)
  have hrN : r.M ≤ N := (Representative.le_joinField_left s r).trans hcN
  have hsN : s.M ≤ N := (Representative.le_joinField_right s r).trans hcN
  obtain ⟨y, hy⟩ := exists_isGenericOver hNs v
  have hz : IsGenericOver N v (r.f.eval y) := by
    have := (r.extend hN hNs hrN).isGenericOver y hy
    rwa [Representative.extend_eval] at this
  have hsy : s.f.eval (r.f.eval y) = y := by
    rw [← Representative.comp_eval s r (hy.of_le hcN), hsr y hy]
    exact QuasiRational.id_eval y
  have hR : r.graphIdeal = locusIdeal (↥N) (r.graphPoint y) :=
    (r.graphIdeal_eq (hy.of_le hrN)).trans
      (r.locusIdeal_graphPoint_eq_of_le hNs hrN hy).symm
  have hS : s.graphIdeal = locusIdeal (↥N) (s.graphPoint (r.f.eval y)) :=
    (s.graphIdeal_eq (hz.of_le hsN)).trans
      (s.locusIdeal_graphPoint_eq_of_le hNs hsN hz).symm
  rw [hR, hS]
  change locusIdeal (↥N) (Sum.elim (r.f.eval y) (s.f.eval (r.f.eval y))) =
    (locusIdeal (↥N) (Sum.elim y (r.f.eval y))).map _
  rw [hsy, locusIdeal_swap']

private theorem inverse_cb_le' (r s : Representative k K v v)
    (hi : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v)) :
    Germ.cb (⟦s⟧ : Germ k v v) ≤ Germ.cb (⟦r⟧ : Germ k v v) := by
  let C := Germ.cb (⟦r⟧ : Germ k v v)
  have hdef : IdealDefinedOver C.toSubfield s.graphIdeal := by
    rw [inverse_graph_eq' r s hi]
    exact idealDefinedOver_rename' C.toSubfield
      (Germ.idealDefinedOver_graphIdeal (⟦r⟧ : Germ k v v) le_rfl) Sum.swap
  change IntermediateField.adjoin k (idealFod s.graphIdeal : Set K) ≤ C
  exact IntermediateField.adjoin_le_iff.mpr (idealDefinedOver_iff.mp hdef)

/-- Inverse germs have the same ordinary canonical base, not just its algebraic closure. -/
private theorem inverse_cb_eq' (r s : Representative k K v v)
    (hi : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v)) :
    Germ.cb (⟦s⟧ : Germ k v v) = Germ.cb (⟦r⟧ : Germ k v v) :=
  le_antisymm (inverse_cb_le' r s hi) (inverse_cb_le' s r hi.symm)

/-- The ordinary canonical base is genuinely finitely generated over k. -/
private theorem cb_fg' (g : Germ k v v) : (Germ.cb g).FG :=
  ⟨Germ.codeSet g, Germ.adjoin_codeSet g⟩

private theorem cb_essFiniteType' (g : Germ k v v) :
    Algebra.EssFiniteType k (Germ.cb g) :=
  IntermediateField.essFiniteType_iff.mpr (cb_fg' g)

/-- The canonical base supplies two independent coefficient derivations once its rank is
at least two. -/
private theorem exists_cb_derivations' (g : Germ k v v)
    (hr : 2 ≤ erk k ∅ (g.cb : Set K)) :
    ∃ D : Fin 2 → Derivation k g.cb g.cb, LinearIndependent g.cb D := by
  have : Algebra.EssFiniteType k g.cb := cb_essFiniteType' g
  apply exists_linearIndependent_derivations
  apply (Cardinal.natCast_le_toENat (n := 2)).mp
  rw [erk_empty_eq_toENat_trdeg] at hr
  rw [show IntermediateField.adjoin k (g.cb : Set K) = g.cb from
    IntermediateField.adjoin_self k g.cb] at hr
  simpa using hr

/-- Actual HW data supplies an automorphism of the formal field over the germ's
ordinary canonical base, with the genuine rational representative's coordinate formula. -/
private theorem exists_coefficient_automorphism' {g₀ : Germ k v v} (hw : Germ.IsHW g₀)
    (hv : erk k ∅ (range v) = 1) {γ : Germ k v v} (hγ : γ ∈ Germ.IsHW.prodSet g₀) :
    ∃ r s : Representative k K v v, (⟦r⟧ : Germ k v v) = γ ∧
      Germ.IsInverse (⟦s⟧ : Germ k v v) γ ∧ r.f.e = 0 ∧ s.f.e = 0 ∧
      ∃ g : coefficientField' (v := v) γ.cb ≃ₐ[γ.cb] coefficientField' (v := v) γ.cb,
        ∀ i, (g ⟨LocusFunctionField.coord k v i,
            IntermediateField.subset_adjoin γ.cb _ (mem_range_self i)⟩ : LocusFunctionField k v) =
          LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.num i)) /
            LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.den i)) := by
  obtain ⟨δ, hδ⟩ := Germ.isUnit_iff.mp (hw.isUnit_of_mem_prodSet hγ)
  obtain ⟨r, hr, hr0⟩ := hw.exists_rational_representative hv hγ
  obtain ⟨s, hs, hs0⟩ := hw.exists_rational_representative hv (hw.inv_mem_prodSet hγ hδ)
  have hi : Germ.IsInverse (⟦s⟧ : Germ k v v) γ := by simpa only [hs] using hδ
  have hinv : Germ.IsInverse (⟦s⟧ : Germ k v v) (⟦r⟧ : Germ k v v) := by
    rw [hr]
    exact hi
  have hCr : Germ.cb (⟦r⟧ : Germ k v v) = γ.cb := congrArg Germ.cb hr
  have hCs : Germ.cb (⟦s⟧ : Germ k v v) = γ.cb := (inverse_cb_eq' r s hinv).trans hCr
  let g := coefficientSubstEquiv' r s hr0 hs0 hinv γ.cb
    (Germ.idealDefinedOver_graphIdeal (⟦r⟧ : Germ k v v) hCr.le)
    (Germ.idealDefinedOver_graphIdeal (⟦s⟧ : Germ k v v) hCs.le)
    (hCr.symm.le.trans (Germ.cb_mk_le r)) (hCs.symm.le.trans (Germ.cb_mk_le s))
  refine ⟨r, s, hr, hi, hr0, hs0, g, fun i ↦ ?_⟩
  change r.subst hr0 (LocusFunctionField.coord k v i) = _
  exact r.subst_coord hr0 i

/-- The actual embedding identifies the formal graph kernel with the contracted germ graph. -/
private theorem ker_aeval_formal_graph'
    {F : Type*} [Field F] [Algebra k F] (γ : Germ k v v)
    (r : Representative k K v v) (hr : (⟦r⟧ : Germ k v v) = γ) (hr0 : r.f.e = 0) (u : ι → F)
    (g : FractionRing (γ.cb ⊗[k] F) ≃ₐ[γ.cb]
      FractionRing (γ.cb ⊗[k] F))
    (φ : FractionRing (γ.cb ⊗[k] F) →ₐ[γ.cb] LocusFunctionField k v)
    (hφx : ∀ i : ι, φ (algebraMap (γ.cb ⊗[k] F) _
      ((1 : γ.cb) ⊗ₜ[k] u i)) = LocusFunctionField.coord k v i)
    (hφgx : ∀ i : ι, φ (g (algebraMap (γ.cb ⊗[k] F) _
      ((1 : γ.cb) ⊗ₜ[k] u i))) =
      r.subst hr0 (LocusFunctionField.coord k v i)) :
    let x : ι → FractionRing (γ.cb ⊗[k] F) := fun i ↦
      algebraMap (γ.cb ⊗[k] F) _ ((1 : γ.cb) ⊗ₜ[k] u i)
    RingHom.ker (aeval (R := γ.cb) (Sum.elim x (fun i ↦ g (x i)))).toRingHom =
      γ.graphIdeal.comap (MvPolynomial.map (algebraMap γ.cb K)) := by
  intro x
  let C := γ.cb
  let z := Sum.elim x (fun i ↦ g (x i))
  have hCM : C ≤ r.M := by
    have h := Germ.cb_mk_le r
    rwa [hr] at h
  have hxy : ∀ j, φ (z j) = Sum.elim (LocusFunctionField.coord k v)
      (fun i ↦ r.subst hr0 (LocusFunctionField.coord k v i)) j := by
    intro j
    cases j with
    | inl i => exact hφx i
    | inr i => exact hφgx i
  have hg : r.graphIdeal = γ.graphIdeal := by rw [← hr]; rfl
  exact (ker_aeval_eq_of_injective' φ φ.injective z _ hxy).trans
    ((r.ker_aeval_graph hr0 C hCM).trans
      (congrArg (fun I : Ideal (MvPolynomial (ι ⊕ ι) K) ↦
        I.comap (MvPolynomial.map (algebraMap C K))) hg))

/-- The actual graph over its ordinary canonical base detects zero variation. -/
private theorem coefficientVariationLinear_injective_of_graph'
    {F : Type*} [Field F] [Algebra k F] (γ : Germ k v v)
    (r : Representative k K v v) (hr : (⟦r⟧ : Germ k v v) = γ) (hr0 : r.f.e = 0) (u : ι → F)
    (g : FractionRing (γ.cb ⊗[k] F) ≃ₐ[γ.cb]
      FractionRing (γ.cb ⊗[k] F))
    (φ : FractionRing (γ.cb ⊗[k] F) →ₐ[γ.cb] LocusFunctionField k v)
    (hφx : ∀ i : ι, φ (algebraMap (γ.cb ⊗[k] F) _
      ((1 : γ.cb) ⊗ₜ[k] u i)) = LocusFunctionField.coord k v i)
    (hφgx : ∀ i : ι, φ (g (algebraMap (γ.cb ⊗[k] F) _
      ((1 : γ.cb) ⊗ₜ[k] u i))) =
      r.subst hr0 (LocusFunctionField.coord k v i)) :
    Function.Injective (coefficientVariationLinear (k := k) g) := by
  have hker := ker_aeval_formal_graph' γ r hr hr0 u g φ hφx hφgx
  apply coefficientVariationLinear_injective (k := k) g
  intro D hD
  apply Germ.derivation_eq_zero_of_graph_stable γ D
  intro P hP
  rw [← hker] at hP ⊢
  exact coefficientDerivative_mem_variationGraphKernel g D hD u P hP

/-- The actual graph over its ordinary canonical base makes infinitesimal variation
faithful. The field comparison and rational inverse are both derived from actual HW data. -/
private theorem exists_faithful_coefficient_variation' {g₀ : Germ k v v}
    (hw : Germ.IsHW g₀) (hv : erk k ∅ (range v) = 1) {γ : Germ k v v}
    (hγ : γ ∈ Germ.IsHW.prodSet g₀) :
    ∃ g : FractionRing (γ.cb ⊗[k] BaseFunctionField k v) ≃ₐ[γ.cb]
        FractionRing (γ.cb ⊗[k] BaseFunctionField k v),
      Function.Injective (coefficientVariationLinear (k := k) g) := by
  obtain ⟨r, s, hr, _, hr0, _, gC, hgC⟩ := exists_coefficient_automorphism' hw hv hγ
  let C := γ.cb
  let F := BaseFunctionField k v
  let E := FractionRing (C ⊗[k] F)
  obtain ⟨e, he⟩ := exists_tensorCoefficientFieldEquiv' (k := k) (v := v) C
  let g : E ≃ₐ[C] E := e.trans (gC.trans e.symm)
  let x : ι → E := fun i ↦ algebraMap (C ⊗[k] F) E ((1 : C) ⊗ₜ[k] BaseFunctionField.coord k v i)
  let φ : E →ₐ[C] LocusFunctionField k v := (coefficientField' (v := v) C).val.comp e.toAlgHom
  have hφx (i : ι) : φ (x i) = LocusFunctionField.coord k v i := he i
  have hφgx (i : ι) : φ (g (x i)) = r.subst hr0 (LocusFunctionField.coord k v i) := by
    have hei : e (x i) = ⟨LocusFunctionField.coord k v i,
        IntermediateField.subset_adjoin C _ (mem_range_self i)⟩ := Subtype.ext (he i)
    change (e (e.symm (gC (e (x i))))).val = _
    rw [e.apply_symm_apply, hei, hgC]
    exact (r.subst_coord hr0 i).symm
  exact ⟨g, coefficientVariationLinear_injective_of_graph' γ r hr hr0
      (BaseFunctionField.coord k v) g φ hφx hφgx⟩

/-- Actual HW data with parameter rank at least two yields two independent regular
K-derivations on the actual locus function field. -/
private theorem exists_independent_regular_locus_derivations' {g₀ : Germ k v v}
    (hw : Germ.IsHW g₀) (hv : erk k ∅ (range v) = 1)
    (hr : 2 ≤ erk k ∅ (g₀.cb : Set K)) :
    ∃ D : Fin 2 → Derivation K (LocusFunctionField k v) (LocusFunctionField k v),
      LinearIndependent K D ∧
        ∀ i (V : ValuationSubring (LocusFunctionField k v)),
          (∀ c : K, algebraMap K _ c ∈ V) → V ≠ ⊤ → ∀ x ∈ V, D i x ∈ V := by
  obtain ⟨g, hg⟩ := exists_faithful_coefficient_variation' hw hv
    (hw.mem_prodSet_of_mem (Germ.self_mem_orbit g₀))
  obtain ⟨D, hD⟩ := exists_cb_derivations' g₀ hr
  let _ : IsFunctionFieldOneVar k (BaseFunctionField k v) :=
    BaseFunctionField.isFunctionFieldOneVar k v hv
  obtain ⟨t, ht, _, hsep⟩ := BaseFunctionField.exists_separating_transcendental k v hv
  let _ := hsep
  obtain ⟨δ, hδ, hreg⟩ := exists_independent_regular_variations ht g hg D hD
  obtain ⟨δ', hδ', _, hreg'⟩ := exists_regular_derivations_baseChange (K := K) ht δ hδ hreg
  obtain ⟨e, _⟩ := exists_tensorLocusFieldEquiv' (k := k) (K := K) (v := v)
  let L := Derivation.transportLinear e
  refine ⟨L ∘ δ', hδ'.map' L (LinearMap.ker_eq_bot.mpr
    (Derivation.transportLinear_injective e)), ?_⟩
  intro i V hKV hV x hx
  exact transportDerivation'_regular e (δ' i) (hreg' i) V hKV hV hx

/-- A rank-one HW locus with canonical-base rank at least two has function field genus zero.
The one-variable structure is derived from `hv`. -/
theorem Germ.IsHW.genus_eq_zero {g₀ : Germ k v v} (hw : Germ.IsHW g₀)
    (hv : erk k ∅ (range v) = 1) (hr : 2 ≤ erk k ∅ (g₀.cb : Set K)) :
    let _ := LocusFunctionField.isFunctionFieldOneVar (k := k) (v := v) hv
    genus K (LocusFunctionField k v) = 0 := by
  let _ := LocusFunctionField.isFunctionFieldOneVar (k := k) (v := v) hv
  obtain ⟨D, hD, hreg⟩ := exists_independent_regular_locus_derivations' hw hv hr
  exact genus_eq_zero_of_linearIndependent_regular D hD hreg


end

end GroupConfig
