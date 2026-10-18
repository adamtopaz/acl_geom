/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.ConstantExtension
import AclGeom.Curves.Rational
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Rationality and genus-zero descent under constant extension

Named source consumer: original-base genus and rational coordinates for blueprint
`lem:affine-action` (#21).

**Status:** proved. A rational generator of the canonical tensor fraction field over any
constant extension of an algebraically closed base descends to the original one-variable
field. The finite coefficient model, common denominator and specialization are internal.
The genus-zero criterion has both one-variable instances explicit; `SchemeCurveGenus`
derives them for the actual regular-affine action. This is genus-zero descent, not a
statement about arbitrary genus under base change.
-/

namespace AclGeom.RationalityDescent

noncomputable section

open TensorProduct Polynomial
open scoped TensorProduct

variable {k : Type*} [Field k] [IsAlgClosed k]

private theorem exists_algHom_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] {r : R} (hr : r ≠ 0) :
    ∃ φ : R →ₐ[k] k, φ r ≠ 0 := by
  classical
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal R).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.mp inferInstance ⊥ inferInstance
  have hex : ∃ M : Ideal R, M.IsMaximal ∧ r ∉ M := by
    by_contra! h
    apply hr
    have hm : r ∈ (⊥ : Ideal R).jacobson := by
      exact Ideal.mem_sInf.mpr fun M hM ↦ h M hM.2
    simpa only [hj, Ideal.mem_bot] using hm
  obtain ⟨M, hM, hrM⟩ := hex
  let : M.IsMaximal := hM
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite k (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ M)
  let ρ : (R ⧸ M) →ₐ[k] k := IsAlgClosed.lift
  let φ : R →ₐ[k] k := ρ.comp (Ideal.Quotient.mkₐ k M)
  refine ⟨φ, fun hz ↦ hrM ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply ρ.toRingHom.injective
  change ρ.toRingHom (Ideal.Quotient.mk M r) = 0 at hz
  exact hz.trans (map_zero ρ.toRingHom).symm

private theorem exists_tensor_specialization {F R : Type*} [Field F] [Algebra k F]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (z : F ⊗[k] R) (hz : z ≠ 0) :
    ∃ φ : R →ₐ[k] k,
      Algebra.TensorProduct.map (AlgHom.id k F) φ z ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k F
  let e := equivFinsuppOfBasisLeft (N := R) b
  have hex : ∃ i, e z i ≠ 0 := by
    by_contra! h
    apply hz
    apply e.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i
  obtain ⟨i, hi⟩ := hex
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero (k := k) hi
  refine ⟨φ, fun heq ↦ hφ ?_⟩
  have hcoord (w : F ⊗[k] R) :
      equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id k F) φ w) i =
        φ (e w i) := by
    induction w using TensorProduct.inductionOn with
    | tmul f r =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        equivFinsuppOfBasisLeft_apply_tmul_apply, e, map_smul]
    | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]
  simpa only [heq, map_zero, Finsupp.zero_apply] using (hcoord z).symm

omit [IsAlgClosed k] in
private theorem exists_finite_constant_model {F K : Type*} [Field F] [Field K]
    [Algebra k F] [Algebra k K] (c : Finset K) (zs : Finset (F ⊗[k] K)) :
    ∃ R : Subalgebra k K, Algebra.FiniteType k R ∧
      (∀ a ∈ c, a ∈ R) ∧ ∀ z ∈ zs, z ∈ (baseChangeIncl F R).range := by
  classical
  let b := Module.Free.chooseBasis k F
  let e := equivFinsuppOfBasisLeft (N := K) b
  let s : Finset K := c ∪ zs.biUnion fun z ↦ (e z).support.image (e z)
  let R := Algebra.adjoin k (s : Set K)
  have hc (a) (ha : a ∈ c) : a ∈ R :=
    Algebra.subset_adjoin (Finset.mem_union_left _ ha)
  have hz (z) (hzz : z ∈ zs) : z ∈ (baseChangeIncl F R).range := by
    apply (mem_range_baseChangeIncl_iff b R z).2
    intro i
    by_cases hi : e z i = 0
    · exact hi ▸ R.zero_mem
    · apply Algebra.subset_adjoin
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨z, hzz, Finset.mem_image.2 ⟨i, Finsupp.mem_support_iff.2 hi, rfl⟩⟩)
  exact ⟨R, Algebra.FiniteType.adjoin_of_finite s.finite_toSet, hc, hz⟩

attribute [local instance] isDomain_tensorProduct_of_isAlgClosed

private theorem exists_finite_specialization {F K : Type*} [Field F] [Field K]
    [Algebra k F] [Algebra k K] (c : Finset K)
    (zs : Finset (FractionRing (K ⊗[k] F))) :
    let eF : F →ₐ[k] FractionRing (K ⊗[k] F) :=
      (IsScalarTower.toAlgHom k (K ⊗[k] F) (FractionRing (K ⊗[k] F))).comp
        Algebra.TensorProduct.includeRight
    ∃ (S : Subalgebra k (FractionRing (K ⊗[k] F)))
      (ψ : S →ₐ[k] F),
      (∀ z ∈ zs, z ∈ S) ∧
      (∀ x : F, ∃ hx : eF x ∈ S, ψ ⟨eF x, hx⟩ = x) ∧
      ∀ a ∈ c, ∃ ha : algebraMap K (FractionRing (K ⊗[k] F)) a ∈ S,
        ψ ⟨algebraMap K (FractionRing (K ⊗[k] F)) a, ha⟩ ∈ (algebraMap k F).range := by
  classical
  let E := FractionRing (K ⊗[k] F)
  let eF : F →ₐ[k] E := (IsScalarTower.toAlgHom k (K ⊗[k] F) E).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (K ⊗[k] F)) zs
  choose n hn using fun z : zs ↦ hd z z.property
  let ys : Finset (K ⊗[k] F) := insert (d : K ⊗[k] F) (Finset.univ.image n)
  let comm := Algebra.TensorProduct.comm k K F
  obtain ⟨R, hR, hc, hy⟩ := exists_finite_constant_model c (ys.image comm)
  have := hR
  let T := F ⊗[k] R
  let χ : T →ₐ[k] K ⊗[k] F := comm.symm.toAlgHom.comp (baseChangeIncl F R)
  have hχ : Function.Injective χ := comm.symm.injective.comp (baseChangeIncl_injective R)
  have hy' (y : K ⊗[k] F) (hyz : y ∈ ys) : y ∈ χ.range := by
    obtain ⟨w, hw⟩ := hy (comm y) (Finset.mem_image_of_mem comm hyz)
    exact ⟨w, congrArg comm.symm hw |>.trans (comm.symm_apply_apply y)⟩
  obtain ⟨dR, hdR⟩ := hy' d (Finset.mem_insert_self _ _)
  change χ dR = (d : K ⊗[k] F) at hdR
  let ν : T →ₐ[k] E := (IsScalarTower.toAlgHom k (K ⊗[k] F) E).comp χ
  have hν : Function.Injective ν :=
    (IsFractionRing.injective (K ⊗[k] F) E).comp hχ
  have hdE : ν dR ≠ 0 := by
    change algebraMap (K ⊗[k] F) E (χ dR) ≠ 0
    rw [hdR]
    simpa only [map_zero] using
      (IsFractionRing.injective (K ⊗[k] F) E).ne_iff.mpr (nonZeroDivisors.ne_zero d.property)
  have hdR0 : dR ≠ 0 := fun hz ↦ hdE (hz ▸ map_zero ν)
  let L := Localization.Away dR
  let i : L →ₐ[k] E := IsLocalization.Away.liftAlgHom dR (f := ν) (isUnit_iff_ne_zero.mpr hdE)
  have himap (x : T) : i (algebraMap T L x) = ν x :=
    IsLocalization.Away.lift_eq dR (g := ν.toRingHom) (isUnit_iff_ne_zero.mpr hdE) x
  have hi : Function.Injective i := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers dR)
      i.toRingHom).2
    intro x y
    constructor
    · intro h
      change i (algebraMap T L x) = i (algebraMap T L y)
      exact congrArg i h
    · intro h
      change i (algebraMap T L x) = i (algebraMap T L y) at h
      rw [himap, himap] at h
      exact congrArg (algebraMap T L) (hν h)
  have hinv : i (IsLocalization.Away.invSelf dR : L) = (ν dR)⁻¹ := by
    apply mul_right_cancel₀ hdE
    rw [inv_mul_cancel₀ hdE]
    calc
      i (IsLocalization.Away.invSelf dR : L) * ν dR =
          i ((IsLocalization.Away.invSelf dR : L) * algebraMap T L dR) := by
            rw [map_mul, himap]
      _ = i 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
      _ = 1 := map_one i
  have hz (z : zs) : (z : E) ∈ i.range := by
    obtain ⟨a, ha⟩ := hy' (n z) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem n
      (Finset.mem_univ z)))
    change χ a = n z at ha
    refine ⟨algebraMap T L a * IsLocalization.Away.invSelf dR, ?_⟩
    rw [map_mul]
    change i (algebraMap T L a) * i (IsLocalization.Away.invSelf dR) = z
    rw [himap, hinv]
    change algebraMap (K ⊗[k] F) E (χ a) * (ν dR)⁻¹ = z
    rw [ha, hn z, Algebra.smul_def]
    change algebraMap (K ⊗[k] F) E d * (z : E) * (ν dR)⁻¹ = z
    have hvd : algebraMap (K ⊗[k] F) E d = ν dR := by
      change _ = algebraMap (K ⊗[k] F) E (χ dR)
      rw [hdR]
    rw [hvd, mul_comm (ν dR), mul_assoc, mul_inv_cancel₀ hdE, mul_one]
  obtain ⟨φ, hφ⟩ := exists_tensor_specialization dR hdR0
  let g : T →ₐ[k] F := (Algebra.TensorProduct.rid k k F).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k F) φ)
  have hgd : g dR ≠ 0 := by
    intro h
    apply hφ
    apply (Algebra.TensorProduct.rid k k F).injective
    change (Algebra.TensorProduct.rid k k F)
      (Algebra.TensorProduct.map (AlgHom.id k F) φ dR) = 0 at h
    simpa only [map_zero] using h
  let f : L →ₐ[k] F := IsLocalization.Away.liftAlgHom dR (f := g) (isUnit_iff_ne_zero.mpr hgd)
  have hfmap (x : T) : f (algebraMap T L x) = g x :=
    IsLocalization.Away.lift_eq dR (g := g.toRingHom) (isUnit_iff_ne_zero.mpr hgd) x
  let e := AlgEquiv.ofInjective i hi
  let ψ : i.range →ₐ[k] F := f.comp e.symm.toAlgHom
  have hψ (w : L) : ψ (e w) = f w := by
    change f (e.symm (e w)) = f w
    rw [e.symm_apply_apply]
  refine ⟨i.range, ψ, fun z hz' ↦ hz ⟨z, hz'⟩, ?_, ?_⟩
  · intro x
    let w : L := algebraMap T L (x ⊗ₜ[k] (1 : R))
    have hw : i w = eF x := by
      rw [himap]
      change algebraMap (K ⊗[k] F) E
        ((Algebra.TensorProduct.comm k K F).symm (baseChangeIncl F R (x ⊗ₜ[k] 1))) =
          algebraMap (K ⊗[k] F) E (1 ⊗ₜ[k] x)
      rw [baseChangeIncl_tmul, Algebra.TensorProduct.comm_symm,
        Algebra.TensorProduct.comm_tmul]
      rfl
    refine ⟨⟨w, hw⟩, ?_⟩
    have hs : (⟨eF x, ⟨w, hw⟩⟩ : i.range) = e w := Subtype.ext hw.symm
    rw [hs, hψ, hfmap]
    change (Algebra.TensorProduct.rid k k F)
      (Algebra.TensorProduct.map (AlgHom.id k F) φ (x ⊗ₜ[k] 1)) = x
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply, map_one, Algebra.TensorProduct.rid_tmul, one_smul]
  · intro a ha
    let r : R := ⟨a, hc a ha⟩
    let w : L := algebraMap T L ((1 : F) ⊗ₜ[k] r)
    have hw : i w = algebraMap K E a := by
      rw [himap]
      change algebraMap (K ⊗[k] F) E
        ((Algebra.TensorProduct.comm k K F).symm (baseChangeIncl F R (1 ⊗ₜ[k] r))) =
          algebraMap (K ⊗[k] F) E (a ⊗ₜ[k] 1)
      rw [baseChangeIncl_tmul, Algebra.TensorProduct.comm_symm,
        Algebra.TensorProduct.comm_tmul]
    refine ⟨⟨w, hw⟩, φ r, ?_⟩
    have hs : (⟨algebraMap K E a, ⟨w, hw⟩⟩ : i.range) = e w := Subtype.ext hw.symm
    rw [hs, hψ, hfmap]
    change algebraMap k F (φ r) = (Algebra.TensorProduct.rid k k F)
      (Algebra.TensorProduct.map (AlgHom.id k F) φ (1 ⊗ₜ[k] r))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul]
    simp only [Algebra.smul_def, mul_one]

/-- Rationality of a one-variable field over an algebraically closed base descends from
any constant extension. The finite coefficient model and specialization are constructed
internally. Named consumer: original-base genus of an actual regular affine action. -/
theorem exists_generator_of_tensor_generator {F K : Type*} [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsFunctionFieldOneVar k F]
    (h : ∃ u : FractionRing (K ⊗[k] F), Transcendental K u ∧
      IntermediateField.adjoin K ({u} : Set (FractionRing (K ⊗[k] F))) = ⊤) :
    ∃ t : F, Transcendental k t ∧ IntermediateField.adjoin k ({t} : Set F) = ⊤ := by
  classical
  let E := FractionRing (K ⊗[k] F)
  let eF : F →ₐ[k] E := (IsScalarTower.toAlgHom k (K ⊗[k] F) E).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨x, hx, hfin⟩ := IsFunctionFieldOneVar.exists_transcendental_finite (k := k) (F := F)
  have : Algebra.EssFiniteType k (IntermediateField.adjoin k ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have := hfin
  have : Algebra.EssFiniteType (IntermediateField.adjoin k ({x} : Set F)) F := inferInstance
  have : Algebra.EssFiniteType k F :=
    Algebra.EssFiniteType.comp k (IntermediateField.adjoin k ({x} : Set F)) F
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k F
  obtain ⟨u, _, hu⟩ := h
  have hrat (a : F) : ∃ p q : K[X], Polynomial.aeval u q ≠ 0 ∧
      eF a = Polynomial.aeval u p / Polynomial.aeval u q := by
    by_cases ha : a = 0
    · exact ⟨0, 1, by simp, by simp [ha]⟩
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K (eF a)).1
      (by rw [hu]; trivial)
    have hq : Polynomial.aeval u q ≠ 0 := by
      intro hq
      rw [hq, div_zero] at hpq
      apply ha
      apply eF.toRingHom.injective
      change eF a = eF 0
      simpa only [map_zero] using hpq
    exact ⟨p, q, hq, hpq⟩
  choose p q hq hpq using fun a : s ↦ hrat a
  let c : Finset K := Finset.univ.biUnion fun a : s ↦ (p a).coeffs ∪ (q a).coeffs
  let zs : Finset E := insert u (Finset.univ.image fun a : s ↦ (Polynomial.aeval u (q a))⁻¹)
  obtain ⟨S, ψ, hz, hF, hC⟩ := exists_finite_specialization c zs
  have huS : u ∈ S := hz u (Finset.mem_insert_self _ _)
  let uS : S := ⟨u, huS⟩
  let t : F := ψ uS
  let D := IntermediateField.adjoin k ({t} : Set F)
  let B : Subalgebra k E := (D.toSubalgebra.comap ψ).map S.val
  have hB {z : E} (hzS : z ∈ S) : z ∈ B ↔ ψ ⟨z, hzS⟩ ∈ D := by
    constructor
    · rintro ⟨w, hw, heq⟩
      change ψ w ∈ D at hw
      have hwz : w = ⟨z, hzS⟩ := Subtype.ext heq
      simpa only [hwz] using hw
    · intro hw
      exact ⟨⟨z, hzS⟩, hw, rfl⟩
  have hBS : B ≤ S := by
    rintro z ⟨w, _, rfl⟩
    exact w.property
  have huB : u ∈ B := (hB huS).2 (IntermediateField.subset_adjoin k _ rfl)
  have hcB (a : K) (ha : a ∈ c) : algebraMap K E a ∈ B := by
    obtain ⟨haS, haψ⟩ := hC a ha
    apply (hB haS).2
    obtain ⟨b, hb⟩ := haψ
    rw [← hb]
    exact D.algebraMap_mem b
  have heval (p : K[X]) (hp : p.coeffs ⊆ c) : Polynomial.aeval u p ∈ B := by
    rw [Polynomial.aeval_eq_sum_range]
    apply B.sum_mem
    intro j _
    rw [Algebra.smul_def]
    apply B.mul_mem ?_ (B.pow_mem huB j)
    by_cases hj : p.coeff j = 0
    · rw [hj, map_zero]
      exact B.zero_mem
    · exact hcB _ (hp (Polynomial.coeff_mem_coeffs hj))
  have hgens (a : s) : (a : F) ∈ D := by
    have hpB : Polynomial.aeval u (p a) ∈ B := heval _ fun b hb ↦
      Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, Finset.mem_union_left _ hb⟩
    have hqB : Polynomial.aeval u (q a) ∈ B := heval _ fun b hb ↦
      Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, Finset.mem_union_right _ hb⟩
    have hqS : Polynomial.aeval u (q a) ∈ S := hBS hqB
    have hqiS : (Polynomial.aeval u (q a))⁻¹ ∈ S := hz _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
    let qS : S := ⟨Polynomial.aeval u (q a), hqS⟩
    let qiS : S := ⟨(Polynomial.aeval u (q a))⁻¹, hqiS⟩
    have hprod : qiS * qS = 1 := Subtype.ext (inv_mul_cancel₀ (hq a))
    have hψprod : ψ qiS * ψ qS = 1 := by
      rw [← map_mul ψ, hprod, map_one ψ]
    have hψq : ψ qS ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hψprod
      exact zero_ne_one hψprod
    have hψqi : ψ qiS = (ψ qS)⁻¹ := (mul_eq_one_iff_eq_inv₀ hψq).1 hψprod
    have hqiB : (Polynomial.aeval u (q a))⁻¹ ∈ B := by
      apply (hB hqiS).2
      change ψ qiS ∈ D
      rw [hψqi]
      exact D.inv_mem ((hB hqS).1 hqB)
    have haB : eF (a : F) ∈ B := by
      rw [hpq a, div_eq_mul_inv]
      exact B.mul_mem hpB hqiB
    obtain ⟨haS, hψa⟩ := hF (a : F)
    have haD := (hB haS).1 haB
    rw [hψa] at haD
    exact haD
  have htop : D = ⊤ := by
    apply top_unique
    rw [← hs]
    apply IntermediateField.adjoin_le_iff.2
    intro a ha
    exact hgens ⟨a, ha⟩
  refine ⟨t, ?_, htop⟩
  intro ht
  have : Algebra.IsAlgebraic k D := IntermediateField.isAlgebraic_adjoin_simple ht.isIntegral
  have hbot : D = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic D
  have hxbot : x ∈ (⊥ : IntermediateField k F) := by
    rw [← hbot, htop]
    trivial
  obtain ⟨b, hb⟩ := (IntermediateField.mem_bot).1 hxbot
  apply hx
  rw [← hb]
  exact isAlgebraic_algebraMap b

/-- Genus zero descends from a canonical constant extension over algebraically closed fields.
The one-variable instances are explicit here; the actual scheme consumer derives them. -/
theorem genus_eq_zero_of_tensor {F K : Type*} [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsFunctionFieldOneVar k F] [IsAlgClosed K]
    [IsFunctionFieldOneVar K (FractionRing (K ⊗[k] F))]
    (h : genus K (FractionRing (K ⊗[k] F)) = 0) : genus k F = 0 := by
  apply genus_eq_zero_iff_exists_generator.2
  exact exists_generator_of_tensor_generator (genus_eq_zero_iff_exists_generator.1 h)

end

end AclGeom.RationalityDescent
