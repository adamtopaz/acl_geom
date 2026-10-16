/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.FunctionField
import GroupConfig.Germ.Rationality

/-!
# The action of a Hrushovski–Weil group on the function field of a curve

A representative `r` of a germ of the locus of `v` with exponent zero is a tuple of fractions
`num_i / den_i` of polynomials over a small field. Substituting these fractions for the
coordinates gives a `K`-algebra endomorphism `Representative.subst` of the function field
`LocusFunctionField k v`: the kernel of the substitution on `K[X]` is exactly the locus ideal,
in both directions, by evaluation at generic points. The endomorphism depends only on the
germ (`Representative.subst_eq_of_equivalent`), is contravariant for composition
(`Representative.subst_comp`), is the identity on the identity germ, and is the identity only
for the identity germ (`Representative.equivalent_id_of_subst_eq_id`).

By the rationality of Hrushovski–Weil germs on curves
(`GroupConfig.Germ.IsHW.exists_rational_representative`), every member of the group
`hw.prodSubgroup` has a representative with exponent zero. Substituting a representative of
the inverse gives a faithful action by `K`-algebra automorphisms of the function field
(`GroupConfig.Germ.IsHW.functionFieldAction`, `functionFieldAction_injective`), with the
generator formula `functionFieldAction_coord` for every such representative.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the faithful function-field action is proved. `CurveGenus` proves genus zero
when the ordinary canonical-base rank is at least two; `MoebiusAction` gives its fractional
linear expression in a generator. Connected-subgroup and affine classification, the original
scheme/action bridge and chart coordinates remain separate targets.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set LocusFunctionField

noncomputable section

/-! ### Substituting fractions -/

private theorem map_substFrac {ι L L' : Type*} [Field L] [Field L'] (φ : L →+* L') {κ : Type*}
    [Fintype κ] (N : MvPolynomial κ L) (P Q : κ → MvPolynomial ι L) (d : ℕ) :
    MvPolynomial.map φ (substFrac N P Q d) =
      substFrac (MvPolynomial.map φ N) (fun j ↦ MvPolynomial.map φ (P j))
        (fun j ↦ MvPolynomial.map φ (Q j)) d := by
  simp only [substFrac, map_sum, map_mul, map_C, map_prod, map_pow,
    support_map_of_injective _ φ.injective, coeff_map]

private theorem totalDegree_map_le {ι L L' : Type*} [CommSemiring L] [CommSemiring L']
    (φ : L →+* L') (P : MvPolynomial ι L) :
    (MvPolynomial.map φ P).totalDegree ≤ P.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset _ _)

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

namespace Representative

variable (r : Representative k K v v)

/-- The substitution `X i ↦ num_i / den_i` of the fractions of `r` into polynomials over
`K`, with values in the function field. -/
private def substPoly : MvPolynomial ι K →ₐ[K] LocusFunctionField k v :=
  aeval fun i ↦ LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.num i)) /
    LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.den i))

/-- The denominators of `r`, over a field containing the field of `r`. -/
private def denIn {M : IntermediateField k K} (hrM : r.M ≤ M) (i : ι) : MvPolynomial ι M :=
  MvPolynomial.map (IntermediateField.inclusion hrM).toRingHom (r.f.den i)

/-- The numerators of `r`, over a field containing the field of `r`. -/
private def numIn {M : IntermediateField k K} (hrM : r.M ≤ M) (i : ι) : MvPolynomial ι M :=
  MvPolynomial.map (IntermediateField.inclusion hrM).toRingHom (r.f.num i)

private theorem mk_den_ne_zero (i : ι) :
    LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.den i)) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall v
  exact mk_map_ne_zero hy (r.isDefinedAt y hy i)

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] in
private theorem aeval_denIn_ne_zero {M : IntermediateField k K} (hrM : r.M ≤ M) {y : ι → K}
    (hy : IsGenericOver r.M v y) (i : ι) : aeval y (r.denIn hrM i) ≠ 0 := by
  rw [denIn, aeval_map_inclusion]
  exact r.isDefinedAt y hy i

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] in
private theorem aeval_prod_denIn_ne_zero [Fintype ι] {M : IntermediateField k K}
    (hrM : r.M ≤ M) {y : ι → K} (hy : IsGenericOver r.M v y) (D : ℕ) :
    aeval y (∏ i, r.denIn hrM i ^ D) ≠ 0 := by
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ by
    rw [map_pow]
    exact pow_ne_zero _ (r.aeval_denIn_ne_zero hrM hy i)

/-- Clearing denominators: `subst(P) * ∏ den^D` is the class of `substFrac`. -/
private theorem substPoly_mul_eq [Fintype ι] {M : IntermediateField k K} (hrM : r.M ≤ M)
    (P : MvPolynomial ι M) {D : ℕ} (hD : P.totalDegree ≤ D) :
    r.substPoly (MvPolynomial.map (algebraMap M K) P) *
        LocusFunctionField.mk k v (MvPolynomial.map (algebraMap M K) (∏ i, r.denIn hrM i ^ D)) =
      LocusFunctionField.mk k v
        (MvPolynomial.map (algebraMap M K) (substFrac P (r.numIn hrM) (r.denIn hrM) D)) := by
  have hden : ∀ i, aeval (coord k v)
      (MvPolynomial.map (algebraMap M K) (r.denIn hrM i)) ≠ 0 := fun i ↦ by
    rw [denIn, map_map_inclusion, aeval_coord]
    exact r.mk_den_ne_zero i
  conv_rhs => rw [map_substFrac, ← aeval_coord,
    aeval_substFrac ((totalDegree_map_le _ P).trans hD) _ _ hden]
  simp only [numIn, denIn, map_map_inclusion, aeval_coord, map_prod, map_pow]
  rfl

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] in
/-- The value of `substFrac` at a generic point. -/
private theorem aeval_substFrac_eq [Fintype ι] (hr : r.f.e = 0) {M : IntermediateField k K}
    (hrM : r.M ≤ M) {y : ι → K} (hy : IsGenericOver r.M v y) (P : MvPolynomial ι M) {D : ℕ}
    (hD : P.totalDegree ≤ D) :
    aeval y (substFrac P (r.numIn hrM) (r.denIn hrM) D) =
      aeval (r.f.eval y) P * aeval y (∏ i, r.denIn hrM i ^ D) := by
  have hden : ∀ i, aeval y (r.denIn hrM i) ≠ 0 := r.aeval_denIn_ne_zero hrM hy
  have hfun : (fun i ↦ aeval y (r.numIn hrM i) / aeval y (r.denIn hrM i)) = r.f.eval y := by
    funext i
    rw [QuasiRational.eval_apply, hr, pRoot_zero, numIn, denIn, aeval_map_inclusion,
      aeval_map_inclusion]
  rw [aeval_substFrac hD _ _ hden, hfun, map_prod]
  simp only [map_pow]

/-- The kernel of the substitution is exactly the locus ideal. -/
private theorem substPoly_eq_zero_iff (hr : r.f.e = 0) (P : MvPolynomial ι K) :
    r.substPoly P = 0 ↔ P ∈ locusIdeal k v := by
  have := Fintype.ofFinite ι
  set M := racl k ((r.M : Set K) ∪ ↑P.coeffs)
  have hM : IsAlgClosed ↥M := isAlgClosed_racl _
  have hMs : IsSmall k (M : Set K) :=
    (r.isSmall.union (IsSmall.of_finite P.coeffs.finite_toSet)).racl
  have hrM : r.M ≤ M := subset_union_left.trans (subset_racl k _)
  obtain ⟨P₀, hP₀⟩ : P ∈ range (MvPolynomial.map (algebraMap M K)) :=
    mem_range_map_iff_coeffs_subset.mpr fun c hc ↦ ⟨⟨c, subset_racl k _ (Or.inr hc)⟩, rfl⟩
  rw [← hP₀]
  obtain ⟨y, hy⟩ := exists_isGenericOver hMs v
  have hz : IsGenericOver M v (r.f.eval y) := by
    have := (r.extend hM hMs hrM).isGenericOver y hy
    rwa [extend_eval] at this
  have hyr : IsGenericOver r.M v y := hy.of_le hrM
  have hprod : aeval y (∏ i, r.denIn hrM i ^ P₀.totalDegree) ≠ 0 :=
    r.aeval_prod_denIn_ne_zero hrM hyr _
  have heq := r.substPoly_mul_eq hrM P₀ le_rfl
  rw [map_mem_locusIdeal_iff_aeval hz]
  constructor
  · intro h0
    rw [h0, zero_mul, eq_comm, mk_map_eq_zero_iff hy, r.aeval_substFrac_eq hr hrM hyr P₀ le_rfl,
      mul_eq_zero] at heq
    exact heq.resolve_right hprod
  · intro h0
    have hmk : LocusFunctionField.mk k v (MvPolynomial.map (algebraMap M K)
        (∏ i, r.denIn hrM i ^ P₀.totalDegree)) ≠ 0 := mk_map_ne_zero hy hprod
    rw [(mk_map_eq_zero_iff hy (substFrac P₀ (r.numIn hrM) (r.denIn hrM) P₀.totalDegree)).2
      (by rw [r.aeval_substFrac_eq hr hrM hyr P₀ le_rfl, h0, zero_mul])] at heq
    exact (mul_eq_zero.1 heq).resolve_right hmk

/-- The `K`-algebra endomorphism of the function field given by substituting the fractions
of a representative with exponent zero. -/
def subst (hr : r.f.e = 0) : LocusFunctionField k v →ₐ[K] LocusFunctionField k v :=
  IsFractionRing.liftAlgHom (A := MvPolynomial ι K ⧸ locusIdeal k v)
    (g := Ideal.Quotient.liftₐ (locusIdeal k v) r.substPoly fun P hP ↦
      (r.substPoly_eq_zero_iff hr P).2 hP) (by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
      change r.substPoly P = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((r.substPoly_eq_zero_iff hr P).1 hx))

private theorem subst_mk (hr : r.f.e = 0) (P : MvPolynomial ι K) :
    r.subst hr (LocusFunctionField.mk k v P) = r.substPoly P := by
  rw [subst, IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap (MvPolynomial ι K ⧸ locusIdeal k v) _
    (Ideal.Quotient.mk _ P)) = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- The substitution sends each coordinate to the corresponding fraction of `r`. -/
theorem subst_coord (hr : r.f.e = 0) (i : ι) :
    r.subst hr (coord k v i) =
      LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.num i)) /
        LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.den i)) := by
  rw [coord, subst_mk, substPoly, aeval_X]

/-- The value of a substituted element at `y` is the value of the element at `r(y)`. -/
private theorem hasValue_subst (hr : r.f.e = 0) {M : IntermediateField k K} (hrM : r.M ≤ M)
    {y : ι → K} (hy : IsGenericOver M v y) {h : LocusFunctionField k v} {c : K}
    (hh : HasValue M (r.f.eval y) h c) : HasValue M y (r.subst hr h) c := by
  have := Fintype.ofFinite ι
  obtain ⟨A, B, hB, rfl, rfl⟩ := hh
  have hyr : IsGenericOver r.M v y := hy.of_le hrM
  set D := max A.totalDegree B.totalDegree
  have hprod : aeval y (∏ i, r.denIn hrM i ^ D) ≠ 0 := r.aeval_prod_denIn_ne_zero hrM hyr D
  have hmk := mk_map_ne_zero hy hprod
  have hA := r.substPoly_mul_eq hrM A (D := D) (le_max_left A.totalDegree B.totalDegree)
  have hB' := r.substPoly_mul_eq hrM B (D := D) (le_max_right A.totalDegree B.totalDegree)
  have hvA := r.aeval_substFrac_eq hr hrM hyr A (D := D) (le_max_left A.totalDegree B.totalDegree)
  have hvB := r.aeval_substFrac_eq hr hrM hyr B (D := D)
    (le_max_right A.totalDegree B.totalDegree)
  refine ⟨substFrac A (r.numIn hrM) (r.denIn hrM) D, substFrac B (r.numIn hrM) (r.denIn hrM) D,
    by rw [hvB]; exact mul_ne_zero hB hprod, ?_, ?_⟩
  · rw [map_div₀, subst_mk, subst_mk, ← hA, ← hB', mul_div_mul_right _ _ hmk]
  · rw [hvA, hvB, mul_div_mul_right _ _ hprod]

/-- The substitution depends only on the germ. -/
theorem subst_eq_of_equivalent {r r' : Representative k K v v} (hr : r.f.e = 0)
    (hr' : r'.f.e = 0) (h : r.Equivalent r') : r.subst hr = r'.subst hr' := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨N, hTN, hN, hNs, hval⟩ := exists_hasValue x (r.isSmall.union r'.isSmall)
  have _ : IsAlgClosed ↥N := hN
  have hrN : r.M ≤ N := fun z hz ↦ hTN (Or.inl hz)
  have hr'N : r'.M ≤ N := fun z hz ↦ hTN (Or.inr hz)
  obtain ⟨y, hy⟩ := exists_isGenericOver hNs v
  have hz : IsGenericOver N v (r.f.eval y) := by
    have := (r.extend hN hNs hrN).isGenericOver y hy
    rwa [extend_eval] at this
  obtain ⟨c, hc⟩ := hval _ hz
  have heq : r.f.eval y = r'.f.eval y :=
    h y (hy.of_le (racl_le_of_isAlgClosed (union_subset hrN hr'N)))
  exact HasValue.eq hy (r.hasValue_subst hr hrN hy hc) (r'.hasValue_subst hr' hr'N hy (heq ▸ hc))

omit [IsAlgClosed k] in
/-- A composite of representatives with exponent zero has exponent zero. -/
theorem comp_f_e_eq_zero {r r' : Representative k K v v} (hr : r.f.e = 0) (hr' : r'.f.e = 0) :
    (r'.comp r).f.e = 0 := by
  change r'.f.e + r.f.e = 0
  rw [hr, hr']

/-- The substitution is contravariant for composition. -/
theorem subst_comp {r r' : Representative k K v v} (hr : r.f.e = 0) (hr' : r'.f.e = 0) :
    (r'.comp r).subst (comp_f_e_eq_zero hr hr') = (r.subst hr).comp (r'.subst hr') := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨N, hTN, hN, hNs, hval⟩ := exists_hasValue x (r.isSmall.union r'.isSmall)
  have _ : IsAlgClosed ↥N := hN
  have hrN : r.M ≤ N := fun z hz ↦ hTN (Or.inl hz)
  have hr'N : r'.M ≤ N := fun z hz ↦ hTN (Or.inr hz)
  have hjN : joinField r' r ≤ N := racl_le_of_isAlgClosed (union_subset hrN hr'N)
  obtain ⟨y, hy⟩ := exists_isGenericOver hNs v
  have hz : IsGenericOver N v (r.f.eval y) := by
    have := (r.extend hN hNs hrN).isGenericOver y hy
    rwa [extend_eval] at this
  have hw : IsGenericOver N v (r'.f.eval (r.f.eval y)) := by
    have := (r'.extend hN hNs hr'N).isGenericOver _ hz
    rwa [extend_eval] at this
  obtain ⟨c, hc⟩ := hval _ hw
  have h1 := (r'.comp r).hasValue_subst (comp_f_e_eq_zero hr hr') hjN hy
    (by rwa [comp_eval r' r (hy.of_le hjN)])
  exact HasValue.eq hy h1 (r.hasValue_subst hr hrN hy (r'.hasValue_subst hr' hr'N hz hc))

/-- The identity germ substitutes trivially. -/
theorem subst_id : (Representative.id v).subst (k := k) rfl = AlgHom.id K _ := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨N, hTN, hN, hNs, hval⟩ := exists_hasValue x (Representative.id (k := k) v).isSmall
  obtain ⟨y, hy⟩ := exists_isGenericOver hNs v
  obtain ⟨c, hc⟩ := hval y hy
  have heval : (Representative.id (k := k) v).f.eval y = y := QuasiRational.id_eval y
  exact HasValue.eq hy ((Representative.id v).hasValue_subst rfl hTN hy
    (by rw [heval]; exact hc)) hc

/-- Only the identity germ substitutes trivially. -/
theorem equivalent_id_of_subst_eq_id (hr : r.f.e = 0) (h : r.subst hr = AlgHom.id K _) :
    r.Equivalent (Representative.id v) := by
  intro y hy
  have hN : IsAlgClosed ↥(racl k ((r.M : Set K) ∪ (Representative.id (k := k) v).M)) :=
    isAlgClosed_racl _
  have hNs : IsSmall k ((racl k ((r.M : Set K) ∪ (Representative.id (k := k) v).M) :
      IntermediateField k K) : Set K) := (r.isSmall.union (Representative.id v).isSmall).racl
  have hrN : r.M ≤ racl k ((r.M : Set K) ∪ (Representative.id (k := k) v).M) :=
    subset_union_left.trans (subset_racl k _)
  rw [show (Representative.id (k := k) v).f.eval y = y from QuasiRational.id_eval y]
  funext i
  have h1 := r.hasValue_subst hr hrN hy (hasValue_coord (k := k) (v := v) i)
  rw [h, AlgHom.id_apply] at h1
  exact HasValue.eq_value hy h1 (hasValue_coord i)

end Representative

/-! ### The action of the Hrushovski–Weil group -/

namespace Germ.IsHW

variable {g₀ : Germ k v v} (hw : IsHW g₀) (hv : erk k ∅ (range v) = 1)
include hw hv

private theorem exists_rep (δ : ↥hw.prodSubgroup) :
    ∃ r : Representative k K v v,
      (⟦r⟧ : Germ k v v) = ((δ : (Germ k v v)ˣ) : Germ k v v) ∧ r.f.e = 0 :=
  hw.exists_rational_representative hv (hw.mem_prodSubgroup.1 δ.2)

/-- The substitution of an exponent-zero representative of a member of the group. -/
private def substOf (δ : ↥hw.prodSubgroup) :
    LocusFunctionField k v →ₐ[K] LocusFunctionField k v :=
  (Classical.choose (hw.exists_rep hv δ)).subst (Classical.choose_spec (hw.exists_rep hv δ)).2

private theorem substOf_eq (δ : ↥hw.prodSubgroup) {r : Representative k K v v}
    (hr : r.f.e = 0) (hrδ : (⟦r⟧ : Germ k v v) = ((δ : (Germ k v v)ˣ) : Germ k v v)) :
    hw.substOf hv δ = r.subst hr :=
  Representative.subst_eq_of_equivalent _ _
    (Quotient.exact ((Classical.choose_spec (hw.exists_rep hv δ)).1.trans hrδ.symm))

private theorem substOf_mul (δ₁ δ₂ : ↥hw.prodSubgroup) :
    hw.substOf hv (δ₁ * δ₂) = (hw.substOf hv δ₂).comp (hw.substOf hv δ₁) := by
  obtain ⟨h₁, h₁e⟩ := Classical.choose_spec (hw.exists_rep hv δ₁)
  obtain ⟨h₂, h₂e⟩ := Classical.choose_spec (hw.exists_rep hv δ₂)
  have hprod : (⟦(Classical.choose (hw.exists_rep hv δ₁)).comp
      (Classical.choose (hw.exists_rep hv δ₂))⟧ : Germ k v v) =
        (((δ₁ * δ₂ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v) := by
    change Germ.comp (⟦Classical.choose (hw.exists_rep hv δ₁)⟧ : Germ k v v)
      ⟦Classical.choose (hw.exists_rep hv δ₂)⟧ = _
    rw [h₁, h₂]
    rfl
  rw [hw.substOf_eq hv (δ₁ * δ₂) (Representative.comp_f_e_eq_zero h₂e h₁e) hprod,
    Representative.subst_comp]
  rfl

private theorem substOf_one : hw.substOf hv 1 = AlgHom.id K _ := by
  rw [hw.substOf_eq hv 1 (r := Representative.id v) rfl rfl, Representative.subst_id]

/-- The faithful action of the Hrushovski–Weil group of a curve by `K`-algebra automorphisms
of the function field of the curve: a member `γ` acts by substituting a rational
representative of `γ⁻¹`. -/
def functionFieldAction :
    ↥hw.prodSubgroup →* (LocusFunctionField k v ≃ₐ[K] LocusFunctionField k v) where
  toFun γ := AlgEquiv.ofAlgHom (hw.substOf hv γ⁻¹) (hw.substOf hv γ)
    (by rw [← substOf_mul, mul_inv_cancel, substOf_one])
    (by rw [← substOf_mul, inv_mul_cancel, substOf_one])
  map_one' := AlgEquiv.ext fun x ↦ by
    change hw.substOf hv 1⁻¹ x = x
    rw [inv_one, substOf_one]
    rfl
  map_mul' γ δ := AlgEquiv.ext fun x ↦ by
    change hw.substOf hv (γ * δ)⁻¹ x = hw.substOf hv γ⁻¹ (hw.substOf hv δ⁻¹ x)
    rw [mul_inv_rev, substOf_mul]
    rfl

/-- The action of `γ` sends each coordinate to the corresponding fraction of ANY rational
representative of `γ⁻¹`. -/
theorem functionFieldAction_coord (γ : ↥hw.prodSubgroup) {r : Representative k K v v}
    (hr : r.f.e = 0)
    (hrγ : (⟦r⟧ : Germ k v v) = (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v))
    (i : ι) :
    hw.functionFieldAction hv γ (coord k v i) =
      LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.num i)) /
        LocusFunctionField.mk k v (MvPolynomial.map (algebraMap r.M K) (r.f.den i)) := by
  change hw.substOf hv γ⁻¹ (coord k v i) = _
  rw [hw.substOf_eq hv γ⁻¹ hr hrγ, Representative.subst_coord]

/-- The action of the Hrushovski–Weil group on the function field is faithful. -/
theorem functionFieldAction_injective : Function.Injective (hw.functionFieldAction hv) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ ↦ ?_
  obtain ⟨hr₁, hr₂⟩ := Classical.choose_spec (hw.exists_rep hv γ⁻¹)
  have hid : hw.substOf hv γ⁻¹ = AlgHom.id K _ := AlgHom.ext fun x ↦ by
    have := AlgEquiv.ext_iff.1 hγ x
    exact this
  have hequiv := (Classical.choose (hw.exists_rep hv γ⁻¹)).equivalent_id_of_subst_eq_id hr₂ hid
  have h1 : (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v) = 1 :=
    hr₁.symm.trans (Quotient.sound hequiv)
  have h2 : γ⁻¹ = 1 := Subtype.ext (Units.ext h1)
  exact inv_eq_one.1 h2

/-- **The action at generic points.** Let `r` be an exponent-zero representative of `γ⁻¹` and
let `y` be generic over a field `M ⊇ M_r`. If `h` has value `c` at `r(y)`, then `γ · h` has value
`c` at `y`. -/
theorem hasValue_functionFieldAction (γ : ↥hw.prodSubgroup) {r : Representative k K v v}
    (hr : r.f.e = 0)
    (hrγ : (⟦r⟧ : Germ k v v) = (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v))
    {M : IntermediateField k K} (hrM : r.M ≤ M) {y : ι → K} (hy : IsGenericOver M v y)
    {h : LocusFunctionField k v} {c : K} (hh : HasValue M (r.f.eval y) h c) :
    HasValue M y (hw.functionFieldAction hv γ h) c := by
  change HasValue M y (hw.substOf hv γ⁻¹ h) c
  rw [hw.substOf_eq hv γ⁻¹ hr hrγ]
  exact r.hasValue_subst hr hrM hy hh

end Germ.IsHW

end

end GroupConfig
